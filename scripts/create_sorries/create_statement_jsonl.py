"""
Build benchmark JSONL files from the LiveLeanTriathlon tree.

Three outputs are produced in this script's directory:

  statement.jsonl                  — "easy mode" — one row per `theorem`/`lemma`
                                     in the project. ``code`` is the file content
                                     from the top through the target declaration,
                                     with every preceding theorem/lemma's proof
                                     replaced by ``sorry``. Earlier declarations
                                     stay as ``lemma X ... := by sorry``, so the
                                     agent can either prove or treat them as
                                     black-box givens. When the target's file
                                     imports project-local sibling files (e.g.
                                     ``MainTheorem.lean`` importing
                                     ``BackgroundLemmas.lean``), their content
                                     with proofs sorry'd is included in an
                                     ``imported_file`` field.

  statements_hard.jsonl            — "hard mode" — one row per ``@[AMS ...]``-tagged
                                     theorem. ``code`` contains imports, opens,
                                     any earlier AMS-tagged theorems in the same
                                     file as ``axiom``s, and the target as
                                     ``theorem ... := by sorry``. No sublemmas;
                                     the agent must re-prove the main result.

  statements_autoformalization.jsonl — "autoformalization mode" — one row per
                                     ``@[AMS ...]``-tagged theorem. ``code``
                                     contains only imports, opens, and the target
                                     theorem (no preceding axioms or lemmas).
                                     Adds ``title``, ``informal_statement``, and
                                     ``informal_proof`` fields. ``title`` and
                                     ``informal_statement`` come from the
                                     surrounding ``\\begin{theorem}…\\end{theorem}``
                                     environment in the corresponding
                                     ``blueprint/src/theorems/*.tex`` file (located
                                     by ``\\lean{<name>}``). ``informal_proof``
                                     contains the full text of that ``.tex`` file,
                                     so the agent has the chapter's worth of
                                     context, not just the proof prose for one
                                     declaration.

Easy and hard rows use the schema::

    {"project_name": str, "name": str, "type": "theorem"|"lemma", "code": str}

Autoformalization rows extend it with ``title``, ``informal_statement``, and
``informal_proof``.

``code`` strings are normalized to be self-contained: project-specific imports
are collapsed to ``import Mathlib``, ``module`` / ``@[expose] public section``
directives and project attributes (``@[AMS ...]``, ``@[blueprint ...]``) are
stripped.
"""

import json
import re
from pathlib import Path

from scripts.create_sorries.create_sorries import (
    EMPTY_BLUEPRINT_FIELD_RE,
    NEWLINE_KEYS,
    SHARED_SUBDIRS,
    find_project_root,
)
from scripts.create_sorries.extract_sublemmas import (
    LeanCodeParser,
    add_newlines_before_keys,
    create_proof_with_sorries,
)

PROJECT_ATTRS = ("@[AMS", "@[blueprint")
IMPORT_LINE_RE = re.compile(r"^\s*(public\s+)?import\s+\S")
MODULE_DIRECTIVE_RE = re.compile(r"^\s*module(\s|$)")
EXPOSE_SECTION_RE = re.compile(r"^\s*@\[expose\]\s+public\s+section\s*$")


def _strip_project_attrs(text: str) -> str:
    """Strip ``@[AMS ...]`` and ``@[blueprint ...]`` decorators.

    Multi-line, with nested brackets, embedded docstrings, and string literals.
    Other attributes (``@[simp]``, ``@[ext]`` …) are left untouched.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        if any(text.startswith(prefix, i) for prefix in PROJECT_ATTRS):
            j = i + 2
            depth = 1
            while j < n and depth > 0:
                c = text[j]
                if c == '"':
                    j += 1
                    while j < n and text[j] != '"':
                        if text[j] == "\\" and j + 1 < n:
                            j += 2
                        else:
                            j += 1
                    j = min(j + 1, n)
                    continue
                if text.startswith("/--", j):
                    j += 3
                    ddepth = 1
                    while j < n and ddepth > 0:
                        if text.startswith("/-", j):
                            ddepth += 1
                            j += 2
                        elif text.startswith("-/", j):
                            ddepth -= 1
                            j += 2
                        else:
                            j += 1
                    continue
                if c == "[":
                    depth += 1
                elif c == "]":
                    depth -= 1
                j += 1
            while j < n and text[j] in " \t":
                j += 1
            if j < n and text[j] == "\n":
                j += 1
            i = j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def _replace_imports_with_mathlib(text: str) -> str:
    """Collapse every ``import`` / ``public import`` line to a single ``import Mathlib``."""
    lines = text.split("\n")
    out: list[str] = []
    inserted = False
    for line in lines:
        if IMPORT_LINE_RE.match(line):
            if not inserted:
                out.append("import Mathlib")
                inserted = True
            continue
        out.append(line)
    if not inserted:
        out = ["import Mathlib", ""] + out
    return "\n".join(out)


def _strip_module_mode(text: str) -> str:
    """Remove ``module`` directives and ``@[expose] public section`` lines."""
    lines = text.split("\n")
    out: list[str] = []
    for line in lines:
        if MODULE_DIRECTIVE_RE.match(line):
            continue
        if EXPOSE_SECTION_RE.match(line):
            continue
        out.append(line)
    return "\n".join(out)


def _normalize(text: str) -> str:
    text = _strip_project_attrs(text)
    text = _strip_module_mode(text)
    text = _replace_imports_with_mathlib(text)
    text = EMPTY_BLUEPRINT_FIELD_RE.sub("", text)
    text = add_newlines_before_keys(text, keys=NEWLINE_KEYS)
    return text


PROJECT_IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import\s+(LiveLeanTriathlon\.[\w.]+)"
)


def _module_to_path(module: str, src_root: Path) -> Path | None:
    """Map ``LiveLeanTriathlon.Foo.Bar`` to ``<src_root>/Foo/Bar.lean`` (or
    ``Foo/Bar/Foo/Bar.lean`` for nested layouts). Returns ``None`` if the file
    doesn't exist.
    """
    parts = module.split(".")
    if not parts or parts[0] != "LiveLeanTriathlon":
        return None
    rel = Path(*parts[1:]).with_suffix(".lean")
    candidate = src_root / rel
    return candidate if candidate.exists() else None


def _collect_project_imports(file_path: Path, src_root: Path) -> list[Path]:
    """Return the transitive set of project-local imports of ``file_path``,
    restricted to files in the *same project subdirectory* (same first path
    component under ``LiveLeanTriathlon/``). Returned in topological order with
    dependencies first.
    """
    rel = file_path.relative_to(src_root)
    if not rel.parts:
        return []
    project = rel.parts[0]
    project_prefix = f"LiveLeanTriathlon.{project}."

    visited: dict[Path, bool] = {}
    order: list[Path] = []

    def dfs(path: Path) -> None:
        if path in visited:
            return
        visited[path] = True
        for line in path.read_text(encoding="utf-8").splitlines():
            m = PROJECT_IMPORT_RE.match(line)
            if not m:
                continue
            module = m.group(1)
            if not module.startswith(project_prefix):
                continue
            dep = _module_to_path(module, src_root)
            if dep is None or dep == file_path or dep == path:
                continue
            dfs(dep)
        if path != file_path:
            order.append(path)

    dfs(file_path)
    return order


def _format_imported_file(text: str) -> str:
    """Strip imports/module/expose/project-attr lines and replace every proof
    with ``sorry``, leaving the surrounding declarations and comments intact.
    """
    text = create_proof_with_sorries(text, keys=["theorem", "lemma"])
    text = _strip_project_attrs(text)
    text = _strip_module_mode(text)
    lines = [ln for ln in text.split("\n") if not IMPORT_LINE_RE.match(ln)]
    text = "\n".join(lines)
    text = EMPTY_BLUEPRINT_FIELD_RE.sub("", text)
    return text.strip("\n")


def _build_imported_file(file_path: Path, src_root: Path) -> str:
    """Concatenate the formatted contents of every transitive project-local
    dependency of ``file_path``, separated by ``-- File: <module>`` markers.
    Returns ``""`` when there are no project-local imports.
    """
    deps = _collect_project_imports(file_path, src_root)
    if not deps:
        return ""
    chunks: list[str] = []
    for dep in deps:
        rel = dep.relative_to(src_root).with_suffix("")
        module = "LiveLeanTriathlon." + ".".join(rel.parts)
        body = _format_imported_file(dep.read_text(encoding="utf-8"))
        if body:
            chunks.append(f"-- File: {module}\n{body}")
    return "\n\n".join(chunks)


def build_easy_entries(
    text: str,
    project_name: str,
    file_path: Path | None = None,
    src_root: Path | None = None,
) -> list[dict]:
    """One entry per theorem/lemma in ``text``.

    When ``file_path`` and ``src_root`` are supplied, every entry from a file
    that imports project-local siblings (e.g. ``MainTheorem.lean`` importing
    ``BackgroundLemmas.lean``) gets an ``imported_file`` field carrying those
    siblings' content with proofs replaced by ``sorry``.
    """
    parser = LeanCodeParser(text)
    blocks = parser.extract_all_blocks(keys=["theorem", "lemma"], allow_overlap=False)
    imported = ""
    if file_path is not None and src_root is not None:
        imported = _build_imported_file(file_path, src_root)
    entries: list[dict] = []
    for block in blocks:
        snippet = "\n".join(parser.cleaned_lines[: block["end"] + 1])
        snippet = create_proof_with_sorries(snippet, keys=["theorem", "lemma"])
        snippet = _normalize(snippet)
        entry: dict = {
            "project_name": project_name,
            "name": block["info"]["name"],
            "type": block["key"],
            "code": snippet,
        }
        if imported:
            entry["imported_file"] = imported
        entries.append(entry)
    return entries


def build_hard_entries(text: str, project_name: str) -> list[dict]:
    """One entry per ``@[AMS]``-tagged theorem in ``text``.

    Earlier AMS-tagged theorems in the same file appear as ``axiom``s; sublemmas
    are dropped entirely.
    """
    parser = LeanCodeParser(text)
    blocks = parser.extract_all_blocks(keys=["theorem", "lemma"], allow_overlap=False)

    ams_blocks: list[dict] = []
    prev_end = -1
    for block in blocks:
        gap = parser.cleaned_lines[prev_end + 1 : block["start"]]
        if any("@[AMS" in line for line in gap):
            ams_blocks.append(block)
        prev_end = block["end"]

    if not ams_blocks:
        return []

    headers = parser.extract_headers()

    entries: list[dict] = []
    for i, target in enumerate(ams_blocks):
        parts: list[str] = []
        if headers["set_option_lines"]:
            parts.extend(headers["set_option_lines"])
            parts.append("")
        if headers["open_lines"]:
            parts.extend(headers["open_lines"])
            parts.append("")
        for prev in ams_blocks[:i]:
            parts.append(parser.block_to_axiom(prev))
            parts.append("")
        target_str = "\n".join(
            parser.cleaned_lines[target["start"] : target["end"] + 1]
        )
        target_str = create_proof_with_sorries(target_str, keys=["theorem", "lemma"])
        parts.append(target_str)

        code = _normalize("\n".join(parts))
        entries.append(
            {
                "project_name": project_name,
                "name": target["info"]["name"],
                "type": target["key"],
                "code": code,
            }
        )
    return entries


AMS_ATTR_RE = re.compile(r"@\[(?:[^\[\]]*?,\s*)?AMS\b")
NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+([\w.]+)\s*$")
NAMESPACE_END_RE = re.compile(r"^\s*end\s+([\w.]+)\s*$")
LEAN_REF_RE = re.compile(r"\\lean\{([^}]+)\}")


def _build_name_to_tex(tex_dir: Path) -> dict[str, Path]:
    """Map every name appearing in ``\\lean{...}`` to its containing ``.tex`` file.

    Comma-separated forms like ``\\lean{foo, bar}`` are split so each name maps
    individually. Last write wins on collisions; collisions are rare and noted
    in the audit.
    """
    name_to_tex: dict[str, Path] = {}
    for tex in sorted(tex_dir.rglob("*.tex")):
        text = tex.read_text(encoding="utf-8")
        for m in LEAN_REF_RE.finditer(text):
            for raw in m.group(1).split(","):
                bare = raw.strip()
                if bare:
                    name_to_tex[bare] = tex
    return name_to_tex


def _resolve_tex(
    name: str, namespaces: list[str], name_to_tex: dict[str, Path]
) -> Path | None:
    """Look up the .tex file for a Lean declaration.

    Tries the fully-qualified name (with current namespace prefix), then the
    bare name. Falls back to a suffix match against any registered key, which
    catches cases where the .tex labels a theorem with a different namespace
    prefix than the surrounding Lean ``namespace`` block.
    """
    if namespaces:
        full = ".".join([*namespaces, name])
        if full in name_to_tex:
            return name_to_tex[full]
    if name in name_to_tex:
        return name_to_tex[name]
    suffix = "." + name
    for key, path in name_to_tex.items():
        if key.endswith(suffix):
            return path
    return None


def _extract_env(tex: str, env: str, lean_name: str) -> str | None:
    """Return the body of the ``\\begin{<env>}…\\end{<env>}`` block whose
    ``\\lean{...}`` argument matches ``lean_name``. Strips ``\\label``,
    ``\\lean``, and ``\\uses`` metadata commands. Returns ``None`` if no such
    block exists.
    """
    pattern = re.compile(
        rf"\\begin\{{{env}\}}(?:\[[^\]]*\])?(.*?)\\end\{{{env}\}}",
        re.DOTALL,
    )
    for m in pattern.finditer(tex):
        body = m.group(1)
        if any(
            ref.strip() == lean_name or lean_name in (s.strip() for s in ref.split(","))
            for ref in LEAN_REF_RE.findall(body)
        ):
            cleaned = re.sub(
                r"^[ \t]*\\(?:label|lean|uses)\{[^}]*\}[ \t]*\r?\n",
                "",
                body,
                flags=re.MULTILINE,
            )
            return cleaned.strip()
    return None


def _extract_title(tex: str, env: str, lean_name: str, fallback_chapter: bool) -> str:
    """Optional ``\\begin{theorem}[Title]`` argument, falling back to the chapter
    title at the top of the file.
    """
    pattern = re.compile(
        rf"\\begin\{{{env}\}}\[([^\]]*)\](.*?)\\end\{{{env}\}}",
        re.DOTALL,
    )
    for m in pattern.finditer(tex):
        body = m.group(2)
        if any(
            ref.strip() == lean_name or lean_name in (s.strip() for s in ref.split(","))
            for ref in LEAN_REF_RE.findall(body)
        ):
            return m.group(1).strip()
    if fallback_chapter:
        m = re.search(r"\\chapter\{([^}]*)\}", tex)
        if m:
            return m.group(1).strip()
    return ""


def build_autoformalization_entries(
    text: str,
    project_name: str,
    name_to_tex: dict[str, Path],
) -> list[dict]:
    """One entry per ``@[AMS ...]``-tagged theorem in ``text``.

    ``code`` contains only imports, opens, and the target theorem with a
    ``sorry`` proof. ``title`` / ``informal_statement`` come from the matching
    ``\\begin{theorem}…\\end{theorem}`` environment in
    ``blueprint/src/theorems/<file>.tex`` (located via ``\\lean{<name>}``).
    ``informal_proof`` is the entire ``.tex`` file content, so the agent has the
    chapter-level context surrounding the target theorem.
    """
    parser = LeanCodeParser(text)
    blocks = parser.extract_all_blocks(keys=["theorem", "lemma"], allow_overlap=False)
    if not blocks:
        return []
    headers = parser.extract_headers()

    namespaces: list[str] = []
    cleaned = parser.cleaned_lines
    namespace_at_line: list[list[str]] = [[] for _ in cleaned]
    current: list[str] = []
    for idx, line in enumerate(cleaned):
        m_open = NAMESPACE_OPEN_RE.match(line)
        if m_open:
            current.append(m_open.group(1))
        m_close = NAMESPACE_END_RE.match(line)
        if m_close and current and current[-1] == m_close.group(1):
            current.pop()
        namespace_at_line[idx] = list(current)

    ams_blocks: list[dict] = []
    prev_end = -1
    for block in blocks:
        gap = cleaned[prev_end + 1 : block["start"]]
        if any(AMS_ATTR_RE.search(line) for line in gap):
            ams_blocks.append(block)
        prev_end = block["end"]

    if not ams_blocks:
        return []

    entries: list[dict] = []
    for target in ams_blocks:
        name = target["info"]["name"]
        if not name or name == "this":
            continue
        ns = (
            namespace_at_line[target["start"]]
            if target["start"] < len(namespace_at_line)
            else []
        )
        tex_path = _resolve_tex(name, ns, name_to_tex)
        full_name = ".".join([*ns, name]) if ns else name

        if tex_path is not None:
            tex_text = tex_path.read_text(encoding="utf-8")
            title = (
                _extract_title(tex_text, "theorem", name, fallback_chapter=False)
                or _extract_title(
                    tex_text, "theorem", full_name, fallback_chapter=False
                )
                or _extract_title(tex_text, "lemma", name, fallback_chapter=False)
                or _extract_title(tex_text, "lemma", full_name, fallback_chapter=False)
                or _extract_title(tex_text, "theorem", name, fallback_chapter=True)
            )
            informal_statement = (
                _extract_env(tex_text, "theorem", name)
                or _extract_env(tex_text, "theorem", full_name)
                or _extract_env(tex_text, "lemma", name)
                or _extract_env(tex_text, "lemma", full_name)
                or ""
            )
            informal_proof = tex_text
        else:
            title = ""
            informal_statement = ""
            informal_proof = ""

        target_str = "\n".join(cleaned[target["start"] : target["end"] + 1])
        target_str = create_proof_with_sorries(target_str, keys=["theorem", "lemma"])

        parts: list[str] = []
        if headers["set_option_lines"]:
            parts.extend(headers["set_option_lines"])
            parts.append("")
        if headers["open_lines"]:
            parts.extend(headers["open_lines"])
            parts.append("")
        parts.append(target_str)
        code = _normalize("\n".join(parts))

        entries.append(
            {
                "project_name": project_name,
                "name": name,
                "type": target["key"],
                "title": title,
                "informal_statement": informal_statement,
                "informal_proof": informal_proof,
                "code": code,
            }
        )
    return entries


def iter_lean_files(project_root: Path):
    """Yield every Lean file under ``LiveLeanTriathlon/`` excluding shared subdirs."""
    src = project_root / "LiveLeanTriathlon"
    for f in sorted(src.rglob("*.lean")):
        rel = f.relative_to(src)
        if rel.parts and rel.parts[0] in SHARED_SUBDIRS:
            continue
        yield f


def write_jsonl(path: Path, entries: list[dict]) -> None:
    with open(path, "w", encoding="utf-8") as f:
        for entry in entries:
            f.write(json.dumps(entry, ensure_ascii=False) + "\n")


def main():
    project_root = find_project_root()
    out_dir = Path(__file__).parent
    name_to_tex = _build_name_to_tex(project_root / "blueprint" / "src" / "theorems")

    easy_entries: list[dict] = []
    hard_entries: list[dict] = []
    auto_entries: list[dict] = []

    src_root = project_root / "LiveLeanTriathlon"
    for f in iter_lean_files(project_root):
        text = f.read_text(encoding="utf-8")
        rel_parts = f.relative_to(src_root).parts
        project_name = rel_parts[0] if rel_parts else f.stem
        easy_entries.extend(
            build_easy_entries(text, project_name, file_path=f, src_root=src_root)
        )
        hard_entries.extend(build_hard_entries(text, project_name))
        auto_entries.extend(
            build_autoformalization_entries(text, project_name, name_to_tex)
        )

    easy_path = out_dir / "statement.jsonl"
    hard_path = out_dir / "statements_hard.jsonl"
    auto_path = out_dir / "statements_autoformalization.jsonl"
    write_jsonl(easy_path, easy_entries)
    write_jsonl(hard_path, hard_entries)
    write_jsonl(auto_path, auto_entries)

    print(f"Wrote {easy_path} ({len(easy_entries)} entries)")
    print(f"Wrote {hard_path} ({len(hard_entries)} entries)")
    print(f"Wrote {auto_path} ({len(auto_entries)} entries)")


if __name__ == "__main__":
    main()
