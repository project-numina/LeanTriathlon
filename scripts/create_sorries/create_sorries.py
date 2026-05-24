"""Generate benchmark variant directories from LiveLeanTriathlon/.

Variants:
    Sorry              - copy of LiveLeanTriathlon/ where every theorem/lemma
                         proof is replaced with `sorry`. Each project folder
                         keeps its single ``All.lean``.
    Easy               - derived from Sorry. Each project folder's ``All.lean``
                         is split into ``Background.lean`` (everything except
                         the final theorem) and ``MainTheorem.lean`` (the final
                         theorem only); ``MainTheorem.lean`` imports
                         ``Background.lean``.
    Hard               - derived from Sorry. Each project folder's ``All.lean``
                         is collapsed to ``MainTheorem.lean`` containing only
                         the definitions, opens/section scaffolding, and the
                         final theorem; all non-final lemmas/theorems are
                         removed.
    Autoformalization  - same as Hard, plus the corresponding
                         ``blueprint/src/theorems/<stem>.tex`` is copied into
                         each project folder.

In every variant the ``Mathlib/`` and ``Util/`` subdirectories are copied
unchanged (no proof transformation, no structural changes); only their imports
are rewritten so the variant tree is internally consistent.

Each variant gets a top-level index file at ``<root>/LiveLeanTriathlon<Variant>.lean``.

Usage:
    python3 scripts/create_sorries/create_sorries.py
    python3 scripts/create_sorries/create_sorries.py --variant Hard
"""

import argparse
import datetime
import re
import shutil
from pathlib import Path

from scripts.create_sorries.extract_sublemmas import (
    add_newlines_before_keys,
    create_proof_with_sorries,
)

VARIANTS = ["Sorry", "Easy", "Hard", "Autoformalization"]

# Subdirs whose contents are not transformed beyond import rewriting.
UNTOUCHED_SUBDIRS = ("Mathlib", "Util")

LOG_FILE = Path(__file__).parent / "create_sorries.log"

NEWLINE_KEYS = [
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "class",
    "variable",
    "open",
    "namespace",
    "set_option",
    "universe",
    "scoped",
    "section",
    "end",
    "structure",
    "inductive",
]

IMPORT_RE = re.compile(r"^(\s*)(public\s+)?import\s+(\S+)(.*)$")

EMPTY_BLUEPRINT_FIELD_RE = re.compile(r"\s*\((?:statement|proof)\s*:=\s*\)")

DECL_LINE_RE = re.compile(
    r"^(?P<indent>[ \t]*)"
    r"(?P<modifiers>(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|partial[ \t]+|unsafe[ \t]+|@\[expose\][ \t]+)*)"
    r"(?P<key>theorem|lemma|def|abbrev|structure|class|instance|inductive)[ \t]+"
    r"(?P<name>[\w.]+)"
)
NEEDED_COMMENT = "-- Needed for def"


# --------------------------------------------------------------------- log


def log_message(message: str) -> None:
    timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    with open(LOG_FILE, "a", encoding="utf-8") as f:
        f.write(f"[{timestamp}] {message}\n")


def find_project_root() -> Path:
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / "lean-toolchain").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with lean-toolchain file")


# --------------------------------------------------------------------- imports


def transform_imports(text: str, mapping: dict[str, str]) -> str:
    """Rewrite ``import`` and ``public import`` lines using ``mapping``.

    Each entry ``old -> new`` rewrites any import whose module path equals
    ``old`` or starts with ``old + '.'``. Imports unaffected by ``mapping``
    pass through unchanged.
    """
    out_lines: list[str] = []
    for line in text.split("\n"):
        m = IMPORT_RE.match(line)
        if not m:
            out_lines.append(line)
            continue
        indent, public, module_path, rest = (
            m.group(1),
            m.group(2) or "",
            m.group(3),
            m.group(4),
        )
        new_module = module_path
        # Apply longest-prefix-wins so e.g. a more specific mapping like
        # "LiveLeanTriathlon.X.All" beats "LiveLeanTriathlon".
        candidates = sorted(
            (k for k in mapping if module_path == k or module_path.startswith(k + ".")),
            key=len,
            reverse=True,
        )
        if candidates:
            k = candidates[0]
            new_module = mapping[k] + module_path[len(k) :]
        out_lines.append(f"{indent}{public}import {new_module}{rest}")
    return "\n".join(out_lines)


def rewrite_all_to_main(text: str, variant: str, project_folders: set[str]) -> str:
    """Rewrite ``LiveLeanTriathlon<Variant>.<Y>.All`` to
    ``LiveLeanTriathlon<Variant>.<Y>.MainTheorem`` in import lines, when ``<Y>`` is
    a project folder. Used by Easy/Hard/Autoformalization where each project
    folder no longer has an ``All.lean``."""
    prefix = f"LiveLeanTriathlon{variant}."
    out_lines: list[str] = []
    for line in text.split("\n"):
        m = IMPORT_RE.match(line)
        if not m:
            out_lines.append(line)
            continue
        indent, public, module_path, rest = (
            m.group(1),
            m.group(2) or "",
            m.group(3),
            m.group(4),
        )
        if module_path.startswith(prefix) and module_path.endswith(".All"):
            inner = module_path[len(prefix) : -len(".All")]
            if inner in project_folders:
                module_path = f"{prefix}{inner}.MainTheorem"
        out_lines.append(f"{indent}{public}import {module_path}{rest}")
    return "\n".join(out_lines)


# --------------------------------------------------------------------- proofs


def sorry_fy(text: str) -> str:
    """Replace every theorem/lemma proof with ``sorry``.

    ``create_proof_with_sorries`` runs through ``LeanCodeParser``, which strips
    all comments — including the leading ``/- … -/`` license block and the
    ``-- Needed for def`` annotations produced by
    ``scripts/mark_needed_for_def.py``. Both are restored afterwards so the
    information propagates to derived variant trees.
    """
    m = LICENSE_HEADER_RE.match(text)
    license_block = m.group(1) if m else ""
    needed = find_needed_decl_keys_and_names(text)

    text = create_proof_with_sorries(text, keys=["theorem", "lemma"])
    text = EMPTY_BLUEPRINT_FIELD_RE.sub("", text)
    text = add_newlines_before_keys(text, keys=NEWLINE_KEYS)
    if license_block and not text.lstrip().startswith("/-"):
        text = license_block + "\n\n" + text.lstrip()
    text = reannotate_needed_decls(text, needed)
    return text


# --------------------------------------------------------------------- declarations


DECORATOR_IN_RE = re.compile(
    r"^\s*(?:open|omit|attribute|set_option|include|variable)\b[^\n]*\bin\s*$"
)
BARE_MODIFIER_RE = re.compile(
    r"^\s*(?:private|protected|noncomputable|partial|unsafe)\s*$"
)


def find_decoration_start(lines: list[str], decl_idx: int) -> int:
    """Return the earliest line index that's part of the decorations preceding
    the declaration at ``decl_idx``: ``@[...]`` attributes (which may span
    multiple lines), ``/-- ... -/`` docstrings, and ``open X in`` prefixes."""
    j = decl_idx - 1
    start = decl_idx
    while j >= 0:
        s = lines[j].strip()
        if not s:
            j -= 1
            continue
        if s.startswith("@["):
            depth = lines[j].count("[") - lines[j].count("]")
            attr_start = j
            while depth > 0 and attr_start > 0:
                attr_start -= 1
                depth += lines[attr_start].count("[") - lines[attr_start].count("]")
            start = attr_start
            j = attr_start - 1
            continue
        if s.endswith("-/"):
            k = j
            while k >= 0 and "/--" not in lines[k]:
                k -= 1
            if k >= 0:
                start = k
                j = k - 1
                continue
            break
        if DECORATOR_IN_RE.match(lines[j]):
            start = j
            j -= 1
            continue
        if BARE_MODIFIER_RE.match(lines[j]):
            start = j
            j -= 1
            continue
        if s == NEEDED_COMMENT:
            start = j
            j -= 1
            continue
        break
    return start


def find_decl_block_end(lines: list[str], decl_idx: int) -> int:
    """Return the last line index belonging to the declaration block starting
    at ``decl_idx``.

    The block extends through:
    - every more-indented line (the proof body and continuations);
    - signature continuations at equal/lower indent that appear before the
      proof-introducing ``:=`` (e.g. wrapped parameter lists);
    - ``termination_by``/``decreasing_by`` clauses at the same indent.
    """
    decl_line = lines[decl_idx]
    base_indent = len(decl_line) - len(decl_line.lstrip())
    end = decl_idx
    walrus_seen = ":=" in decl_line
    k = decl_idx + 1
    while k < len(lines):
        line = lines[k]
        if not line.strip():
            k += 1
            continue
        line_indent = len(line) - len(line.lstrip())
        s = line.lstrip()
        if line_indent > base_indent:
            end = k
            if ":=" in line:
                walrus_seen = True
            k += 1
            continue
        if s.startswith("termination_by") or s.startswith("decreasing_by"):
            end = k
            k += 1
            continue
        if not walrus_seen:
            end = k
            if ":=" in line:
                walrus_seen = True
            k += 1
            continue
        break
    return end


def find_all_decls(text: str, keys: tuple[str, ...]) -> list[dict]:
    """Return ordered list of declarations matching any of ``keys``.

    Each entry has ``decl_line`` (line index of the keyword), ``start_line``
    (earliest decoration line), ``end_line`` (last proof/body line),
    ``key``, and ``name``.
    """
    lines = text.split("\n")
    decls: list[dict] = []
    i = 0
    while i < len(lines):
        m = DECL_LINE_RE.match(lines[i])
        if m and m.group("key") in keys:
            start_line = find_decoration_start(lines, i)
            end_line = find_decl_block_end(lines, i)
            decls.append(
                {
                    "decl_line": i,
                    "start_line": start_line,
                    "end_line": end_line,
                    "key": m.group("key"),
                    "name": m.group("name"),
                }
            )
            i = end_line + 1
        else:
            i += 1
    return decls


def has_needed_for_def_comment(body_lines: list[str], decl: dict) -> bool:
    """True if the decl's decoration block contains a ``-- Needed for def`` comment."""
    return any(
        body_lines[i].strip() == NEEDED_COMMENT
        for i in range(decl["start_line"], decl["decl_line"])
    )


def find_needed_decl_keys_and_names(text: str) -> set[tuple[str, str]]:
    """Return ``(key, name)`` for ``lemma``/``theorem`` declarations carrying
    a ``-- Needed for def`` comment."""
    lines = text.split("\n")
    return {
        (d["key"], d["name"])
        for d in find_all_decls(text, keys=("lemma", "theorem"))
        if has_needed_for_def_comment(lines, d)
    }


def reannotate_needed_decls(text: str, needed: set[tuple[str, str]]) -> str:
    """Insert ``-- Needed for def`` above each ``(key, name)`` in ``needed``
    whose block does not already carry the comment. Used after ``sorry_fy``
    strips comments so the source-file annotation propagates to derived
    variant trees."""
    if not needed:
        return text
    lines = text.split("\n")
    decls = find_all_decls(text, keys=("lemma", "theorem"))
    insertions: dict[int, str] = {}
    for d in decls:
        if (d["key"], d["name"]) not in needed:
            continue
        if has_needed_for_def_comment(lines, d):
            continue
        indent_match = re.match(r"^([ \t]*)", lines[d["decl_line"]])
        indent = indent_match.group(1) if indent_match else ""
        insertions[d["start_line"]] = f"{indent}{NEEDED_COMMENT}"
    if not insertions:
        return text
    out: list[str] = []
    for i, line in enumerate(lines):
        if i in insertions:
            out.append(insertions[i])
        out.append(line)
    return "\n".join(out)


# --------------------------------------------------------------------- file parsing


LICENSE_HEADER_RE = re.compile(r"\A\s*(/-.*?-/)", re.DOTALL)
EXPOSE_RE = re.compile(r"^\s*@\[expose\]\s+public\s+section\s*$")
MODULE_RE = re.compile(r"^\s*module\s*$")


def parse_all_lean(text: str) -> dict:
    """Return ``{license, header_lines, body_lines, body_start_line}``.

    ``license`` is the leading ``/- … -/`` block (without trailing newlines)
    or empty. ``header_lines`` is everything from start through the
    ``@[expose] public section`` line. ``body_lines`` is everything after.
    """
    m = LICENSE_HEADER_RE.match(text)
    license_header = m.group(1) if m else ""

    lines = text.split("\n")
    expose_idx = None
    for i, line in enumerate(lines):
        if EXPOSE_RE.match(line):
            expose_idx = i
            break

    if expose_idx is None:
        return {
            "license": license_header,
            "header_lines": lines,
            "body_lines": [],
            "body_start_line": len(lines),
        }
    return {
        "license": license_header,
        "header_lines": lines[: expose_idx + 1],
        "body_lines": lines[expose_idx + 1 :],
        "body_start_line": expose_idx + 1,
    }


# --------------------------------------------------------------------- copy


def copy_lean_tree(source: Path, target: Path) -> None:
    """Copy the entire ``source`` tree to ``target``, replacing ``target``."""
    if target.exists():
        shutil.rmtree(target)
    shutil.copytree(source, target)


def project_folder_names(root: Path) -> set[str]:
    """Names of subdirectories of ``root`` that contain an ``All.lean``."""
    return {
        p.name
        for p in root.iterdir()
        if p.is_dir() and p.name not in UNTOUCHED_SUBDIRS and (p / "All.lean").is_file()
    }


def is_project_file(file_path: Path, variant_root: Path) -> bool:
    """True if ``file_path`` is inside a project folder (not Mathlib/Util)."""
    try:
        rel = file_path.relative_to(variant_root)
    except ValueError:
        return False
    if not rel.parts:
        return False
    return rel.parts[0] not in UNTOUCHED_SUBDIRS


# --------------------------------------------------------------------- index


def write_index(project_root: Path, variant_dir: Path, variant: str) -> Path:
    target_prefix = f"LiveLeanTriathlon{variant}"
    lean_files = sorted(variant_dir.rglob("*.lean"))
    lines = ["module  -- shake: keep-all", ""]
    for f in lean_files:
        rel = f.relative_to(variant_dir).with_suffix("")
        module = ".".join(rel.parts)
        lines.append(f"public import {target_prefix}.{module}")
    index_path = project_root / f"{target_prefix}.lean"
    index_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return index_path


# --------------------------------------------------------------------- Sorry


def build_sorry(project_root: Path) -> None:
    source = project_root / "LiveLeanTriathlon"
    target = project_root / "LiveLeanTriathlonSorry"
    log_message("=== building Sorry ===")
    copy_lean_tree(source, target)

    mapping = {"LiveLeanTriathlon": "LiveLeanTriathlonSorry"}

    for f in sorted(target.rglob("*.lean")):
        text = f.read_text(encoding="utf-8")
        text = transform_imports(text, mapping)
        if is_project_file(f, target) and f.name == "All.lean":
            text = sorry_fy(text)
        f.write_text(text, encoding="utf-8")

    write_index(project_root, target, "Sorry")
    log_message(f"wrote {target}")


# --------------------------------------------------------------------- Easy


DECL_KEYS_ALL = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class",
    "instance",
    "inductive",
)


def _final_theorem_decl(body: list[str]) -> dict | None:
    """Find the last ``theorem`` declaration in ``body``."""
    final = None
    for d in find_all_decls("\n".join(body), keys=("theorem",)):
        final = d
    return final


def filter_drop_final_theorem(body: list[str]) -> list[str]:
    """Return ``body`` with the final-theorem declaration block removed."""
    final = _final_theorem_decl(body)
    if final is None:
        return body
    drop = set(range(final["start_line"], final["end_line"] + 1))
    return _collapse_blank_runs([line for i, line in enumerate(body) if i not in drop])


def filter_keep_scaffolding_and_final(
    body: list[str],
    keep_keys: tuple[str, ...],
    keep_needed_for_def: bool = False,
) -> list[str]:
    """Return a copy of ``body`` keeping only:
    - the final ``theorem`` declaration block;
    - declaration blocks whose key is in ``keep_keys`` (e.g. defs/structures);
    - lemmas annotated with ``-- Needed for def`` (when
      ``keep_needed_for_def=True``);
    - non-declaration scaffolding (sections, namespaces, opens, set_options,
      variables, etc.).

    Other declaration blocks (lemmas, non-final theorems, and defs not in
    ``keep_keys``) are removed along with their decorations.
    """
    decls = find_all_decls("\n".join(body), keys=DECL_KEYS_ALL)
    theorem_decls = [d for d in decls if d["key"] == "theorem"]
    final = theorem_decls[-1] if theorem_decls else None
    drop = set()
    for d in decls:
        if d is final:
            continue
        if d["key"] in keep_keys:
            continue
        if (
            keep_needed_for_def
            and d["key"] in ("lemma", "theorem")
            and has_needed_for_def_comment(body, d)
        ):
            continue
        drop.update(range(d["start_line"], d["end_line"] + 1))
    return _collapse_blank_runs([line for i, line in enumerate(body) if i not in drop])


def _scaffolding_header_lines(license_block: str, imports: list[str]) -> list[str]:
    out: list[str] = []
    if license_block:
        out.append(license_block)
        out.append("")
    out.append("module")
    out.append("")
    out.extend(imports)
    out.append("")
    out.append("@[expose] public section")
    out.append("")
    return out


def split_for_easy(all_text: str, parent_module: str) -> tuple[str, str]:
    """Split ``all_text`` (an ``All.lean`` body) into Background and MainTheorem
    file contents.

    Background.lean keeps everything from ``All.lean`` minus the final theorem
    block. MainTheorem.lean keeps the section/namespace/open scaffolding and
    the final theorem only (so the theorem compiles in the same namespace
    context it had in ``All.lean``); it imports ``parent_module`` to pick up
    the definitions and lemmas from Background.
    """
    parsed = parse_all_lean(all_text)
    body = parsed["body_lines"]

    bg_body = filter_drop_final_theorem(body)
    background_text = "\n".join(parsed["header_lines"] + bg_body)
    if not background_text.endswith("\n"):
        background_text += "\n"

    # MainTheorem keeps scaffolding + final theorem; defs/lemmas come from Background.
    main_body = filter_keep_scaffolding_and_final(body, keep_keys=())
    main_lines = _scaffolding_header_lines(
        parsed["license"], [f"public import {parent_module}"]
    )
    main_lines.extend(main_body)
    main_text = "\n".join(main_lines)
    if not main_text.endswith("\n"):
        main_text += "\n"
    return background_text, main_text


def _collapse_blank_runs(lines: list[str]) -> list[str]:
    out: list[str] = []
    blank_run = 0
    for line in lines:
        if not line.strip():
            blank_run += 1
            if blank_run <= 1:
                out.append(line)
        else:
            blank_run = 0
            out.append(line)
    while out and not out[-1].strip():
        out.pop()
    return out


def build_easy(project_root: Path) -> None:
    sorry_dir = project_root / "LiveLeanTriathlonSorry"
    target = project_root / "LiveLeanTriathlonEasy"
    if not sorry_dir.is_dir():
        raise RuntimeError(f"{sorry_dir} not found; run with --variant Sorry first")

    log_message("=== building Easy ===")
    copy_lean_tree(sorry_dir, target)

    mapping = {"LiveLeanTriathlonSorry": "LiveLeanTriathlonEasy"}
    project_folders = project_folder_names(target)

    for f in sorted(target.rglob("*.lean")):
        text = f.read_text(encoding="utf-8")
        text = transform_imports(text, mapping)
        f.write_text(text, encoding="utf-8")

    for folder in sorted(target.iterdir()):
        if not folder.is_dir() or folder.name in UNTOUCHED_SUBDIRS:
            continue
        all_lean = folder / "All.lean"
        if not all_lean.is_file():
            continue

        all_text = all_lean.read_text(encoding="utf-8")
        all_text = rewrite_all_to_main(all_text, "Easy", project_folders)

        bg_text, main_text = split_for_easy(
            all_text, f"LiveLeanTriathlonEasy.{folder.name}.Background"
        )
        (folder / "Background.lean").write_text(bg_text, encoding="utf-8")
        (folder / "MainTheorem.lean").write_text(main_text, encoding="utf-8")
        all_lean.unlink()

    write_index(project_root, target, "Easy")
    log_message(f"wrote {target}")


# --------------------------------------------------------------------- Hard


def strip_non_final_theorems_lemmas(text: str) -> str:
    """Remove all theorem and lemma blocks except the final ``theorem``;
    preserve definitions, lemmas annotated ``-- Needed for def``, and
    section/namespace/open scaffolding so the kept theorem compiles in the
    same context."""
    parsed = parse_all_lean(text)
    body = parsed["body_lines"]
    new_body = filter_keep_scaffolding_and_final(
        body,
        keep_keys=("def", "abbrev", "structure", "class", "instance", "inductive"),
        keep_needed_for_def=True,
    )
    return "\n".join(parsed["header_lines"] + new_body) + "\n"


def build_hard(project_root: Path) -> None:
    sorry_dir = project_root / "LiveLeanTriathlonSorry"
    target = project_root / "LiveLeanTriathlonHard"
    if not sorry_dir.is_dir():
        raise RuntimeError(f"{sorry_dir} not found; run with --variant Sorry first")

    log_message("=== building Hard ===")
    copy_lean_tree(sorry_dir, target)

    mapping = {"LiveLeanTriathlonSorry": "LiveLeanTriathlonHard"}
    project_folders = project_folder_names(target)

    for f in sorted(target.rglob("*.lean")):
        text = f.read_text(encoding="utf-8")
        text = transform_imports(text, mapping)
        f.write_text(text, encoding="utf-8")

    for folder in sorted(target.iterdir()):
        if not folder.is_dir() or folder.name in UNTOUCHED_SUBDIRS:
            continue
        all_lean = folder / "All.lean"
        if not all_lean.is_file():
            continue
        all_text = all_lean.read_text(encoding="utf-8")
        all_text = rewrite_all_to_main(all_text, "Hard", project_folders)
        main_text = strip_non_final_theorems_lemmas(all_text)
        (folder / "MainTheorem.lean").write_text(main_text, encoding="utf-8")
        all_lean.unlink()

    write_index(project_root, target, "Hard")
    log_message(f"wrote {target}")


# --------------------------------------------------------------------- Autoformalization


def _camel_to_kebab(s: str) -> str:
    out: list[str] = []
    for i, c in enumerate(s):
        if c.isupper() and i > 0:
            out.append("-")
        out.append(c.lower())
    return "".join(out)


def build_autoformalization(project_root: Path) -> None:
    sorry_dir = project_root / "LiveLeanTriathlonSorry"
    target = project_root / "LiveLeanTriathlonAutoformalization"
    tex_dir = project_root / "blueprint" / "src" / "theorems"
    if not sorry_dir.is_dir():
        raise RuntimeError(f"{sorry_dir} not found; run with --variant Sorry first")

    log_message("=== building Autoformalization ===")
    copy_lean_tree(sorry_dir, target)

    mapping = {"LiveLeanTriathlonSorry": "LiveLeanTriathlonAutoformalization"}
    project_folders = project_folder_names(target)

    for f in sorted(target.rglob("*.lean")):
        text = f.read_text(encoding="utf-8")
        text = transform_imports(text, mapping)
        f.write_text(text, encoding="utf-8")

    missing_tex: list[str] = []
    for folder in sorted(target.iterdir()):
        if not folder.is_dir() or folder.name in UNTOUCHED_SUBDIRS:
            continue
        all_lean = folder / "All.lean"
        if not all_lean.is_file():
            continue
        all_text = all_lean.read_text(encoding="utf-8")
        all_text = rewrite_all_to_main(all_text, "Autoformalization", project_folders)
        main_text = strip_non_final_theorems_lemmas(all_text)
        (folder / "MainTheorem.lean").write_text(main_text, encoding="utf-8")
        all_lean.unlink()

        stem = _camel_to_kebab(folder.name)
        tex_src = tex_dir / f"{stem}.tex"
        if tex_src.is_file():
            shutil.copy2(tex_src, folder / f"{stem}.tex")
        else:
            missing_tex.append(folder.name)

    write_index(project_root, target, "Autoformalization")
    if missing_tex:
        print(
            f"Warning: no .tex found for {len(missing_tex)} folders: "
            + ", ".join(missing_tex)
        )
    log_message(f"wrote {target}")


# --------------------------------------------------------------------- main


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "--variant",
        choices=[*VARIANTS, "all"],
        default="all",
        help="Which variant to generate (default: all).",
    )
    args = ap.parse_args()

    project_root = find_project_root()
    targets = VARIANTS if args.variant == "all" else [args.variant]

    builders = {
        "Sorry": build_sorry,
        "Easy": build_easy,
        "Hard": build_hard,
        "Autoformalization": build_autoformalization,
    }
    for variant in targets:
        builders[variant](project_root)
        print(f"Built {variant}")


if __name__ == "__main__":
    main()
