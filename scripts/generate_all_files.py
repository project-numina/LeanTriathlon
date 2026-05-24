#!/usr/bin/env python3
"""Generate ``All.lean`` files for project folders in ``LiveLeanTriathlon/``.

For each folder that contains ``MainTheorem.lean`` (and optionally
``BackgroundLemmas.lean``), produce an ``All.lean`` file that:

- Imports the union of the imports from both files, excluding the cross-imports
  ``LiveLeanTriathlon.<folder>.MainTheorem`` and
  ``LiveLeanTriathlon.<folder>.BackgroundLemmas``.
- Has a single ``@[expose] public section``.
- Contains the post-``@[expose] public section`` content of
  ``BackgroundLemmas.lean`` wrapped in ``section Background … end Background``
  (when that file is present), followed by the post-``@[expose] public section``
  content of ``MainTheorem.lean`` wrapped in ``section Main … end Main``.

Run after editing project source:
    python3 scripts/generate_all_files.py
"""

import re
from pathlib import Path

WORKSPACE = Path(__file__).resolve().parent.parent
LEAN_ROOT = WORKSPACE / "LiveLeanTriathlon"

EXPOSE_RE = re.compile(r"^\s*@\[expose\]\s+public\s+section\s*$")
MODULE_RE = re.compile(r"^\s*module\s*$")
IMPORT_RE = re.compile(
    r"^(?P<kind>(?:public\s+)?(?:meta\s+)?)import\s+(?P<name>\S+)\s*$"
)
LICENSE_HEADER_RE = re.compile(r"\A\s*(/-.*?-/)", re.DOTALL)
SCOPE_OPEN_NAMED_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:section|namespace)\s+([\w.]+)\s*$"
)
SCOPE_OPEN_ANON_RE = re.compile(r"^\s*(?:noncomputable\s+)?section\s*$")
END_NAMED_RE = re.compile(r"^\s*end\s+([\w.]+)\s*$")
END_ANON_RE = re.compile(r"^\s*end\s*$")


def parse_file(path: Path) -> tuple[str, list[tuple[str, str]], str]:
    """Return ``(license_header, imports, post_expose_content)``.

    - ``license_header`` is the leading ``/- … -/`` block (without trailing
      newlines), or empty if absent.
    - ``imports`` is a list of ``(kind, name)`` from the import region (between
      ``module`` and ``@[expose] public section``), preserving source order.
      ``kind`` is one of ``""``, ``"public "``, ``"meta "``, ``"public meta "``.
    - ``post_expose_content`` is everything after the ``@[expose] public
      section`` line, with surrounding blank lines stripped. Empty if the
      marker is absent.
    """
    text = path.read_text(encoding="utf-8")

    m = LICENSE_HEADER_RE.match(text)
    license_header = m.group(1) if m else ""

    lines = text.splitlines()

    module_idx = None
    for i, line in enumerate(lines):
        if MODULE_RE.match(line):
            module_idx = i
            break

    expose_idx = None
    for i, line in enumerate(lines):
        if EXPOSE_RE.match(line):
            expose_idx = i
            break

    import_start = (module_idx + 1) if module_idx is not None else 0
    import_end = expose_idx if expose_idx is not None else len(lines)

    imports: list[tuple[str, str]] = []
    for line in lines[import_start:import_end]:
        im = IMPORT_RE.match(line)
        if im:
            kind = (im.group("kind") or "").strip()
            kind = (kind + " ") if kind else ""
            imports.append((kind, im.group("name")))

    if expose_idx is not None:
        post = "\n".join(lines[expose_idx + 1 :]).strip("\n")
    else:
        post = ""

    return license_header, imports, post


def _rewrite_to_all(name: str, all_folders: set[str]) -> str:
    """Rewrite ``LiveLeanTriathlon.<X>.MainTheorem`` and
    ``LiveLeanTriathlon.<X>.BackgroundLemmas`` to ``LiveLeanTriathlon.<X>.All`` when
    ``<X>`` is a project folder that has its own ``All.lean``."""
    if not name.startswith("LiveLeanTriathlon."):
        return name
    parts = name.split(".")
    if len(parts) < 3:
        return name
    target = parts[1]
    if target not in all_folders:
        return name
    if parts[-1] not in ("MainTheorem", "BackgroundLemmas"):
        return name
    return f"LiveLeanTriathlon.{target}.All"


def merge_imports(
    main_imports: list[tuple[str, str]],
    bg_imports: list[tuple[str, str]],
    folder: str,
    all_folders: set[str],
) -> list[tuple[str, str]]:
    """Return the union of imports, deduped, preserving first-seen order, with
    the two cross-imports between ``MainTheorem`` and ``BackgroundLemmas``
    inside ``folder`` filtered out, and cross-folder imports of those modules
    rewritten to ``All``.

    If the same import appears with both ``public`` and non-``public`` kinds,
    the more permissive ``public`` form wins.
    """
    cross_self = {
        f"LiveLeanTriathlon.{folder}.MainTheorem",
        f"LiveLeanTriathlon.{folder}.BackgroundLemmas",
    }
    seen: dict[str, str] = {}
    order: list[str] = []
    for kind, name in [*main_imports, *bg_imports]:
        if name in cross_self:
            continue
        name = _rewrite_to_all(name, all_folders)
        if name not in seen:
            seen[name] = kind
            order.append(name)
        elif "public" in kind and "public" not in seen[name]:
            seen[name] = kind
    return [(seen[n], n) for n in order]


def render_imports(imports: list[tuple[str, str]]) -> str:
    """Render imports, with a blank line between Mathlib/external imports and
    LiveLeanTriathlon imports."""
    external = [imp for imp in imports if not imp[1].startswith("LiveLeanTriathlon.")]
    internal = [imp for imp in imports if imp[1].startswith("LiveLeanTriathlon.")]
    groups = []
    if external:
        groups.append("\n".join(f"{kind}import {name}" for kind, name in external))
    if internal:
        groups.append("\n".join(f"{kind}import {name}" for kind, name in internal))
    return "\n\n".join(groups)


def close_unbalanced_scopes(content: str) -> str:
    """Close any ``section``/``namespace`` scopes that ``content`` leaves open
    at end-of-file. Lean auto-closes them at EOF, but when ``content`` is
    nested inside ``section Background``/``section Main``, the outer ``end``
    fires while these scopes are still open, breaking the parse."""
    stack: list[str | None] = []
    for line in content.splitlines():
        m = SCOPE_OPEN_NAMED_RE.match(line)
        if m:
            stack.append(m.group(1))
            continue
        if SCOPE_OPEN_ANON_RE.match(line):
            stack.append(None)
            continue
        m = END_NAMED_RE.match(line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        if END_ANON_RE.match(line) and stack and stack[-1] is None:
            stack.pop()
            continue
    if not stack:
        return content
    closes = []
    while stack:
        scope = stack.pop()
        closes.append("end" if scope is None else f"end {scope}")
    return content.rstrip("\n") + "\n\n" + "\n".join(closes)


def render_section(name: str, body: str) -> str:
    body = close_unbalanced_scopes(body.strip("\n"))
    if not body:
        return f"section {name}\n\nend {name}"
    return f"section {name}\n\n{body}\n\nend {name}"


def make_all(folder_path: Path, all_folders: set[str]) -> str | None:
    main_path = folder_path / "MainTheorem.lean"
    bg_path = folder_path / "BackgroundLemmas.lean"
    if not main_path.is_file():
        return None

    main_license, main_imports, main_post = parse_file(main_path)
    if bg_path.is_file():
        _, bg_imports, bg_post = parse_file(bg_path)
        has_bg = True
    else:
        bg_imports, bg_post, has_bg = [], "", False

    imports = merge_imports(main_imports, bg_imports, folder_path.name, all_folders)

    parts: list[str] = []
    if main_license:
        parts.append(main_license)
    parts.append("module")
    if imports:
        parts.append(render_imports(imports))
    parts.append("@[expose] public section")
    if has_bg:
        parts.append(render_section("Background", bg_post))
    parts.append(render_section("Main", main_post))
    return "\n\n".join(parts) + "\n"


def main() -> None:
    folders = [f for f in sorted(LEAN_ROOT.iterdir()) if f.is_dir()]
    all_folders = {f.name for f in folders if (f / "MainTheorem.lean").is_file()}
    written = 0
    skipped: list[str] = []
    for folder in folders:
        out = make_all(folder, all_folders)
        if out is None:
            skipped.append(folder.name)
            continue
        target = folder / "All.lean"
        target.write_text(out, encoding="utf-8")
        written += 1
    print(f"Wrote {written} All.lean files.")
    if skipped:
        print(
            f"Skipped {len(skipped)} folders without MainTheorem.lean: "
            + ", ".join(skipped)
        )


if __name__ == "__main__":
    main()
