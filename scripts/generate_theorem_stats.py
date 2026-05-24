#!/usr/bin/env python3
"""Generate scripts/theorem_stats.json from the current Lean and blueprint sources.

Produces statistics including:
  - AMS subject classification per theorem
  - Whether each theorem's proof contains sorry
  - Whether the theorem's blueprint .tex file has substantive informal
    content (longer than 500 characters)
  - Whether the theorem's directory contains a BackgroundLemmas.lean file
  - Summary counts

Run this after adding or modifying theorems:
    python3 scripts/generate_theorem_stats.py
"""

import re
import json
from pathlib import Path
from collections import defaultdict

AMS_DESCRIPTIONS: dict[int, str] = {
    0: "General and overarching topics",
    1: "History and biography",
    3: "Mathematical logic and foundations",
    5: "Combinatorics",
    6: "Order, lattices, ordered algebraic structures",
    8: "General algebraic systems",
    11: "Number theory",
    12: "Field theory and polynomials",
    13: "Commutative algebra",
    14: "Algebraic geometry",
    15: "Linear and multilinear algebra; matrix theory",
    16: "Associative rings and algebras",
    17: "Nonassociative rings and algebras",
    18: "Category theory; homological algebra",
    19: "K-theory",
    20: "Group theory and generalizations",
    22: "Topological groups, Lie groups",
    26: "Real functions",
    28: "Measure and integration",
    30: "Functions of a complex variable",
    31: "Potential theory",
    32: "Several complex variables and analytic spaces",
    33: "Special functions",
    34: "Ordinary differential equations",
    35: "Partial differential equations",
    37: "Dynamical systems and ergodic theory",
    39: "Difference and functional equations",
    40: "Sequences, series, summability",
    41: "Approximations and expansions",
    42: "Harmonic analysis on Euclidean spaces",
    43: "Abstract harmonic analysis",
    44: "Integral transforms, operational calculus",
    45: "Integral equations",
    46: "Functional analysis",
    47: "Operator theory",
    49: "Calculus of variations and optimal control; optimization",
    51: "Geometry",
    52: "Convex and discrete geometry",
    53: "Differential geometry",
    54: "General topology",
    55: "Algebraic topology",
    57: "Manifolds and cell complexes",
    58: "Global analysis, analysis on manifolds",
    60: "Probability theory and stochastic processes",
    62: "Statistics",
    65: "Numerical analysis",
    68: "Computer science",
    70: "Mechanics of particles and systems",
    74: "Mechanics of deformable solids",
    76: "Fluid mechanics",
    78: "Optics, electromagnetic theory",
    80: "Classical thermodynamics, heat transfer",
    81: "Quantum theory",
    82: "Statistical mechanics, structure of matter",
    83: "Relativity and gravitational theory",
    85: "Astronomy and astrophysics",
    86: "Geophysics",
    90: "Operations research, mathematical programming",
    91: "Game theory, economics, social and behavioral sciences",
    92: "Biology and other natural sciences",
    93: "Systems theory; control",
    94: "Information and communication, circuits",
    97: "Mathematics education",
}

# Regex to match `sorry` as a standalone tactic/term (not in comments or strings)
SORRY_RE = re.compile(r"\bsorry\b")
# Regex to match single-line comments
LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)
# Regex to match block comments (non-nested, simple)
BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)


def strip_comments(text: str) -> str:
    """Remove Lean comments from source text."""
    text = BLOCK_COMMENT_RE.sub("", text)
    text = LINE_COMMENT_RE.sub("", text)
    return text


# Path components whose entire subtree is excluded from every scan in this
# script. ``Sorry`` is generated; ``Mistakes`` is a deliberate "this is what
# breakage looks like" demo and its declarations must not pollute lookups.
EXCLUDED_PATH_PARTS = ("/Sorry/", "/Mistakes/")


def _is_excluded(lean_file: Path) -> bool:
    s = str(lean_file)
    return any(part in s for part in EXCLUDED_PATH_PARTS)


def scan_lean_ams(lean_dir: Path) -> dict[str, list[int]]:
    """Return mapping from declaration name to sorted list of AMS codes."""
    lean_ams: dict[str, list[int]] = {}
    decl_keywords = (
        r"(?:theorem|lemma|def|noncomputable\s+def|abbrev|structure|class|instance)"
    )
    pattern = re.compile(
        r"@\[[^\]]*\bAMS\b([^\]]*)\]"
        r"(?:\s*@\[[^\]]*\][^\S\n]*)*"
        r"\s+"
        r"(?:" + decl_keywords + r")\s+"
        r"([\w.]+)",
        re.MULTILINE,
    )
    for lean_file in lean_dir.rglob("*.lean"):
        if _is_excluded(lean_file):
            continue
        try:
            content = lean_file.read_text(encoding="utf-8")
        except Exception:
            continue
        for m in pattern.finditer(content):
            nums = sorted(set(int(x) for x in m.group(1).split() if x.isdigit()))
            decl = m.group(2)
            lean_ams[decl] = nums
            lean_ams[decl.split(".")[-1]] = nums
    return lean_ams


NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+([\w.]+)\s*$")
NAMESPACE_END_RE = re.compile(r"^\s*end\s+([\w.]+)\s*$")
DECL_RE = re.compile(
    r"^\s*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|@\[expose\]\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance)"
    r"\s+([\w.]+)"
)


def scan_lean_decl_files(lean_dir: Path) -> dict[str, Path]:
    """Return mapping from fully-qualified declaration name to the .lean file
    that defines it.

    Tracks ``namespace … end`` blocks line-by-line so that
    ``namespace PartialOrder ; theorem dilworth …`` is recorded under
    ``PartialOrder.dilworth``, not just ``dilworth``. Bare-name aliases use
    ``setdefault`` so they don't get clobbered by later same-bare-name
    declarations.
    """
    decl_to_file: dict[str, Path] = {}
    for lean_file in lean_dir.rglob("*.lean"):
        if _is_excluded(lean_file):
            continue
        try:
            content = lean_file.read_text(encoding="utf-8")
        except Exception:
            continue
        ns_stack: list[str] = []
        for line in content.splitlines():
            m_open = NAMESPACE_OPEN_RE.match(line)
            if m_open:
                ns_stack.append(m_open.group(1))
                continue
            m_close = NAMESPACE_END_RE.match(line)
            if m_close and ns_stack and ns_stack[-1] == m_close.group(1):
                ns_stack.pop()
                continue
            m_decl = DECL_RE.match(line)
            if m_decl:
                bare = m_decl.group(1)
                full = ".".join([*ns_stack, bare]) if ns_stack else bare
                decl_to_file[full] = lean_file
                decl_to_file.setdefault(bare, lean_file)
    return decl_to_file


def directory_has_sorry(directory: Path) -> bool:
    """Check if any .lean file in a directory tree contains sorry (outside comments)."""
    for lean_file in directory.rglob("*.lean"):
        if _is_excluded(lean_file):
            continue
        try:
            content = lean_file.read_text(encoding="utf-8")
        except Exception:
            continue
        cleaned = strip_comments(content)
        if SORRY_RE.search(cleaned):
            return True
    return False


def scan_final_lean_names(theorems_dir: Path) -> dict[str, str]:
    """Return mapping from tex filename stem to lean name of the final environment."""
    lean_re = re.compile(r"\\lean\{([^}]+)\}")
    env_begin = re.compile(r"\\begin\{(theorem|lemma|definition)\}")
    result: dict[str, str] = {}
    for tex_file in sorted(theorems_dir.glob("*.tex")):
        content = tex_file.read_text(encoding="utf-8")
        blocks: list[tuple[int, str]] = []
        for begin_m in env_begin.finditer(content):
            env_type = begin_m.group(1)
            end_pat = re.compile(r"\\end\{" + env_type + r"\}")
            end_m = end_pat.search(content, begin_m.end())
            if end_m:
                block_content = content[begin_m.start() : end_m.end()]
                lean_m = lean_re.search(block_content)
                if lean_m:
                    blocks.append((begin_m.start(), lean_m.group(1).strip()))
        if blocks:
            result[tex_file.stem] = blocks[-1][1]
    return result


INFORMAL_CHAR_THRESHOLD = 500


def build_stats(workspace: Path) -> dict:
    lean_dir = workspace / "LiveLeanTriathlon"
    theorems_dir = workspace / "blueprint/src/theorems"
    lean_ams = scan_lean_ams(lean_dir)
    decl_to_file = scan_lean_decl_files(lean_dir)
    final_names = scan_final_lean_names(theorems_dir)

    theorems: dict[str, dict] = {}
    for stem, lean_name in sorted(final_names.items()):
        short = lean_name.split(".")[-1]
        codes = lean_ams.get(lean_name) or lean_ams.get(short) or []

        # Determine sorry status and BackgroundLemmas.lean presence by checking
        # the theorem's directory.
        has_sorry = False
        has_background_lemmas = False
        decl_file = decl_to_file.get(lean_name) or decl_to_file.get(short)
        if decl_file is not None:
            theorem_dir = decl_file.parent
            has_sorry = directory_has_sorry(theorem_dir)
            has_background_lemmas = (theorem_dir / "BackgroundLemmas.lean").is_file()

        # has_informal: tex file for the theorem is longer than 500 chars.
        tex_file = theorems_dir / f"{stem}.tex"
        has_informal = False
        if tex_file.is_file():
            has_informal = (
                len(tex_file.read_text(encoding="utf-8")) > INFORMAL_CHAR_THRESHOLD
            )

        theorems[lean_name] = {
            "ams_codes": codes,
            "has_sorry": has_sorry,
            "has_informal": has_informal,
            "has_background_lemmas": has_background_lemmas,
        }

    # AMS summary: total / with_sorry / without_sorry per code
    ams_summary: dict[int, dict[str, int]] = defaultdict(
        lambda: {"count": 0, "with_sorry": 0, "without_sorry": 0}
    )
    for info in theorems.values():
        for c in info["ams_codes"]:
            ams_summary[c]["count"] += 1
            if info["has_sorry"]:
                ams_summary[c]["with_sorry"] += 1
            else:
                ams_summary[c]["without_sorry"] += 1

    # Sorry summary
    total = len(theorems)
    with_sorry = sum(1 for info in theorems.values() if info["has_sorry"])
    without_sorry = total - with_sorry

    return {
        "description": (
            "Statistics for LiveLeanTriathlon theorem declarations. "
            "Each entry in 'theorems' maps a Lean declaration name to its AMS "
            "subject code(s), whether its proof contains sorry, whether the "
            "theorem's blueprint .tex file has substantive informal content "
            "(longer than 500 characters), and whether the theorem's directory has a "
            "BackgroundLemmas.lean file. "
            "Regenerate with: python3 scripts/generate_theorem_stats.py"
        ),
        "sorry_summary": {
            "total": total,
            "with_sorry": with_sorry,
            "without_sorry": without_sorry,
        },
        "ams_summary": {
            str(k): {
                "description": AMS_DESCRIPTIONS.get(k, ""),
                "count": v["count"],
                "with_sorry": v["with_sorry"],
                "without_sorry": v["without_sorry"],
            }
            for k, v in sorted(
                ams_summary.items(), key=lambda item: (-item[1]["count"], item[0])
            )
        },
        "theorems": theorems,
    }


def main() -> None:
    workspace = Path(__file__).parent.parent
    stats = build_stats(workspace)
    out = workspace / "scripts" / "theorem_stats.json"
    out.write_text(json.dumps(stats, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out}")

    total = len(stats["theorems"])
    tagged = sum(1 for v in stats["theorems"].values() if v["ams_codes"])
    print(f"\n--- AMS Classification ---")
    print(f"  {tagged}/{total} theorems have AMS tags")
    for code, info in stats["ams_summary"].items():
        print(
            f"  AMS {code:>3} ({info['description']}): "
            f"{info['count']} total, {info['without_sorry']} proved, {info['with_sorry']} sorry"
        )

    sorry = stats["sorry_summary"]
    print(f"\n--- Sorry Status ---")
    print(f"  {sorry['without_sorry']}/{sorry['total']} theorems proven (no sorry)")
    print(f"  {sorry['with_sorry']}/{sorry['total']} theorems still have sorry")

    # List theorems with sorry
    sorry_theorems = [
        name for name, info in stats["theorems"].items() if info["has_sorry"]
    ]
    if sorry_theorems:
        print(f"\n  Theorems with sorry:")
        for name in sorry_theorems:
            print(f"    - {name}")


if __name__ == "__main__":
    main()
