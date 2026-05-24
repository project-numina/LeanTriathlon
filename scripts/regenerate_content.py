#!/usr/bin/env python3
"""Regenerate blueprint/src/content.tex from all .tex files in blueprint/src/theorems/."""

import os
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
THEOREMS_DIR = REPO_ROOT / "blueprint" / "src" / "theorems"
CONTENT_TEX = REPO_ROOT / "blueprint" / "src" / "content.tex"

HEADER = """\
% In this file you should put the actual content of the blueprint.
% It will be used both by the web and the print version.
% It should *not* include the \\begin{document}
%
% If you want to split the blueprint content into several files then
% the current file can be a simple sequence of \\input. Otherwise It
% can start with a \\section or \\chapter for instance.

"""

def main():
    tex_files = sorted(THEOREMS_DIR.glob("*.tex"))
    lines = []
    for f in tex_files:
        stem = f.stem
        lines.append(f"\\input{{theorems/{stem}}}\n")

    content = HEADER + "".join(lines)
    CONTENT_TEX.write_text(content)
    print(f"Wrote {len(lines)} entries to {CONTENT_TEX}")

if __name__ == "__main__":
    main()
