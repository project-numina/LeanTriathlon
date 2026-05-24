#!/usr/bin/env python3
"""
Check and add license headers to Lean files.

This script checks that all Lean files in the repository have the proper
license header, and optionally adds missing headers.
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List, Tuple


DEFAULT_PROJECT = "Project Numina"
DEFAULT_AUTHORS = "Numina Team"
DEFAULT_YEAR = "2026"


def get_license_header(
    project: str = DEFAULT_PROJECT,
    authors: str = DEFAULT_AUTHORS,
    year: str = DEFAULT_YEAR,
) -> str:
    """Generate the license header text."""
    return f"""/-
Copyright (c) {year} {project}. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: {authors}
-/
"""


def has_license_header(content: str) -> bool:
    """
    Check if the file content starts with a recognized license header.

    Two formats are accepted:

    1. Standard Numina header — a ``/- ... -/`` block containing
       ``Copyright ... All rights reserved``, ``Apache 2.0 license``,
       ``LICENSE``, and an ``Authors:`` line.

    2. Upstream Apache 2.0 header (e.g. for files imported from other
       projects) — a ``/- ... -/`` block containing ``Copyright`` and
       ``Apache License, Version 2.0``. Such files are expected to keep
       their original attribution rather than being rewritten to the
       Numina style.
    """
    # Check if file starts with /-
    if not content.lstrip().startswith("/-"):
        return False

    # Extract the first comment block
    match = re.match(r"\s*/-(.*?)-/", content, re.DOTALL)
    if not match:
        return False

    comment_content = match.group(1)

    # Format 1: standard Numina header
    has_copyright = (
        "Copyright" in comment_content and "All rights reserved" in comment_content
    )
    has_license = (
        "Apache 2.0 license" in comment_content and "LICENSE" in comment_content
    )
    has_authors = "Authors:" in comment_content
    if has_copyright and has_license and has_authors:
        return True

    # Format 2: upstream Apache 2.0 header (preserved attribution)
    if (
        "Copyright" in comment_content
        and "Apache License, Version 2.0" in comment_content
    ):
        return True

    return False


def find_lean_files(root_dir: Path, exclude_dirs: List[str] = None) -> List[Path]:
    """Find all .lean files in the LiveLeanTriathlon directory."""
    if exclude_dirs is None:
        exclude_dirs = [".lake", "build", ".git"]

    lean_files = []
    # Only search within the LiveLeanTriathlon subdirectory
    LiveLeanTriathlon_dir = root_dir / "LiveLeanTriathlon"

    if not LiveLeanTriathlon_dir.exists():
        return []

    for path in LiveLeanTriathlon_dir.rglob("*.lean"):
        # Check if any parent directory is in exclude_dirs
        if any(excluded in path.parts for excluded in exclude_dirs):
            continue
        lean_files.append(path)

    # Exclude LiveLeanTriathlon.lean in the top-level directory
    tld_file = root_dir / "LiveLeanTriathlon.lean"
    if tld_file in lean_files:
        lean_files.remove(tld_file)

    return sorted(lean_files)


def add_license_header(file_path: Path, project: str, authors: str, year: str) -> None:
    """Add license header to a file."""
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    header = get_license_header(project, authors, year)

    # Add a newline after header if content doesn't start with one
    if content and not content.startswith("\n"):
        new_content = header + "\n" + content
    else:
        new_content = header + content

    with open(file_path, "w", encoding="utf-8") as f:
        f.write(new_content)


def check_files(
    root_dir: Path,
    fix: bool = False,
    project: str = DEFAULT_PROJECT,
    authors: str = DEFAULT_AUTHORS,
    year: str = DEFAULT_YEAR,
    exclude_dirs: List[str] = None,
) -> Tuple[List[Path], List[Path]]:
    """
    Check all Lean files for license headers.

    Returns:
        Tuple of (files_with_header, files_without_header)
    """
    lean_files = find_lean_files(root_dir, exclude_dirs)

    files_with_header = []
    files_without_header = []

    for file_path in lean_files:
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            if has_license_header(content):
                files_with_header.append(file_path)
            else:
                files_without_header.append(file_path)
                if fix:
                    add_license_header(file_path, project, authors, year)
                    print(f"✓ Added header to: {file_path.relative_to(root_dir)}")
        except Exception as e:
            print(f"Error processing {file_path}: {e}", file=sys.stderr)

    return files_with_header, files_without_header


def main():
    parser = argparse.ArgumentParser(
        description="Check and add license headers to Lean files.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Check all files
  python check_license.py

  # Check files and add missing headers
  python check_license.py --fix

  # Use custom project name and authors
  python check_license.py --fix --project "My Project" --authors "John Doe"

  # Check files in a specific directory
  python check_license.py --root /path/to/repo
        """,
    )

    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd().parent if Path.cwd().name == "scripts" else Path.cwd(),
        help="Root directory to search for Lean files (default: parent of current directory if in scripts/, else current directory)",
    )

    parser.add_argument(
        "--fix", action="store_true", help="Add missing license headers to files"
    )

    parser.add_argument(
        "--project",
        type=str,
        default=DEFAULT_PROJECT,
        help=f'Project name for the header (default: "{DEFAULT_PROJECT}")',
    )

    parser.add_argument(
        "--authors",
        type=str,
        default=DEFAULT_AUTHORS,
        help=f'Authors for the header (default: "{DEFAULT_AUTHORS}")',
    )

    parser.add_argument(
        "--year",
        type=str,
        default=DEFAULT_YEAR,
        help=f'Copyright year (default: "{DEFAULT_YEAR}")',
    )

    parser.add_argument(
        "--exclude",
        type=str,
        nargs="+",
        default=[".lake", "build", ".git"],
        help="Directories to exclude (default: .lake build .git)",
    )

    args = parser.parse_args()

    if not args.root.exists():
        print(f"Error: Directory {args.root} does not exist", file=sys.stderr)
        sys.exit(1)

    print(f"Checking Lean files in: {args.root}")
    print(f"Excluding directories: {', '.join(args.exclude)}")
    print()

    files_with_header, files_without_header = check_files(
        args.root,
        fix=args.fix,
        project=args.project,
        authors=args.authors,
        year=args.year,
        exclude_dirs=args.exclude,
    )

    total_files = len(files_with_header) + len(files_without_header)

    if args.fix:
        print(f"\n{'=' * 60}")
        print("Summary:")
        print(f"  Total Lean files: {total_files}")
        print(
            f"  Files with headers: {len(files_with_header) + len(files_without_header)}"
        )
        print(f"  Headers added: {len(files_without_header)}")
    else:
        if files_without_header:
            print(f"Files missing license headers ({len(files_without_header)}):")
            for file_path in files_without_header:
                print(f"  ✗ {file_path.relative_to(args.root)}")
            print()

        if files_with_header:
            print(f"Files with license headers ({len(files_with_header)}):")
            for file_path in files_with_header:
                print(f"  ✓ {file_path.relative_to(args.root)}")
            print()

        print(f"{'=' * 60}")
        print("Summary:")
        print(f"  Total Lean files: {total_files}")
        print(f"  With headers: {len(files_with_header)}")
        print(f"  Without headers: {len(files_without_header)}")

        if files_without_header:
            print("\nRun with --fix to add missing headers automatically.")
            sys.exit(1)

    print(f"{'=' * 60}")
    print("✓ All files have license headers!" if not files_without_header else "")


if __name__ == "__main__":
    main()
