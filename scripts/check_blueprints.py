#!/usr/bin/env -S uv run python
"""A comprehensive tool for validating LaTeX blueprint files to ensure proper structure and consistency.

Usage:
    uv run python check_blueprints.py [options]

    or make the script executable and run directly:
    chmod +x check_blueprints.py
    ./check_blueprints.py [options]

Options:
    -c, --config PATH    Path to configuration file (default: check_blueprints.json)
    -v, --verbose        Show all information including warnings (default: True)
    --conclusion         Print detailed environment block information and conclusion (default: True)
    -h, --help          Show this help message and exit

Examples:
    # Run with default settings
    python check_blueprints.py

    # Run with custom config file
    python check_blueprints.py --config my_config.json

    # Run with minimal output (errors only)
    python check_blueprints.py --no-verbose --no-conclusion

Check items:
1. Label validation: Ensures lemma/def/theorem environments have unique labels within each file, warns about cross-file duplicates
2. Proof binding: Verifies proof environments are properly bound to their parent lemma/theorem blocks
3. Lean block validation: Ensures definition/lemma/theorem environments contain \\lean{{}} blocks
4. Dependency tracking: Validates that all \\uses{} references point to existing labels and identifies unused labels
5. Circular dependencies: Detects circular dependencies in \\uses{} references within each file
6. Transitive usage: Ensures all environments are used transitively by the final environment in each file
7. File inclusion: Confirms all theorem files in the theorems folder are properly referenced in content.tex
8. Chapter structure: Ensures theorem files contain \\chapter commands and that \\chapter comes before any \\section commands
9. Theorem folder correspondence: Ensures each theorem .tex file in theorems/ has a matching CamelCase folder in LiveLeanTriathlon/
10. AMS tags: Ensures the final environment in each theorem file has @[AMS ...] on its Lean declaration
11. File header format: Ensures each theorem file starts with \\chapter, followed by a proof-description line, followed by a \\url reference somewhere in the opening paragraph
12. Theorem environment presence: Ensures each .tex file in theorems/ contains at least one labelled environment (theorem/lemma/definition)

TODO:
1. Ensure that theorems are in order: If A \\uses B, then B should appear before A in the file,
   or in a file recursively imported by the file that holds A
"""

import re
import json
import argparse
from pathlib import Path
from typing import Dict, List, Set, Optional
from dataclasses import dataclass
from collections import defaultdict


@dataclass
class CheckResult:
    """Check result"""

    success: bool
    message: str
    file_path: str
    line_number: Optional[int] = None
    is_warning: bool = False  # Whether it's a warning (non-critical error)


@dataclass
class EnvironmentBlock:
    """LaTeX environment block"""

    env_type: str
    label: Optional[str]
    uses: List[str]
    start_line: int
    end_line: int
    content: str
    file_path: str  # File path where this block is located
    has_lean: bool = False  # Whether this block contains \lean{} command
    proof_block: Optional["EnvironmentBlock"] = None  # Bound proof block
    parent_block: Optional["EnvironmentBlock"] = None  # Parent lemma/theorem block


class BlueprintChecker:
    """Blueprint checker"""

    def __init__(self, config_path: str = None):
        """Initialize checker"""
        self.config = self._load_config(config_path)
        self.workspace_root = Path(__file__).parent.parent
        self.blueprint_dir = self.workspace_root / self.config["paths"]["blueprint_dir"]
        self.theorems_dir = self.workspace_root / self.config["paths"]["theorems_dir"]
        self.content_file = self.workspace_root / self.config["paths"]["content_file"]

        # Store check results
        self.results: List[CheckResult] = []
        self.all_labels: Dict[str, Set[str]] = defaultdict(
            set
        )  # label -> set of file_paths
        self.file_labels: Dict[str, Set[str]] = defaultdict(
            set
        )  # file_path -> set of labels
        self.environment_blocks: List[EnvironmentBlock] = []

    def _load_config(self, config_path: str = None) -> Dict:
        """Load configuration file"""
        if config_path is None:
            config_path = Path(__file__).parent / "check_blueprints.json"

        try:
            with open(config_path, "r", encoding="utf-8") as f:
                return json.load(f)
        except FileNotFoundError:
            # If config file doesn't exist, use default config
            return {
                "environments": {
                    "require_label": ["lemma", "def", "theorem"],
                    "require_proof": ["lemma", "theorem"],
                    "must_be_referenced": ["lemma", "theorem"],
                },
                "rules": {
                    "check_label_uniqueness": True,
                    "check_dependencies": True,
                    "check_file_references": True,
                    "check_proof_bindings": True,
                    "check_chapter_first": True,
                    "check_theorem_folder_correspondence": True,
                },
                "paths": {
                    "blueprint_dir": "blueprint/src",
                    "theorems_dir": "blueprint/src/theorems",
                    "content_file": "blueprint/src/content.tex",
                },
            }

    def _strip_latex_comments(self, content: str) -> str:
        """Strip LaTeX comments (% to end of line), respecting escaped \\%"""
        return re.sub(r"(?<!\\)%[^\n]*", "", content)

    def _extract_environment_blocks(
        self, content: str, file_path: str
    ) -> List[EnvironmentBlock]:
        """Extract LaTeX environment blocks and process binding relationships"""
        # First extract all environment blocks
        all_blocks = self._extract_all_environment_blocks(content, file_path)

        # Process binding relationships
        return self._process_block_bindings(all_blocks)

    def _extract_all_environment_blocks(
        self, content: str, file_path: str
    ) -> List[EnvironmentBlock]:
        """Extract all LaTeX environment blocks (without processing binding relationships)"""
        blocks = []
        lines = content.split("\n")

        # Regex pattern to match environment start and end
        env_pattern = (
            r"\\begin\{("
            + "|".join(
                self.config["environments"]["require_label"]
                + ["proof"]  # proof environment always needs checking
            )
            + r")\}"
        )

        i = 0
        while i < len(lines):
            line = lines[i]
            match = re.search(env_pattern, line)
            if match:
                env_type = match.group(1)
                start_line = i + 1

                # Find corresponding \end{env_type}
                end_line = self._find_end_environment(lines, i, env_type)
                if end_line == -1:
                    i += 1
                    continue

                # Extract environment content
                env_content = "\n".join(lines[i : end_line + 1])

                # Extract label
                label = self._extract_label(env_content)

                # Extract uses
                uses = self._extract_uses(env_content)

                # Extract lean
                has_lean = self._extract_lean(env_content)

                block = EnvironmentBlock(
                    env_type=env_type,
                    label=label,
                    uses=uses,
                    start_line=start_line,
                    end_line=end_line + 1,
                    content=env_content,
                    file_path=file_path,
                    has_lean=has_lean,
                )
                blocks.append(block)

                # Recursively process nested environments (inside the found environment)
                nested_content = "\n".join(lines[i + 1 : end_line])
                nested_blocks = self._extract_all_environment_blocks(
                    nested_content, file_path
                )
                # Adjust line numbers for nested blocks
                for nested_block in nested_blocks:
                    nested_block.start_line += i + 1
                    nested_block.end_line += i + 1
                blocks.extend(nested_blocks)

                i = end_line + 1
            else:
                i += 1

        return blocks

    def _process_block_bindings(
        self, blocks: List[EnvironmentBlock]
    ) -> List[EnvironmentBlock]:
        """Process environment block binding relationships"""
        # Sort by line number
        blocks.sort(key=lambda x: x.start_line)

        result_blocks = []
        i = 0

        while i < len(blocks):
            block = blocks[i]

            # If environment type requires proof, check if followed by proof
            if block.env_type in self.config["environments"]["require_proof"]:
                # Check if next block is proof (allow any number of empty lines in between)
                if i + 1 < len(blocks) and blocks[i + 1].env_type == "proof":
                    proof_block = blocks[i + 1]
                    # Bind proof to lemma/theorem
                    block.proof_block = proof_block
                    proof_block.parent_block = block

                    # Merge proof's uses into lemma/theorem
                    block.uses.extend(proof_block.uses)

                    result_blocks.append(block)
                    i += 2  # Skip proof block
                else:
                    result_blocks.append(block)
                    i += 1
            else:
                # proof block should already be bound, skip
                if block.parent_block is None:
                    result_blocks.append(block)
                i += 1

        return result_blocks

    def _find_end_environment(
        self, lines: List[str], start_idx: int, env_type: str
    ) -> int:
        """Find environment end position"""
        end_pattern = rf"\\end\{{{re.escape(env_type)}\}}"
        depth = 1

        for i in range(start_idx + 1, len(lines)):
            line = lines[i]

            # Check if new environment of same type starts
            begin_pattern = rf"\\begin\{{{re.escape(env_type)}\}}"
            if re.search(begin_pattern, line):
                depth += 1

            # Check if environment ends
            if re.search(end_pattern, line):
                depth -= 1
                if depth == 0:
                    return i

        return -1

    def _extract_label(self, content: str) -> Optional[str]:
        """Extract label"""
        label_pattern = r"\\label\{([^}]+)\}"
        match = re.search(label_pattern, content)
        return match.group(1) if match else None

    def _extract_uses(self, content: str) -> List[str]:
        """Extract uses references"""
        uses_pattern = r"\\uses\{([^}]+)\}"
        matches = re.findall(uses_pattern, content)

        # Handle comma-separated multiple references
        all_uses = []
        for match in matches:
            # Split by comma and strip whitespace
            uses = [use.strip() for use in match.split(",")]
            all_uses.extend(uses)

        return all_uses

    def _extract_lean(self, content: str) -> bool:
        """Check if content contains \\lean{} command"""
        lean_pattern = r"\\lean\{[^}]*\}"
        return bool(re.search(lean_pattern, content))

    def _extract_lean_name(self, content: str) -> Optional[str]:
        """Extract the Lean declaration name from \\lean{name} command"""
        lean_pattern = r"\\lean\{([^}]+)\}"
        match = re.search(lean_pattern, content)
        return match.group(1).strip() if match else None

    def _check_tex_file(self, file_path: Path) -> List[CheckResult]:
        """Check single .tex file"""
        results = []

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
        except Exception as e:
            results.append(
                CheckResult(
                    success=False,
                    message=f"Cannot read file: {e}",
                    file_path=str(file_path),
                )
            )
            return results

        # Extract environment blocks (strip comments first)
        blocks = self._extract_environment_blocks(
            self._strip_latex_comments(content), str(file_path)
        )
        self.environment_blocks.extend(blocks)

        # Check each environment block
        for block in blocks:
            # Check label requirements
            if block.env_type in self.config["environments"]["require_label"]:
                if not block.label:
                    results.append(
                        CheckResult(
                            success=False,
                            message=f"{block.env_type} environment missing \\label",
                            file_path=str(file_path),
                            line_number=block.start_line,
                        )
                    )
                else:
                    # Check label uniqueness
                    current_file = str(file_path)

                    # Check for duplicates within same file
                    if block.label in self.file_labels[current_file]:
                        results.append(
                            CheckResult(
                                success=False,
                                message=f"Duplicate label within same file: {block.label}",
                                file_path=current_file,
                                line_number=block.start_line,
                            )
                        )
                    else:
                        # Record to file label set
                        self.file_labels[current_file].add(block.label)

                        # Check for duplicates across files
                        if block.label in self.all_labels:
                            other_files = self.all_labels[block.label]
                            results.append(
                                CheckResult(
                                    success=True,
                                    message=f"Duplicate label across files: {block.label} (already used in {', '.join(other_files)})",
                                    file_path=current_file,
                                    line_number=block.start_line,
                                    is_warning=True,
                                )
                            )

                        # Add current file to this label's file set
                        self.all_labels[block.label].add(current_file)

                # Check if has lean block
                if (
                    self.config["rules"]["check_lean_blocks"]
                    and block.env_type in self.config["environments"]["require_lean"]
                    and not block.has_lean
                ):
                    results.append(
                        CheckResult(
                            success=False,
                            message=f"{block.env_type} environment {block.label} missing \\lean{{}} block",
                            file_path=str(file_path),
                            line_number=block.start_line,
                        )
                    )

                # Check if followed by proof block
                if (
                    self.config["rules"]["check_proof_bindings"]
                    and block.env_type in self.config["environments"]["require_proof"]
                    and not block.proof_block
                ):
                    results.append(
                        CheckResult(
                            success=False,
                            message=f"{block.env_type} environment {block.label} missing \\proof block",
                            file_path=str(file_path),
                            line_number=block.start_line,
                        )
                    )

            elif block.env_type == "proof":
                # Check for standalone proof blocks
                if (
                    self.config["rules"]["check_proof_bindings"]
                    and not block.parent_block
                ):
                    results.append(
                        CheckResult(
                            success=False,
                            message=f"Found standalone \\proof block, should be bound to {', '.join(self.config['environments']['require_proof'])} environment",
                            file_path=str(file_path),
                            line_number=block.start_line,
                        )
                    )

        return results

    def _build_dependency_graph(
        self, blocks: List[EnvironmentBlock]
    ) -> Dict[str, Set[str]]:
        """Build dependency graph from blocks (label -> set of labels it uses)"""
        graph = {}
        for block in blocks:
            if block.label:
                graph[block.label] = set(block.uses)
        return graph

    def _detect_cycle(
        self,
        graph: Dict[str, Set[str]],
        start_node: str,
        visited: Set[str],
        rec_stack: Set[str],
    ) -> Optional[List[str]]:
        """Detect cycle in directed graph using DFS. Returns cycle path if found."""
        visited.add(start_node)
        rec_stack.add(start_node)

        if start_node in graph:
            for neighbor in graph[start_node]:
                if neighbor not in visited:
                    cycle = self._detect_cycle(graph, neighbor, visited, rec_stack)
                    if cycle:
                        return [start_node] + cycle
                elif neighbor in rec_stack:
                    # Found a cycle
                    return [start_node, neighbor]

        rec_stack.remove(start_node)
        return None

    def _find_all_cycles(self, graph: Dict[str, Set[str]]) -> List[List[str]]:
        """Find all cycles in the dependency graph"""
        visited = set()
        cycles = []

        for node in graph:
            if node not in visited:
                rec_stack = set()
                cycle = self._detect_cycle(graph, node, visited, rec_stack)
                if cycle:
                    cycles.append(cycle)

        return cycles

    def _compute_reachable(
        self, graph: Dict[str, Set[str]], start_nodes: Set[str]
    ) -> Set[str]:
        """Compute all nodes reachable from start_nodes (transitive closure)"""
        reachable = set()
        stack = list(start_nodes)

        while stack:
            node = stack.pop()
            if node in reachable:
                continue
            reachable.add(node)

            if node in graph:
                for neighbor in graph[node]:
                    if neighbor not in reachable:
                        stack.append(neighbor)

        return reachable

    def _check_circular_dependencies(self) -> List[CheckResult]:
        """Check for circular dependencies within each file"""
        results = []

        if not self.config["rules"].get("check_circular_dependencies", True):
            return results

        # Group blocks by file
        blocks_by_file = defaultdict(list)
        for block in self.environment_blocks:
            if (
                block.label
                and block.env_type in self.config["environments"]["require_label"]
            ):
                blocks_by_file[block.file_path].append(block)

        # Check each file separately
        for file_path, blocks in blocks_by_file.items():
            # Build dependency graph for this file only
            graph = self._build_dependency_graph(blocks)

            # Get all labels defined in this file
            file_labels = {block.label for block in blocks}

            # Filter graph to only include edges between labels defined in this file
            filtered_graph = {
                label: deps & file_labels
                for label, deps in graph.items()
                if label in file_labels
            }

            # Find cycles
            cycles = self._find_all_cycles(filtered_graph)

            for cycle in cycles:
                # Format cycle path
                cycle_path = " -> ".join(cycle)
                if cycle[0] == cycle[-1]:
                    cycle_path = " -> ".join(cycle)
                else:
                    cycle_path = " -> ".join(cycle) + " -> " + cycle[0]

                # Report error for the first block in the cycle
                first_label = cycle[0]
                block = next((b for b in blocks if b.label == first_label), None)
                if block:
                    results.append(
                        CheckResult(
                            success=False,
                            message=f"Circular dependency detected: {cycle_path}",
                            file_path=file_path,
                            line_number=block.start_line,
                        )
                    )

        return results

    def _check_transitive_usage(self) -> List[CheckResult]:
        """Check that all environments are used transitively by the final environment in each file"""
        results = []

        if not self.config["rules"].get("check_transitive_usage", True):
            return results

        # Group blocks by file
        blocks_by_file = defaultdict(list)
        for block in self.environment_blocks:
            if (
                block.label
                and block.env_type in self.config["environments"]["require_label"]
            ):
                blocks_by_file[block.file_path].append(block)

        # Check each file separately
        for file_path, blocks in blocks_by_file.items():
            if not blocks:
                continue

            # Sort blocks by line number to find the final environment
            sorted_blocks = sorted(blocks, key=lambda b: b.start_line)
            final_block = sorted_blocks[-1]

            # Build dependency graph
            graph = self._build_dependency_graph(blocks)

            # Find all labels defined in this file
            file_labels = {block.label for block in blocks}

            # Compute all labels reachable from the final block
            reachable = self._compute_reachable(graph, {final_block.label})

            # Check if all other labels in the file are reachable
            for block in blocks:
                if block.label != final_block.label and block.label not in reachable:
                    results.append(
                        CheckResult(
                            success=False,
                            message=f"{block.env_type} '{block.label}' is not used (transitively) by the final environment '{final_block.label}' in this file",
                            file_path=file_path,
                            line_number=block.start_line,
                        )
                    )

        return results

    def _check_dependencies(self) -> List[CheckResult]:
        """Check dependencies"""
        results = []

        if not self.config["rules"]["check_dependencies"]:
            return results

        # Collect all defined labels
        all_defined_labels = {
            block.label for block in self.environment_blocks if block.label
        }

        # Collect blocks that must be referenced (based on configuration)
        blocks_to_check = {
            block.label: block
            for block in self.environment_blocks
            if block.label
            and block.env_type
            in self.config["environments"].get("must_be_referenced", [])
        }

        # Collect all uses references
        all_uses = set()
        for block in self.environment_blocks:
            all_uses.update(block.uses)

        # Check for undefined uses references
        for block in self.environment_blocks:
            for use_ref in block.uses:
                if use_ref not in all_defined_labels:
                    results.append(
                        CheckResult(
                            success=False,
                            message=f"Undefined reference in \\uses: {use_ref}",
                            file_path=block.file_path,
                            line_number=block.start_line,
                        )
                    )

        # Check for unused labels
        for label, block in blocks_to_check.items():
            if label not in all_uses:
                results.append(
                    CheckResult(
                        success=False,
                        message=f"Unused {block.env_type}: {label}",
                        file_path=block.file_path,
                        line_number=block.start_line,
                    )
                )

        return results

    def _check_file_references(self) -> List[CheckResult]:
        """Check file references - ensures content.tex contains imports of exactly those files in theorems folder"""
        results = []

        if not self.config["rules"]["check_file_references"]:
            return results

        # Read content.tex file
        try:
            with open(self.content_file, "r", encoding="utf-8") as f:
                content = f.read()
        except Exception as e:
            results.append(
                CheckResult(
                    success=False,
                    message=f"Cannot read content.tex: {e}",
                    file_path=str(self.content_file),
                )
            )
            return results

        # Extract all \input{} references that point to theorems folder
        input_pattern = r"\\input\{([^}]+)\}"
        referenced_theorem_files = set()
        all_referenced_files = set()

        for match in re.finditer(input_pattern, content):
            ref_path = match.group(1)
            # Add .tex extension if not present
            if not ref_path.endswith(".tex"):
                ref_path += ".tex"
            all_referenced_files.add(ref_path)

            # Check if this reference points to theorems folder
            if ref_path.startswith("theorems/"):
                referenced_theorem_files.add(ref_path)

        # Get actual files in theorems folder
        actual_theorem_files = set()
        if self.theorems_dir.exists():
            for tex_file in self.theorems_dir.glob("*.tex"):
                relative_path = f"theorems/{tex_file.name}"
                actual_theorem_files.add(relative_path)

        # Check for files in theorems folder that are not referenced
        missing_references = actual_theorem_files - referenced_theorem_files
        for missing_file in missing_references:
            filename = missing_file.replace("theorems/", "")
            results.append(
                CheckResult(
                    success=False,
                    message=f"File {filename} exists in theorems folder but not referenced in content.tex",
                    file_path=str(self.theorems_dir / filename),
                )
            )

        # Check for references to theorems files that don't exist
        invalid_references = referenced_theorem_files - actual_theorem_files
        for invalid_ref in invalid_references:
            filename = invalid_ref.replace("theorems/", "")
            results.append(
                CheckResult(
                    success=False,
                    message=f"content.tex references {invalid_ref} but file does not exist in theorems folder",
                    file_path=str(self.content_file),
                )
            )

        return results

    def _check_chapter_first(self) -> List[CheckResult]:
        """Check that chapter comes first before any sections in theorems files"""
        results = []

        if not self.config["rules"]["check_chapter_first"]:
            return results

        # Check files in theorems folder
        if self.theorems_dir.exists():
            for tex_file in self.theorems_dir.glob("*.tex"):
                file_results = self._check_single_file_chapter_section_order(tex_file)
                results.extend(file_results)

        return results

    def _kebab_to_camel_case(self, kebab_str: str) -> str:
        """Convert kebab-case to UpperCamelCase"""
        components = kebab_str.split("-")
        return "".join(word.capitalize() for word in components)

    def _camel_to_kebab_case(self, camel_str: str) -> str:
        """Convert UpperCamelCase to kebab-case"""
        result = []
        for i, char in enumerate(camel_str):
            if char.isupper() and i > 0:
                result.append("-")
            result.append(char.lower())
        return "".join(result)

    def _check_single_file_chapter_section_order(
        self, file_path: Path
    ) -> List[CheckResult]:
        """Check chapter/section order in a single file"""
        results = []

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()
        except Exception as e:
            results.append(
                CheckResult(
                    success=False,
                    message=f"Cannot read file: {e}",
                    file_path=str(file_path),
                )
            )
            return results

        lines = content.split("\n")

        # Scan line by line until we find \chapter or \section
        for i, line in enumerate(lines):
            line_number = i + 1  # Convert to 1-based line number

            # Check for \chapter command
            if re.search(r"\\chapter\{", line):
                # Found \chapter first, this is correct
                return results

            # Check for \section command
            if re.search(r"\\section\{", line):
                # Found \section before any \chapter, this is an error
                results.append(
                    CheckResult(
                        success=False,
                        message="First \\section command found before any \\chapter command",
                        file_path=str(file_path),
                        line_number=line_number,
                    )
                )
                return results

        # If we reach here, no \chapter was found
        results.append(
            CheckResult(
                success=False,
                message="File must contain at least one \\chapter command",
                file_path=str(file_path),
            )
        )

        return results

    def _check_file_header_format(self) -> List[CheckResult]:
        """Check that each theorem file starts with \\chapter, then proof description, then a \\url somewhere in the opening paragraph"""
        results = []

        if not self.theorems_dir.exists():
            return results

        for tex_file in self.theorems_dir.glob("*.tex"):
            try:
                with open(tex_file, "r", encoding="utf-8") as f:
                    lines = f.readlines()
            except Exception as e:
                results.append(
                    CheckResult(
                        success=False,
                        message=f"Cannot read file: {e}",
                        file_path=str(tex_file),
                    )
                )
                continue

            # Collect non-blank, non-comment lines with their 1-based line numbers
            text_lines = []
            for i, line in enumerate(lines):
                stripped = line.strip()
                if stripped and not stripped.startswith("%"):
                    text_lines.append((i + 1, stripped))

            # Check line 1: must be \chapter{...}
            if not text_lines or not re.match(r"\\chapter\{", text_lines[0][1]):
                lineno = text_lines[0][0] if text_lines else None
                results.append(
                    CheckResult(
                        success=False,
                        message="First non-blank line must be a \\chapter{} command",
                        file_path=str(tex_file),
                        line_number=lineno,
                    )
                )
                continue

            # Check line 2: must match "This section contains a (stub of a) proof of ..." or "This section contains a proof of ..."
            if len(text_lines) < 2 or not re.match(
                r"This section contains a (\(stub of a\) )?proof of ", text_lines[1][1]
            ):
                lineno = text_lines[1][0] if len(text_lines) >= 2 else None
                results.append(
                    CheckResult(
                        success=False,
                        message='Second non-blank line must be "This section contains a (stub of a) proof of ..." or "This section contains a proof of ..."',
                        file_path=str(tex_file),
                        line_number=lineno,
                    )
                )
                continue

            # Check opening paragraph: must contain a \url{...} reference somewhere
            # before the first \begin{...} environment
            opening_lines = []
            for lineno, content in text_lines[2:]:
                if re.match(r"\\begin\{", content):
                    break
                opening_lines.append((lineno, content))
            if not any(
                re.search(r"\\url\{[^}]+\}", content) for _, content in opening_lines
            ):
                lineno = (
                    opening_lines[-1][0]
                    if opening_lines
                    else (text_lines[2][0] if len(text_lines) >= 3 else None)
                )
                results.append(
                    CheckResult(
                        success=False,
                        message="Opening paragraph must contain a \\url{} reference",
                        file_path=str(tex_file),
                        line_number=lineno,
                    )
                )

        return results

    def _check_theorem_folder_correspondence(self) -> List[CheckResult]:
        """Check that theorem files correspond to LiveLeanTriathlon folders"""
        results = []

        if not self.config["rules"].get("check_theorem_folder_correspondence", True):
            return results

        # Get theorem files (without .tex extension)
        theorem_files = set()
        if self.theorems_dir.exists():
            for tex_file in self.theorems_dir.glob("*.tex"):
                theorem_files.add(tex_file.stem)

        # Get LiveLeanTriathlon folders
        live_lean_triathlon_dir = self.workspace_root / "LiveLeanTriathlon"
        live_lean_triathlon_folders = set()
        if live_lean_triathlon_dir.exists():
            for item in live_lean_triathlon_dir.iterdir():
                if item.is_dir() and item.name not in ["Mathlib", "Mistakes"]:
                    live_lean_triathlon_folders.add(item.name)

        # Check that each theorem file has a corresponding folder
        for theorem_file in theorem_files:
            expected_folder = self._kebab_to_camel_case(theorem_file)
            if expected_folder not in live_lean_triathlon_folders:
                results.append(
                    CheckResult(
                        success=False,
                        message=f"Theorem file {theorem_file}.tex has no corresponding folder. Expected: LiveLeanTriathlon/{expected_folder}/",
                        file_path=str(self.theorems_dir / f"{theorem_file}.tex"),
                    )
                )

        return results

    def _check_theorem_env_present(self) -> List[CheckResult]:
        """Check that each .tex file in theorems/ contains at least one labelled
        environment (theorem/lemma/definition)."""
        results = []

        if not self.config["rules"].get("check_theorem_env_present", True):
            return results

        if not self.theorems_dir.exists():
            return results

        required_envs = set(self.config["environments"]["require_label"])

        # Group blocks by file path
        blocks_by_file: Dict[str, list] = defaultdict(list)
        for block in self.environment_blocks:
            if block.env_type in required_envs:
                blocks_by_file[block.file_path].append(block)

        for tex_file in sorted(self.theorems_dir.glob("*.tex")):
            file_path = str(tex_file)
            if not blocks_by_file.get(file_path):
                results.append(
                    CheckResult(
                        success=False,
                        message=(
                            f"Theorem file contains no labelled environment "
                            f"(expected at least one of: {sorted(required_envs)})"
                        ),
                        file_path=file_path,
                    )
                )

        return results

    def _check_lean_ams_tags(self) -> List[CheckResult]:
        """Check that the final environment in each theorem file has @[AMS ...] in the corresponding Lean file,
        and that the specific codes match those recorded in scripts/theorem_stats.json."""
        results = []

        if not self.config["rules"].get("check_lean_ams_tags", True):
            return results

        lean_dir = self.workspace_root / "LiveLeanTriathlon"
        if not lean_dir.exists():
            return results

        # Load the expected AMS codes from the stats file
        stats_file = self.workspace_root / "scripts" / "theorem_stats.json"
        expected_codes: Dict[str, List[int]] = {}
        if stats_file.exists():
            try:
                stats = json.loads(stats_file.read_text(encoding="utf-8"))
                expected_codes = {
                    name: (info["ams_codes"] if isinstance(info, dict) else info)
                    for name, info in stats.get("theorems", {}).items()
                    if (info["ams_codes"] if isinstance(info, dict) else info)
                }
            except Exception:
                pass  # treat as empty; missing/malformed stats file won't cause false positives

        # Build a map from lean declaration name -> sorted list of AMS codes
        # by scanning all .lean files once
        lean_ams_codes: Dict[str, List[int]] = {}
        decl_keywords = (
            r"(?:theorem|lemma|def|noncomputable\s+def|abbrev|structure|class|instance)"
        )
        ams_decl_pattern = re.compile(
            r"@\[[^\]]*\bAMS\b([^\]]*)\]"  # capture the numbers after AMS
            r"(?:\s*@\[[^\]]*\][^\S\n]*)*"  # optional additional attributes
            r"\s+"
            r"(?:" + decl_keywords + r")\s+"
            r"([\w.]+)",  # declaration name (may include namespace dots)
            re.MULTILINE,
        )
        for lean_file in lean_dir.rglob("*.lean"):
            try:
                content = lean_file.read_text(encoding="utf-8")
            except Exception:
                continue
            for m in ams_decl_pattern.finditer(content):
                nums = sorted(set(int(x) for x in m.group(1).split() if x.isdigit()))
                decl = m.group(2)
                lean_ams_codes[decl] = nums
                lean_ams_codes[decl.split(".")[-1]] = nums

        # Group environment blocks by file, restricted to theorem files
        theorem_files: Set[str] = set()
        if self.theorems_dir.exists():
            for tex_file in self.theorems_dir.glob("*.tex"):
                theorem_files.add(str(tex_file))

        blocks_by_file: Dict[str, list] = defaultdict(list)
        for block in self.environment_blocks:
            if (
                block.label
                and block.env_type in self.config["environments"]["require_label"]
                and block.file_path in theorem_files
            ):
                blocks_by_file[block.file_path].append(block)

        for file_path, blocks in blocks_by_file.items():
            if not blocks:
                continue

            # Find the final environment (highest line number)
            final_block = max(blocks, key=lambda b: b.start_line)

            lean_name = self._extract_lean_name(final_block.content)
            if not lean_name:
                continue  # Missing \lean{} already caught by check_lean_blocks

            # Also check the short name: declaration may live inside a `namespace` block,
            # so the file contains e.g. `theorem dilworth` while the tex uses `PartialOrder.dilworth`
            short_name = lean_name.split(".")[-1]
            actual_codes = lean_ams_codes.get(lean_name) or lean_ams_codes.get(
                short_name
            )

            if not actual_codes:
                results.append(
                    CheckResult(
                        success=False,
                        message=f"Final environment '{final_block.label}' (lean: {lean_name}) is missing @[AMS ...] attribute in Lean file",
                        file_path=file_path,
                        line_number=final_block.start_line,
                    )
                )
                continue

            # Look up what the stats file expects for this declaration
            expected = expected_codes.get(lean_name) or expected_codes.get(short_name)
            if expected is None:
                # Declaration has an AMS tag but is not tracked in theorem_stats.json
                results.append(
                    CheckResult(
                        success=False,
                        message=(
                            f"Final environment '{final_block.label}' (lean: {lean_name}) "
                            f"has @[AMS {actual_codes}] but is not recorded in scripts/theorem_stats.json. "
                            f"Run: python3 scripts/generate_theorem_stats.py"
                        ),
                        file_path=file_path,
                        line_number=final_block.start_line,
                    )
                )
            elif sorted(actual_codes) != sorted(expected):
                results.append(
                    CheckResult(
                        success=False,
                        message=(
                            f"Final environment '{final_block.label}' (lean: {lean_name}) "
                            f"has @[AMS {actual_codes}] but scripts/theorem_stats.json expects {expected}. "
                            f"Run: python3 scripts/generate_theorem_stats.py"
                        ),
                        file_path=file_path,
                        line_number=final_block.start_line,
                    )
                )

        return results

    def check_all(self) -> List[CheckResult]:
        """Execute all checks"""
        self.results = []
        self.all_labels = defaultdict(set)
        self.file_labels = defaultdict(set)
        self.environment_blocks = []

        # Check all .tex files
        if self.blueprint_dir.exists():
            for tex_file in self.blueprint_dir.rglob("*.tex"):
                if tex_file.name != "content.tex":  # content.tex handled separately
                    self.results.extend(self._check_tex_file(tex_file))

        # Check dependencies
        self.results.extend(self._check_dependencies())

        # Check circular dependencies
        self.results.extend(self._check_circular_dependencies())

        # Check transitive usage
        self.results.extend(self._check_transitive_usage())

        # Check file references
        self.results.extend(self._check_file_references())

        # Check chapter/section order
        self.results.extend(self._check_chapter_first())

        # Check file header format (chapter, proof description, url line)
        self.results.extend(self._check_file_header_format())

        # Check theorem folder correspondence
        self.results.extend(self._check_theorem_folder_correspondence())

        # Check AMS tags on final environments
        self.results.extend(self._check_lean_ams_tags())

        # Check that each theorem .tex file has at least one labelled environment
        self.results.extend(self._check_theorem_env_present())

        return self.results

    def print_results(self, verbose: bool = True, show_blocks: bool = False):
        """Print check results"""
        if show_blocks and self.environment_blocks:
            print("=== Environment Blocks Information ===")
            print(f"Found {len(self.environment_blocks)} environment blocks:")
            for i, block in enumerate(self.environment_blocks, 1):
                print(f"  {i}. {block.env_type}")
                print(f"      Label: {block.label}")
                print(f"      Uses: {block.uses}")
                print(f"      File: {block.file_path}")
                print(f"      Line range: {block.start_line}-{block.end_line}")
                print(f"      Bound proof: {'Yes' if block.proof_block else 'No'}")
                print(
                    f"      Parent block: {block.parent_block.label if block.parent_block else 'None'}"
                )
                print(
                    f"      Content preview: {block.content[:100].replace(chr(10), ' ')}..."
                )
                print()

            # Statistics
            env_types = {}
            for block in self.environment_blocks:
                env_types[block.env_type] = env_types.get(block.env_type, 0) + 1

            print(f"📊 Block Statistics:")
            print(f"   Total blocks: {len(self.environment_blocks)}")
            print(f"   Environment type distribution: {env_types}")

            # All labels
            labels = [block.label for block in self.environment_blocks if block.label]
            print(f"   Found labels: {labels}")

            # All uses references
            all_uses = [use for block in self.environment_blocks for use in block.uses]
            print(f"   Found uses references: {all_uses}")

            # Binding relationships
            print(f"\n🔗 Binding Relationships:")
            for block in self.environment_blocks:
                if block.env_type in ["lemma", "theorem"]:
                    if block.proof_block:
                        print(
                            f"   ✅ {block.env_type} {block.label} -> proof (line {block.proof_block.start_line})"
                        )
                    else:
                        print(f"   ❌ {block.env_type} {block.label} -> missing proof")
                elif block.env_type == "proof":
                    if block.parent_block:
                        print(
                            f"   ✅ proof (line {block.start_line}) -> {block.parent_block.env_type} {block.parent_block.label}"
                        )
                    else:
                        print(
                            f"   ❌ proof (line {block.start_line}) -> standalone proof block"
                        )
            print()

        if not self.results:
            print("✅ All checks passed!")
            return

        # Separate errors and warnings
        errors = [r for r in self.results if not r.success]
        warnings = [r for r in self.results if r.success and r.is_warning]

        if errors:
            print(f"❌ Found {len(errors)} errors:\n")
            for i, result in enumerate(errors, 1):
                location = (
                    f" ({result.file_path}:{result.line_number})"
                    if result.line_number
                    else f" ({result.file_path})"
                )
                print(f"{i}. ❌ {result.message}{location}")

        if warnings and verbose:
            print(f"\n⚠️  Found {len(warnings)} warnings:\n")
            for i, result in enumerate(warnings, 1):
                location = (
                    f" ({result.file_path}:{result.line_number})"
                    if result.line_number
                    else f" ({result.file_path})"
                )
                print(f"{i}. ⚠️  {result.message}{location}")
        elif warnings and not verbose:
            print(f"\n⚠️  Found {len(warnings)} warnings (use --verbose to see details)")

        if not errors and not warnings:
            print("✅ All checks passed!")


def main():
    """Main function"""
    parser = argparse.ArgumentParser(description="Check Blueprint LaTeX files")
    parser.add_argument(
        "--config",
        "-c",
        help="Configuration file path (default: check_blueprints.json)",
    )

    # Output control group
    output_group = parser.add_mutually_exclusive_group()
    output_group.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        default=True,
        help="Show all information including warnings (default: True)",
    )

    # Block information control
    parser.add_argument(
        "--conclusion",
        action="store_true",
        default=True,
        help="Print detailed environment block information and conclusion (default: True)",
    )

    args = parser.parse_args()

    # Determine output modes
    verbose = args.verbose
    show_blocks = args.conclusion

    checker = BlueprintChecker(args.config)
    results = checker.check_all()
    checker.print_results(verbose=verbose, show_blocks=show_blocks)

    # If there are errors (not warnings), exit with code 1
    errors = [r for r in results if not r.success]
    if errors:
        exit(1)


if __name__ == "__main__":
    main()
