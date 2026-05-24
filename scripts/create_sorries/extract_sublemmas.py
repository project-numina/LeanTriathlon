import re
from copy import copy
from typing import Any

DOT_KEYS = [".", "·"]
DOT_KEYS_TUPLE = (".", "·")

# Lean 4 modifiers that may appear before a `theorem` / `lemma` / `def` / etc. keyword.
# Detected so the parser still recognizes the declaration even when prefixed.
DECL_MODIFIERS = frozenset(
    {"private", "protected", "noncomputable", "partial", "unsafe", "@[expose]"}
)


# ====================================================
# parser
# ====================================================
class LeanCodeParser:
    def __init__(self, code: str):
        self.original_code = code
        self.original_lines = code.splitlines()
        self.cleaned_lines = self.strip_comments_and_blank_lines(code)
        self.cleaned_code = "\n".join(self.cleaned_lines)

    def formatting(self, code: str, keys: list[str] | None = None) -> str:
        """Format the code by adding spaces around operators."""
        if keys is None:
            keys = [":="]
        ret = re.sub(r":=", " := ", code, flags=re.DOTALL)
        ret = re.sub(r"  :=", " :=", ret, flags=re.DOTALL)
        ret = re.sub(r":=  ", ":= ", ret, flags=re.DOTALL)
        ret = re.sub(r":= \n", ":=\n", ret, flags=re.DOTALL)
        return ret  # noqa RET504

    def strip_brackets(self, code: str) -> str:
        pattern = r"\([^()]*?\)|{[^{}]*?}|\[[^\[\]]*?\]"
        return re.sub(pattern, "", code)

    @staticmethod
    def _strip_comments(code: str) -> str:
        """Strip ``/- ... -/`` block comments and ``-- ...`` line comments.

        Preserves ``/-- ... -/`` docstrings and string literals so that
        ``--`` inside ``"foo--bar"`` or inside a docstring is left intact.
        Block comments may nest (Lean syntax). String literals support ``\\``
        escapes.
        """
        out: list[str] = []
        i = 0
        n = len(code)
        while i < n:
            c = code[i]
            # String literal
            if c == '"':
                j = i + 1
                while j < n:
                    if code[j] == "\\" and j + 1 < n:
                        j += 2
                        continue
                    if code[j] == '"':
                        j += 1
                        break
                    j += 1
                out.append(code[i:j])
                i = j
                continue
            # Docstring /-- ... -/
            if c == "/" and code.startswith("/--", i):
                depth = 1
                j = i + 3
                while j < n and depth > 0:
                    if code.startswith("/-", j):
                        depth += 1
                        j += 2
                    elif code.startswith("-/", j):
                        depth -= 1
                        j += 2
                    else:
                        j += 1
                out.append(code[i:j])
                i = j
                continue
            # Block comment /- ... -/
            if c == "/" and code.startswith("/-", i):
                depth = 1
                j = i + 2
                while j < n and depth > 0:
                    if code.startswith("/-", j):
                        depth += 1
                        j += 2
                    elif code.startswith("-/", j):
                        depth -= 1
                        j += 2
                    else:
                        j += 1
                i = j
                continue
            # Line comment -- ...
            if c == "-" and code.startswith("--", i):
                j = code.find("\n", i)
                if j == -1:
                    break
                i = j  # keep the newline
                continue
            out.append(c)
            i += 1
        return "".join(out)

    def strip_comments_and_blank_lines(self, code: str) -> list[str]:
        cleaned = []
        tmp_code = self._strip_comments(code)
        tmp_code = self.formatting(tmp_code)
        for line in tmp_code.splitlines():
            stripped_line = line.rstrip()
            if not stripped_line.strip():
                continue
            noind_stripped = stripped_line.lstrip()
            if noind_stripped.startswith((". ", "· ")):
                indent = len(stripped_line) - len(noind_stripped)
                dot_line = " " * indent + "."
                rest_line = " " * (indent + 2) + noind_stripped[2:]
                cleaned.append(dot_line)
                if rest_line.strip():
                    cleaned.append(rest_line)
            else:
                cleaned.append(stripped_line)
        return cleaned

    def get_indent(self, line: str) -> int:
        return len(line) - len(line.lstrip(" "))

    def extract_headers(self) -> dict:
        """
        each import and opens should only in one line

        out:
        {
            "import_list": ["Mathlib", "Aesop"],
            "open_list": ["Nat", "Real", "Polynomial"],
            "set_option_list": ["set_option maxHeartbeats 0"]
        }
        """
        import_list = []
        open_list = []
        set_option_list = []
        import_lines = []
        open_lines = []
        set_option_lines = []
        for line in self.cleaned_lines:
            tokens = line.split()
            key = tokens[0]
            if key == "import":
                import_list.extend(
                    copy(tokens[1:]),
                )  # Use extend instead of append in loop
                import_lines.append(line)
            elif key == "open":
                open_list.extend(
                    copy(tokens[1:]),
                )  # Use extend instead of append in loop
                open_lines.append(line)
            elif key == "set_option":
                set_option_list.append(line)
                set_option_lines.append(line)
        if "scoped" in open_list:
            open_list.remove("scoped")
        return {
            "import_list": import_list,
            "open_list": open_list,
            "set_option_list": set_option_list,
            "import_lines": import_lines,
            "open_lines": open_lines,
            "set_option_lines": set_option_lines,
        }

    def extract_other(
        self,
        keys: list[str] | None = None,
        except_line_prefix_list: list[str] | None = None,
    ) -> str:
        if keys is None:
            keys = ["theorem", "lemma"]

        if except_line_prefix_list is None:
            except_line_prefix_list = ["import", "open", "set_option"]

        blocks = self.extract_all_blocks(
            keys=keys,
            allow_overlap=False,
        )

        # except key blocks
        if not blocks:
            selected_lines = self.cleaned_lines
        else:
            in_block_ranges = sorted(
                [(block["start"], block["end"]) for block in blocks]
            )
            selected_lines = []
            current_bid = 0
            for lid, line in enumerate(self.cleaned_lines):
                while (
                    current_bid < len(in_block_ranges)
                    and lid > in_block_ranges[current_bid][1]
                ):
                    current_bid += 1

                is_in_block = False
                if current_bid < len(in_block_ranges):
                    block_start, block_end = in_block_ranges[current_bid]
                    if block_start <= lid <= block_end:
                        is_in_block = True
                if not is_in_block:
                    selected_lines.append(line)

        # except lines with specific prefix
        return "\n".join(
            [
                line
                for line in selected_lines
                if not any(
                    line.strip().startswith(prefix)
                    for prefix in except_line_prefix_list
                )
            ],
        ).strip()

    @staticmethod
    def extract_name_from_code(code: str, key: str, default="this") -> str | None:
        """
        examples:
            'key v1 : xxx'         ->      'v1'
            'key : xxx'            ->      'this'
            'key := xxx'           ->      'this'
            'key t1 (x : T) : ...' ->      't1'
            'key (x : T) : ...'    ->      'this'
            'private key v1 : xxx' ->      'v1'  (modifiers stripped)
        """
        code = code.strip()
        while True:
            tokens = code.split(maxsplit=1)
            if tokens and tokens[0] in DECL_MODIFIERS:
                code = tokens[1] if len(tokens) > 1 else ""
            else:
                break
        if not code.startswith(f"{key} "):
            return None

        rest = code[len(key) :].strip()

        # Use tuple for multiple startswith checks
        if rest.startswith((":", "(", ":=")):
            return default

        match = re.match(r"^([^ :\{\[\(]+)", rest)
        if match:
            return match.group(1)

        # Shouldn't goto here if there's no error
        return None

    @staticmethod
    def get_all_theorem_names(code: str) -> list[str]:
        """
        get all theorem names from the code
        """
        p = LeanCodeParser(code)
        blocks = p.extract_all_blocks(keys=["theorem", "lemma"])
        return [block["info"]["name"] for block in blocks]

    @staticmethod
    def get_theorem_name(code: str, default: str = "this") -> str:
        """
        examples:
            'theorem v1 : xxx'         ->      'v1'
            'theorem : xxx'            ->      'this'
            'theorem := xxx'           ->      'this'
            'theorem t1 (x : T) : ...' ->      't1'
        """
        assert code.startswith(
            ("theorem", "lemma")
        ), f"code must start with 'theorem' or 'lemma', but got {code}"
        if code.startswith("theorem"):
            return LeanCodeParser.extract_name_from_code(code, "theorem", default)
        return LeanCodeParser.extract_name_from_code(code, "lemma", default)

    def extract_statement_and_proof_from_code(
        self,
        code: str,
    ) -> tuple[str, str] | None:
        """
        example:
            'have : 1 + 1 = 2 := by sorry'      ->      ('have : 1 + 1 = 2', 'by sorry')
        """
        if ":=" not in code:
            return None

        pos = _find_top_level_walrus(code)
        if pos is not None:
            statement = code[:pos].strip()
            proof = code[pos + 2:].strip()
            return (statement, proof)

        parts = code.split(":=", maxsplit=1)
        statement = parts[0].strip()
        proof = parts[1].strip() if len(parts) == 2 else ""
        return (statement, proof)

    def parse_block(self, lines: list[str], key: str):
        """
        in:
            Make sure lines is actually a have block

        out:
        {
            "name"          :   str
            "statement"     :   str   "theorem ___ {_} (_):__"
            "proof"         :   str   "by ___" or "___"
            "with_sorry"    :   Bool
            "proof_style"   :   str   "tactic" / "term" / "unknown"
            "inner_indent"  :   inner_indent
        }
        """

        raw = "\n".join(lines)

        if key in DOT_KEYS:
            name = "."

            statement = "."
            proof = raw.lstrip()[1:].lstrip()

        else:
            name = self.extract_name_from_code(lines[0], key=key)

            statement, proof = self.extract_statement_and_proof_from_code(raw) or (
                "",
                "",
            )

        with_sorry = "sorry" in raw.split()

        proof_style = (
            "tactic"
            if proof.startswith("by")
            else ("dot_block" if key in DOT_KEYS else ("term" if proof else "unknown"))
        )

        # inner_indent
        cleaned_raw_proof = re.sub(r"^[^\n]*", "", proof, count=1)
        cleaned_raw_proof = re.sub(r"^(?:\s*\n)+", "", cleaned_raw_proof, count=1)
        inner_indent = len(cleaned_raw_proof) - len(cleaned_raw_proof.lstrip())
        if inner_indent <= 0:
            inner_indent = self.get_indent(lines[0]) + 2

        return {
            "name": name,
            "statement": statement,
            "proof": proof,
            "with_sorry": with_sorry,
            "proof_style": proof_style,
            "inner_indent": inner_indent,
        }

    def get_block_from_lid(
        self,
        start_line_index: int,
        keys: list[str] | None = None,
    ) -> dict[str, Any]:
        """Get a block from a line index.
        out:
        {
            "key"           :   str
            "start"         :   start line (int)
            "end"           :   end line (int)
            "lines"         :   content (List[str])
            "indent"        :   base indent (int)
            "key"           :   key
            "info"          :   call parse_block (Dict)
        }
        """

        if keys is None:
            keys = ["theorem"]

        if start_line_index >= len(self.cleaned_lines):
            return None

        start_line = self.cleaned_lines[start_line_index]
        tokens = start_line.split()
        i = 0
        while i < len(tokens) and tokens[i] in DECL_MODIFIERS:
            i += 1
        if i >= len(tokens) or tokens[i] not in keys:
            return None
        key = tokens[i]

        start_indent = self.get_indent(start_line)
        block_lines = [start_line]
        i = start_line_index + 1
        while i < len(self.cleaned_lines):
            line = self.cleaned_lines[i]
            line_indent = self.get_indent(line)
            if line_indent > start_indent:
                block_lines.append(line)
                i += 1
            elif not line.strip():
                # actually not necessary, but put it here for safe
                i += 1
            elif line_indent == start_indent:
                if key in DOT_KEYS:
                    break
                # in case someone wrote the statement in multiple line and didn't indent
                if ":=" not in self.strip_brackets("\n".join(block_lines)):
                    block_lines.append(line)
                    i += 1
                else:
                    break
            else:
                break

        info = self.parse_block(block_lines, key=key)

        return {
            "start": start_line_index,
            "end": i - 1,
            "lines": block_lines,
            "indent": start_indent,
            "key": key,
            "info": info,
        }

    def _docstring_line_indices(self) -> set[int]:
        """Return the set of cleaned-line indices that fall inside a ``/-- ... -/`` docstring.

        Used so block detection ignores lines like ``Using lemma \\ref{lem:foo}``
        that appear inside attribute docstrings and would otherwise be parsed
        as Lean declarations.
        """
        indices: set[int] = set()
        code = "\n".join(self.cleaned_lines)
        i = 0
        n = len(code)
        line = 0
        depth = 0
        doc_start_line = -1
        while i < n:
            if code[i] == "\n":
                if depth > 0 and line > doc_start_line:
                    indices.add(line)
                line += 1
                i += 1
                continue
            if depth == 0 and code.startswith("/--", i):
                depth = 1
                doc_start_line = line
                i += 3
                continue
            if depth > 0:
                if code.startswith("/-", i):
                    depth += 1
                    i += 2
                    continue
                if code.startswith("-/", i):
                    depth -= 1
                    i += 2
                    continue
            i += 1
        return indices

    def extract_all_blocks(
        self,
        keys: list[str] | None = None,
        allow_overlap: bool = True,
        min_proof_lines: int = 0,
        max_proof_lines: int = 10000,
    ) -> Any:
        """Extract all blocks from the code."""
        if keys is None:
            keys = ["theorem"]

        in_doc = self._docstring_line_indices()
        blocks = []
        i = 0
        while i < len(self.cleaned_lines):
            if i in in_doc:
                i += 1
                continue
            block = self.get_block_from_lid(i, keys=keys)

            if (
                block
                and min_proof_lines
                <= len(block["info"]["proof"].splitlines())
                <= max_proof_lines
            ):
                blocks.append(block)
                if not allow_overlap:
                    i = block["end"]
            i += 1
        return blocks

    def block_to_axiom(self, block: dict) -> str:
        """
        convert a block to an axiom

        replace statement[key] -> axiom
        remove proof
        """
        res = block["info"]["statement"].replace(block["key"], "axiom", 1)
        return res


# ====================================================
# tools
# ====================================================


def create_statement_with_lemmas(
    original_statement: str,
    lemmas: list[str],
) -> str:
    """
    headers : import / open
    original_statement :
        should contain exactly one theorem, no def / abbrev
        'theorem' should be at the beginning of one line
        the proof should have nonempty indentation
    lemmas :
        should only contain theorems / lemmas, no def / abbrev
        'theorem / lemma' should be at the beginning of one line
        the proof should have nonempty indentation
    """
    final_import_set = set()
    final_open_set = set()
    final_set_option_set = set()
    final_other_set = set()
    final_lemma_codes = []
    final_main_theorem_codes = []

    # handle original_statement
    p = LeanCodeParser(original_statement)
    headers = p.extract_headers()
    blocks = p.extract_all_blocks(keys=["theorem", "lemma"], allow_overlap=False)
    other = p.extract_other()
    if len(other) > 0:
        final_other_set.add(other)
    final_import_set = final_import_set.union(headers["import_list"])
    final_open_set = final_open_set.union(headers["open_list"])
    final_set_option_set = final_set_option_set.union(headers["set_option_list"])
    final_main_theorem_codes = ["\n".join(block["lines"]) for block in blocks]

    # handle lemmas
    for lemma_raw in lemmas:
        p = LeanCodeParser(lemma_raw)
        headers = p.extract_headers()
        blocks = p.extract_all_blocks(keys=["theorem", "lemma"], allow_overlap=False)
        other = p.extract_other()
        if len(other) > 0:
            final_other_set.add(other)
        final_import_set = final_import_set.union(headers["import_list"])
        final_open_set = final_open_set.union(headers["open_list"])
        final_set_option_set = final_set_option_set.union(headers["set_option_list"])
        for block in blocks:
            raw = "\n".join(block["lines"])
            raw = raw.replace("theorem ", "lemma ", 1)
            final_lemma_codes.append(raw)

    final_code = ""
    for x in sorted(final_import_set):
        final_code += f"import {x}"
        final_code += "\n"
    final_code += "\n"

    if len(final_set_option_set) > 0:
        for x in sorted(final_set_option_set):
            final_code += x.strip()
            final_code += "\n"
        final_code += "\n"

    if len(final_open_set) > 0:
        final_code += "open"
        for x in sorted(final_open_set):
            final_code += f" {x}"
        final_code += "\n"

    if len(final_other_set) > 0:
        final_code += "\n"
        for x in sorted(final_other_set):
            final_code += x
            final_code += "\n\n"

    final_code += "\n"
    for x in final_lemma_codes:
        final_code += x
        final_code += "\n\n"
    final_code += "\n"

    for x in final_main_theorem_codes:
        final_code += x
        final_code += "\n\n"

    return final_code, final_lemma_codes


def _find_top_level_walrus(text: str) -> int | None:
    """Return the position of the first proof-introducing ``:=`` in ``text``.

    "Proof-introducing" excludes ``:=`` that belong to ``let``-bindings inside
    the theorem signature (e.g. ``lemma foo : let x := 1; … := by …``). The
    algorithm tracks bracket depth (so default values inside ``(x := default)``
    are skipped) and a per-``let`` counter (so each ``let``'s ``:=`` is also
    skipped before we accept the proof boundary).
    """
    paren = bracket = brace = 0
    let_pending = 0
    i = 0
    n = len(text)
    while i < n - 1:
        c = text[i]
        if c == "(":
            paren += 1
            i += 1
            continue
        if c == ")":
            paren -= 1
            i += 1
            continue
        if c == "[":
            bracket += 1
            i += 1
            continue
        if c == "]":
            bracket -= 1
            i += 1
            continue
        if c == "{":
            brace += 1
            i += 1
            continue
        if c == "}":
            brace -= 1
            i += 1
            continue
        if (
            paren == 0
            and bracket == 0
            and brace == 0
            and text.startswith("let ", i)
            and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_"))
        ):
            let_pending += 1
            i += 4
            continue
        if c == ":" and text[i + 1] == "=" and paren == 0 and bracket == 0 and brace == 0:
            if let_pending > 0:
                let_pending -= 1
                i += 2
                continue
            return i
        i += 1
    return None


def gen_one_sorry_of_block(
    original_cleaned: str, block_to_replace: dict[str, Any]
) -> str:
    blockinfo = block_to_replace["info"]
    raw_block = "\n".join(block_to_replace["lines"])
    sorry_str = "by sorry" if blockinfo["proof_style"] in ["tactic"] else "sorry"

    walrus_pos = _find_top_level_walrus(raw_block)
    if walrus_pos is None:
        # No top-level := found — leave the original unchanged.
        return original_cleaned

    raw_block_with_sorry = raw_block[:walrus_pos] + ":= " + sorry_str
    return original_cleaned.replace(raw_block, raw_block_with_sorry, 1)


def create_proof_with_sorries(
    original_statement: str,
    keys: list[str] = ["have", "replace"],
    max_sorry_cnt: int = 100000,
    min_proof_lines: int = 0,
    max_proof_lines: int = 100000,
) -> str:
    p = LeanCodeParser(original_statement)
    blocks = p.extract_all_blocks(
        keys=keys,
        allow_overlap=False,
        min_proof_lines=min_proof_lines,
        max_proof_lines=max_proof_lines,
    )
    blocks = sorted(blocks, key=lambda x: x["end"] - x["start"], reverse=True)
    blocks = blocks[:max_sorry_cnt]
    raw_cleaned = "\n".join(p.cleaned_lines)
    for block in blocks:
        raw_cleaned = gen_one_sorry_of_block(raw_cleaned, block)
    return raw_cleaned

def add_newlines_before_keys(code: str, keys: list[str]) -> str:
    """
    add newlines before the lines that start with the keys
    """
    lines = code.splitlines()
    result_lines = []

    for line in lines:
        if any(line.startswith(key) for key in keys):
            result_lines.append("")
        result_lines.append(line)

    return "\n".join(result_lines)

def remove_imports(code: str, prefixes: list[str]) -> str:
    lines = code.splitlines()
    result_lines = []
    for line in lines:
        if not line.startswith("import"):
            result_lines.append(line)
            continue
        package_name = line.split()[1]
        if any(package_name.startswith(prefix) for prefix in prefixes):
            continue
        result_lines.append(line)
    return "\n".join(result_lines)

def convert_not_last_to_axiom(code: str, keys: list[str] = ["theorem", "lemma"]) -> str:
    """
    convert all theorems and lemmas to axioms, except the last one
    """
    p = LeanCodeParser(code)
    blocks = p.extract_all_blocks(keys=keys, allow_overlap=False)
    for block in blocks[:-1]:
        orig_str = "\n".join(block["lines"])
        axiom_str = p.block_to_axiom(block)
        code = code.replace(orig_str, axiom_str, 1)
    return code
