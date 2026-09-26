#!/usr/bin/env python3
"""Lexical regression guard, NOT an Isabelle parser or an ML security sandbox.

Policy: reject proof-hole/axiom/oracle commands and quick_and_dirty outside
comments, strings and cartouches; inspect embedded executable text and all
local .ML files for an explicit denylist of trust-changing ML identifiers.
All non-document cartouches receive this conservative ML inspection. Quoted
ML command bodies are inspected too. ML_file paths must be literal, local,
existing .ML files; those files are inspected even outside theories/.
ML document antiquotations are rejected for manual review, not treated as
inert prose. Ordinary document text and non-ML document antiquotations remain
opaque; custom antiquotation behavior is outside this lexical policy.

Nested comments, escaped double-quoted strings, and nested ASCII-symbol or
Unicode cartouches are recognized. Unclosed lexical regions fail closed.
Only the initial UTF-8 source is examined. Arbitrary ML, antiquotations,
aliases, generated code, custom commands, process execution and external
session heaps can defeat any lexical denylist. This check does not replace
kernel-object audits, a reviewed axiom inventory, or manual ML review.
It intentionally rejects some harmless uses of the listed identifiers;
do not add a blanket ML exemption to accommodate such a false positive.
"""

from dataclasses import dataclass
from pathlib import Path
import argparse
import re
import sys


FORBIDDEN_OUTER = frozenset({
    "sorry", "oops", "admit", "axiomatization", "axioms", "oracle",
    "quick_and_dirty",
})
# Match identifier components, so qualification/line breaks/comments do not
# disguise references, and `open Skip_Proof; cheat_tac` is also rejected.
FORBIDDEN_ML = frozenset({
    "Skip_Proof", "cheat_tac", "skip_proof", "make_thm", "make_thm_cterm", "prove_sorry",
    "sorry_proof", "add_axiom", "add_axioms", "add_axiom_global",
    "add_axioms_global", "add_oracle", "invoke_oracle", "quick_and_dirty",
    "ML_Context", "ML_Compiler", "ML_Compiler0", "ML_Antiquotation",
    "Outer_Syntax", "PolyML", "use", "use_text",
})
PROSE = frozenset({
    "chapter", "section", "subsection", "subsubsection", "paragraph",
    "subparagraph", "text", "text_raw", "txt", "txt_raw",
})
ML_COMMANDS = frozenset({
    "ML", "ML_val", "ML_prf", "ML_command", "SML", "SML_export",
    "setup", "local_setup", "method_setup", "attribute_setup",
    "simproc_setup", "declaration", "syntax_declaration", "parse_ast_translation",
    "parse_translation", "print_translation", "typed_print_translation",
    "print_ast_translation", "code_printing",
})
ML_FILES = frozenset({"ML_file", "ML_file_debug", "ML_file_no_debug", "SML_file"})
OPEN_CARTOUCHES = ("\\<open>", "‹")
CLOSE_CARTOUCHES = ("\\<close>", "›")
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")
DOCUMENT_ML = re.compile(r"@\{\s*ML(?:_[A-Za-z_]+)?\b|\\<\^ML(?:_[A-Za-z_]+)?>")


@dataclass(frozen=True)
class Token:
    kind: str
    value: str
    start: int
    end: int
    content_start: int


class LexicalError(ValueError):
    def __init__(self, offset, message):
        super().__init__(message)
        self.offset = offset


def opening_at(source, pos, markers):
    return next((m for m in markers if source.startswith(m, pos)), None)


def lex(source):
    """Yield regions/tokens with original source offsets; comments are omitted."""
    pos = 0
    while pos < len(source):
        start = pos
        if source[pos].isspace():
            pos += 1
        elif source.startswith("(*", pos):
            depth = 1
            pos += 2
            while pos < len(source) and depth:
                if source.startswith("(*", pos):
                    depth += 1
                    pos += 2
                elif source.startswith("*)", pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            if depth:
                raise LexicalError(start, "unterminated nested comment")
        elif source.startswith("*)", pos):
            raise LexicalError(start, "unmatched comment close")
        elif source[pos] == '"':
            pos += 1
            body = pos
            while pos < len(source):
                if source[pos] == "\\":
                    pos += 2
                elif source[pos] == '"':
                    break
                else:
                    pos += 1
            if pos >= len(source):
                raise LexicalError(start, "unterminated quoted string")
            yield Token("string", source[body:pos], start, pos + 1, body)
            pos += 1
        elif marker := opening_at(source, pos, OPEN_CARTOUCHES):
            pos += len(marker)
            body = pos
            depth = 1
            while pos < len(source) and depth:
                if marker := opening_at(source, pos, OPEN_CARTOUCHES):
                    depth += 1
                    pos += len(marker)
                elif marker := opening_at(source, pos, CLOSE_CARTOUCHES):
                    depth -= 1
                    close = pos
                    pos += len(marker)
                else:
                    pos += 1
            if depth:
                raise LexicalError(start, "unterminated cartouche")
            yield Token("cartouche", source[body:close], start, pos, body)
        elif opening_at(source, pos, CLOSE_CARTOUCHES):
            raise LexicalError(start, "unmatched cartouche close")
        elif source.startswith("\\<comment>", pos):
            pos += len("\\<comment>")
            yield Token("document_comment", "", start, pos, start)
        elif source.startswith("--", pos) or source[pos] == "―":
            pos += 2 if source.startswith("--", pos) else 1
            yield Token("document_comment", "", start, pos, start)
        elif match := IDENTIFIER.match(source, pos):
            pos = match.end()
            yield Token("identifier", match.group(), start, pos, start)
        else:
            pos += 1
            yield Token("symbol", source[start:pos], start, pos, start)


def decode_outer_string(raw):
    # Only outer quote/backslash escapes are decoded. In particular, Isabelle
    # symbols such as \<open> and ML string escape sequences are not evaluated.
    return re.sub(r'\\([\\"])', r"\1", raw)


def inspect_ml(source, base=0):
    findings = []
    previous = None
    try:
        for token in lex(source):
            if token.kind == "identifier" and token.value in FORBIDDEN_ML:
                findings.append((base + token.start, f"forbidden ML trust identifier: {token.value}"))
            elif token.kind == "cartouche":
                # Conservative treatment of nested executable/antiquotation
                # cartouches. ML strings and nested ML comments stay opaque.
                findings.extend(inspect_ml(token.value, base + token.content_start))
            elif token.kind == "string" and previous in {"put_bool", "put_bool_default"}:
                if decode_outer_string(token.value) == "quick_and_dirty":
                    findings.append((base + token.start, "forbidden ML option update: quick_and_dirty"))
            previous = token.value
    except LexicalError as error:
        findings.append((base + error.offset, str(error)))
    return findings


def inspect_theory(source):
    """Return (findings, literal ML_file references), without accessing files."""
    findings, references = [], []
    pending = None
    try:
        tokens = list(lex(source))
        for index, token in enumerate(tokens):
            if token.kind == "identifier":
                # Locale facts named .axioms and a binding `and axioms:` are
                # not the obsolete axiom-introducing outer command. Keep this
                # narrow exemption; punctuation alone must not hide a command.
                qualified = (index >= 2 and tokens[index - 1].value == "."
                             and tokens[index - 2].kind == "identifier"
                             and tokens[index - 2].end == tokens[index - 1].start
                             and tokens[index - 1].end == token.start)
                axiom_label = (token.value == "axioms" and index > 0
                               and tokens[index - 1].value in {
                                   "and", "have", "assume", "assumes", "lemma",
                                   "theorem", "corollary", "proposition"}
                               and index + 1 < len(tokens) and tokens[index + 1].value == ":")
                if token.value in FORBIDDEN_OUTER and not (qualified or axiom_label):
                    findings.append((token.start, f"forbidden Isabelle trust token: {token.value}"))
                # The symbol \<proof> is an alias of sorry (Pure); it lexes as
                # the adjacent tokens \ < proof >, so it is caught here.
                proof_symbol = (token.value == "proof" and index >= 2 and index + 1 < len(tokens)
                                and tokens[index - 1].value == "<" and tokens[index - 2].value == "\\"
                                and tokens[index - 2].end == tokens[index - 1].start
                                and tokens[index - 1].end == token.start
                                and tokens[index + 1].value == ">"
                                and token.end == tokens[index + 1].start)
                if proof_symbol:
                    findings.append((tokens[index - 2].start, "forbidden Isabelle trust token: \\<proof>"))
                if pending == "file":
                    findings.append((token.start, "ML_file requires a quoted literal local .ML path"))
                    pending = None
                if pending is None:
                    if token.value in PROSE:
                        pending = "prose"
                    elif token.value in ML_COMMANDS:
                        pending = "ml"
                    elif token.value in ML_FILES:
                        pending = "file"
            elif token.kind == "document_comment":
                pending = "prose"
            elif token.kind in {"string", "cartouche"}:
                if pending == "file":
                    if token.kind != "string":
                        findings.append((token.start, "ML_file requires a quoted literal local .ML path"))
                    else:
                        references.append((token.start, decode_outer_string(token.value)))
                elif pending == "prose":
                    for match in DOCUMENT_ML.finditer(token.value):
                        findings.append((token.content_start + match.start(),
                                         "ML document antiquotation forbidden by lexical policy; requires manual review"))
                elif pending == "ml" or token.kind == "cartouche":
                    content = decode_outer_string(token.value) if token.kind == "string" else token.value
                    findings.extend(inspect_ml(content, token.content_start))
                pending = None
        if pending == "file":
            findings.append((len(source), "ML_file has no literal local .ML path"))
    except LexicalError as error:
        findings.append((error.offset, str(error)))
    return findings, references


def source_files(root):
    """All preserved theory sources, not just the selected proof closure."""
    return sorted({*root.joinpath("theories").rglob("*.thy"),
                   *root.joinpath("theories").rglob("*.ML"),
                   *root.joinpath("theories").rglob("*.sml"), root / "ROOT"})


def check_repository(root):
    root = root.resolve()
    pending = source_files(root)
    visited, findings = set(), []
    while pending:
        path = pending.pop()
        resolved = path.resolve()
        if resolved in visited:
            continue
        visited.add(resolved)
        if not resolved.is_relative_to(root):
            findings.append(f"{path}: source resolves outside repository")
            continue
        try:
            source = resolved.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            findings.append(f"{path}: unreadable source: {error}")
            continue
        if path.suffix in {".ML", ".sml"}:
            issues, references = inspect_ml(source), []
        else:
            issues, references = inspect_theory(source)
        for offset, ref in references:
            target = (resolved.parent / ref).resolve()
            if not target.is_relative_to(root) or target.suffix != ".ML" or not target.is_file():
                issues.append((offset, f"ML_file must name an existing repository-local .ML file: {ref}"))
            else:
                pending.append(target)
        for offset, message in issues:
            line = source.count("\n", 0, offset) + 1
            findings.append(f"{path.relative_to(root)}:{line}: {message}")
    return len(visited), sorted(findings)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    count, findings = check_repository(args.root)
    if findings:
        print("ISABELLE-TRUST-SOURCE-FAILED", file=sys.stderr)
        print("\n".join(findings), file=sys.stderr)
        return 1
    print(f"ISABELLE-TRUST-SOURCE-CLEAN: {count} files; lexical policy only, not an ML sandbox")
    return 0


if __name__ == "__main__":
    sys.exit(main())
