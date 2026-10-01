#!/usr/bin/env python3
"""Check local source coverage; not a replacement for Isabelle or source review."""
from pathlib import Path
import re

APP = Path(__file__).resolve().parents[1]
root = (APP / "ROOT").read_text(encoding="utf-8")

# Parse every session: name, directory, theories block (sessions blocks ignored).
sessions = {}
for block in re.split(r"\n(?=session )", root.strip()):
    head = re.match(r'session\s+(\S+)\s+in\s+"([^"]+)"', block)
    assert head, ("unparsed session header", block[:60])
    name, directory = head.groups()
    assert "timeout = 60" in block, ("missing timeout", name)
    body = block.split("  theories\n", 1)
    assert len(body) == 2, ("no theories block", name)
    theories = re.findall(r"^    ([A-Za-z_][A-Za-z_0-9]*)\s*$", body[1], re.M)
    sessions[name] = (APP / directory, theories)

selected = {}
for name, (directory, theories) in sessions.items():
    files = {p.stem: p for p in directory.glob("*.thy")}
    assert set(theories) == set(files), ("ROOT/source mismatch", name, set(theories) ^ set(files))
    for theory in theories:
        assert theory not in selected, ("theory in two sessions", theory)
        selected[theory] = files[theory]

all_files = {p.resolve() for p in (APP / "theories").rglob("*.thy")}
selected_files = {p.resolve() for p in selected.values()}
assert all_files == selected_files, ("unselected theory files", sorted(map(str, all_files ^ selected_files)))

local_sessions = set(sessions)
for name, path in sorted(selected.items()):
    source = path.read_text(encoding="utf-8")
    assert re.search(r"^theory\s+" + re.escape(name) + r"\b", source), path
    header = source.split("\nbegin", 1)[0]
    assert "/Users/" not in header and "Higher_Order_Metaphysics" not in header, path
    assert "../" not in header, ("unexpected path import", path)
    for imported in re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', header.split("imports", 1)[1]):
        qualifier, _, base = imported.rpartition(".")
        if qualifier and qualifier not in local_sessions:
            continue
        if base.startswith("Typed_") or base.startswith("Classicism_"):
            assert base in selected, ("missing local theory", path, imported)
            if qualifier:
                assert selected[base].parent == sessions[qualifier][0], ("wrong session qualifier", path, imported)

assert "Classicism_2_11_Audit" in selected
print(f"2.11-PACKAGE-CLEAN: {len(selected)} theory files in {len(sessions)} sessions, "
      "all selected; no parent-research imports")
