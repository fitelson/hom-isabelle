#!/usr/bin/env python3
"""Check core-only packaging and enumerate the local ROOT/import closure.

This is a packaging check, not an Isabelle parser or a proof checker.
The Isabelle build is the authoritative check of imports and proofs.
"""
import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def inventory():
    root = (ROOT / "ROOT").read_text()
    blocks = re.split(r"(?=^session )", root, flags=re.M)
    sessions, selected = [], []
    for block in blocks:
        match = re.match(r'session (\w+) in "([^"]+)"', block)
        if not match:
            continue
        name, directory = match.groups()
        assert name.startswith("Bacon_"), name
        assert directory.startswith(("theories/base", "theories/classicism", "theories/core_audit")), directory
        sessions.append(name)
        tail = block.split("\n  theories\n", 1)[1]
        selected.extend(re.findall(r"^    (\w+)\s*$", tail, flags=re.M))
    files = {}
    for path in (ROOT / "theories").rglob("*.thy"):
        text = path.read_text()
        name = re.search(r"^theory (\w+)", text, flags=re.M)
        assert name, path
        key = name.group(1)
        assert key not in files, ("duplicate theory", key)
        files[key] = path
    visited = set()
    pending = list(selected)
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        assert name in files, ("missing local theory", name)
        visited.add(name)
        text = files[name].read_text()
        header = text.split("\nbegin", 1)[0]
        imported = header.split("imports", 1)[1]
        for item in re.findall(r"[A-Za-z_][A-Za-z_0-9.]*", imported):
            short = item.rsplit(".", 1)[-1]
            if short in files:
                pending.append(short)
            elif short.startswith("Bacon_"):
                raise AssertionError(("unresolved project import", name, item))
        assert not re.search(r"\b(?:Goodman_\w*|Bacon_PP_\w*|AOT)\b", imported), name
    unselected = sorted(str(files[n].relative_to(ROOT)) for n in files.keys() - visited)
    return {"sessions": sessions, "checked_source_closure": sorted(str(files[n].relative_to(ROOT)) for n in visited),
            "unselected_source_files": unselected}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--inventory", action="store_true")
    args = p.parse_args()
    data = inventory()
    for forbidden in ["theories/goodman", "theories/zalta", "sources/pdfs", "vampire",
                      "finite_core_search", "pure_diagonal_search"]:
        assert not (ROOT / forbidden).exists(), forbidden
    required = {"Bacon_Book_ZF_Countable_Model_Existence.thy", "Bacon_Book_ZF_Model_Existence_Audit.thy"}
    assert required <= {Path(x).name for x in data["checked_source_closure"]}
    assert not any(Path(x).name in required for x in data["unselected_source_files"])
    if args.inventory:
        print(json.dumps(data, indent=2))
    else:
        print("CORE-ONLY-PACKAGING-CLEAN: %d sessions, %d reachable .thy files, %d preserved unselected .thy files"
              % (len(data["sessions"]), len(data["checked_source_closure"]), len(data["unselected_source_files"])))


if __name__ == "__main__":
    main()
