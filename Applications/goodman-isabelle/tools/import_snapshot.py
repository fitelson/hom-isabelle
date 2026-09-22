#!/usr/bin/env python3
"""One-time, non-overwriting extraction; not needed to build this repository.

Copies theory bytes unchanged and mechanically relocates session directories.
The source integration directory and both upstream repositories stay untouched.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]


def relocated(path):
    parts = Path(path).parts
    first = {"theories": "axiom_extension", "legacy": "preserved",
             "legacy-additions": "preserved-additions"}.get(parts[0], parts[0])
    return Path("theories", first, *parts[1:])


def save_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x") as out:
        json.dump(value, out, indent=2, sort_keys=True)
        out.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    args = parser.parse_args()
    source = args.source.resolve()
    if (ROOT / "theories").exists() or (ROOT / "ROOT").exists():
        raise SystemExit("Refusing to overwrite an existing extraction.")
    files = []
    for path in sorted(source.rglob("*.thy")):
        relative = path.relative_to(source)
        if relative.parts[0] in {"verification", "pp_model_attempt_2026_09_19"}:
            continue
        dest = ROOT / relocated(relative)
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, dest)
        files.append({"source": relative.as_posix(),
                      "path": dest.relative_to(ROOT).as_posix(),
                      "sha256": hashlib.sha256(dest.read_bytes()).hexdigest()})
    for path in [source / "ROOT", *sorted((source / "legacy").rglob("ROOT")),
                 *sorted((source / "legacy-additions").rglob("ROOT"))]:
        relative = path.relative_to(source)
        dest = ROOT / (relative if len(relative.parts) == 1 else relocated(relative))
        dest.parent.mkdir(parents=True, exist_ok=True)
        text = path.read_text()
        if relative.as_posix() == "ROOT":
            text = re.sub(r'\bin "([^"]+)"',
                          lambda m: 'in "' + relocated(m[1]).as_posix() + '"', text)
        with dest.open("x") as out:
            out.write(text)
    with (ROOT / "ROOTS").open("x") as out:
        out.write("\n".join(relocated(p).as_posix()
                            for p in (source / "ROOTS").read_text().splitlines()) + "\n")
    inputs = json.loads((source / "verification/inputs.json").read_text())
    save_json(ROOT / "dependencies/bacon-dorr.json", {
        "repository": "https://github.com/fitelson/hom-isabelle.git",
        "revision": inputs["core"]["head"], "sha256": inputs["core"]["sha256"]})
    frozen = []
    for path in [source / "legacy/manifest.json",
                 *sorted((source / "legacy-additions").glob("*/manifest.json"))]:
        for item in json.loads(path.read_text())["theories"]:
            row = dict(item)
            row["frozen"] = relocated(row["frozen"]).as_posix()
            frozen.append(row)
    save_json(ROOT / "verification/provenance/frozen.json", {
        "description": "82 preserved historical theory bodies; only import headers were adapted before extraction.",
        "source_repository": "https://github.com/fitelson/higher-order-metaphysics-in-isabelle",
        "source_head": inputs["goodman_reference"]["head"],
        "source_includes_uncommitted_work": True, "theories": frozen})
    save_json(ROOT / "verification/provenance/extraction.json", {
        "date": "2026-09-20", "source_directory_name": source.name,
        "source_is_git_checkout": False,
        "theory_bytes_unchanged": True, "theories": files,
        "unselected_theories": [
            "theories/preserved-additions/exact-enumeration/Bacon_PP_ZF_Exact_Enumeration.thy",
            "theories/preserved-additions/exact-completeness/Bacon_PP_ZF_Exact_Completeness.thy"]})
    print(f"Copied {len(files)} theory files unchanged; recorded {len(frozen)} frozen bodies.")


if __name__ == "__main__":
    main()
