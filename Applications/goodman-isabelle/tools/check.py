#!/usr/bin/env python3
"""Serial verification against pinned core sources, embedded or standalone."""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_path(root, name):
    path = (root / name).resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError("Manifest path escapes its root: " + name)
    return path


def default_core(root=ROOT):
    enclosing = root.parent.parent
    if root.parent.name == "Applications" and (enclosing / "ROOT").is_file():
        return enclosing
    return root.parent / "bacon-dorr-isabelle"


def embedded_core(root, core):
    return root.parent.name == "Applications" and core.resolve() == root.parent.parent.resolve()


def core_fingerprints(core):
    paths = [core / "ROOT"]
    if (core / "ROOTS").exists():
        paths.append(core / "ROOTS")
    paths.extend(p for p in (core / "theories").rglob("*")
                 if p.is_file() and p.suffix in {".thy", ".ML", ".sml"})
    return {p.relative_to(core).as_posix(): sha256(p) for p in sorted(paths)}


def verify_inputs(core):
    pin = json.loads((ROOT / "dependencies/bacon-dorr.json").read_text())
    if not (core / "ROOT").is_file():
        raise SystemExit("Core checkout not found. See README.md or set BACON_DORR_ROOT.")
    actual = core_fingerprints(core)
    if actual != pin["sha256"]:
        raise SystemExit("Core source drift: use the pinned revision; do not silently refresh its manifest.")
    if (core / ".git").exists() and not embedded_core(ROOT, core):
        revision = subprocess.check_output(["git", "-C", str(core), "rev-parse", "HEAD"], text=True).strip()
        if revision != pin["revision"]:
            raise SystemExit("Core Git revision differs from the dependency pin.")
    frozen = json.loads((ROOT / "verification/provenance/frozen.json").read_text())["theories"]
    for item in frozen:
        if sha256(safe_path(ROOT, item["frozen"])) != item["frozen_sha256"]:
            raise SystemExit("Preserved-source drift: " + item["frozen"])
    mode = "Embedded core source hashes match the pinned baseline" if embedded_core(ROOT, core) else "Core revision/source hashes match"
    print(f"{mode}; {len(frozen)} preserved files unchanged.", flush=True)


def verify_snapshot():
    data = json.loads((ROOT / "verification/provenance/extraction.json").read_text())
    expected = {row["path"]: row["sha256"] for row in data["theories"]}
    actual = {p.relative_to(ROOT).as_posix(): sha256(p) for p in (ROOT / "theories").rglob("*.thy")}
    if expected != actual:
        raise SystemExit("Theory tree differs from the initial extraction (expected after reviewed development).")
    print(f"All {len(actual)} theory files are byte-identical to the extraction snapshot.", flush=True)


def trust_scan():
    for p in (ROOT / "theories").rglob("*.thy"):
        text = p.read_text()
        if re.search(r"(?m)^\s*(sorry|oops|axiomatization|oracle)\b", text) or "quick_and_dirty" in text:
            raise SystemExit("Disallowed proof escape: " + p.relative_to(ROOT).as_posix())


def run_logged(command, log):
    with log.open("x") as out:
        out.write("Command: " + repr(command) + "\n")
        out.flush()
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True, bufsize=1)
        for line in process.stdout:
            print(line, end="", flush=True)
            out.write(line)
            out.flush()
        code = process.wait()
        out.write("\nExit status: " + str(code) + "\n")
    if code:
        raise SystemExit(code)


def audit_summary(directory):
    catalogs = sorted(directory.rglob("*-audit.txt"))
    rows = 0
    replay = 0
    for path in catalogs:
        text = path.read_text()
        rows += len(re.findall(r"oracles=0 residual_hyps=0 flex_flex=0", text))
        replay += sum(map(int, re.findall(r"(\d+) clean historical replay endpoints", text)))
    return {"catalogs": len(catalogs), "integration_entries": rows - replay,
            "historical_replay_entries": replay, "clean_rows": rows}


def audit_catalogs(directory):
    return {p.relative_to(directory).as_posix(): sorted(re.findall(
        r"(?m)^([^:\n]+): oracles=0 residual_hyps=0 flex_flex=0 statement_premises=\d+$", p.read_text()))
        for p in directory.rglob("*-audit.txt")}


def validate_catalogs(actual, expected):
    if not expected or actual != expected:
        raise ValueError("Audit exports differ from verification/catalogs.json: missing, extra or changed entries. Review the catalog manifest explicitly.")


def active_isabelle_processes(output, own_pid):
    found = []
    for line in output.splitlines():
        fields = line.split(maxsplit=1)
        if len(fields) != 2 or fields[0] == str(own_pid):
            continue
        try:
            args = shlex.split(fields[1])
        except ValueError:
            found.append(line)  # Fail conservatively on unparseable candidates.
            continue
        tool = any(Path(arg).name == "isabelle" or arg == "isabelle.Isabelle_Tool" for arg in args)
        if tool and any(arg in {"build", "export"} for arg in args):
            found.append(line)
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core", type=Path, default=Path(os.environ.get("BACON_DORR_ROOT", default_core())))
    parser.add_argument("--inputs-only", action="store_true")
    parser.add_argument("--snapshot", action="store_true", help="Also verify the initial extraction byte-for-byte")
    parser.add_argument("--export", action="store_true", help="Export all integration audits after the successful build")
    args = parser.parse_args()
    core = args.core.expanduser().resolve()
    verify_inputs(core)
    if args.snapshot:
        verify_snapshot()
    trust_scan()
    subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", str(ROOT / "tools/tests")], check=True)
    if args.inputs_only:
        return
    runs = ROOT / "verification/runs"
    runs.mkdir(parents=True, exist_ok=True)
    with (ROOT / "verification/build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        active = subprocess.run(["pgrep", "-fl", "isabelle.*(build|export)"], capture_output=True, text=True)
        candidates = active_isabelle_processes(active.stdout, os.getpid())
        if candidates:
            raise SystemExit("Another possible Isabelle build/export is active; inspect first:\n" + "\n".join(candidates))
        stamp = datetime.datetime.now().strftime("%Y-%m-%dT%H-%M-%S-%f")
        log = runs / ("build-" + stamp + ".log")
        print("Build log:", log, flush=True)
        run_logged(["isabelle", "build", "-v", "-j", "1", "-d", str(core), "-D", str(ROOT),
                    "-o", "timeout=60", "-o", "export_theory=true"], log)
        verify_inputs(core)
        if args.export:
            output = ROOT / "verification/exports" / stamp
            output.mkdir(parents=True, exist_ok=False)
            sessions = re.findall(r"^session (Goodman_Integration_\S+)", (ROOT / "ROOT").read_text(), re.M)
            for session in sessions:
                run_logged(["isabelle", "export", "-n", "-d", str(core), "-d", str(ROOT),
                            "-O", str(output), "-x", "*:*-audit.txt", "-x", "*:*-statements.txt", session],
                           runs / ("export-" + stamp + "-" + session + ".log"))
            expected = json.loads((ROOT / "verification/catalogs.json").read_text())
            validate_catalogs(audit_catalogs(output), expected)
            summary = audit_summary(output)
            with (output / "summary.json").open("x") as out:
                json.dump(summary, out, indent=2)
                out.write("\n")
            print("Export:", output, summary, flush=True)


if __name__ == "__main__":
    main()
