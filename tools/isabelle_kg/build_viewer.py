#!/usr/bin/env python3
"""Generate an offline, audit-free session viewer from a saved Isabelle export.

Python standard library only. This does not run Isabelle, refresh the export,
or change graph.json. Theory ownership comes from qualified theory names,
not the exporter session field (which may describe a session importing it).
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
TEMPLATE = Path(__file__).with_name("viewer.html")
PLACEHOLDER = "__ISABELLE_GRAPH_DATA__"


def is_audit(node: dict) -> bool:
    path = str(node.get("file", "")).replace("\\", "/")
    name = str(node.get("name", "")).lower()
    return "/core_audit/" in path or "audit" in name or "catalog" in name


def session_label(name: str) -> str:
    label = name.removeprefix("Bacon_").removesuffix("_Development")
    label = label.replace("Lambda_I", "λI").replace("ZF", "HOL–ZF")
    return label.replace("_", " ")


def project_graph(graph: dict) -> dict:
    """Induced mathematical-theory graph, aggregated by owning session.

    Edges through excluded theories are NOT contracted into new edges.
    Regression theories containing mathematical examples are retained unless
    their own name/path identifies them as audit or catalog infrastructure.
    """
    if graph.get("schema") != "isabelle-kg-v1":
        raise ValueError("expected an isabelle-kg-v1 export")
    sessions = set(graph["sessions"])
    owners = {}
    seen = set()
    excluded = 0
    for node in graph["nodes"]:
        if node["id"] in seen:
            raise ValueError("duplicate node ID: " + node["id"])
        seen.add(node["id"])
        if node["kind"] != "theory" or node.get("external", False):
            continue
        # Core views must not pick up application material from a custom export.
        path_parts = str(node.get("file", "")).replace("\\", "/").split("/")
        if "Applications" in path_parts:
            continue
        if is_audit(node):
            excluded += 1
            continue
        owner, separator, _ = node["name"].partition(".")
        if not separator or owner not in sessions:
            raise ValueError("cannot resolve qualified theory owner: " + node["name"])
        owners[node["id"]] = owner
    if not owners:
        raise ValueError("no non-audit project theories in this export")
    counts = Counter(owners.values())
    names = sorted(counts)
    index = {name: i for i, name in enumerate(names)}
    imports = {
        (edge["source"], edge["target"])
        for edge in graph["edges"]
        if edge["kind"] == "IMPORTS"
        and edge["source"] in owners and edge["target"] in owners
        and owners[edge["source"]] != owners[edge["target"]]
    }
    links = Counter((index[owners[a]], index[owners[b]]) for a, b in imports)
    theory_names = {node["name"] for node in graph["nodes"] if node["id"] in owners}
    retained = {
        node["id"] for node in graph["nodes"]
        if not node.get("external", False) and (
            node["id"] in owners
            or (node["kind"] == "session" and node["name"] in counts)
            or (node["kind"] not in ("session", "theory")
                and node.get("theory") in theory_names)
        )
    }
    connections = sum(edge["source"] in retained and edge["target"] in retained
                      for edge in graph["edges"])
    return {
        "names": names,
        "labels": [session_label(name) for name in names],
        "counts": [counts[name] for name in names],
        "edges": [[a, b, n] for (a, b), n in sorted(links.items())],
        "excluded_audit_theories": excluded,
        "theories": len(owners),
        "mathematical_nodes": len(retained),
        "mathematical_connections": connections,
    }


def render_viewer(graph: dict, digest: str, template: str) -> str:
    if template.count(PLACEHOLDER) != 1:
        raise ValueError("viewer template must contain exactly one data placeholder")
    data = project_graph(graph)
    data["source_sha256"] = digest
    payload = json.dumps(data, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    # Prevent graph names from terminating the inert JSON script element.
    for char in ("<", ">", "&", "\u2028", "\u2029"):
        payload = payload.replace(char, "\\u%04x" % ord(char))
    return template.replace(PLACEHOLDER, payload)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, default=ROOT / "isabelle-kg/bacon/graph.json",
                        help="existing export (default: repository isabelle-kg/bacon/graph.json)")
    parser.add_argument("--output", type=Path,
                        help="HTML destination (default: viewer.html next to the input graph)")
    parser.add_argument("--force", action="store_true", help="replace an existing generated HTML file")
    args = parser.parse_args(argv)
    source = args.graph.expanduser().resolve()
    output = args.output.expanduser() if args.output else source.with_name("viewer.html")
    try:
        if not source.is_file():
            raise ValueError("graph export not found; first run tools/isabelle_kg/build_graph.sh serially")
        if output.is_symlink() or output.resolve() == source:
            raise ValueError("output must not be a symlink or the input graph")
        if output.suffix.lower() != ".html":
            raise ValueError("output must have the .html extension")
        if output.exists() and not args.force:
            raise ValueError("output exists; use --force to regenerate this HTML file")
        raw = source.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        graph = json.loads(raw)
        del raw
        html = render_viewer(graph, digest, TEMPLATE.read_text(encoding="utf-8"))
        output.parent.mkdir(parents=True, exist_ok=True)
        # Exclusive creation unless replacement was explicitly requested.
        with output.open("w" if args.force else "x", encoding="utf-8", newline="\n") as handle:
            handle.write(html)
        print("Viewer: " + str(output.resolve()))
        print("Open this file in a browser; no server, network access, or API account is needed.")
        print("Snapshot only: generating the viewer does not refresh Isabelle's export.")
        return 0
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print("Viewer generation failed: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
