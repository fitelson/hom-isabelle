#!/usr/bin/env python3
"""Query the exact Isabelle entity/dependency graph without third-party packages."""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
import json
from pathlib import Path
import sys


def load_graph(path: Path):
    graph = json.loads(path.read_text(encoding="utf-8"))
    nodes = {node["id"]: node for node in graph["nodes"]}
    outgoing = defaultdict(list)
    incoming = defaultdict(list)
    for edge in graph["edges"]:
        outgoing[edge["source"]].append(edge)
        incoming[edge["target"]].append(edge)
    return graph, nodes, outgoing, incoming


def resolve(nodes, query: str) -> list[str]:
    needle = query.casefold()
    exact = [
        node_id
        for node_id, node in nodes.items()
        if needle in {
            node_id.casefold(),
            node["name"].casefold(),
            node["short_name"].casefold(),
        }
    ]
    if exact:
        return sorted(exact)
    return sorted(
        node_id
        for node_id, node in nodes.items()
        if needle in node_id.casefold()
        or needle in node["name"].casefold()
        or needle in node.get("statement", "").casefold()
    )


def describe(node: dict) -> str:
    location = ""
    if node.get("file"):
        location = f" [{node['file']}"
        if node.get("line"):
            location += f":{node['line']}"
        location += "]"
    external = " external" if node.get("external") else ""
    return f"{node['id']} ({node['kind']}{external}){location}"


def choose(nodes, query: str) -> str:
    matches = resolve(nodes, query)
    if not matches:
        raise SystemExit(f"No node matches: {query}")
    if len(matches) > 1:
        shown = "\n".join(f"  {item}" for item in matches[:30])
        extra = "" if len(matches) <= 30 else f"\n  ... {len(matches) - 30} more"
        raise SystemExit(f"Ambiguous query ({len(matches)} matches):\n{shown}{extra}")
    return matches[0]


def walk(start, adjacency, allowed_kinds, depth):
    seen = {start}
    queue = deque([(start, 0)])
    result = []
    while queue:
        current, distance = queue.popleft()
        if distance >= depth:
            continue
        for edge in adjacency.get(current, []):
            if allowed_kinds and edge["kind"] not in allowed_kinds:
                continue
            other = edge["target"] if edge["source"] == current else edge["source"]
            result.append((distance + 1, edge, other))
            if other not in seen:
                seen.add(other)
                queue.append((other, distance + 1))
    return result


def command_stats(graph) -> None:
    print(json.dumps(graph["stats"], indent=2, sort_keys=True))


def command_search(nodes, query, limit) -> None:
    matches = resolve(nodes, query)
    for node_id in matches[:limit]:
        print(describe(nodes[node_id]))
    if len(matches) > limit:
        print(f"... {len(matches) - limit} more", file=sys.stderr)


def command_explain(nodes, outgoing, incoming, query) -> None:
    node_id = choose(nodes, query)
    node = nodes[node_id]
    print(describe(node))
    if node.get("type"):
        print(f"type: {node['type']}")
    if node.get("statement"):
        print(f"statement: {node['statement']}")
    print("outgoing:")
    for edge in sorted(outgoing.get(node_id, []), key=lambda item: (item["kind"], item["target"])):
        print(f"  {edge['kind']} -> {describe(nodes[edge['target']])}")
    print("incoming:")
    for edge in sorted(incoming.get(node_id, []), key=lambda item: (item["kind"], item["source"])):
        print(f"  {edge['kind']} <- {describe(nodes[edge['source']])}")


def command_walk(nodes, adjacency, query, kinds, depth, reverse=False) -> None:
    node_id = choose(nodes, query)
    allowed = set(kinds) if kinds else set()
    for distance, edge, other in walk(node_id, adjacency, allowed, depth):
        arrow = "<-" if reverse else "->"
        print(f"{distance}: {edge['kind']} {arrow} {describe(nodes[other])}")


def command_path(nodes, outgoing, incoming, source_query, target_query, undirected) -> None:
    source = choose(nodes, source_query)
    target = choose(nodes, target_query)
    queue = deque([source])
    parent = {source: None}
    parent_edge = {}
    while queue and target not in parent:
        current = queue.popleft()
        candidates = list(outgoing.get(current, []))
        if undirected:
            candidates.extend(incoming.get(current, []))
        for edge in candidates:
            other = edge["target"] if edge["source"] == current else edge["source"]
            if other not in parent:
                parent[other] = current
                parent_edge[other] = edge
                queue.append(other)
    if target not in parent:
        raise SystemExit("No path found")
    chain = []
    current = target
    while current != source:
        chain.append((parent[current], parent_edge[current], current))
        current = parent[current]
    chain.reverse()
    print(describe(nodes[source]))
    for previous, edge, current in chain:
        direction = "->" if edge["source"] == previous else "<-"
        print(f"  {edge['kind']} {direction} {describe(nodes[current])}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--graph",
        type=Path,
        default=None,
        help="graph JSON path; overrides --family",
    )
    parser.add_argument(
        "--family",
        choices=("bacon",),
        default="bacon",
        help="theory-family graph to query (default: bacon)",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    subparsers.add_parser("stats")

    search = subparsers.add_parser("search")
    search.add_argument("query")
    search.add_argument("--limit", type=int, default=30)

    explain = subparsers.add_parser("explain")
    explain.add_argument("query")

    for name in ("deps", "used-by"):
        command = subparsers.add_parser(name)
        command.add_argument("query")
        command.add_argument("--depth", type=int, default=1)
        command.add_argument(
            "--kind",
            action="append",
            dest="kinds",
            help="edge kind to follow; repeatable",
        )

    path = subparsers.add_parser("path")
    path.add_argument("source")
    path.add_argument("target")
    path.add_argument("--directed", action="store_true")

    args = parser.parse_args()
    graph_path = args.graph or Path("isabelle-kg") / args.family / "graph.json"
    graph, nodes, outgoing, incoming = load_graph(graph_path)

    if args.command == "stats":
        command_stats(graph)
    elif args.command == "search":
        command_search(nodes, args.query, args.limit)
    elif args.command == "explain":
        command_explain(nodes, outgoing, incoming, args.query)
    elif args.command == "deps":
        kinds = args.kinds or ["DEPENDS_ON"]
        command_walk(nodes, outgoing, args.query, kinds, args.depth)
    elif args.command == "used-by":
        kinds = args.kinds or ["DEPENDS_ON"]
        command_walk(nodes, incoming, args.query, kinds, args.depth, reverse=True)
    elif args.command == "path":
        command_path(
            nodes, outgoing, incoming, args.source, args.target, not args.directed
        )


if __name__ == "__main__":
    main()
