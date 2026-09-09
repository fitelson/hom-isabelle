# Isabelle-native dependency graph

The graph is generated from Isabelle's exported theory/proof metadata.
It is not an AI-generated approximation. It covers only the selected
core sessions in this standalone repository.

From the repository root:

```sh
./tools/isabelle_kg/build_graph.sh
python3 tools/isabelle_kg/query_graph.py stats
python3 tools/isabelle_kg/query_graph.py search paper_named_closed_strong_completeness
python3 tools/isabelle_kg/query_graph.py explain paper_ZF_arbitrary_signature_action_iff
python3 tools/isabelle_kg/query_graph.py deps paper_ZF_arbitrary_signature_action_iff --depth 2
```

The build command first checks the core, compiles the bundled Scala exporter,
then extracts proof dependencies and runs the maintained dependency-policy
checks. Run it serially, never beside another Isabelle build or export.
It requires no API access or third-party Python libraries.

Data is written to `isabelle-kg/bacon/graph.json` and is not committed.
The `bacon` directory name is retained for tool compatibility; there is
only one graph family here. Graph output includes local source locations.
Rebuild after changing theory sources; stale graphs are not current evidence.

`DEPENDS_ON` edges concern exported proof dependencies. They do not establish
that a formal statement exactly matches its published source.
