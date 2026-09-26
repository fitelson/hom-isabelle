# Isabelle-native dependency graph

The graph is generated from Isabelle's exported theory/proof metadata.
It is not an AI-generated approximation. It covers only the selected
core sessions in this standalone repository.

From the repository root:

```sh
./tools/isabelle_kg/build_graph.sh
python3 tools/isabelle_kg/query_graph.py stats
python3 tools/isabelle_kg/query_graph.py search paper_named_closed_strong_completeness
python3 tools/isabelle_kg/query_graph.py search generic_interpretation_exists
python3 tools/isabelle_kg/query_graph.py explain paper_ZF_arbitrary_signature_action_iff
python3 tools/isabelle_kg/query_graph.py deps paper_ZF_arbitrary_signature_action_iff --depth 2
```

The build command first checks the core, compiles the bundled Scala exporter,
then extracts proof dependencies and runs the maintained dependency-policy
checks. Run it serially, never beside another Isabelle build or export.
It requires no API access or third-party Python libraries.

For ambiguous names, search first and copy the full returned node ID into
`explain`. The [reading guide](READING_GUIDE.md#reading-a-theorem) gives an
example and explains why a displayed machine statement is not the preferred
mathematical presentation. To distinguish build, source-review and explicit
audit coverage, follow the [evidence recipe](VERIFICATION.md#check-the-evidence-for-one-result).

Data is written to `isabelle-kg/bacon/graph.json` and is not committed.
The `bacon` directory name is retained for tool compatibility; there is
only one graph family here. Graph output includes local source locations.
Rebuild after changing theory sources; stale graphs are not current evidence.

`DEPENDS_ON` edges concern exported proof dependencies. They do not establish
that a formal statement exactly matches its published source.

## Explore the graph in a browser

After the export above exists, generate the local viewer:

```sh
python3 tools/isabelle_kg/build_viewer.py
```

Open `isabelle-kg/bacon/viewer.html` in a browser (double-click it, or use
`open isabelle-kg/bacon/viewer.html` on macOS). Click a session to see its
direct imports and importing sessions; **All sessions** returns to the
overview. The detail lists show the number of theory-import links between
each pair of sessions. No web server, internet access, JavaScript package
installation, AI service, or API account is needed. The generator uses
Python 3.9+ and its standard library; `viewer.html` beside the script is
its bundled template, not the generated viewer.

The header distinguishes two scales. **Mathematical graph** counts the
retained theory and session nodes, their nonexternal declared entities, and
all exported edge records whose endpoints are retained (including proof
dependencies). **Session view** counts the displayed session nodes and
aggregated direct-import connections. Both exclude audit/catalog theories
and their entities; the large underlying totals are not the number of marks
drawn on screen.

The default view is mathematical code only: theories with `Audit` or
`Catalog` in their qualified names, and theories under `core_audit/`, are
excluded before aggregating imports. Empty audit sessions disappear too.
Mathematical regression theories remain. Edges touching an excluded theory
are omitted, not contracted into inferred dependencies. Thus a path through
an audit is not displayed as a direct mathematical import. Applications
and external Isabelle theories are excluded. This is a session-level
projection of `IMPORTS`, not a rendering of the millions of individual
proof-dependency edges. Use `query_graph.py` for theorem-level exploration.

The viewer does **not** run Isabelle or refresh the export. It can be
generated without starting another build, but it describes only the saved
snapshot; after theory changes, rebuild the export serially before treating
the view as current evidence. Qualified theory names determine ownership,
not an export's importing-session field. The source export's SHA-256 is
included in the viewer. Identical input bytes and generator/template files
produce identical HTML; timestamps and machine-specific source paths are
not embedded. Generated graph/viewer files stay in the ignored
`isabelle-kg/` directory.

Existing output is protected. To regenerate it explicitly, or choose paths:

```sh
python3 tools/isabelle_kg/build_viewer.py --force
python3 tools/isabelle_kg/build_viewer.py --graph path/to/graph.json --output path/to/viewer.html
python3 -m unittest discover -s tools/tests -p 'test_graph_viewer.py'
```

The viewer tests also run in the default check's Python test discovery.
Running just these tests does not build or export Isabelle sessions.
