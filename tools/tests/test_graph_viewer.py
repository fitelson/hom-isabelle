"""Standard-library tests for the offline session graph viewer; no Isabelle."""
import contextlib
import copy
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "isabelle_kg/build_viewer.py"
SPEC = importlib.util.spec_from_file_location("graph_viewer", SCRIPT)
viewer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(viewer)


def theory(name, path=None, external=False):
    return {"id": "theory:" + name, "name": name, "kind": "theory",
            "session": "Wrong_Importing_Session", "external": external,
            "file": path or "/checkout/theories/base/" + name.split(".")[-1] + ".thy"}


def edge(a, b, kind="IMPORTS"):
    return {"source": "theory:" + a, "target": "theory:" + b, "kind": kind}


def fixture():
    return {"schema": "isabelle-kg-v1", "sessions": ["Bacon_B", "Bacon_A", "Bacon_Core_Audit"],
            "nodes": [theory("Bacon_A.Math"), theory("Bacon_B.More"),
                      theory("Bacon_B.Regression"), theory("Bacon_B.Example_Audit"),
                      theory("Bacon_Core_Audit.Helper", "/checkout/theories/core_audit/Helper.thy"),
                      theory("HOL.Main", external=True)],
            "edges": [edge("Bacon_B.More", "Bacon_A.Math"),
                      edge("Bacon_B.Regression", "Bacon_A.Math"),
                      edge("Bacon_B.Example_Audit", "Bacon_A.Math"),
                      edge("Bacon_Core_Audit.Helper", "Bacon_B.More"),
                      edge("Bacon_B.More", "Bacon_A.Math", "DEPENDS_ON"),
                      edge("Bacon_A.Math", "HOL.Main")]}


class GraphViewerTests(unittest.TestCase):
    def test_audit_filter_ownership_and_import_counts(self):
        result = viewer.project_graph(fixture())
        self.assertEqual(result["names"], ["Bacon_A", "Bacon_B"])
        self.assertEqual(result["counts"], [1, 2])
        self.assertEqual(result["edges"], [[1, 0, 2]])
        self.assertEqual(result["excluded_audit_theories"], 2)

    def test_no_contraction_through_audits(self):
        graph = fixture()
        graph["edges"] = [edge("Bacon_B.More", "Bacon_B.Example_Audit"),
                          edge("Bacon_B.Example_Audit", "Bacon_A.Math")]
        self.assertEqual(viewer.project_graph(graph)["edges"], [])

    def test_statistics_exclude_audits_and_external_nodes(self):
        graph = fixture()
        graph["nodes"] += [
            {"id":"session:Bacon_A", "name":"Bacon_A", "kind":"session"},
            {"id":"theorem:good", "name":"good", "kind":"theorem", "theory":"Bacon_A.Math"},
            {"id":"theorem:audit", "name":"audit", "kind":"theorem", "theory":"Bacon_B.Example_Audit"},
            {"id":"theorem:external", "name":"external", "kind":"theorem", "theory":"Bacon_A.Math", "external":True},
        ]
        graph["edges"] += [
            {"source":"theory:Bacon_A.Math", "target":"theorem:good", "kind":"DECLARES"},
            {"source":"theorem:audit", "target":"theorem:good", "kind":"DEPENDS_ON"},
            {"source":"theorem:good", "target":"theorem:external", "kind":"DEPENDS_ON"},
        ]
        result = viewer.project_graph(graph)
        self.assertEqual(result["mathematical_nodes"], 5)
        self.assertEqual(result["mathematical_connections"], 4)
        self.assertEqual(len(result["edges"]), 1)

    def test_duplicate_imports_not_counted_twice(self):
        graph = fixture()
        graph["edges"].append(copy.deepcopy(graph["edges"][0]))
        self.assertEqual(viewer.project_graph(graph)["edges"], [[1, 0, 2]])

    def test_applications_excluded(self):
        graph = fixture()
        graph["nodes"].append(theory("Bacon_B.Private", "/checkout/Applications/private/theories/P.thy"))
        self.assertEqual(viewer.project_graph(graph)["theories"], 3)

    def test_catalog_and_windows_paths(self):
        self.assertTrue(viewer.is_audit(theory("Bacon_A.Catalog")))
        self.assertTrue(viewer.is_audit(theory("Bacon_A.Helper", r"C:\repo\theories\core_audit\Helper.thy")))
        self.assertFalse(viewer.is_audit(theory("Bacon_A.Model_Regression")))

    def test_projection_is_order_independent(self):
        graph = fixture()
        other = copy.deepcopy(graph)
        for key in ("nodes", "edges", "sessions"):
            other[key].reverse()
        self.assertEqual(viewer.project_graph(graph), viewer.project_graph(other))

    def test_invalid_exports(self):
        graph = fixture()
        graph["schema"] = "unknown"
        with self.assertRaises(ValueError): viewer.project_graph(graph)
        graph = fixture()
        graph["nodes"].append(graph["nodes"][0])
        with self.assertRaises(ValueError): viewer.project_graph(graph)
        graph = fixture()
        graph["nodes"][0]["name"] = "Unknown.Math"
        with self.assertRaises(ValueError): viewer.project_graph(graph)

    def test_empty_filtered_export(self):
        graph = {"schema":"isabelle-kg-v1", "sessions":[], "nodes":[], "edges":[]}
        with self.assertRaises(ValueError): viewer.project_graph(graph)

    def test_safe_embedded_json(self):
        graph = fixture()
        bad = "Bacon_A</script><script>alert(1)</script>"
        graph["sessions"].append(bad)
        graph["nodes"].append(theory(bad + ".Math"))
        result = viewer.render_viewer(graph, "abc", "<script>__ISABELLE_GRAPH_DATA__</script>")
        self.assertNotIn("<script>alert", result)
        payload = result[len("<script>"):-len("</script>")]
        self.assertIn(bad, json.loads(payload)["names"])

    def test_template_and_determinism(self):
        template = viewer.TEMPLATE.read_text()
        a = viewer.render_viewer(fixture(), "a" * 64, template)
        self.assertEqual(a, viewer.render_viewer(fixture(), "a" * 64, template))
        self.assertNotIn(viewer.PLACEHOLDER, a)
        self.assertNotIn("window.openai", a)
        self.assertNotIn("fetch(", a)
        self.assertNotIn("https://", a)
        with self.assertRaises(ValueError): viewer.render_viewer(fixture(), "abc", "no placeholder")

    def test_cli_overwrite_and_input_protection(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "graph.json"
            output = Path(directory) / "viewer.html"
            source.write_text(json.dumps(fixture()))
            original = source.read_bytes()
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(viewer.main(["--graph", str(source)]), 0)
                first = output.read_bytes()
                self.assertEqual(viewer.main(["--graph", str(source)]), 1)
                self.assertEqual(viewer.main(["--graph", str(source), "--force"]), 0)
                self.assertEqual(first, output.read_bytes())
                self.assertEqual(viewer.main(["--graph", str(source), "--output", str(source), "--force"]), 1)
                link = Path(directory) / "link.html"
                link.symlink_to(output)
                self.assertEqual(viewer.main(["--graph", str(source), "--output", str(link), "--force"]), 1)
            self.assertEqual(source.read_bytes(), original)

    def test_missing_input(self):
        with tempfile.TemporaryDirectory() as directory:
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(viewer.main(["--graph", str(Path(directory) / "missing.json")]), 1)


if __name__ == "__main__":
    unittest.main()
