"""Read-only checks of packaging and proof boundary metadata."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("checker", ROOT / "tools/check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class RepositoryTests(unittest.TestCase):
    def test_embedded_core_location(self):
        if ROOT.parent.name == "Applications":
            self.assertEqual(checker.default_core(), ROOT.parent.parent)
            self.assertTrue(checker.embedded_core(ROOT, ROOT.parent.parent))
        self.assertFalse(checker.embedded_core(Path('/tmp/goodman-isabelle'), Path('/tmp/bacon-dorr-isabelle')))

    def test_core_pin_includes_ml(self):
        pin = json.loads((ROOT / "dependencies/bacon-dorr.json").read_text())
        self.assertIn('theories/core_audit/Bacon_Core_Audit_Check.ML', pin['sha256'])

    def test_process_guard_does_not_match_checker_or_itself(self):
        text = "123 python /tmp/goodman-isabelle/tools/check.py --export\n124 bash /Applications/Isabelle/bin/isabelle build -j 1\n125 java isabelle.Isabelle_Tool export X\n"
        self.assertEqual(len(checker.active_isabelle_processes(text, 999)), 2)
        self.assertEqual(len(checker.active_isabelle_processes(text, 124)), 1)

    def test_incomplete_audit_export_fails(self):
        expected = {"X/audit.txt": ["lemma_a", "lemma_b"]}
        for actual in ({}, {"X/audit.txt": ["lemma_a"]}, {"Y/audit.txt": ["lemma_a", "lemma_b"]}):
            with self.assertRaises(ValueError):
                checker.validate_catalogs(actual, expected)
        checker.validate_catalogs(expected, expected)

    def test_committed_audits_match_manifest(self):
        expected = json.loads((ROOT / "verification/catalogs.json").read_text())
        checker.validate_catalogs(checker.audit_catalogs(ROOT / "verification/audits"), expected)

    def test_manifest_paths_stay_inside_repository(self):
        with self.assertRaises(ValueError):
            checker.safe_path(ROOT, "../escape")
        self.assertEqual(checker.safe_path(ROOT, "ROOT"), ROOT / "ROOT")

    def test_session_directories_exist(self):
        for root in [ROOT / "ROOT", *sorted((ROOT / "theories").rglob("ROOT"))]:
            for relative in re.findall(r'\bin "([^"]+)"', root.read_text()):
                self.assertTrue((root.parent / relative).is_dir(), (root, relative))
        for relative in (ROOT / "ROOTS").read_text().splitlines():
            self.assertTrue((ROOT / relative / "ROOT").is_file(), relative)

    def test_unselected_files_are_explicit(self):
        data = json.loads((ROOT / "verification/provenance/extraction.json").read_text())
        declared = "\n".join(p.read_text() for p in [ROOT / "ROOT", *(ROOT / "theories").rglob("ROOT")])
        for relative in data["unselected_theories"]:
            p = ROOT / relative
            self.assertTrue(p.is_file())
            self.assertNotRegex(declared, r"(?m)^\s+" + re.escape(p.stem) + r"\s*$")

    def test_no_absolute_machine_paths_in_proof_inputs(self):
        for path in [ROOT / "ROOT", ROOT / "ROOTS", *(ROOT / "theories").rglob("*.thy")]:
            self.assertNotIn("/Users/", path.read_text(), str(path))

    def test_all_preserved_files_have_provenance(self):
        frozen = json.loads((ROOT / "verification/provenance/frozen.json").read_text())["theories"]
        expected = {row["frozen"] for row in frozen}
        actual = {p.relative_to(ROOT).as_posix() for d in ("preserved", "preserved-additions")
                  for p in (ROOT / "theories" / d).rglob("*.thy")}
        self.assertEqual(actual, expected)


if __name__ == "__main__":
    unittest.main()
