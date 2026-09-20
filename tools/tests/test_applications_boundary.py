"""Applications are ordinary folders outside the core session graph."""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]


class ApplicationsBoundaryTests(unittest.TestCase):
    def test_core_root_does_not_select_applications(self):
        self.assertNotIn('Applications/', (ROOT / 'ROOT').read_text())
        self.assertNotIn('Goodman_', (ROOT / 'ROOT').read_text())
        if (ROOT / 'ROOTS').exists():
            self.assertNotIn('Applications', (ROOT / 'ROOTS').read_text())

    def test_goodman_is_an_ordinary_separately_checked_folder(self):
        app = ROOT / 'Applications/goodman-isabelle'
        self.assertTrue((app / 'ROOT').is_file())
        self.assertTrue((app / 'check_isabelle.sh').is_file())
        self.assertFalse((app / '.git').exists())
        if (ROOT / '.gitmodules').exists():
            self.assertNotIn('Applications/goodman-isabelle', (ROOT / '.gitmodules').read_text())


if __name__ == '__main__':
    unittest.main()
