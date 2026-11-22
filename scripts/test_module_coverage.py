"""Adversarial tests for the repository-wide Lean import/axiom coverage scan."""
from pathlib import Path
import tempfile
import unittest

from scripts.audit_module_coverage import analyze, masked_code


class LeanModuleCoverageTests(unittest.TestCase):
    def test_nested_comments_and_escaped_strings_are_not_code(self):
        code = (
            'import Kk.Real\n'
            '/- nested /- import Kk.Fake -/ sorry -/\n'
            '-- axiom line ignored\n'
            'def x := "sorry \\\" import Kk.Hidden"\n'
            'theorem safe : True := by trivial\n'
        )
        out = masked_code(code)
        self.assertIn("import Kk.Real", out)
        for word in ("Kk.Fake", "Kk.Hidden", "sorry", "axiom"):
            self.assertNotIn(word, out)
        self.assertEqual(code.count("\n"), out.count("\n"))

    def test_reachable_and_standalone_modules_are_distinguished(self):
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp)
            (repo / "Kk").mkdir()
            (repo / "scripts").mkdir()
            (repo / "Kk.lean").write_text("import Kk.A\n", encoding="utf-8")
            (repo / "Kk" / "A.lean").write_text(
                "import Kk.B\n/- axiom falseA : False -/\n", encoding="utf-8")
            (repo / "Kk" / "B.lean").write_text(
                "theorem ok : True := by trivial\n", encoding="utf-8")
            (repo / "Kk" / "Standalone.lean").write_text(
                "axiom bad : False\n", encoding="utf-8")
            (repo / "scripts" / "check_axioms.lean").write_text(
                "#check @Kk.ok\n#print axioms Kk.ok\n", encoding="utf-8")
            report = analyze(repo)
            self.assertEqual(report["total_kK_modules"], 3)
            self.assertEqual(report["root_direct_local_imports"], 1)
            self.assertEqual(report["root_reachable_modules_including_root"], 3)
            self.assertEqual(report["unreachable_local_modules"], ["Kk.Standalone"])
            self.assertEqual(report["missing_local_imports"], [])
            self.assertEqual(report["suspicious_token_counts"], {"axiom": 1})
            self.assertEqual(report["central_check_without_print"], [])

    def test_missing_internal_import_is_detected(self):
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp)
            (repo / "Kk").mkdir()
            (repo / "scripts").mkdir()
            (repo / "Kk.lean").write_text("import Kk.Absent\n", encoding="utf-8")
            (repo / "scripts" / "check_axioms.lean").write_text(
                "#check @Kk.ok\n", encoding="utf-8")
            report = analyze(repo)
            self.assertEqual(report["missing_local_imports"], ["Kk.Absent"])
            self.assertEqual(report["central_check_without_print"], ["Kk.ok"])


if __name__ == "__main__":
    unittest.main()
