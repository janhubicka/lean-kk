"""Tests for the standalone exact-axiom audit runner."""
import tempfile
from pathlib import Path
import unittest

from scripts.check_scoped_axiom_gates import discover, check_one


class ScopedAuditTests(unittest.TestCase):
    def test_discovery_excludes_production_modules(self):
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp)
            (repo / "Kk").mkdir()
            for name in ("AlphaAxiomAudit.lean", "BetaAxiomAudit.lean",
                         "NormalProof.lean"):
                (repo / "Kk" / name).write_text("import Kk.NormalProof\n",
                                              encoding="utf-8")
            self.assertEqual([path.name for path in discover(repo)],
                             ["AlphaAxiomAudit.lean", "BetaAxiomAudit.lean"])

    def test_only_standard_axioms_are_accepted(self):
        source = ("import Kk.Test\n"
                  "#check @Kk.foo\n"
                  "#print axioms Kk.foo\n")
        good = "'Kk.foo' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(check_one(source, good), [])
        self.assertTrue(check_one(source, good.replace("propext", "My.Oracle")))
        self.assertTrue(check_one(source, good + "\nsorryAx"))
        self.assertTrue(check_one(source, ""))

    def test_no_vacuous_or_comment_only_report(self):
        self.assertTrue(check_one("import Kk.Foo\n", ""))
        self.assertTrue(check_one("/- #print axioms Kk.missing -/\n", ""))
        self.assertTrue(check_one(
            '#print axioms Kk.real\n',
            "'Kk.other' depends on axioms: [propext]"))
        self.assertEqual(check_one(
            '#print axioms Kk.axiomfree\n',
            "'Kk.axiomfree' does not depend on any axioms"), [])


if __name__ == "__main__":
    unittest.main()
