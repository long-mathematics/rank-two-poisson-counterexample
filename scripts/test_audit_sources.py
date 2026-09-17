"""Regression tests for the source/build/ledger guard's failure paths."""
from pathlib import Path
import tempfile
import unittest

import audit_sources as audit


class AuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "RankTwoPoisson").mkdir()
        (self.root / "RankTwoPoisson.lean").write_text("import RankTwoPoisson.Proof\n")
        (self.root / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\n@[default_target]\nlean_lib RankTwoPoisson where\n")
        self.proof = self.root / "RankTwoPoisson/Proof.lean"
        self.proof.write_text("theorem good : True := by trivial\n")
        (self.root / "rank_two_poisson_counterexample.tex").write_text(
            r"\begin{theorem}\label{thm:main}Statement.\end{theorem}")
        (self.root / "FORMALIZATION_STATUS.md").write_text("| `thm:main` | PARTIAL | description |\n")

    def test_clean_fixture(self):
        self.assertEqual(audit.check_sources(self.root), (3, 2))
        self.assertEqual(audit.check_ledger(self.root), 1)

    def test_nested_comments_and_strings(self):
        self.proof.write_text('/- sorry /- admit -/ axiom -/\n-- unsafe\ndef s := "sorry"\n')
        audit.check_sources(self.root)

    def test_reject_escapes(self):
        for escape in ("sorry", "admit", "sorryAx", "axiom", "unsafe", "native_decide",
                       "implemented_by", "extern", "Lean.ofReduceBool", "debug.skipKernelTC", "by?"):
            with self.subTest(escape=escape):
                self.proof.write_text(f"theorem bad : True := by {escape}\n")
                with self.assertRaisesRegex(ValueError, "forbidden proof escape"):
                    audit.check_sources(self.root)

    def test_interpolated_expression(self):
        self.proof.write_text('def s := s!"{sorry}"\n')
        with self.assertRaisesRegex(ValueError, "forbidden"):
            audit.check_sources(self.root)

    def test_missing_module(self):
        self.proof.write_text("import RankTwoPoisson.Missing\n")
        with self.assertRaisesRegex(ValueError, "Missing project module"):
            audit.check_sources(self.root)

    def test_omitted_module(self):
        (self.root / "RankTwoPoisson/Orphan.lean").write_text("theorem hidden : True := by trivial")
        with self.assertRaisesRegex(ValueError, "absent from build umbrella"):
            audit.check_sources(self.root)

    def test_multiple_imports_and_nested_modules(self):
        (self.root / "RankTwoPoisson/Sub").mkdir()
        (self.root / "RankTwoPoisson/Sub/Extra.lean").write_text("")
        (self.root / "RankTwoPoisson.lean").write_text(
            "import RankTwoPoisson.Proof RankTwoPoisson.Sub.Extra\n")
        self.assertEqual(audit.check_sources(self.root), (4, 3))

    def test_wrong_default_target(self):
        (self.root / "lakefile.lean").write_text("lean_lib RankTwoPoisson where\n")
        with self.assertRaisesRegex(ValueError, "default Lake target"):
            audit.check_sources(self.root)

    def test_mathematics_outside_library(self):
        (self.root / "Forgotten.lean").write_text("")
        with self.assertRaisesRegex(ValueError, "mathematical sources"):
            audit.check_sources(self.root)

    def test_ledger_missing_or_duplicate_entry(self):
        for text in ("", "| `thm:main` | PROVED | x |\n" * 2):
            (self.root / "FORMALIZATION_STATUS.md").write_text(text)
            with self.assertRaisesRegex(ValueError, "ledger differ"):
                audit.check_ledger(self.root)

    def test_unterminated_comment(self):
        with self.assertRaisesRegex(ValueError, "Unterminated"):
            audit.code_only("/- hidden")

    def test_circular_or_unknown_dependencies(self):
        ledger = self.root / "FORMALIZATION_STATUS.md"
        for dependency in ("A01", "Z99"):
            ledger.write_text("| `thm:main` | PARTIAL | description |\n"
                              f"| A01 | MISSING | claim | {dependency} |\n")
            with self.assertRaisesRegex(ValueError, "ledger dependency"):
                audit.check_ledger(self.root)

    def test_metaprogramming_in_mathematics(self):
        self.proof.write_text("run_cmd do pure ()\n")
        with self.assertRaisesRegex(ValueError, "metaprogramming"):
            audit.check_sources(self.root)


if __name__ == "__main__":
    unittest.main()
