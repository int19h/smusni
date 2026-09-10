"""Positive and negative tests for the tracked documentation gate."""

import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CHECKER = Path(__file__).with_name("check-docs.py")
SPEC = importlib.util.spec_from_file_location("check_docs", CHECKER)
checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checker)


class DocumentationChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in checker.CORPUS:
            (self.root / name).write_text(f"# {name}\n")
        (self.root / "AGENTS.md").write_text("Standalone charter\n")
        (self.root / "spec.md").write_text(" ".join(f"P{i}" for i in range(1, 38)))

    def specimen(self, text):
        (self.root / "samples.md").write_text(text)

    def run_checker(self):
        return subprocess.run([sys.executable, str(CHECKER), str(self.root)],
                              capture_output=True, text=True)

    def test_valid_comments_strings_and_indentation(self):
        self.specimen('  ```lisp\n(foo "a; ) \\" b" [x {y}]) ; (\n  ```\n')
        self.assertEqual(checker.lisp_balance(self.root), [])
        self.assertEqual(self.run_checker().returncode, 0)

    def test_balanced_counts_wrong_nesting(self):
        self.specimen("```lisp\n([)]\n```\n")
        self.assertTrue(checker.lisp_balance(self.root))
        self.assertEqual(self.run_checker().returncode, 1)

    def test_unclosed_opening_has_source_line(self):
        self.specimen("Heading\n```lisp\n(foo\n```\n")
        self.assertIn((self.root / "samples.md", 3, "unclosed ("),
                      checker.lisp_balance(self.root))

    def test_unclosed_fence_and_string(self):
        for text, problem in [('```lisp\n(foo)', "unclosed Lisp fence"),
                              ('```lisp\n"foo\n```', "unclosed string")]:
            with self.subTest(problem=problem):
                self.specimen(text)
                self.assertTrue(any(p == problem for _, _, p in
                                    checker.lisp_balance(self.root)))

    def test_missing_file_link_and_pin_fail(self):
        (self.root / "spec.md").write_text("P1 [missing](absent.md)")
        self.assertEqual(self.run_checker().returncode, 1)
        (self.root / "spec.md").unlink()
        self.assertEqual(self.run_checker().returncode, 1)

    def test_embedded_corpus_fails_standalone(self):
        (self.root / "AGENTS.md").write_text(
            "Charter\n" + (self.root / "primer.md").read_text())
        self.assertFalse(checker.agents_is_standalone(self.root))
        self.assertEqual(self.run_checker().returncode, 1)


if __name__ == "__main__":
    unittest.main()
