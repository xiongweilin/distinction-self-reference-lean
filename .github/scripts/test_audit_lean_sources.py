"""Adversarial lexical tests for the single retained source-audit scanner."""
from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

PATH = Path(__file__).with_name("audit_lean_sources.py")
SPEC = importlib.util.spec_from_file_location("audit_lean_sources", PATH)
assert SPEC is not None and SPEC.loader is not None
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


class AuditScannerTests(unittest.TestCase):
    def test_ignores_nested_comments_and_escaped_strings(self):
        lean = (
            "/- hidden sorry /- hidden axiom -/ hidden constant -/\n"
            "-- admit is ordinary prose\n"
            'def sentence := "a quote: \\"axiom\\" and sorry"\n'
            "theorem actual : True := by trivial\n"
        )
        cleaned = audit.strip_comments_and_strings(lean)
        self.assertEqual(cleaned.count("\n"), lean.count("\n"))
        self.assertIsNone(audit.BANNED_WORDS.search(cleaned))

    def test_detects_code_not_only_comment_or_string(self):
        for fragment in (
            "theorem bad : True := by sorry\n",
            "axiom fabricated : False\n",
            "constant unproved : Nat\n",
            "theorem bad : True := by admit\n",
        ):
            with self.subTest(fragment=fragment):
                self.assertIsNotNone(audit.BANNED_WORDS.search(
                    audit.strip_comments_and_strings(fragment)
                ))

    def test_rejects_unclosed_lexical_regions(self):
        for fragment in ('/- unterminated', 'def x := "unterminated'):
            with self.subTest(fragment=fragment):
                with self.assertRaises(ValueError):
                    audit.strip_comments_and_strings(fragment)


if __name__ == "__main__":
    unittest.main()
