#!/usr/bin/env python3
"""Regression checks for active and archived manuscript correspondence.

Copyright (c) 2026 Yawara Ishida. Released under Apache-2.0; see LICENSE.
These checks exercise source integrity; they do not certify mathematical fidelity.
"""

from copy import deepcopy
import hashlib
import tomllib
import unittest

import paper_map


class SourceMapTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = tomllib.loads(paper_map.MAP.read_text())

    def setUp(self):
        self.data = deepcopy(self.original)

    def item(self, item_id):
        return next(item for item in self.data["items"] if item["id"] == item_id)

    def test_current_map(self):
        paper_map.validate(self.data)

    def test_archive_hash_is_checked(self):
        self.data["archived_sources"][0]["sha256"] = "0" * 64
        with self.assertRaisesRegex(paper_map.MapError, "Archived TeX SHA256"):
            paper_map.validate(self.data)

    def test_missing_archive_registration_is_rejected(self):
        self.data["archived_sources"] = []
        with self.assertRaisesRegex(paper_map.MapError, "missing archived source"):
            paper_map.validate(self.data)

    def test_archived_question_cannot_become_active(self):
        self.item("questions.locally_finite_varieties")["source_status"] = "active"
        with self.assertRaises(paper_map.MapError):
            paper_map.validate(self.data)

    def test_prose_locator_must_be_in_range(self):
        for start, end in [(10000, 10006), (-1, 5), ("230", "236")]:
            with self.subTest(start=start, end=end):
                item = self.item("preliminaries.exponent_three")
                item["line_start"], item["line_end"] = start, end
                with self.assertRaisesRegex(paper_map.MapError, "source locator outside manuscript"):
                    paper_map.validate(self.data)

    def test_archived_question_requires_original_locator(self):
        self.item("questions.locally_finite_varieties")["line_start"] += 1
        with self.assertRaisesRegex(paper_map.MapError, "incorrect line_start"):
            paper_map.validate(self.data)

    def test_retained_item_cannot_switch_archives(self):
        path = "archives/T3_modelcompanion_v7.tex"
        self.data["archived_sources"].append({
            "path": path, "sha256": hashlib.sha256(paper_map.repo_path(path).read_bytes()).hexdigest(),
        })
        self.item("questions.locally_finite_varieties")["source_path"] = path
        with self.assertRaisesRegex(paper_map.MapError, "must use archived v8 source"):
            paper_map.validate(self.data)

    def test_deleted_question_is_not_silently_dropped(self):
        self.data["items"].remove(self.item("questions.locally_finite_varieties"))
        with self.assertRaises(paper_map.MapError):
            paper_map.validate(self.data)

    def test_takeuchi_archived_formulation_requires_source(self):
        locator = self.item("questions.takeuchi_conjecture")["additional_source_locations"][0]
        del locator["source_path"]
        with self.assertRaisesRegex(paper_map.MapError, "inactive Burnside formulation"):
            paper_map.validate(self.data)

    def test_active_item_cannot_point_at_archive(self):
        self.item("main.bounded_witness")["source_path"] = self.data["archived_sources"][0]["path"]
        with self.assertRaisesRegex(paper_map.MapError, "incorrect source path"):
            paper_map.validate(self.data)

    def test_open_conjecture_is_not_marked_proved(self):
        self.item("questions.takeuchi_conjecture")["formalization"] = "proved"
        with self.assertRaisesRegex(paper_map.MapError, "leaves this question or conjecture open"):
            paper_map.validate(self.data)

    def test_nested_disabled_source_preserves_lines(self):
        source = "first\n\\if0\nhidden\n\\iftrue\nalso hidden\n\\fi\n\\else\nshown\n\\fi\nlast\n"
        active = paper_map.active_tex(source)
        self.assertEqual(source.count("\n"), active.count("\n"))
        self.assertNotIn("hidden", active)
        self.assertIn("shown", active)
        self.assertEqual(active.splitlines()[-1], "last")


if __name__ == "__main__":
    unittest.main()
