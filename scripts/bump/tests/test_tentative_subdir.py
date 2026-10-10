"""The statement records of a library whose Lake project is a subdirectory of its repository (openai-math `lean`, fagin and immerman-vardi `proofs`) link repository-relative files
(`…/blob/<sha>/lean/OAI/X.lean`); the library's modules are relative to the project (`OAI.X`). Not stripped, the plan of openai-math found no module with an entry and planned no shard (2026-10-09)."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import gate2_batch as g  # noqa: E402


def records(lib: str, *paths: str) -> list[str]:
    d = Path(tempfile.mkdtemp())
    f = d / "r.jsonl"
    f.write_text("".join(json.dumps({"name": f"{lib}.t{i}", "library": lib, "source_url": f"https://github.com/o/r/blob/{'a' * 40}/{p}#L1"}) + "\n" for i, p in enumerate(paths)), encoding="utf-8")
    return [str(f)]


class TentativeSubdir(unittest.TestCase):
    def test_the_subdir_prefix_is_stripped_for_a_library_that_has_one(self):
        with mock.patch.object(g, "subdirs_of_libraries", return_value={"openai-math": "lean"}):
            ents = g.tentative_entries(records("openai-math", "lean/OAI/Complex/Bezout.lean", "lean/ComparatorChallenges/C1.lean"))
        self.assertEqual({e["sourcePath"] for e in ents.values()}, {"OAI/Complex/Bezout.lean", "ComparatorChallenges/C1.lean"})
        self.assertEqual({g.module_of(e["sourcePath"]) for e in ents.values()}, {"OAI.Complex.Bezout", "ComparatorChallenges.C1"})

    def test_other_libraries_and_paths_without_the_prefix_are_untouched(self):
        with mock.patch.object(g, "subdirs_of_libraries", return_value={"openai-math": "lean"}):
            self.assertEqual({e["sourcePath"] for e in g.tentative_entries(records("carleson", "lean/Carleson/X.lean")).values()}, {"lean/Carleson/X.lean"})
            self.assertEqual({e["sourcePath"] for e in g.tentative_entries(records("openai-math", "OAI/Y.lean")).values()}, {"OAI/Y.lean"})
            self.assertEqual({e["sourcePath"] for e in g.tentative_entries(records("openai-math", "leanish/Z.lean")).values()}, {"leanish/Z.lean"})  # a directory that merely starts with the same letters

    def test_the_real_registry_knows_the_subdir_libraries(self):
        subs = g.subdirs_of_libraries()
        if subs:  # skipped where sources.json is not checked out
            self.assertEqual(subs.get("openai-math"), "lean")
            self.assertIn("fagin", subs)


if __name__ == "__main__":
    unittest.main()
