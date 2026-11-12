"""A job that checks out a LIST of scripts/bump files checks out everything those files import from scripts/bump.

2026-11-12: bundle_layers.py began to import grind_sets.py (which imports adapters.py), the attest job of bump-library.yml lists the files it needs one by one and
did not list them, and every run with `parts` died in `Pack` with `ModuleNotFoundError: No module named 'grind_sets'` after the whole bump had succeeded.
"""

from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BUMP = ROOT / "scripts" / "bump"
WORKFLOWS = ROOT / ".github" / "workflows"
LISTED = re.compile(r'sparse-checkout set --no-cone((?:\s+"/scripts/bump/[A-Za-z0-9_]+\.py")+)')
IMPORT = re.compile(r"^(?:import|from)\s+([A-Za-z_][A-Za-z0-9_]*)\b", re.M)


def local_imports(name: str) -> set[str]:
    src = (BUMP / f"{name}.py").read_text(encoding="utf-8")
    return {m for m in IMPORT.findall(src) if (BUMP / f"{m}.py").exists()}


def closure(names: set[str]) -> set[str]:
    seen, stack = set(), list(names)
    while stack:
        n = stack.pop()
        if n not in seen:
            seen.add(n)
            stack.extend(local_imports(n))
    return seen


class ListedScriptsCarryTheirImports(unittest.TestCase):
    def test_every_explicit_list_is_closed_under_imports(self):
        problems, checked = [], 0
        for wf in sorted(WORKFLOWS.glob("*.yml")):
            for m in LISTED.finditer(wf.read_text(encoding="utf-8")):
                listed = set(re.findall(r'/scripts/bump/([A-Za-z0-9_]+)\.py', m.group(1)))
                checked += 1
                missing = sorted(closure(listed) - listed)
                if missing:
                    problems.append(f"{wf.name}: lists {sorted(listed)} but they import {missing}")
        self.assertGreater(checked, 0, "no explicit list found: the pattern no longer matches the workflow")
        self.assertEqual(problems, [])


if __name__ == "__main__":
    unittest.main()
