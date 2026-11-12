"""A job that checks out a LIST of scripts/bump files checks out everything those files import from scripts/bump.

2026-11-12: bundle_layers.py began to import grind_sets.py (which imports adapters.py), the attest job of bump-library.yml lists the files it needs one by one and
did not list them, and every run with `parts` died in `Pack` with `ModuleNotFoundError: No module named 'grind_sets'` after the whole bump had succeeded.
"""

from __future__ import annotations

import ast
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BUMP = ROOT / "scripts" / "bump"
WORKFLOWS = ROOT / ".github" / "workflows"
LISTED = re.compile(r'sparse-checkout set --no-cone((?:\s+"/scripts/bump/[A-Za-z0-9_]+\.py")+)')


def imported_modules(src: str) -> set[str]:
    """the top-level names a source imports ANYWHERE (a function-level `import x` runs at call time and fails the same way), by the syntax tree"""
    tree = ast.parse(src)
    mods: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            mods.update(a.name.split(".")[0] for a in node.names)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            mods.add(node.module.split(".")[0])
    return mods


def local_imports(name: str) -> set[str]:
    return {m for m in imported_modules((BUMP / f"{name}.py").read_text(encoding="utf-8")) if (BUMP / f"{m}.py").exists()}


def closure(names: set[str]) -> set[str]:
    seen, stack = set(), list(names)
    while stack:
        n = stack.pop()
        if n not in seen:
            seen.add(n)
            stack.extend(local_imports(n))
    return seen


class ImportScan(unittest.TestCase):
    def test_indented_and_nested_imports_are_found(self):
        src = "import os\n\ndef f():\n    import grind_sets\n    from adapters import code_mask\n\nclass C:\n    def g(self):\n        import tolerant_build as tb\n"
        self.assertEqual(imported_modules(src), {"os", "grind_sets", "adapters", "tolerant_build"})

    def test_relative_and_dotted_forms(self):
        self.assertEqual(imported_modules("import a.b\nfrom c.d import e\nfrom . import f\n"), {"a", "c"})


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
