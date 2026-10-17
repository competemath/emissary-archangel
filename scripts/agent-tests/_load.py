"""Shared by the tests of the agent jail: put scripts/ on the path and load the hyphen-named scripts as modules."""
from __future__ import annotations

import importlib.util
import os
import sys

TESTS = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = os.path.dirname(TESTS)
ROOT = os.path.dirname(SCRIPTS)
BRIDGE = os.environ.get("BRIDGE_PATH") or os.path.join(ROOT, "public", "local-claude-bridge.mjs")

sys.dont_write_bytecode = True
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)

_cache = {}


def load_script(name: str):
    """Import scripts/<name>.py (hyphens allowed in the file name) as a module, once."""
    if name not in _cache:
        spec = importlib.util.spec_from_file_location(name.replace("-", "_"), os.path.join(SCRIPTS, name + ".py"))
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        _cache[name] = module
    return _cache[name]
