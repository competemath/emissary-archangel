#!/usr/bin/env python3
"""`warden selftest`, run as the agent user by scripts/agent-jail.py, minus the probes a uid jail cannot answer.

Installed root-owned at /opt/emissary-jail/agent-selftest-inner.py next to a copy of scripts/warden. Everything else is the
vendored battery: same probes, same exit codes, same report. The probes left out are listed in agent-jail.SKIPPED_PROBES with
their reasons, and this script prints them, so a reader of the log sees what was not run.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
for candidate in (os.environ.get("EMISSARY_JAIL_PY"), os.path.join(HERE, "py"), HERE):
    if candidate and os.path.isdir(os.path.join(candidate, "warden")):
        sys.path.insert(0, candidate)
        break

from warden import selftest  # noqa: E402

SKIPPED = {
    "userns_differs_from_host": "the agent shares the host's user namespace by design (uid isolation, no namespace jail); the "
    "nested_userns_denied probe, with user namespaces switched off, is what covers this vector",
}


def main(argv=None) -> int:
    probes = [p for p in selftest.default_probes() if p.name not in SKIPPED]
    if "--list" not in (argv if argv is not None else sys.argv[1:]):
        for name, why in sorted(SKIPPED.items()):
            print("not run: %s (%s)" % (name, why))
    return selftest.main(argv, probes=probes)


if __name__ == "__main__":
    sys.exit(main())
