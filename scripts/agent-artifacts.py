#!/usr/bin/env python3
"""Before a shard's out/ directory is uploaded as an artifact: redact secrets, and refuse the upload if one would remain.

    python3 scripts/agent-artifacts.py out [--report out/secretscan-report.txt]

Anything the agent wrote or read can end up in a log or a trace, and artifacts are readable by anyone who can read the
repository's runs. This runs warden's secret scanner (the code behind `python3 -m warden secretscan --redact`) over every file
of the directory:

* logs, traces, the ledger rows and every other file: each finding is replaced in place by [REDACTED:<kind>], the file is
  scanned again, and a finding that is still there fails the run. A .json or .jsonl file must still parse afterwards.
* bank.jsonl is data that will become pull requests, so it is not rewritten: a record with a finding is moved, redacted, to
  quarantine/bank.rejected.jsonl and is not banked; the other records stay.

Exit status: 0 clean (or fully redacted), 1 something would remain or a rewritten file no longer parses, 2 bad input. The report
names file, line and kind of every finding, never the value.
"""
from __future__ import annotations

import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from warden import secretscan  # noqa: E402

MAX_BYTES = secretscan.MAX_FILE_BYTES
RECORD_FILE = "bank.jsonl"


def walk(directory: str):
    for base, dirs, files in os.walk(directory):
        dirs.sort()
        for name in sorted(files):
            path = os.path.join(base, name)
            if os.path.isfile(path) and not os.path.islink(path):
                yield path


def parses(path: str, text: str) -> bool:
    if path.endswith(".json"):
        try:
            json.loads(text)
        except ValueError:
            return False
    elif path.endswith(".jsonl"):
        for line in text.splitlines():
            if line.strip():
                try:
                    json.loads(line)
                except ValueError:
                    return False
    return True


def process(directory: str):
    """Returns (report lines, failed). Rewrites files in place."""
    report = []
    failed = False
    quarantine_lines = []
    for path in walk(directory):
        rel = os.path.relpath(path, directory)
        if os.path.getsize(path) > MAX_BYTES:
            report.append("%s: too large to scan (over %d bytes)" % (rel, MAX_BYTES))
            failed = True
            continue
        with open(path, "rb") as fh:
            text = fh.read().decode("utf-8", errors="replace")
        finds = secretscan.scan(text, rel)
        if not finds:
            continue
        for f in finds:
            report.append("%s:%d: %s" % (rel, f.line, f.kind))
        if rel == RECORD_FILE:
            keep = []
            for line in text.splitlines():
                if line.strip() and secretscan.scan(line, rel):
                    quarantine_lines.append(secretscan.redact(line))
                elif line.strip():
                    keep.append(line)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("".join(l + "\n" for l in keep))
            continue
        redacted = secretscan.redact(text)
        if secretscan.scan(redacted, rel):
            report.append("%s: a secret remains after redaction" % rel)
            failed = True
            continue
        if not parses(path, redacted):
            report.append("%s: no longer parses after redaction" % rel)
            failed = True
            continue
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(redacted)
    if quarantine_lines:
        qdir = os.path.join(directory, "quarantine")
        os.makedirs(qdir, exist_ok=True)
        with open(os.path.join(qdir, "bank.rejected.jsonl"), "a", encoding="utf-8") as fh:
            fh.write("".join(l + "\n" for l in quarantine_lines))
        report.append("%d bank record(s) moved to quarantine/bank.rejected.jsonl" % len(quarantine_lines))
    return report, failed


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("directory")
    ap.add_argument("--report")
    ns = ap.parse_args(argv)
    if not os.path.isdir(ns.directory):
        print("agent-artifacts: %s is not a directory" % ns.directory, file=sys.stderr)
        return 2
    report, failed = process(ns.directory)
    # the second pass is the check that matters: whatever the first one did, nothing may be left
    left = []
    for path in walk(ns.directory):
        if os.path.getsize(path) <= MAX_BYTES:
            with open(path, "rb") as fh:
                left += ["%s:%d: %s" % (os.path.relpath(path, ns.directory), f.line, f.kind) for f in secretscan.scan(fh.read().decode("utf-8", errors="replace"), path)]
    if left:
        failed = True
        report += ["STILL PRESENT: " + l for l in left]
    text = "\n".join(report) + ("\n" if report else "")
    if ns.report:
        with open(ns.report, "w", encoding="utf-8") as fh:
            fh.write(text)
    sys.stdout.write(text)
    print("agent-artifacts: %s" % ("a secret would remain: the artifact must not be uploaded" if failed else "clean (%d finding(s) redacted)" % len([r for r in report if ":" in r and "moved" not in r])))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
