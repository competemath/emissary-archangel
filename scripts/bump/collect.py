#!/usr/bin/env python3
"""collect.py RUNS.txt OUTDIR — download the artifacts of finished bump-library runs and tabulate them.

RUNS.txt: one `key run_id` per line. For each finished run, `gh run download` into OUTDIR/<key>/ (skipped if already there) and
one row: modules clean/total, Gate 2 declarations checked / passed, fail reasons, definitions identical/defeq/drift,
records banked, run minutes. Prints a markdown table and writes OUTDIR/summary.json.
"""

import json
import subprocess
import sys
from pathlib import Path

REPO = "competemath/emissary-archangel"


def gh(*args: str) -> str:
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else ""


def row(key: str, run: str, out: Path) -> dict:
    info = json.loads(gh("run", "view", run, "-R", REPO, "--json", "status,conclusion,createdAt,updatedAt") or "{}")
    r = {"key": key, "run": run, "status": info.get("status"), "conclusion": info.get("conclusion")}
    if info.get("status") != "completed":
        return r
    from datetime import datetime

    t = lambda s: datetime.fromisoformat(s.replace("Z", "+00:00"))
    r["minutes"] = round((t(info["updatedAt"]) - t(info["createdAt"])).total_seconds() / 60)
    d = out / key
    if not d.exists():
        d.mkdir(parents=True)
        subprocess.run(["gh", "run", "download", run, "-R", REPO, "-D", str(d)], capture_output=True)
    def find(name: str):
        return next(iter(d.rglob(name)), None)  # the early `gate2-*` artifact and the final `bump-*` one

    art = d
    if find("tb-final.json"):
        tb = json.loads(find("tb-final.json").read_text())
        r["modules"] = tb["modules"]
        r["clean"] = tb["by_state"].get("clean", 0)
        r["errors"] = tb["by_state"].get("errors", 0)
        r["lake_would_build"] = tb["lake_would_build"]
    if find("gate2-results.json"):
        g = json.loads(find("gate2-results.json").read_text())
        r["checked"], r["passed"] = g["checked"], g["pass"]
        r["equal"], r["entails"] = g["pass_equal"], g["pass_entails"]
        r["fail_reasons"] = g["fail_reasons"]
        r["controls_wrongly_passed"] = len(g["controls"]["wrongly_passed"])
        r["definitions"] = g.get("definitions", {}).get("by_result", {})
        r["by_outcome"] = g["by_pipeline_outcome"]
    logs = sorted(d.rglob("build-s*-p*.log"))
    if logs:  # the last portfolio build: how many proofs it closed, and with what
        import re
        from collections import Counter

        r["portfolio_closed"] = dict(Counter(re.findall(r"PORTFOLIO-OK (\w+)", logs[-1].read_text(errors="replace"))))
    if find("bank.jsonl"):
        r["records"] = sum(1 for ln in find("bank.jsonl").read_text().splitlines() if ln.strip())
    if find("plan.json"):
        r["skipped"] = json.loads(find("plan.json").read_text().splitlines()[0]).get("skipped")
    if find("gate2-results.json"):
        r["def_controls"] = g.get("definition_controls")
    return r


def main() -> None:
    runs = [ln.split() for ln in Path(sys.argv[1]).read_text().splitlines() if ln.strip()]
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    rows = [row(k, i, out) for k, i in runs]
    (out / "summary.json").write_text(json.dumps(rows, indent=1))
    print("| library | run | min | modules clean/total | lake | Gate 2 checked | passed | equal/entails | fails | defs id/defeq/drift | records |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    tot = {"checked": 0, "passed": 0, "records": 0}
    for r in rows:
        d = r.get("definitions", {})
        print(
            f"| {r['key']} | {r['run']} | {r.get('minutes', '…')} | {r.get('clean', '–')}/{r.get('modules', '–')} | {r.get('lake_would_build', '–')} | {r.get('checked', '–')} | {r.get('passed', '–')} | "
            f"{r.get('equal', '–')}/{r.get('entails', '–')} | {r.get('fail_reasons', '')} | {d.get('identical', 0)}/{d.get('defeq', 0)}/{d.get('drift', 0)} | {r.get('records', '–')} |"
        )
        for k in tot:
            tot[k] += r.get(k, 0) or 0
    print(f"\nTotal: {tot['checked']} declarations checked, {tot['passed']} passed, {tot['records']} records")


if __name__ == "__main__":
    main()
