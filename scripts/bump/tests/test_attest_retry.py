"""The attestation is tried three times, 5 and 15 minutes apart, in every emissary workflow that attests (bump-library, bump-sharded, memory-intake).

The real case: 2026-11-07, rekor (the public transparency log) answered HTTP 500 ("error creating tlog entry - (500) unexpected result from transparency log"): Tengoku's queue
publish of #751 failed at 13:54 and 14:28, and the sandbox campaign of emissary#154 (run 42381696374) failed in its judge. A bump whose attestation fails uploads no bundle, and the
opener refuses a bundle without one. Here each workflow's own steps (read from the file) are run through a small model of GitHub's step rules (an `if` without a status function
means success() && it; continue-on-error makes a failed step's outcome 'failure' and its conclusion 'success'), for every sequence of answers from the log. Invariants: the
attestation is tried until it succeeds, at most three times; the waits run only between failed tries; the job fails exactly when all three fail; the upload runs exactly when one
succeeded; a step that fails before the attestation still stops everything; memory-intake attests (and waits) only when it has a bundle.
"""

from __future__ import annotations

import itertools
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
WORKFLOWS = {"bump-library.yml": "attest", "bump-sharded.yml": "finish", "memory-intake.yml": "collect"}


def steps_of(wf: str) -> list[dict]:
    import yaml

    return yaml.safe_load((ROOT / ".github" / "workflows" / wf).read_text())["jobs"][WORKFLOWS[wf]]["steps"]


def is_attest(step: dict) -> bool:
    return "actions/attest-build-provenance@" in str(step.get("uses", ""))


def evaluate(cond: str | None, outcomes: dict[str, str], job_ok: bool, has_bundle: bool) -> bool:
    """GitHub's `if` for the few forms these workflows use; anything else is a test failure, not a guess"""
    if cond is None:
        return job_ok
    terms = [t.strip() for t in cond.split("&&")]
    statusless = not any(re.search(r"\b(success|failure|always|cancelled)\(\)", t) for t in terms)
    value = job_ok if statusless else True
    for t in terms:
        if m := re.fullmatch(r"steps\.(\w+)\.outcome == '(\w+)'", t):
            value = value and outcomes.get(m.group(1), "skipped") == m.group(2)
        elif t == "hashFiles('out/*/bundle.tar') != ''":
            value = value and has_bundle
        elif t in ("success()", "always()"):
            value = value and (job_ok if t == "success()" else True)
        elif re.fullmatch(r"\$\{\{.*\}\}", t) or t.startswith("inputs.") or t.startswith("vars.") or t.startswith("github.") or t.startswith("env."):
            continue  # a condition on the dispatch, not on the steps: taken as true here
        else:
            raise AssertionError(f"an `if` this model does not know: {t!r}")
    return value


def simulate(steps: list[dict], answers: list[bool], fail_before: bool = False, has_bundle: bool = True) -> dict:
    """answers: what the transparency log says to each attestation that runs, in order (True: written). fail_before: a step before the attestation fails."""
    job_ok, outcomes, ran, tries, answer = True, {}, [], 0, iter(answers)
    first_attest = next(i for i, s in enumerate(steps) if is_attest(s))
    # the last step before the attestation that can fail the job (bump-sharded's raze-plan step is advisory: continue-on-error)
    breaker = max(i for i in range(first_attest) if not steps[i].get("continue-on-error"))
    for i, s in enumerate(steps):
        if not evaluate(s.get("if"), outcomes, job_ok, has_bundle):
            if "id" in s:
                outcomes[s["id"]] = "skipped"
            continue
        ran.append(s.get("id") or s.get("name") or s.get("uses"))
        if is_attest(s):
            tries += 1
            ok = next(answer)
        else:
            ok = not (fail_before and i == breaker)
        if "id" in s:
            outcomes[s["id"]] = "success" if ok else "failure"
        if not ok and not s.get("continue-on-error"):
            job_ok = False
    upload = any("upload-artifact" in str(steps[i].get("uses", "")) for i in range(len(steps)) if (steps[i].get("id") or steps[i].get("name") or steps[i].get("uses")) in ran)
    return {"ok": job_ok, "tries": tries, "ran": ran, "upload": upload, "waits": [r for r in ran if str(r).startswith("The transparency log refused")]}


class Retry(unittest.TestCase):
    def test_the_three_workflows_have_the_three_tries_and_nothing_else_attests(self):
        for wf in WORKFLOWS:
            attests = [s for s in steps_of(wf) if is_attest(s)]
            self.assertEqual([s.get("id") for s in attests], ["attest_1", "attest_2", "attest_3"], wf)
            self.assertTrue(attests[0].get("continue-on-error") and attests[1].get("continue-on-error"), wf)
            self.assertFalse(attests[2].get("continue-on-error", False), wf)  # the last failure fails the job
            self.assertEqual(len({str(s["with"]) for s in attests}), 1, wf)  # the same subject every time
        others = [p.name for p in (ROOT / ".github" / "workflows").glob("*.yml") if p.name not in WORKFLOWS and "attest-build-provenance@" in p.read_text()]
        self.assertEqual(others, [], "a workflow that attests without the retries")

    def test_every_sequence_of_answers(self):
        n = 0
        for wf in WORKFLOWS:
            st = steps_of(wf)
            for k in range(1, 4):
                for answers in itertools.product([False, True], repeat=k):
                    if any(answers[:-1]) or (k < 3 and not answers[-1]):
                        continue  # only sequences that end the tries: failures, then a success, or three failures
                    r = simulate(st, list(answers))
                    first_ok = answers.index(True) + 1 if True in answers else None
                    self.assertEqual(r["tries"], first_ok or 3, (wf, answers))
                    self.assertEqual(r["ok"], first_ok is not None, (wf, answers))
                    self.assertEqual(r["upload"], first_ok is not None, (wf, answers))  # never an unattested upload
                    self.assertEqual(len(r["waits"]), (first_ok or 3) - 1, (wf, answers))  # a wait only between failed tries
                    n += 1
        self.assertEqual(n, 12)  # 3 workflows x (written at once, at the second try, at the third, never)

    def test_a_failure_before_the_attestation_still_stops_everything(self):
        for wf in WORKFLOWS:
            r = simulate(steps_of(wf), [True, True, True], fail_before=True)
            self.assertEqual((r["ok"], r["tries"], r["upload"]), (False, 0, False), wf)

    def test_memory_intake_without_a_bundle_neither_attests_nor_waits(self):
        r = simulate(steps_of("memory-intake.yml"), [False, False, False], has_bundle=False)
        self.assertEqual((r["ok"], r["tries"], r["waits"]), (True, 0, []))

    def test_the_waits_and_the_time_limits(self):
        for wf, job in WORKFLOWS.items():
            waits = [s["run"] for s in steps_of(wf) if str(s.get("name", "")).startswith("The transparency log refused")]
            self.assertEqual(waits, ["sleep 300", "sleep 900"], wf)
        import yaml

        limits = {wf: yaml.safe_load((ROOT / ".github" / "workflows" / wf).read_text())["jobs"][job]["timeout-minutes"] for wf, job in WORKFLOWS.items()}
        self.assertEqual(limits, {"bump-library.yml": 50, "bump-sharded.yml": 140, "memory-intake.yml": 50})  # each 20 minutes more than before


if __name__ == "__main__":
    unittest.main()
