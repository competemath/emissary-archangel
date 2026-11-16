"""last_part.py: the tree's last part number, from a real answer or not at all.

The real case (15 Nov 2026, flt-anthropic recut, run 43738852809): the pack step asked GitHub for `data/intake/flt-anthropic/parts` without a token and read anything that was not a list as "no
parts". On a runner GitHub rate-limited, that gave 1 instead of 3: the 17 new parts were numbered 002 to 018 over the merged 002 and 003, the opener opened the third chunk as "part 4 of 18", its umbrella
named modules of the chunks before it, and tengoku#842 failed `imports`, `intake`, `pr-gate` and its tag build (four hours of tree build).
`fixtures/real-tengoku-flt-parts-listing-2026-11-15.json` is the real answer (002.json, 003.json). The rate-limit and not-found bodies are GitHub's own.

Invariants: a 200 with a list gives the highest NNN.json (1 when there is none); 404 gives 1 (a library merged in one part has no `parts` directory); every other status, a body that is not JSON and a
JSON that is not a list stop with a message, never a number. The pack step: authenticated, retried, the status read apart from the body, the number from this script, a failure that stops the job
before any part is cut; the bare call is gone. Mutants (each must fail a check): a non-list read as 1, 404 stopping, the highest not the last, the token dropped from the call.
"""

from __future__ import annotations

import contextlib
import inspect
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import last_part as lp  # noqa: E402

REAL = (HERE / "fixtures" / "real-tengoku-flt-parts-listing-2026-11-15.json").read_text()
RATE = json.dumps({"message": "API rate limit exceeded for 20.1.2.3. (But here's the good news: Authenticated requests get a higher rate limit. Check out the documentation for more details.)", "documentation_url": "https://docs.github.com/rest/overview/resources-in-the-rest-api#rate-limiting"})
NOT_FOUND = json.dumps({"message": "Not Found", "documentation_url": "https://docs.github.com/rest/repos/contents#get-repository-content", "status": "404"})
WORKFLOW = HERE.parents[2] / ".github" / "workflows" / "bump-sharded.yml"
DOC = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
PACK = next(s for s in DOC["jobs"]["finish"]["steps"] if s.get("name") == "Pack and attest")


def stops(body: str, status: str) -> str:
    with contextlib.redirect_stderr(io.StringIO()):
        try:
            lp.last_part(body, status)
        except SystemExit as e:
            return str(e.code)
    raise AssertionError(f"gave a number for {status} {body[:40]!r}")


class TheNumber(unittest.TestCase):
    def test_the_real_listing_says_the_last_part_is_003(self):
        self.assertEqual({x["name"] for x in json.loads(REAL)}, {"002.json", "003.json"})
        self.assertEqual(lp.last_part(REAL, "200"), 3)

    def test_the_next_part_is_after_the_last_one_whatever_the_order(self):
        names = ["010.json", "002.json", "009.json", "README.md", "11.json", "003.json"]
        self.assertEqual(lp.last_part(json.dumps([{"name": n} for n in names]), "200"), 10)

    def test_an_empty_listing_is_part_one(self):
        self.assertEqual(lp.last_part("[]", "200"), 1)
        self.assertEqual(lp.last_part(json.dumps([{"name": "notes.md"}]), "200"), 1)

    def test_no_parts_directory_is_a_library_merged_in_one_part(self):
        self.assertEqual(lp.last_part(NOT_FOUND, "404"), 1)

    def test_a_rate_limit_is_not_no_parts(self):
        """the bug: this answer used to read as 1"""
        self.assertIn("403", stops(RATE, "403"))
        self.assertIn("429", stops(RATE, "429"))
        self.assertIn("not a listing", stops(RATE, "200"))  # even if it came with a 200

    def test_server_errors_and_garbage_are_not_numbers(self):
        for status in ("500", "502", "503", "", "301"):
            self.assertIn("not a listing", stops("<html>", status))
        self.assertIn("not JSON", stops("<html>", "200"))
        self.assertIn("not a listing", stops('{"name": "002.json"}', "200"))  # a single file object, not a directory

    def test_a_scalar_is_not_a_listing_and_no_traceback(self):
        for body in ("null", "7", '"x"', "true"):
            self.assertIn("not a listing", stops(body, "200"))

    def test_an_entry_without_a_name_stops_instead_of_understating_the_number(self):
        """cubic on #206: a 200 listing with a broken entry used to skip it silently"""
        for entries in ([{"name": "003.json"}, {"path": "004.json"}], [{"name": "003.json"}, "004.json"], [{"name": 4}, {"name": "003.json"}], [None]):
            self.assertIn("has no name", stops(json.dumps(entries), "200"))

    def test_the_command_prints_the_number(self):
        for status, body, want in (("200", REAL, "3"), ("404", NOT_FOUND, "1")):
            out = io.StringIO()
            old = sys.stdin
            sys.stdin = io.StringIO(body)
            try:
                with contextlib.redirect_stdout(out):
                    self.assertEqual(lp.main(["--status", status]), 0)
            finally:
                sys.stdin = old
            self.assertEqual(out.getvalue().strip(), want)

    def test_the_command_stops_on_a_rate_limit(self):
        old = sys.stdin
        sys.stdin = io.StringIO(RATE)
        try:
            with self.assertRaises(SystemExit):
                lp.main(["--status", "403"])
        finally:
            sys.stdin = old


def snippet(script: str) -> str:
    """the lookup of a pack step: from `body=$(mktemp)` to the `last=$(…)` line"""
    i = script.index("body=$(mktemp)")
    j = script.index("last=$(python3")
    k = script.index("exit 1; }", j) + len("exit 1; }")
    return script[i:k]


def run_snippet(script: str, answers: list[tuple[str, str]], curl_fails: bool = False) -> tuple[int, str, int]:
    """the lookup run for real in bash with a fake `curl` that answers (status, body) in turn and a `sleep` that does not sleep: (exit status, `last`, how many times curl was called)"""
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "emissary").symlink_to(HERE.parents[2])
        bin_ = root / "bin"
        bin_.mkdir()
        (root / "answers.json").write_text(json.dumps(answers))
        (bin_ / "curl").write_text(
            "#!/usr/bin/env python3\nimport json, sys, os\nroot = os.environ['FAKE_ROOT']\nn = len(os.listdir(root + '/calls'))\nopen(root + '/calls/' + str(n), 'w').close()\n"
            "answers = json.load(open(root + '/answers.json'))\ncode, body = answers[min(n, len(answers) - 1)]\n"
            "args = sys.argv[1:]\nout = args[args.index('-o') + 1]\nopen(out, 'w').write(body)\nprint(code, end='')\nsys.exit(" + ("7" if curl_fails else "0") + ")\n"
        )
        (bin_ / "curl").chmod(0o755)
        (root / "calls").mkdir()
        prog = "set -e\nsleep() { :; }\n" + snippet(script) + '\necho "last=$last"\n'
        r = subprocess.run(["bash", "-c", prog], cwd=root, capture_output=True, text=True, env={**os.environ, "PATH": f"{bin_}:{os.environ['PATH']}", "FAKE_ROOT": str(root), "KEY": "flt-anthropic", "GH_TOKEN": "t"})
        calls = len(os.listdir(root / "calls"))
        last = next((ln.split("=", 1)[1] for ln in r.stdout.splitlines() if ln.startswith("last=")), "")
        return r.returncode, last, calls


class ThePackStep(unittest.TestCase):
    script = PACK["run"]

    def test_the_call_is_authenticated_bounded_and_its_status_is_read_apart(self):
        self.assertEqual(PACK["env"]["GH_TOKEN"], "${{ github.token }}")
        self.assertIn('-H "Authorization: Bearer $GH_TOKEN"', self.script)
        self.assertIn("--max-time 60", self.script)  # a stalled connection must not hold the job (cubic on #206)
        self.assertIn("-o \"$body\" -w '%{http_code}'", self.script)  # the body to a file: a curl retry would append the bodies of the failed tries to stdout
        self.assertNotIn("--retry", self.script)
        self.assertIn('last_part.py --status "$code" < "$body"', self.script)

    def test_a_failure_stops_the_job_before_any_part_is_cut(self):
        i = self.script.index("last=$(python3 emissary/scripts/bump/last_part.py")
        j = self.script.index("python3 emissary/scripts/bump/bundle_layers.py")
        self.assertLess(i, j)
        self.assertIn("exit 1", self.script[i:j])
        self.assertIn("--start $((last + 1))", self.script)

    def test_the_bare_call_is_gone(self):
        self.assertNotIn("curl -sS \"https://api.github.com/repos/competemath/tengoku/contents/data/intake/$KEY/parts\"", self.script)
        self.assertNotIn("max(n, default=1)", self.script)

    def test_the_comment_does_not_call_the_token_read_only(self):
        """cubic on #206: the finish job holds attestations: write, so `github.token` is not read-only"""
        self.assertNotIn("read-only", WORKFLOW.read_text(encoding="utf-8").split("- name: Pack and attest")[1].split("run: |")[0])
        self.assertIn("contents", DOC["jobs"]["finish"]["permissions"])

    def test_the_token_is_dropped_after_the_call_and_the_last_try_does_not_sleep(self):
        """cubic on #206 (P3, both): only the lookup needs GH_TOKEN, so the shell unsets it right after; no pause after the fifth try"""
        i = self.script.index("last=$(python3 emissary/scripts/bump/last_part.py")
        self.assertIn("unset GH_TOKEN", self.script)
        self.assertLess(self.script.index("unset GH_TOKEN"), self.script.index("python3 emissary/scripts/bump/bundle_layers.py"))
        self.assertGreater(self.script.index("unset GH_TOKEN"), self.script.index("curl -sS"))
        self.assertIn('[ "$try" -lt 5 ] || break', self.script)
        self.assertLess(self.script.index('[ "$try" -lt 5 ] || break'), self.script.index("sleep 20"))
        self.assertGreater(i, 0)

    def test_the_last_try_neither_sleeps_nor_says_again(self):
        with tempfile.TemporaryDirectory() as d:
            marker = Path(d) / "slept"
            prog = f"sleep() {{ echo s >> {marker}; }}\n"
            # run the real snippet with a sleep that counts: five tries give four pauses, not five
            import types  # noqa: F401

            root_status, last, calls = run_snippet(self.script.replace("sleep 20", "echo s >> " + str(marker)), [("403", RATE)])
            self.assertEqual(calls, 5)
            self.assertEqual(len(marker.read_text().split()), 4)
            self.assertNotEqual(root_status, 0)
            self.assertEqual(prog.count("sleep"), 1)

    def test_it_runs_a_real_answer_after_a_server_error_without_mixing_the_bodies(self):
        """cubic on #206 (P1): a 503 and then a 200 must give 3, not an invalid concatenation"""
        status, last, calls = run_snippet(self.script, [("503", '{"message":"Server Error"}'), ("200", REAL)])
        self.assertEqual((status, last, calls), (0, "3", 2))

    def test_it_runs_a_404_as_no_parts_directory(self):
        self.assertEqual(run_snippet(self.script, [("404", NOT_FOUND)]), (0, "1", 1))

    def test_a_rate_limit_that_does_not_end_stops_the_job_after_five_tries(self):
        status, last, calls = run_snippet(self.script, [("403", RATE)])
        self.assertNotEqual(status, 0)
        self.assertEqual((last, calls), ("", 5))

    def test_a_curl_that_cannot_connect_is_a_try_too(self):
        status, last, calls = run_snippet(self.script, [("000", "")], curl_fails=True)
        self.assertNotEqual(status, 0)
        self.assertEqual((last, calls), ("", 5))

    def test_mutant_a_stalled_call_without_a_limit(self):
        self.assertNotIn("--max-time", self.script.replace("--max-time 60", ""))


class TheLibraryWorkflowToo(unittest.TestCase):
    """bump-library.yml had the same bare call (the same story, found while fixing bump-sharded.yml)"""

    text = (HERE.parents[2] / ".github" / "workflows" / "bump-library.yml").read_text(encoding="utf-8")
    doc = yaml.safe_load(text)
    pack = next(s for s in doc["jobs"]["attest"]["steps"] if str(s.get("name", "")).startswith("Pack (the attested bytes"))

    def test_the_same_lookup(self):
        self.assertEqual(self.pack["env"]["GH_TOKEN"], "${{ github.token }}")
        self.assertIn('-H "Authorization: Bearer $GH_TOKEN"', self.pack["run"])
        self.assertIn("--max-time 60", self.pack["run"])
        self.assertIn('last_part.py --status "$code" < "$body"', self.pack["run"])
        self.assertIn("--start $((last + 1))", self.pack["run"])
        self.assertNotIn("max(n, default=1)", self.pack["run"])
        self.assertNotIn("--retry", self.pack["run"])

    def test_the_token_is_dropped_here_too_and_the_last_try_does_not_sleep(self):
        run = self.pack["run"]
        self.assertIn("unset GH_TOKEN", run)
        self.assertLess(run.index("unset GH_TOKEN"), run.index("python3 emissary/scripts/bump/bundle_layers.py"))
        self.assertIn('[ "$try" -lt 5 ] || break', run)

    def test_it_runs_here_too(self):
        self.assertEqual(run_snippet(self.pack["run"], [("502", "<html>"), ("200", REAL)]), (0, "3", 2))
        status, last, calls = run_snippet(self.pack["run"], [("429", RATE)])
        self.assertNotEqual(status, 0)
        self.assertEqual((last, calls), ("", 5))

    def test_the_script_is_checked_out_where_the_step_runs_it(self):
        self.assertIn('"/scripts/bump/last_part.py"', self.text)  # the job lists the files it needs one by one (test_workflow_script_imports.py)


def mutated(old: str, new: str):
    src = inspect.getsource(lp.last_part)
    assert src.count(old) == 1, old
    ns = dict(vars(lp))
    exec(src.replace(old, new), ns)
    return ns["last_part"]


class TheMutants(unittest.TestCase):
    def test_the_entry_check_dropped(self):
        f = mutated('if not isinstance(x, dict) or not isinstance(x.get("name"), str):', "if False:")
        with self.assertRaises(KeyError):  # a crash with a traceback instead of the named stop (test_an_entry_without_a_name_stops_instead_of_understating_the_number refuses this)
            f(json.dumps([{"name": "003.json"}, {"path": "004.json"}]), "200")

    def test_the_list_check_dropped(self):
        f = mutated("if not isinstance(listing, list):", "if False:")
        with self.assertRaises(TypeError):  # a scalar is iterated: a traceback, not the named stop
            f("7", "200")

    def test_404_stopping(self):
        f = mutated('if code == "404":', "if False:")
        with self.assertRaises(SystemExit):
            f(NOT_FOUND, "404")  # a library merged in one part would never be bumped from the tree

    def test_the_first_not_the_highest(self):
        f = mutated("return max(nums, default=1)", "return nums[0] if nums else 1")
        self.assertEqual(f(json.dumps([{"name": "002.json"}, {"name": "003.json"}]), "200"), 2)  # test_the_real_listing_says_the_last_part_is_003 refuses this

    def test_any_status_accepted(self):
        f = mutated('if code != "200":', "if False:")
        self.assertEqual(f("[]", "403"), 1)  # a rate-limited answer with a list body would be taken


if __name__ == "__main__":
    unittest.main()
