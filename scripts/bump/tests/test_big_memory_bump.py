"""Modules too big for a runner's RAM, in the bump (flt-anthropic, 5 Nov 2026: 86 modules, the top of the proof, were left out of its setup because the P2M.Sol proofs they import
needed more than 14 GB; the bump rebuilds the library on the tree's Mathlib and judges it in one Lean process, on the same 16 GB runners).

  1. gate2_guard counts swap when the job added it: the limit is a share of RAM + swap, and what a process holds is VmRSS + VmSwap. Checked on a grid of machines and on the real
     /proc of the machine the test runs on (Linux; skipped elsewhere), and with broken versions that must be caught.
  2. only_modules (plan_shards.restrict_wanted): judge the named modules only. Checked on the REAL module names of every library set up so far (scripts/fixtures/real-module-lists.json,
     110 libraries, 14,913 modules) with import graphs laid over them, through the real planner: the targets of the plan are exactly the named modules that have entries, every shard builds
     the closure of its targets, a name the library does not have stops the run.
  3. the workflows carry the knobs through (swap_gb, build_timeout_min, only_modules) and validate them before they reach a shell.
"""

import json
import os
import random
import re
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import gate2_guard as gg  # noqa: E402
import plan_shards as ps  # noqa: E402

ROOT = Path(__file__).resolve().parents[3]
WORKFLOWS = ROOT / ".github" / "workflows"
REAL = json.loads((ROOT / "scripts" / "fixtures" / "real-module-lists.json").read_text())


def meminfo(mem_kb: int, swap_kb: int) -> str:
    return "\n".join([f"MemTotal:       {mem_kb} kB", f"MemFree:        {mem_kb // 3} kB", f"MemAvailable:   {mem_kb // 2} kB", "Buffers:          123456 kB", f"SwapCached:            0 kB",
                      f"SwapTotal:      {swap_kb} kB", f"SwapFree:       {swap_kb} kB", "Dirty:               456 kB", ""])


class GuardCountsSwap(unittest.TestCase):
    GB = 1024 * 1024

    def test_limit_grid(self):
        n = 0
        for mem_gb in (2, 4, 7, 8, 16, 32, 64):
            for swap_gb in (0, 1, 4, 16, 48, 100):
                for share in (0.1, 0.5, 0.8, 0.92, 1.0):
                    text = meminfo(mem_gb * self.GB, swap_gb * self.GB)
                    plain = gg.limit_from_meminfo(text, share, False)
                    counted = gg.limit_from_meminfo(text, share, True)
                    self.assertEqual(plain, int(mem_gb * self.GB * share))
                    self.assertEqual(counted, int((mem_gb + swap_gb) * self.GB * share))
                    self.assertGreaterEqual(counted, plain)
                    n += 1
        self.assertGreaterEqual(n, 200)

    def test_default_is_unchanged(self):
        # without count_swap nothing changes, whatever the swap: the 4 GB a hosted runner has by default must not raise the limit
        self.assertEqual(gg.limit_from_meminfo(meminfo(16 * self.GB, 4 * self.GB)), int(16 * self.GB * gg.RUNNER_SHARE))
        self.assertEqual(gg.mem_limit_kb.__defaults__, (gg.RUNNER_SHARE, False))

    def test_no_memtotal(self):
        self.assertIsNone(gg.limit_from_meminfo("SwapTotal: 100 kB\n", 0.8, True))
        self.assertIsNone(gg.limit_from_meminfo("", 0.8, False))

    def test_footprint_from_status(self):
        for rss in (0, 1, 123456, 15 * self.GB):
            for swap in (0, 1, 98765, 40 * self.GB):
                text = f"Name:\tlean\nVmPeak:\t{rss + swap + 5} kB\nVmRSS:\t{rss} kB\nRssAnon:\t{rss // 2} kB\nVmSwap:\t{swap} kB\nThreads:\t4\n"
                self.assertEqual(gg.footprint_from_status(text), rss + swap)
        self.assertEqual(gg.footprint_from_status("Name:\tx\nThreads:\t1\n"), 0)

    @unittest.skipUnless(Path("/proc/self/status").exists() and Path("/proc/meminfo").exists(), "needs a Linux /proc")
    def test_real_proc(self):
        real = Path("/proc/self/status").read_text()
        want = sum(int(m.group(1)) for m in re.finditer(r"^(?:VmRSS|VmSwap):\s+(\d+) kB", real, re.M))
        self.assertEqual(gg.footprint_from_status(real), want)
        self.assertGreater(want, 0)
        info = Path("/proc/meminfo").read_text()
        mem = int(re.search(r"^MemTotal:\s+(\d+) kB", info, re.M).group(1))
        swap = int(re.search(r"^SwapTotal:\s+(\d+) kB", info, re.M).group(1))
        self.assertEqual(gg.limit_from_meminfo(info, 0.8, False), int(mem * 0.8))
        self.assertEqual(gg.limit_from_meminfo(info, 0.8, True), int((mem + swap) * 0.8))
        self.assertEqual(gg.mem_limit_kb(0.8, True), int((mem + swap) * 0.8))
        # the process group of a real child: counting swap never reports less than not counting it
        import subprocess
        p = subprocess.Popen([sys.executable, "-c", "import time; x = bytearray(30_000_000); time.sleep(3)"], start_new_session=True)
        try:
            time.sleep(0.5)
            self.assertGreaterEqual(gg.rss_kb(p.pid, True), gg.rss_kb(p.pid, False))
            self.assertGreater(gg.rss_kb(p.pid, False), 20_000)
        finally:
            p.kill()
            p.wait()

    def test_guard_kills_on_the_footprint_when_asked(self):
        # run_guarded takes count_swap and passes it to the reading; a child under the limit ends on its own either way
        log = Path(tempfile.mkdtemp()) / "g.log"
        for count_swap in (False, True):
            r = gg.run_guarded([sys.executable, "-c", "print(1)"], ".", dict(os.environ), log, 20, 10**9, poll_s=0.05, count_swap=count_swap)
            self.assertEqual(r.kind, "ok")

    def test_broken_versions_are_caught(self):
        def broken_always(meminfo_text, share=0.8, count_swap=False):
            return gg.limit_from_meminfo(meminfo_text, share, True)

        def broken_never(meminfo_text, share=0.8, count_swap=False):
            return gg.limit_from_meminfo(meminfo_text, share, False)

        def broken_status(text):
            return sum(int(m.group(1)) for m in re.finditer(r"^VmRSS:\s+(\d+) kB", text, re.M))

        text = meminfo(16 * self.GB, 48 * self.GB)
        self.assertNotEqual(broken_always(text, 0.8, False), gg.limit_from_meminfo(text, 0.8, False))
        self.assertNotEqual(broken_never(text, 0.8, True), gg.limit_from_meminfo(text, 0.8, True))
        status = "VmRSS:\t100 kB\nVmSwap:\t900 kB\n"
        self.assertNotEqual(broken_status(status), gg.footprint_from_status(status))

    def test_the_driver_and_the_shard_pass_it_on(self):
        drv = (HERE / "gate2_driver.py").read_text()
        self.assertIn('ap.add_argument("--count-swap", action="store_true"', drv)
        self.assertIn("mem_limit_kb(a.rss_share, a.count_swap)", drv)
        self.assertIn("count_swap=a.count_swap", drv)
        shard = (WORKFLOWS / "bump-shard.yml").read_text()
        self.assertIn('$([ "$SWAP_GB" != 0 ] && echo --count-swap)', shard)


def real_graph(rng: random.Random, mods: list[str]):
    """Real module names with a random import graph over them: each module imports up to 3 earlier ones (a DAG), and has a size."""
    order = sorted(mods)
    rng.shuffle(order)
    imp = {m: [] for m in order}
    for i, m in enumerate(order):
        if i:
            imp[m] = sorted({order[rng.randrange(max(0, i - 40), i)] for _ in range(rng.randint(0, 3))})
    weight = {m: rng.randint(20, 3000) for m in order}
    return imp, weight


def closure(imp: dict[str, list[str]], ms) -> set[str]:
    out, stack = set(), list(ms)
    while stack:
        m = stack.pop()
        if m in out:
            continue
        out.add(m)
        stack.extend(imp[m])
    return out


class OnlyModules(unittest.TestCase):
    def test_restrict_wanted_on_real_names(self):
        rng = random.Random(20261105)
        cases = 0
        for lib, mods in REAL.items():
            mods = sorted(set(mods))
            if len(mods) < 3:
                continue
            modset = set(mods)
            for _ in range(8):
                wanted = {m for m in mods if rng.random() < rng.choice((0.1, 0.5, 0.9, 1.0))}
                only = set(rng.sample(mods, rng.randint(1, min(len(mods), 40))))
                cases += 1
                expect = wanted & only
                if expect:
                    got = ps.restrict_wanted(wanted, only, modset)
                    self.assertEqual(got, expect, lib)
                    self.assertLessEqual(got, only)
                    self.assertLessEqual(got, wanted)
                else:
                    with self.assertRaises(ValueError, msg=lib):
                        ps.restrict_wanted(wanted, only, modset)
                # nothing named: nothing changes (and the result is a copy)
                same = ps.restrict_wanted(wanted, set(), modset)
                self.assertEqual(same, wanted)
                self.assertIsNot(same, wanted)
                # a name the library does not have stops the run, whatever else is named
                with self.assertRaises(ValueError) as cm:
                    ps.restrict_wanted(wanted, only | {lib + ".NoSuchModule"}, modset)
                self.assertIn("does not have", str(cm.exception))
                self.assertIn(lib + ".NoSuchModule", str(cm.exception))
        self.assertGreaterEqual(cases, 800)

    def test_the_real_planner_judges_exactly_the_named_modules(self):
        rng = random.Random(7)
        planned = 0
        for lib, mods in REAL.items():
            mods = sorted(set(mods))
            if len(mods) < 12:
                continue
            imp, weight = real_graph(rng, mods)
            wanted = {m for m in mods if rng.random() < 0.8}
            only = set(rng.sample(sorted(wanted), rng.randint(1, min(len(wanted), 30))))
            restricted = ps.restrict_wanted(wanted, only, set(imp))
            for k in (1, 3, 8):
                plan = ps.plan(imp, weight, k, wanted=restricted)
                targets = [t for s in plan["shards"] for t in s["targets"]]
                self.assertEqual(sorted(targets), sorted(restricted), f"{lib} k={k}: every named module is judged once, and nothing else")
                for s in plan["shards"]:
                    self.assertEqual(set(s["build"]), closure(imp, s["targets"]), f"{lib} k={k}: a shard builds exactly the closure of its targets, no module more")
                full = ps.plan(imp, weight, k, wanted=wanted)
                self.assertLessEqual(sum(len(s["build"]) for s in plan["shards"]), sum(len(s["build"]) for s in full["shards"]) + len(mods), f"{lib} k={k}")
                planned += 1
        self.assertGreaterEqual(planned, 200)

    def test_broken_versions_are_caught(self):
        mods = {"A", "B", "C"}
        # a version that ignores the named modules, one that drops the unknown-name error, and one that lets an empty result through
        def ignores(wanted, only, modules):
            return set(wanted)

        def no_error(wanted, only, modules):
            return wanted & only if only else set(wanted)

        self.assertNotEqual(ignores({"A", "B"}, {"A"}, mods), ps.restrict_wanted({"A", "B"}, {"A"}, mods))
        self.assertEqual(no_error({"A"}, {"Z"}, mods), set())  # the broken one says nothing where the real one stops
        with self.assertRaises(ValueError):
            ps.restrict_wanted({"A"}, {"Z"}, mods)
        with self.assertRaises(ValueError):
            ps.restrict_wanted({"A"}, {"B"}, mods)


def knob_problems(sharded: str, shard: str) -> list[str]:
    """What is wrong with the way the two workflows carry swap_gb, build_timeout_min and only_modules (empty: nothing)."""
    bad = []
    need = [
        (sharded, r'swap_gb: \{ description: "[^"]*", default: "0" \}', "bump-sharded swap_gb input, default 0"),
        (sharded, r'build_timeout_min: \{ description: "[^"]*", default: "90" \}', "bump-sharded build_timeout_min input, default 90"),
        (sharded, r'only_modules: \{ description: "[^"]*", default: "" \}', "bump-sharded only_modules input, default empty"),
        (shard, r'swap_gb: \{ type: string, default: "0"', "bump-shard swap_gb input, default 0"),
        (shard, r'build_timeout_min: \{ type: string, default: "90"', "bump-shard build_timeout_min input, default 90"),
        (sharded, re.escape("swap_gb: ${{ inputs.swap_gb }}"), "swap_gb handed to the shards"),
        (sharded, re.escape("build_timeout_min: ${{ inputs.build_timeout_min }}"), "build_timeout_min handed to the shards"),
        (sharded, re.escape('ONLY_MODULES: "${{ inputs.only_modules }}"'), "only_modules reaches the plan through env"),
        (sharded, re.escape("ps.restrict_wanted(wanted, only, set(imp))"), "the plan restricts the wanted set"),
        (shard, re.escape('--timeout "$BUILD_TIMEOUT_MIN"'), "tolerant_build gets the timeout"),
        (shard, r"- name: This shard's modules[\s\S]*- name: The old exports of this shard's targets[\s\S]*- name: elan[\s\S]*- name: The library at its pinned commit[\s\S]*- name: Build this shard's modules", "the old exports are fetched before the library is built (a failed download must cost minutes, not the shard)"),
        (shard, re.escape('run: sh emissary/scripts/add-swap.sh "$SWAP_GB" 40'), "the swap is added by add-swap.sh, sized from the free space"),
        (shard, re.escape('$([ "$SWAP_GB" != 0 ] && echo --count-swap)'), "Gate 2 counts swap when swap was added"),
        (shard, r'BUILD_TIMEOUT_MIN" =~ \^\[1-9\]\[0-9\]\{0,2\}\$ \]\] && \[ "\$BUILD_TIMEOUT_MIN" -le 170 \]', "build_timeout_min is checked: 1-170 (the job has 345 minutes)"),
        (sharded, re.escape("python3 scripts/bump/plan_inputs.py ../plan/inputs.json"), "the plan records what the shards are built with through plan_inputs.py"),
        (sharded, re.escape("ps.parse_only(os.environ.get(\"ONLY_MODULES\", \"\"))"), "only_modules is parsed strictly (a list with no name is an error)"),
        (shard, r'SWAP_GB" =~ \^\(0\|\[1-9\]\[0-9\]\{0,2\}\)\$', "swap_gb is checked: a number of GB"),
    ]
    for text, pattern, what in need:
        if not re.search(pattern, text):
            bad.append(what)
    if "ps.restrict_wanted" in sharded and 'k = int(os.environ["SHARDS"] or 0)' in sharded and sharded.index("ps.restrict_wanted") > sharded.index('k = int(os.environ["SHARDS"] or 0)'):
        bad.append("the plan is cut before the wanted set is restricted")
    if "    steps:\n" in shard:
        steps = shard.split("    steps:\n", 1)[1]
        marks = [steps.find(x) for x in ("The memory knobs are numbers", "- name: Free disk", "This shard's modules, and only the exports", "Swap (swap_gb)", "The library at its pinned commit")]
        if -1 in marks or marks != sorted(marks):
            bad.append("the steps are not in the order: knobs checked, disk freed, scripts checked out, swap added, library built")
        swap_body = steps.split("Swap (swap_gb)", 1)[1].split("      - ", 1)[0] if "Swap (swap_gb)" in steps else ""
        if "${{" in swap_body.split("run: |", 1)[-1]:
            bad.append("a ${{ }} expression sits inside the swap step's shell")
    return bad


class WorkflowsCarryTheKnobs(unittest.TestCase):
    def setUp(self):
        self.sharded = (WORKFLOWS / "bump-sharded.yml").read_text()
        self.shard = (WORKFLOWS / "bump-shard.yml").read_text()

    def test_the_real_workflows_carry_the_knobs(self):
        self.assertEqual(knob_problems(self.sharded, self.shard), [])

    def test_broken_workflows_are_caught(self):
        s, h = self.sharded, self.shard
        mutants = {
            "no swap_gb in the sharded workflow": (s.replace("swap_gb: ${{ inputs.swap_gb }}", ""), h),
            "no timeout for tolerant_build": (s, h.replace(' --timeout "$BUILD_TIMEOUT_MIN"', "")),
            "Gate 2 never counts swap": (s, h.replace('$([ "$SWAP_GB" != 0 ] && echo --count-swap)', "")),
            "the timeout is not checked": (s, h.replace('-le 170', "-le 99999")),
            "the timeout cap is the whole job again": (s, h.replace('-le 170', "-le 340")),
            "the swap size is not checked": (s, h.replace("^(0|[1-9][0-9]{0,2})$", "^[0-9]+$")),
            "only_modules is not applied": (s.replace("ps.restrict_wanted(wanted, only, set(imp))", "wanted"), h),
            "the plan is cut before the restriction": (s.replace('          try:  # ONLY THESE', '          k = int(os.environ["SHARDS"] or 0)\n          try:  # ONLY THESE', 1), h),
            "the swap comes before the disk is freed": (s, h.replace("- name: Free disk", "- name: Swap (swap_gb), for modules that do not fit in a runner's RAM\n        if: inputs.swap_gb != '0'\n        run: true\n      - name: Free disk", 1)),
            "the swap comes before the scripts are checked out": (s, h.replace("      - uses: actions/download-artifact", "      - name: Swap (swap_gb), for modules that do not fit in a runner's RAM\n        run: true\n      - uses: actions/download-artifact", 1)),
            "an expression inside the swap shell": (s, h.replace('add-swap.sh "$SWAP_GB" 40', 'add-swap.sh "${{ inputs.swap_gb }}" 40')),
            "the old exports are fetched after the build again": (s, h.replace(h[h.index("      - name: The old exports of this shard's targets"):h.index("      - name: elan\n")], "").replace("      - name: What the passed theorems are made of\n", "      - name: The old exports of this shard's targets\n        run: node scripts/fetch-exports.mjs \"$KEY\" --modules targets.txt\n      - name: What the passed theorems are made of\n", 1)),
            "a fixed swap file instead of add-swap.sh": (s, h.replace('run: sh emissary/scripts/add-swap.sh "$SWAP_GB" 40', 'run: sudo fallocate -l "${SWAP_GB}G" /swapfile')),
        }
        for name, (ms, mh) in mutants.items():
            self.assertNotEqual((ms, mh), (s, h), name + ": the mutation did not apply")
            self.assertTrue(knob_problems(ms, mh), f"not caught: {name}")


import time  # noqa: E402  (used by the real-proc test)

class FetchExportsRetries(unittest.TestCase):
    def test_a_504_is_retried_for_minutes_and_a_part_is_appended_only_when_complete(self):
        src = (ROOT / "scripts" / "fetch-exports.mjs").read_text()
        m = re.search(r"curl -fL --retry (\d+) --retry-delay (\d+) --progress-bar -o \"\$2\" \"\$1\"", src)
        self.assertIsNotNone(m, "curl needs --retry N --retry-delay S and -o PART: each part into its own file")
        self.assertGreaterEqual(int(m.group(1)) * int(m.group(2)), 90, "the retries must span at least a minute and a half (3 retries over 7 seconds lost a 3-hour shard)")
        self.assertNotIn("--retry-all-errors", src, "curl already retries 408, 429 and 5xx; --retry-all-errors would also retry a 404 for two minutes")
        self.assertIn('cat "$1" >> "$2"', src)
        self.assertLess(src.index('-o "$2" "$1"'), src.index('cat "$1" >> "$2"'))

    @unittest.skipUnless(shutil.which("node") and shutil.which("tar") and shutil.which("zstd"), "needs node, tar and zstd")
    def test_the_real_script_with_a_fake_curl(self):
        # a two-part archive; curl is a recorder that honours -o. A failing second part must leave nothing of it in the archive and fail the script; a good run unpacks the files.
        import hashlib
        import subprocess

        tmp = Path(tempfile.mkdtemp())
        exports = tmp / "exports" / "k"
        exports.mkdir(parents=True)
        stage = tmp / "stage"
        stage.mkdir()
        (stage / "Lib.A.ndjson").write_text("a\n" * 2000)
        (stage / "Lib.A.names.json").write_text("[]")
        archive = tmp / "k.tar.zst"
        subprocess.run(["tar", "--zstd", "-cf", str(archive), "-C", str(stage), "."], check=True)
        blob = archive.read_bytes()
        half = len(blob) // 2
        (tmp / "p1").write_bytes(blob[:half])
        (tmp / "p2").write_bytes(blob[half:])
        rec = {"archive": {"sha256": hashlib.sha256(blob).hexdigest(), "asset": "k.tar.zst", "bytes": len(blob), "files": 2, "url": "http://x/whole",
                           "parts": [{"url": "http://x/p1"}, {"url": "http://x/p2"}]}}
        (exports / "setup.ci.json").write_text(json.dumps(rec))
        (tmp / "mods.txt").write_text("Lib.A\n")
        bindir = tmp / "bin"
        bindir.mkdir()
        curl = bindir / "curl"
        curl.write_text('#!/bin/sh\nurl=; out=\nwhile [ $# -gt 0 ]; do case "$1" in -o) out=$2; shift;; http*) url=$1;; esac; shift; done\n'
                        'echo "$url" >> "$CURL_LOG"\n'
                        'case "$url" in\n  */p1) cp "$P1" "$out";;\n  */p2) if [ -n "$FAIL_P2" ]; then head -c 1000 "$P2" > "$out"; exit 22; fi; cp "$P2" "$out";;\nesac\n')
        curl.chmod(0o755)
        env = {**os.environ, "PATH": f"{bindir}:{os.environ['PATH']}", "GATE2_EXPORTS_DIR": str(tmp / "exports"), "CURL_LOG": str(tmp / "log"), "P1": str(tmp / "p1"), "P2": str(tmp / "p2")}
        script = str(ROOT / "scripts" / "fetch-exports.mjs")
        bad = subprocess.run(["node", script, "k", "--modules", str(tmp / "mods.txt")], env={**env, "FAIL_P2": "1"}, capture_output=True, text=True)
        self.assertNotEqual(bad.returncode, 0, "a part that cannot be downloaded must fail the script")
        self.assertFalse((exports / "Lib.A.ndjson").exists())
        good = subprocess.run(["node", script, "k", "--modules", str(tmp / "mods.txt")], env=env, capture_output=True, text=True)
        self.assertEqual(good.returncode, 0, good.stdout + good.stderr)
        self.assertEqual((exports / "Lib.A.ndjson").read_text(), "a\n" * 2000)
        self.assertEqual(list((tmp / "log").read_text().split()).count("http://x/p1"), 2)


class PlanInputsRecord(unittest.TestCase):
    def test_defaults_leave_the_record_as_it_was_and_other_settings_change_it(self):
        import plan_inputs as pi
        base = {"MATHLIB": "v4.34.0-rc2", "TOOLCHAIN": "leanprover/lean4:v4.34.0-rc2", "IMPORTS": "faithful", "TENGOKU_REF": ""}
        old = json.dumps({k.lower(): v for k, v in base.items()}, indent=1, sort_keys=True)  # what the workflow wrote before swap_gb and build_timeout_min existed
        cases = 0
        for swap in ("0", "16", "48", "100"):
            for timeout in ("90", "120", "170"):
                for imports in ("full", "faithful"):
                    env = {**base, "IMPORTS": imports, "SWAP_GB": swap, "BUILD_TIMEOUT_MIN": timeout}
                    rec = pi.record(env)
                    cases += 1
                    if swap == "0" and timeout == "90":
                        self.assertEqual(pi.dump(rec), json.dumps({k.lower(): v for k, v in {**base, "IMPORTS": imports}.items()}, indent=1, sort_keys=True))
                    else:
                        self.assertNotEqual(pi.dump(rec), pi.dump(pi.record({**base, "IMPORTS": imports})), "other settings must not look like the defaults")
        self.assertEqual(pi.dump(pi.record(base)), old, "an environment with neither setting (an older caller) gives the old record")
        self.assertEqual(cases, 24)
        # two runs that differ only in swap or only in timeout never compare equal
        a, b, c = (pi.dump(pi.record({**base, "SWAP_GB": s, "BUILD_TIMEOUT_MIN": t})) for s, t in (("48", "90"), ("0", "170"), ("48", "170")))
        self.assertEqual(len({a, b, c, pi.dump(pi.record(base))}), 4)


class OnlyListParsing(unittest.TestCase):
    def test_a_list_with_no_name_is_an_error_not_everything(self):
        self.assertEqual(ps.parse_only(""), set())
        self.assertEqual(ps.parse_only("A,B,,C "), {"A", "B", "C"})
        self.assertEqual(ps.parse_only(" A , B"), {"A", "B"})
        for raw in (",", ",,", " ", ", ,", " , "):
            if raw.strip():
                with self.assertRaises(ValueError, msg=repr(raw)):
                    ps.parse_only(raw)
            else:
                self.assertEqual(ps.parse_only(raw), set())


class GuardEnforcesSwapAwareLimit(unittest.TestCase):
    def test_count_swap_decides_whether_the_process_is_killed(self):
        # a long-lived child; the footprint is read through rss_kb, which is replaced by one that returns what a process with 100 MB in RAM and 9.9 GB in swap would show: killed only when swap counts
        real = gg.rss_kb
        seen = []

        def fake(pid, count_swap=False):
            seen.append(count_swap)
            return 10_000_000 if count_swap else 100_000

        gg.rss_kb = fake
        try:
            log = Path(tempfile.mkdtemp()) / "g.log"
            plain = gg.run_guarded([sys.executable, "-c", "import time; time.sleep(1.5)"], ".", dict(os.environ), log, 20, 5_000_000, poll_s=0.05, count_swap=False)
            counted = gg.run_guarded([sys.executable, "-c", "import time; time.sleep(30)"], ".", dict(os.environ), log, 20, 5_000_000, poll_s=0.05, count_swap=True)
        finally:
            gg.rss_kb = real
        self.assertEqual(plain.kind, "ok", "100 MB resident is under the 5 GB limit when swap is not counted")
        self.assertEqual(counted.kind, "memory", "9.9 GB in swap is over the limit when swap is counted: the child must be killed")
        self.assertLess(counted.seconds, 10)
        self.assertEqual(set(seen), {False, True})


if __name__ == "__main__":
    unittest.main()
