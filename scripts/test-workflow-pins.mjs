// node scripts/test-workflow-pins.mjs — nothing the workflows install or run on moves under them (exits 1 on a failure). Static text; no network.
//   - the real workflows have no unpinned install, no moving tag, no script piped into a shell from a branch, no unpinned action, and the heavy ones no -latest runner;
//   - the scanner (scripts/check-workflow-pins.mjs) finds EVERY injected violation on random workflow texts and flags no clean line; and each mutant of it (one rule left out) is noticed;
//   - what this change pinned stays pinned: the Claude CLI of translate.yml is an exact version, the elan installer a commit.
import { readFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { HEAVY, RULES, checkDir, findUnpinned } from "./check-workflow-pins.mjs"

const wf = join(dirname(fileURLToPath(import.meta.url)), "..", ".github", "workflows")
let bad = 0
const check = (name, ok, got) => {
  if (!ok) { bad++; console.log("FAIL", name, got === undefined ? "" : JSON.stringify(got)) } else console.log("ok", name)
}

const real = checkDir(wf)
check("the real workflows: nothing unpinned", real.length === 0, real.slice(0, 5))
const translate = readFileSync(join(wf, "translate.yml"), "utf8")
check("the Claude CLI that translates is installed at an exact version", /npm install -g -q @anthropic-ai\/claude-code@\d+\.\d+\.\d+ && claude --version/.test(translate), translate.match(/.*claude-code.*/)?.[0])
const elans = [...new Set(elanFiles().flatMap((t) => [...t.matchAll(/raw\.githubusercontent\.com\/leanprover\/elan\/([^/]+)\/elan-init\.sh/g)].map((m) => m[1])))]
check("every elan installer is fetched at one and the same full commit", elans.length === 1 && /^[0-9a-f]{40}$/.test(elans[0]), elans)
function elanFiles() {
  return ["setup-sharded", "setup-libraries", "translate", "bump-library", "bump-shard", "trial-library-build", "generator-trial", "tolerant-smoke"].map((f) => readFileSync(join(wf, `${f}.yml`), "utf8"))
}
const heavy = ["setup-auto", "setup-libraries", "setup-sharded", "setup-tests", "bump-all", "bump-library", "bump-shard", "bump-sharded", "bump-tests", "translate", "translate-all"]
check("every heavy workflow (setup-*, bump-*, translate*) runs on ubuntu-26.04, the image the runs of 2026-10-25..28 were on", heavy.every((f) => { const t = readFileSync(join(wf, `${f}.yml`), "utf8"); const r = [...t.matchAll(/^\s*runs-on:\s*(.+)$/gm)].map((m) => m[1].trim()); return r.length > 0 && r.every((x) => x === "ubuntu-26.04") }), heavy)
check("the heavy pattern matches exactly those files", heavy.every((f) => HEAVY.test(f + ".yml")) && !HEAVY.test("lint-drift.yml") && !HEAVY.test("memory-intake.yml"), null)

// ---- the scanner against injected violations ----
let seed = 5
const rnd = (n) => {
  seed = (seed + 0x6d2b79f5) | 0
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed)
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
  return ((t ^ (t >>> 14)) >>> 0) % n
}
const pick = (xs) => xs[rnd(xs.length)]
const SHA = "0123456789abcdef0123456789abcdef01234567"
const good = [
  "      - uses: actions/checkout@" + SHA + " # v4",
  "      - uses: ./.github/workflows/bump-shard.yml",
  "        run: npm install -g -q @anthropic-ai/claude-code@2.1.312 && claude --version",
  "        run: npm install -g typescript@5.4.2 eslint@9.0.0-beta.1",
  "          sudo /opt/svc/bin/pip install -q \"mcp==1.30.0\" \"uvicorn==0.52.4\"",
  "          python3 -m pip install --quiet requests==2.32.3",
  "          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/" + SHA + "/elan-init.sh | sh -s -- -y --default-toolchain none",
  "          curl -sSfL https://example.org/data.json -o data.json",
  "    runs-on: ubuntu-26.04",
  "          npm test",
  "          # npm install -g left-pad@latest   (a comment says what not to do)",
  "          echo done # runs-on: ubuntu-latest",
]
const violations = [
  "      - uses: actions/checkout@v4",
  "      - uses: actions/setup-node@main",
  "        run: npm install -g @anthropic-ai/claude-code",
  "        run: npm install -g -q @anthropic-ai/claude-code && claude --version",
  "        run: npm install -g typescript@5.4.2 eslint",
  "        run: npm install --global left-pad@^1.0.0",
  "        run: npm i -g left-pad@1.x",
  "          sudo pip install mcp",
  "          pip3 install -q \"mcp>=1.0\"",
  "          python -m pip install requests",
  "          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y",
  "          curl -fsSL https://example.org/install.sh | bash",
  "          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/0e36a07/elan-init.sh | sh",
  "        run: npm install -g foo@latest",
  "        run: npx foo@next",
  "    runs-on: ubuntu-latest",
]
const wrap = (lines) => "name: t\njobs:\n  j:\n    steps:\n" + lines.join("\n") + "\n"
const run = (skip) => {
  seed = 5
  let exact = true
  for (let i = 0; i < 300; i++) {
    const lines = [], injected = new Set()
    for (let k = 0, n = 2 + rnd(10); k < n; k++) {
      if (rnd(3) === 0) { const v = pick(violations); lines.push(v); injected.add(lines.length) } else lines.push(pick(good))
    }
    // the runner rule is for the heavy workflows: the random texts are scanned as one
    const found = new Set(findUnpinned(wrap(lines), "setup-x.yml", skip).map((v) => v.line - 4))
    for (const n of injected) exact &&= found.has(n)
    for (const n of found) exact &&= injected.has(n)
  }
  return exact
}
check("on 300 random workflow texts the scanner flags exactly the injected violations and no clean line", run([]), null)
check("a -latest runner is a violation in a heavy workflow and not in a light one", findUnpinned("    runs-on: ubuntu-latest\n", "setup-sharded.yml").length === 1 && findUnpinned("    runs-on: ubuntu-latest\n", "bump-tests.yml").length === 1 && findUnpinned("    runs-on: ubuntu-latest\n", "translate-all.yml").length === 1 && findUnpinned("    runs-on: ubuntu-latest\n", "lint-drift.yml").length === 0, null)
check("the scanner says what is wrong and where", (() => { const v = findUnpinned("a\nb\n        run: npm install -g foo\n", "w.yml")[0]; return v.file === "w.yml" && v.line === 3 && /not an exact version/.test(v.why) })(), null)

// ---- the old workflows (what this change replaced) would have been caught ----
const before = [
  ["translate.yml", "        run: npm install -g -q @anthropic-ai/claude-code && claude --version"],
  ["setup-sharded.yml", "          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none"],
  ["setup-libraries.yml", "    runs-on: ubuntu-latest"],
  ["bump-sharded.yml", "    runs-on: ubuntu-latest"],
]
check("the lines this change replaced are each a violation", before.every(([f, l]) => findUnpinned(l + "\n", f).length === 1), null)

// ---- mutants: leave one rule out of the scanner; the check on the random texts must fail, so each rule is needed ----
check("the rules the mutants leave out are all of them", RULES.length === 6, RULES)
for (const rule of RULES) check(`mutant: a scanner without the ${rule} rule is noticed`, run([rule]) === false, rule)
process.exit(bad ? 1 : 0)
