// node scripts/test-lint-drift.mjs — the check that the pinned content lint (scripts/bump/lint/) is still tengoku's (exits 1 on a failure). No network.
//   - compare() on in-memory file maps: identical maps agree; ANY change of ANY of the four files, however small (a byte, a final newline, line endings, a re-indented JSON), is drift and names exactly that file;
//     a file missing on either side is drift; the summary names the options / keywords / definitions added and removed, exactly;
//   - mutants of compare() (one file ignored, text trimmed before comparing, JSON compared by value, only the lengths compared) are caught by the same checks;
//   - an offline fixture (scripts/fixtures/lint-drift: 8 options missing, one definition, a Lean version) through the real command line, and the real pinned files against a copy of themselves;
//   - the reading of tengoku (gh api with a token, raw.githubusercontent.com without; both at the one commit the ref pointed at; a failed gh falls back; a bad ref is refused) with stubs;
//   - the workflow: daily and on demand, read-only check, ONE issue by title written by a job that holds issues: write and nothing else, actions pinned to commits.
import { spawnSync } from "node:child_process"
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { FILES, REPO, compare, fetchUpstream, lineDiff, render } from "./check-lint-drift.mjs"

const root = join(dirname(fileURLToPath(import.meta.url)), "..")
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) { bad++; console.log("FAIL", name, detail === undefined ? "" : JSON.stringify(detail)) } else console.log("ok", name)
}

// deterministic random numbers (mulberry32)
let seed = 20261028
const rnd = (n) => {
  seed = (seed + 0x6d2b79f5) | 0
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed)
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
  return ((t ^ (t >>> 14)) >>> 0) % n
}
const pick = (xs) => xs[rnd(xs.length)]
const words = ["alpha", "beta", "gamma", "linter.all", "maxRecDepth", "def", "theorem", "MODIFIERS", "private", "meta", "x", "pp.all", "autoImplicit"]
const sentence = () => Array.from({ length: 1 + rnd(8) }, () => pick(words)).join(" ")
const pyText = () => Array.from({ length: 5 + rnd(30) }, (_, i) => (rnd(5) === 0 ? `def f${i}_${rnd(99)}(x):\n    return ${rnd(10)}` : rnd(6) === 0 ? `CONST_${i} = ${rnd(10)}` : `# ${sentence()}`)).join("\n") + "\n"
const optionsText = (opts) => JSON.stringify({ $comment: sentence(), allowed: opts }, null, 1) + "\n"
const keywordsText = (cmds, lean = "leanprover/lean4:v4.34.0-rc2") => JSON.stringify({ about: sentence(), lean, commands: cmds }, null, 1) + "\n"
const universe = (p, n) => Array.from({ length: n }, (_, i) => `${p}${i}`)
const subset = (xs) => xs.filter(() => rnd(2) === 0)
const randomMaps = () => {
  const opts = subset(universe("opt.", 30)), cmds = subset(universe("#cmd", 30))
  const m = { "allowlist.py": pyText(), "allowed-options.json": optionsText(opts), "lean_lex.py": pyText(), "command-keywords.json": keywordsText(cmds) }
  return { pinned: { ...m }, upstream: { ...m } }
}
// every way a file can differ by a little
const edits = [
  (t) => t + "x",
  (t) => t.slice(0, -1), // the final newline
  (t) => t + "\n",
  (t) => t.replace(/\n/, "\r\n"),
  (t) => t.replace(/\n/, " \n"),
  (t) => { const i = rnd(t.length); return t.slice(0, i) + (t[i] === "a" ? "b" : "a") + t.slice(i + 1) },
  (t) => t.replace(/^/, " "),
]
const FILE_NAMES = FILES.map((f) => f.name)

// ---- the properties, as a suite that can be run against any compare() ----
function suite(cmp) {
  const failures = []
  const note = (what) => failures.push(what)
  for (let i = 0; i < 150; i++) {
    const { pinned, upstream } = randomMaps()
    if (cmp(pinned, upstream).drift) note("identical maps are drift")
    if (!cmp(pinned, upstream).files.every((f) => f.status === "same")) note("identical maps have a file that is not same")
    const name = pick(FILE_NAMES)
    const changed = { ...upstream, [name]: pick(edits)(upstream[name]) }
    if (changed[name] === upstream[name]) continue
    const r = cmp(pinned, changed)
    if (!r.drift) note(`a change of ${name} is not drift`)
    const different = r.files.filter((f) => f.status !== "same").map((f) => f.name)
    if (different.join() !== name) note(`a change of ${name} names ${different.join() || "nothing"}`)
  }
  // a re-indented JSON means the same and is not the same bytes
  const { pinned, upstream } = randomMaps()
  const compact = { ...upstream, "allowed-options.json": JSON.stringify(JSON.parse(upstream["allowed-options.json"])) }
  if (!cmp(pinned, compact).drift) note("re-indented JSON is not drift")
  // a file that is gone on either side
  for (const name of FILE_NAMES) {
    const { pinned: p, upstream: u } = randomMaps()
    const { [name]: _gone, ...rest } = u
    if (!cmp(p, rest).drift) note(`${name} missing upstream is not drift`)
    const { [name]: _g2, ...rest2 } = p
    if (!cmp(rest2, u).drift) note(`${name} missing in the pinned copy is not drift`)
  }
  // every file, alone, is compared
  for (const name of FILE_NAMES) {
    const { pinned: p, upstream: u } = randomMaps()
    u[name] = u[name] + "// changed\n"
    if (!cmp(p, u).drift) note(`${name} alone changed is not drift`)
  }
  return failures
}

const baseline = suite(compare) // once: the failures printed are those of the run that decided
check("identical maps agree; any small change of any one file is drift and names exactly that file; missing files are drift; a re-indented JSON is drift", baseline.length === 0, baseline.slice(0, 3))

// ---- mutants: break compare() the way a shortcut would; the suite must notice ----
const mutants = {
  ...Object.fromEntries(FILE_NAMES.map((n) => [`ignoring ${n}`, (p, u) => compare({ ...p, [n]: "" }, { ...u, [n]: "" })])),
  "trimming the text before comparing": (p, u) => compare(Object.fromEntries(Object.entries(p).map(([k, v]) => [k, v.trim()])), Object.fromEntries(Object.entries(u).map(([k, v]) => [k, v.trim()]))),
  "normalising line endings before comparing": (p, u) => compare(Object.fromEntries(Object.entries(p).map(([k, v]) => [k, v.replace(/\r\n/g, "\n")])), Object.fromEntries(Object.entries(u).map(([k, v]) => [k, v.replace(/\r\n/g, "\n")]))),
  "comparing JSON by value": (p, u) => {
    const norm = (m) => Object.fromEntries(Object.entries(m).map(([k, v]) => [k, k.endsWith(".json") ? (() => { try { return JSON.stringify(JSON.parse(v)) } catch { return v } })() : v]))
    return compare(norm(p), norm(u))
  },
  "comparing only the lengths": (p, u) => compare(Object.fromEntries(Object.entries(p).map(([k, v]) => [k, "x".repeat(v.length)])), Object.fromEntries(Object.entries(u).map(([k, v]) => [k, "x".repeat(v.length)]))),
  "a missing file counts as same": (p, u) => {
    const r = compare(p, u)
    const files = r.files.map((f) => (f.status.startsWith("missing") ? { ...f, status: "same" } : f))
    return { drift: files.some((f) => f.status !== "same"), files }
  },
  "a drift reported but under the wrong file": (p, u) => {
    const r = compare(p, u)
    const files = r.files.map((f, i) => ({ ...f, name: r.files[(i + 1) % r.files.length].name }))
    return { ...r, files }
  },
}
for (const [name, cmp] of Object.entries(mutants)) { const failed = suite(cmp); check(`mutant: ${name} is noticed`, failed.length > 0, failed.length) }

// ---- a file that is JSON but not the shape the comparison reads is drift with a detail, never an exception (the workflow must still write the summary and open the issue) ----
{
  const odd = ["null", "5", "true", "[]", '"x"', '{"allowed": null}', '{"allowed": 5}', '{"commands": "x"}', '{"commands": {"a": 1}}', "{}", "{not json"]
  let neverThrows = true, drifts = true
  for (const file of FILES.filter((f) => f.kind === "options" || f.kind === "keywords")) {
    const good = file.kind === "options" ? optionsText(["a", "b"]) : keywordsText(["def"])
    for (const bad of odd) for (const [p, u] of [[good, bad], [bad, good]]) {
      try {
        const r = compare({ [file.name]: p }, { [file.name]: u }, [file])
        drifts &&= r.drift && r.files[0].details.length > 0
        render(r)
      } catch { neverThrows = false }
    }
  }
  check("JSON that is null, a number, a list, a string, or has the list field of the wrong type never throws, in either file or direction: it is drift with a detail", neverThrows && drifts, { neverThrows, drifts })
  const r = compare({ "allowed-options.json": optionsText(["a"]) }, { "allowed-options.json": "null" }, FILES.filter((f) => f.name === "allowed-options.json"))
  check("the detail says what is wrong and where the file is", /tengoku is JSON but not an object \(null\)/.test(r.files[0].details[0]), r.files[0].details)
}

// ---- the summary says exactly what differs ----
const listed = (details, label) => {
  const line = details.find((d) => d.startsWith(label))
  return line ? [...line.matchAll(/`([^`]+)`/g)].map((m) => m[1]).sort() : []
}
let exact = true
for (let i = 0; i < 100; i++) {
  const u = universe("opt.", 25)
  const a = subset(u), b = subset(u), ka = subset(universe("#cmd", 25)), kb = subset(universe("#cmd", 25))
  const r = compare({ "allowed-options.json": optionsText(a), "command-keywords.json": keywordsText(ka) }, { "allowed-options.json": optionsText(b), "command-keywords.json": keywordsText(kb) }, FILES.filter((f) => f.kind !== "py"))
  const o = r.files.find((f) => f.name === "allowed-options.json").details, k = r.files.find((f) => f.name === "command-keywords.json").details
  exact &&= JSON.stringify(listed(o, "options tengoku allows")) === JSON.stringify(b.filter((x) => !a.includes(x)).sort())
  exact &&= JSON.stringify(listed(o, "options the pinned copy allows")) === JSON.stringify(a.filter((x) => !b.includes(x)).sort())
  exact &&= JSON.stringify(listed(k, "command keywords tengoku has")) === JSON.stringify(kb.filter((x) => !ka.includes(x)).sort())
  exact &&= JSON.stringify(listed(k, "command keywords the pinned copy has")) === JSON.stringify(ka.filter((x) => !kb.includes(x)).sort())
}
check("the options and command keywords added and removed are listed exactly, on 100 random pairs", exact)
{
  const r = compare({ "allowlist.py": "A = 1\ndef f():\n    pass\nclass K:\n    pass\n" }, { "allowlist.py": "A = 1\ndef g():\n    pass\nB_C = 2\n" }, FILES.filter((f) => f.name === "allowlist.py"))
  const d = r.files[0].details
  check("definitions added and removed are listed (def, class, CONSTANT)", listed(d, "definitions in tengoku").join() === "B_C,g" && listed(d, "definitions in the pinned copy").join() === "K,f", d)
  check("a difference of whitespace at the ends of lines alone is named as such", compare({ "lean_lex.py": "a\nb\n" }, { "lean_lex.py": "a  \r\nb" }, FILES.filter((f) => f.name === "lean_lex.py")).files[0].details.some((x) => /only in line endings/.test(x)), null)
}
{
  let ok = true
  for (let i = 0; i < 100; i++) {
    const a = Array.from({ length: rnd(20) }, () => `l${rnd(15)}`), b = Array.from({ length: rnd(20) }, () => `l${rnd(15)}`)
    const { removed, added } = lineDiff(a.join("\n"), b.join("\n"))
    // what is left after taking the removed lines out of a and the added out of b is the common subsequence: the same on both sides
    const common = (xs, gone) => xs.filter((_, i) => !gone.some((g) => g.line === i + 1))
    ok &&= common(a.join("\n").split("\n"), removed).join() === common(b.join("\n").split("\n"), added).join()
  }
  check("lineDiff leaves the same lines on both sides (a common subsequence), on 100 random pairs", ok)
}
{
  const big = "x\n".repeat(200000)
  const r = compare({ "lean_lex.py": big }, { "lean_lex.py": big + "y\n" }, FILES.filter((f) => f.name === "lean_lex.py"))
  check("a huge pair is still compared and summarised (set fallback, no memory blow-up)", r.drift && render(r).length < 70000, null)
  const long = compare({ "lean_lex.py": Array.from({ length: 4000 }, (_, i) => `line ${i} ${"z".repeat(100)}`).join("\n") }, { "lean_lex.py": Array.from({ length: 4000 }, (_, i) => `other ${i} ${"z".repeat(100)}`).join("\n") }, FILES.filter((f) => f.name === "lean_lex.py"))
  check("a summary never passes what an issue holds", render(long).length <= 61000, render(long).length)
}

// ---- the offline fixture, through the real command line ----
const cli = (args, env = {}) => spawnSync("node", [join(root, "scripts", "check-lint-drift.mjs"), ...args], { encoding: "utf8", env: { PATH: process.env.PATH, HOME: process.env.HOME, ...env } })
const fx = join(root, "scripts", "fixtures", "lint-drift")
const tmp = mkdtempSync(join(tmpdir(), "lint-drift-"))
const summary = join(tmp, "summary.md")
let r = cli(["--pinned-dir", join(fx, "pinned"), "--upstream-dir", join(fx, "upstream"), "--summary-file", summary])
check("fixture: exits 1 on drift, and the file written is the text printed", r.status === 1 && existsSync(summary) && r.stdout.includes(readFileSync(summary, "utf8").trim()), [r.status, r.stderr.slice(0, 200)])
check("fixture: names the three files that differ and not the identical one", /### allowlist\.py — differs/.test(r.stdout) && /### allowed-options\.json — differs/.test(r.stdout) && /### command-keywords\.json — differs/.test(r.stdout) && /### lean_lex\.py — identical/.test(r.stdout), r.stdout.slice(0, 300))
check("fixture: the 8 options the pinned copy lacks are listed, sorted", /options tengoku allows that the pinned copy lacks \(8\): `autoImplicit`, `backward\.privateInPublic`, `backward\.privateInPublic\.warn`, `exponentiation\.threshold`, `linter\.style\.longLine`, `linter\.style\.setOption`, `pp\.all`, `relaxedAutoImplicit`\n/.test(r.stdout), r.stdout)
check("fixture: the definition, the keyword and the Lean version are listed", /definitions in tengoku that the pinned copy lacks: `_command_lead`/.test(r.stdout) && /command keywords tengoku has that the pinned copy lacks \(1\): `meta`/.test(r.stdout) && /Lean version differs: pinned leanprover\/lean4:v4\.34\.0-rc2, tengoku leanprover\/lean4:v4\.35\.0/.test(r.stdout), "")
check("fixture: prints an ::error:: line with the files, for the log", /::error::.*allowlist\.py, allowed-options\.json, command-keywords\.json/.test(r.stderr), r.stderr)

// the real pinned files against a copy of themselves laid out like tengoku: identical; then one byte, one file missing, no folder
const realPinned = join(root, "scripts", "bump", "lint")
const layout = join(tmp, "tengoku")
for (const f of FILES) {
  mkdirSync(join(layout, dirname(f.upstream)), { recursive: true })
  cpSync(join(realPinned, f.name), join(layout, f.upstream))
}
r = cli(["--pinned-dir", realPinned, "--upstream-dir", layout])
check("the real pinned files against a copy of themselves: exit 0, 'identical'", r.status === 0 && /identical to `competemath\/tengoku`/.test(r.stdout), [r.status, r.stderr.slice(0, 200)])
for (const f of FILES) {
  const file = join(layout, f.upstream)
  const was = readFileSync(file)
  writeFileSync(file, Buffer.concat([was, Buffer.from("\n")]))
  r = cli(["--pinned-dir", realPinned, "--upstream-dir", layout])
  check(`one extra newline at the end of ${f.name} is drift (exit 1), naming ${f.name} only`, r.status === 1 && (r.stdout.match(/ — differs/g) || []).length === 1 && r.stdout.includes(`### ${f.name} — differs`), [r.status, r.stdout.slice(0, 200)])
  rmSync(file)
  r = cli(["--pinned-dir", realPinned, "--upstream-dir", layout])
  check(`${f.upstream} missing upstream is drift (exit 1)`, r.status === 1 && r.stdout.includes(`tengoku has no ${f.upstream}`), [r.status])
  writeFileSync(file, was)
}
r = cli(["--pinned-dir", realPinned, "--upstream-dir", join(tmp, "nowhere")])
check("an upstream folder that does not exist is exit 2 (nothing is known), not drift", r.status === 2 && /could not read/.test(r.stderr), [r.status, r.stderr])
r = cli(["--bogus"])
check("an unknown argument is exit 2", r.status === 2, r.status)
r = cli(["--ref", "../etc", "--source", "raw"])
check("a ref that is not a name is refused before anything is read (exit 2)", r.status === 2 && /ref is a branch/.test(r.stderr), r.stderr)

// ---- reading tengoku, with stubs (no network) ----
const SHA = "0123456789abcdef0123456789abcdef01234567"
const body = (name) => `content of ${name}\n`
function stubs({ ghFails = false, shaFails = false, status = 200, missing = [], ghStatus = 404, badToken = false } = {}) {
  const calls = { gh: [], fetch: [] }
  const run = (cmd, args) => {
    calls.gh.push([cmd, ...args])
    if (ghFails) throw new Error("gh: not logged in")
    if (args[1].includes("/commits/")) return Buffer.from(SHA + "\n")
    const path = args[1].replace(/^repos\/[^/]+\/[^/]+\/contents\//, "").replace(/\?ref=.*$/, "")
    if (missing.includes(path)) throw Object.assign(new Error("Command failed: gh api"), { stderr: Buffer.from(`gh: ${ghStatus === 404 ? "Not Found" : "Server Error"} (HTTP ${ghStatus})\n`) })
    return Buffer.from(body(path))
  }
  const fetchImpl = async (url, opts = {}) => {
    calls.fetch.push({ url, headers: opts.headers })
    if (url.startsWith("https://api.github.com/")) {
      if (badToken && opts.headers?.Authorization) return { ok: false, status: 401, text: async () => "" }
      return { ok: !shaFails, status: shaFails ? 403 : 200, text: async () => SHA }
    }
    const path = url.replace(/^https:\/\/raw\.githubusercontent\.com\/[^/]+\/[^/]+\/[^/]+\//, "")
    if (missing.includes(path)) return { ok: false, status: ghStatus, arrayBuffer: async () => Buffer.alloc(0) }
    return { ok: status === 200, status, arrayBuffer: async () => Buffer.from(body(path)) }
  }
  return { calls, run, fetchImpl }
}
{
  const s = stubs()
  const got = await fetchUpstream({ env: { GH_TOKEN: "t" }, run: s.run, fetchImpl: s.fetchImpl })
  check("with a token the four files come through gh api, all at the commit main pointed at", got.via === "gh api" && got.commit === SHA && s.calls.fetch.length === 0 && s.calls.gh.filter((c) => c[2].includes("/contents/")).length === 4 && s.calls.gh.filter((c) => c[2].includes("/contents/")).every((c) => c[2].endsWith(`?ref=${SHA}`)), s.calls.gh.map((c) => c[2]))
  check("the files are read from tengoku's paths and returned under the pinned names, byte for byte", FILES.every((f) => got.files[f.name].equals(Buffer.from(body(f.upstream)))), Object.keys(got.files))
  check("gh api asks for the raw bytes of the file", s.calls.gh.filter((c) => c[2].includes("/contents/")).every((c) => c.includes("Accept: application/vnd.github.raw+json")), null)
}
{
  const s = stubs()
  const got = await fetchUpstream({ env: {}, run: s.run, fetchImpl: s.fetchImpl })
  const raw = s.calls.fetch.map((c) => c.url).filter((u) => u.startsWith("https://raw.githubusercontent.com/"))
  check("without a token they come from raw.githubusercontent.com, at the commit, never through gh", got.via === "raw.githubusercontent.com" && s.calls.gh.length === 0 && raw.length === 4 && raw.every((u) => u.includes(`/${REPO}/${SHA}/`)), s.calls.fetch)
}
{
  const s = stubs({ shaFails: true })
  let msg = ""
  try { await fetchUpstream({ env: {}, ref: "main", run: s.run, fetchImpl: s.fetchImpl }) } catch (e) { msg = e.message }
  check("when the commit cannot be resolved nothing is read at the name of the ref: an error, and no raw request is made", /no commit for main could be resolved \(HTTP 403\)/.test(msg) && s.calls.fetch.every((c) => c.url.startsWith("https://api.github.com/")), [msg, s.calls.fetch.length])
  const t = stubs()
  await fetchUpstream({ env: { GH_TOKEN: "tok" }, source: "raw", run: t.run, fetchImpl: t.fetchImpl })
  const withToken = t.calls.fetch.find((c) => c.url.startsWith("https://api.github.com/")).headers
  const u = stubs()
  await fetchUpstream({ env: {}, source: "raw", run: u.run, fetchImpl: u.fetchImpl })
  check("raw mode sends the token to the API lookup of the commit when there is one (rate limits), never to raw.githubusercontent.com", withToken.Authorization === "Bearer tok" && !("Authorization" in u.calls.fetch[0].headers) && t.calls.fetch.filter((c) => c.url.startsWith("https://raw.")).every((c) => !c.headers), null)
}
{
  // gh failed because the token is bad: the raw fallback must not die on the same token at the commit lookup (401); it asks again without it
  const s = stubs({ ghFails: true, badToken: true })
  const got = await fetchUpstream({ env: { GH_TOKEN: "expired" }, run: s.run, fetchImpl: s.fetchImpl, warn: () => {} })
  const lookups = s.calls.fetch.filter((c) => c.url.startsWith("https://api.github.com/"))
  check("auto mode: a token refused with 401 at the commit lookup is dropped and the lookup repeated as anyone, so the public raw fallback still works", got.via === "raw.githubusercontent.com" && got.commit === SHA && lookups.length === 2 && lookups[0].headers.Authorization === "Bearer expired" && !("Authorization" in lookups[1].headers), lookups.map((l) => l.headers))
  const t = stubs({ shaFails: true })
  let msg = ""
  try { await fetchUpstream({ env: { GH_TOKEN: "tok" }, source: "raw", run: t.run, fetchImpl: t.fetchImpl }) } catch (e) { msg = e.message }
  check("only a 401 repeats the lookup (a 403 with a token is not retried), and the error says why", /HTTP 403/.test(msg) && t.calls.fetch.filter((c) => c.url.startsWith("https://api.github.com/")).length === 1, msg)
}
{
  // a file tengoku deleted: at the resolved commit a 404 is drift (a missing upstream entry), through either reader; any other failure stays a read error
  for (const [label, opts] of [["gh api", { env: { GH_TOKEN: "t" } }], ["raw", { env: {}, source: "raw" }]]) {
    const gone = FILES[1].upstream
    const s = stubs({ missing: [gone] })
    const got = await fetchUpstream({ ...opts, run: s.run, fetchImpl: s.fetchImpl })
    const pinned = Object.fromEntries(FILES.map((f) => [f.name, Buffer.from(body(f.upstream))]))
    const r = compare(pinned, got.files)
    check(`${label}: a file tengoku deleted (404 at the resolved commit) is drift naming it, not a read error`, got.files[FILES[1].name] === undefined && r.drift && r.files.filter((f) => f.status !== "same").map((f) => f.name).join() === FILES[1].name && r.files[1].status === "missing-upstream", r.files.map((f) => f.status))
    const e = stubs({ missing: [gone], ghStatus: 500 })
    let threw = false
    try { await fetchUpstream({ ...opts, run: e.run, fetchImpl: e.fetchImpl, warn: () => {} }) } catch { threw = true }
    check(`${label}: a server error on the file is a read error (exit 2), not drift`, threw, null)
  }
}
{
  const s = stubs({ ghFails: true })
  const got = await fetchUpstream({ env: { GH_TOKEN: "t" }, run: s.run, fetchImpl: s.fetchImpl, warn: () => {} })
  check("a gh that fails (no gh, bad token) falls back to the raw files with a token in auto mode", got.via === "raw.githubusercontent.com" && Object.keys(got.files).length === 4, got.via)
  let threw = false
  try { await fetchUpstream({ env: { GH_TOKEN: "t" }, source: "gh", run: s.run, fetchImpl: s.fetchImpl }) } catch { threw = true }
  check("source gh does not fall back", threw, null)
}
{
  const s = stubs({ status: 500 })
  let msg = ""
  try { await fetchUpstream({ env: {}, run: s.run, fetchImpl: s.fetchImpl }) } catch (e) { msg = e.message }
  check("a file that cannot be read (HTTP 500) is an error naming it, not an empty file", /scripts\/ci\/allowlist\.py: HTTP 500/.test(msg), msg)
  const refused = []
  for (const ref of ["../x", "a b", "main;rm", "", "a..b", "x?y"]) { try { await fetchUpstream({ ref, env: {}, run: s.run, fetchImpl: s.fetchImpl }); refused.push(false) } catch { refused.push(true) } }
  check("a ref that is not a plain name is refused", refused.every(Boolean), refused)
}

// ---- the workflow ----
const wfText = readFileSync(join(root, ".github", "workflows", "lint-drift.yml"), "utf8")
const jobs = {}
{
  let name = null
  for (const line of wfText.slice(wfText.indexOf("\njobs:\n") + 6).split("\n")) {
    const m = line.match(/^  ([a-z][a-z-]*):\s*$/)
    if (m) { name = m[1]; jobs[name] = []; continue }
    if (name) jobs[name].push(line)
  }
}
const job = (n) => (jobs[n] || []).join("\n")
const perm = (b) => (b.match(/^    permissions:\s*(.*)$/m) || [])[1] ?? null
const head = wfText.slice(0, wfText.indexOf("\njobs:\n"))
check("the workflow runs daily and on demand, and holds no permission by default", /schedule:\n\s+- cron: "\d+ \d+ \* \* \*"/.test(head) && /workflow_dispatch:/.test(head) && /\npermissions: \{\}\n/.test(head), head.slice(-300))
check("the check job reads contents and nothing else; the report job writes issues and nothing else; no other job has a permission", perm(job("check")) === "{ contents: read }" && perm(job("report")) === "{ issues: write }" && Object.keys(jobs).join() === "check,report", [perm(job("check")), perm(job("report")), Object.keys(jobs)])
check("the report job checks nothing out and runs no node, and the check job never writes", !/actions\/checkout|setup-node|\bnode\b/.test(job("report").replace(/#.*$/gm, "")) && !/gh issue|issues:/.test(job("check")), "")
check("ONE issue by exact title: found by title, edited when open, created when not", /title="pinned content lint differs from tengoku main"/.test(job("report")) && /\.title == \$t/.test(job("report")) && /gh issue edit "\$number"/.test(job("report")) && /gh issue create[^\n]*--title "\$title"/.test(job("report")), "")
check("the report job runs only on drift, and drift is told apart from a lint that could not be read (exit 2 fails the check job)", /needs\.check\.outputs\.drift == 'true'/.test(job("report")) && /1\) echo "drift=true"/.test(job("check")) && /\*\) echo "::error::[^\n]*exit "\$rc"/.test(job("check")), "")
check("no ${{ }} expression sits inside a shell script (values reach it through env)", ![...wfText.matchAll(/run: \|\n((?: {10}.*\n?|\n)+)/g)].some((m) => /\$\{\{/.test(m[1])), "")
check("every action is pinned to a full commit", [...wfText.matchAll(/uses: ([^\s]+)/g)].every((m) => /@[0-9a-f]{40}$/.test(m[1])), [...wfText.matchAll(/uses: ([^\s]+)/g)].map((m) => m[1]))
check("the check job gives the token to the script, which uses gh api with it", /GH_TOKEN: "\$\{\{ github\.token \}\}"/.test(job("check")) && /node scripts\/check-lint-drift\.mjs --summary-file drift\.md/.test(job("check")), "")
const testsWf = readFileSync(join(root, ".github", "workflows", "lint-drift-tests.yml"), "utf8")
const section = (name) => { const m = testsWf.match(new RegExp(`\\n  ${name}:\\n(?:    .*\\n)*`)); return m ? m[0] : "" }
const wantedPaths = ["scripts/check-lint-drift.mjs", "scripts/test-lint-drift.mjs", "scripts/bump/lint/**", "scripts/fixtures/lint-drift/**", ".github/workflows/lint-drift*.yml", ".github/workflows/lint-drift*.yaml"]
const missingPaths = ["push", "pull_request"].flatMap((ev) => wantedPaths.filter((p) => !section(ev).includes(`"${p}"`)).map((p) => `${ev}: ${p}`))
check("these tests run in CI for each of the check, its test, the pinned copy, the fixture and both workflow names, on push AND on pull request (each path asserted in each event)", /node scripts\/test-lint-drift\.mjs/.test(testsWf) && section("push") !== "" && section("pull_request") !== "" && missingPaths.length === 0, missingPaths)

rmSync(tmp, { recursive: true, force: true })
process.exit(bad ? 1 : 0)
