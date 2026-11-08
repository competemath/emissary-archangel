// node scripts/test-attest-statements.mjs — the statement attestation (scripts/attest/): what it records, and that it cannot become a Tengoku record. No Lean, no network.
//   - the seeder turns FATE-X-shaped files into setup records (and refuses a file that does not hold exactly one theorem);
//   - the verdict reader, the entries and the attestation's own invariants (each broken one is caught);
//   - the driver, end to end with a stand-in for the Gate 2 daemon: passes, kernel refusals, a missing export, a declaration it cannot find;
//   - it refuses to write under any directory a record is banked from;
//   - the workflow holds no way to bank or publish, signs in a job that compiles nothing, and names the guards.
import assert from "node:assert/strict"
import { execFileSync, spawnSync } from "node:child_process"
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs"
import os from "node:os"
import { join } from "node:path"
import { ADMISSION_DIRS, EXPORT_MODES, SCHEMA, limitsFor, assertNotAdmissionPath, buildAttestation, checkAttestation, exportCandidates, problemEntry, readVerdict, sha256 } from "./attest/lib.mjs"

const ROOT = new URL("..", import.meta.url).pathname
const tmp = mkdtempSync(join(os.tmpdir(), "attest-test-"))
let n = 0
const ok = (msg) => console.log(`ok  ${msg}`)
const eq = (a, b, msg) => (assert.deepEqual(a, b, msg), n++)

// ---- seeder -----------------------------------------------------------------------------
const repo = join(tmp, "repo")
mkdirSync(join(repo, "FATEX"), { recursive: true })
const file = (i, body) => writeFileSync(join(repo, "FATEX", `${i}.lean`), body)
file(1, "import Mathlib\n\nnamespace Problem1\n\n/--\nProve the theorem lemma foo : False := by simp -- a doc comment that mentions theorem\n-/\ntheorem alpha {R : Type} [CommRing R] (x : R) :\n    x = x := by\n  sorry\n\nend Problem1\n")
file(2, "import Mathlib\n\nnamespace Problem2\n\ndef D : Nat := 3 -- theorem not here\n\n@[simp] lemma «beta_2» (n : Nat) : n + D = D + n := by\n  sorry\n\nend Problem2\n")
file(3, "import Mathlib\n\ntheorem a : True := by trivial\ntheorem b : True := by trivial\n")
const seed = (count) => spawnSync("python3", ["-I", join(ROOT, "scripts/attest/seed_tentative.py"), "--repo", repo, "--commit", "c0ffee", "--repo-url", "https://example.test/FATE-X", "--out", join(tmp, "seed.jsonl"), "--count", String(count)], { encoding: "utf8" })
let r = seed(2)
assert.equal(r.status, 0, r.stderr)
const rows = readFileSync(join(tmp, "seed.jsonl"), "utf8").trim().split("\n").map((l) => JSON.parse(l))
eq(rows.map((x) => x.name), ["alpha", "«beta_2»"], "names are the declared ones; a doc comment's `theorem` is not a declaration")
eq(rows[0].statement, "theorem alpha {R : Type} [CommRing R] (x : R) :\n    x = x", "the statement stops at `:=`")
assert.match(rows[0].proof, /^:= by\s+sorry$/)
assert.equal(rows[0].source_url, "https://example.test/FATE-X/blob/c0ffee/FATEX/1.lean#L8", "the line is the declaration's own")
assert.equal(rows[1].source_url.endsWith("FATEX/2.lean#L7"), true)
r = seed(3)
assert.notEqual(r.status, 0)
assert.match(r.stderr, /2 theorem\/lemma declarations, expected exactly 1/)
ok("seeder: records in setup-source's shape; one theorem per file, or an error")

// ---- verdicts, entries, the attestation's invariants ----------------------------------------
const pass = readVerdict({ ok: true, reason: "pass", text: "x\n✅ GATE2_PASS new=P.t_archangel old=P.t goal=∀ ... new_statement=∀ (x : Nat),\n  x = x old_statement=∀ (x : Nat), x = x\n\nWHAT THIS MEANS" })
assert.equal(pass.ok, true)
assert.equal(pass.identical, true, "the same printed statement, whitespace aside")
const differ = readVerdict({ ok: true, reason: "pass", text: "GATE2_PASS new_statement=a ≤ b old_statement=b ≥ a" })
assert.equal(differ.identical, false)
const failv = readVerdict({ ok: false, reason: "rejected", text: "GATE2_FAIL reason=rejected msg=Type mismatch new_statement=A old_statement=B" })
assert.equal(failv.ok, false)
assert.equal(failv.reason, "rejected")
eq(readVerdict({ ok: false, text: "" }).reason, "no_verdict")
eq(exportCandidates("FATEX", 9), ["FATEX.«9»", "FATEX.9"])
ok("verdict reader and export names")

const P = (i, extra = {}) => ({ id: `p${i}`, index: i, name: `t${i}`, statement: `theorem t${i} : True := by\n  sorry\n`, ...extra })
const e1 = problemEntry({ problem: P(1), qualifiedName: "Problem1.t1", oldId: "k/FATEX.«1»", exportSha256: sha256("x"), verdict: pass, gate2Text: "" })
const e2 = problemEntry({ problem: P(2, { port: { kind: "tree-name-clash" } }), qualifiedName: "Problem2.t2", oldId: "k/FATEX.«2»", exportSha256: sha256("y"), verdict: failv, gate2Text: "GATE2_FAIL reason=rejected   msg=boom" })
assert.equal(e1.verdict, "pass")
assert.equal(e2.verdict, "fail")
assert.equal(e2.port, "tree-name-clash")
assert.equal(e2.detail, "GATE2_FAIL reason=rejected msg=boom")
const A = buildAttestation({ subject: "s", upstream: {}, target: {}, inputs: {}, gate2: {}, problems: [e1, e2], run: {} })
eq(checkAttestation(A), [], "a well-formed attestation holds")
eq([A.schema, A.kind, A.admissible], [SCHEMA, "statement-only", false])
eq(A.counts, { total: 2, pass: 1, fail: 1, failReasons: { rejected: 1 } })
const broken = (f) => checkAttestation(f(structuredClone(A)))
assert.ok(broken((a) => ((a.admissible = true), a)).some((m) => /admissible/.test(m)), "admissible: true is caught")
assert.ok(broken((a) => ((a.kind = "translation"), a)).some((m) => /kind/.test(m)))
assert.ok(broken((a) => (a.problems.push({ ...a.problems[0] }), a)).some((m) => /twice/.test(m)))
assert.ok(broken((a) => ((a.problems[0].exportSha256 = ""), a)).some((m) => /export hash/.test(m)), "a pass with no export hash is caught")
assert.ok(broken((a) => ((a.counts.pass = 2), a)).some((m) => /counts.pass/.test(m)))
assert.ok(broken((a) => ((a.problems = []), a)).some((m) => /no problems/.test(m)))
ok("entries and the attestation's invariants")

// ---- where it may write ----------------------------------------------------------------------
for (const d of ADMISSION_DIRS) {
  assert.throws(() => assertNotAdmissionPath(join(ROOT, d), ROOT), /refusing/, d)
  assert.throws(() => assertNotAdmissionPath(join(ROOT, d, "fate-x", "run"), ROOT), /refusing/, `${d}/…`)
}
assert.doesNotThrow(() => assertNotAdmissionPath(join(ROOT, "out"), ROOT))
assert.doesNotThrow(() => assertNotAdmissionPath(join(ROOT, "data", "attest", "out"), ROOT))
assert.doesNotThrow(() => assertNotAdmissionPath(join(ROOT, "data", "bankruptcy"), ROOT), "a sibling that merely starts with the same letters is fine")
ok("no output under a directory a record is banked from")

// ---- the driver, end to end, with a stand-in for the Gate 2 daemon --------------------------------
const stub = join(tmp, "stub-bridge.mjs")
writeFileSync(
  stub,
  `export { findTargetDecl } from ${JSON.stringify(new URL("../public/local-claude-bridge.mjs", import.meta.url).href)}
export async function gate2ForScript(script, ref) {
  globalThis.__calls = (globalThis.__calls || 0) + 1
  if (ref.bare_name === "kernelno") return { ok: false, reason: "rejected", text: "GATE2_FAIL reason=rejected msg=Type mismatch new_statement=A old_statement=B" }
  return { ok: true, reason: "pass", text: "GATE2_PASS new=" + ref.old_export_names + "_archangel old=" + ref.old_export_names + " new_statement=T old_statement=T" }
}
`,
)
const exportsDir = join(tmp, "exports")
mkdirSync(exportsDir)
const probs = [
  { id: "p1", index: 1, name: "good", statement: "namespace Problem1\n\ntheorem good : True := by\n  sorry\n\nend Problem1\n" },
  { id: "p2", index: 2, name: "kernelno", statement: "namespace Problem2\n\ntheorem kernelno : True := by\n  sorry\n\nend Problem2\n" },
  { id: "p3", index: 3, name: "noexport", statement: "namespace Problem3\n\ntheorem noexport : True := by\n  sorry\n\nend Problem3\n" },
  { id: "p4", index: 4, name: "elsewhere", statement: "namespace Problem4\n\ntheorem other : True := by\n  sorry\n\nend Problem4\n", port: { kind: "modifier" } },
]
for (const i of [1, 2, 4]) writeFileSync(join(exportsDir, `FATEX.«${i}».ndjson`), `{"export":${i}}\n`)
writeFileSync(join(tmp, "problems.json"), JSON.stringify(probs))
writeFileSync(join(tmp, "source.json"), JSON.stringify({ label: "test", repo: "https://example.test/x", commit: "abc", toolchain: "leanprover/lean4:v4.28.0", licence: "MIT" }))
const drive = (out, extra = []) =>
  spawnSync(process.execPath, [join(ROOT, "scripts/attest/attest-statements.mjs"), "--problems", join(tmp, "problems.json"), "--exports", exportsDir, "--key", "k", "--root", "FATEX", "--gate2", "http://127.0.0.1:1/sse", "--source", join(tmp, "source.json"), "--out", out, "--bridge", stub, ...extra], {
    encoding: "utf8",
    env: { ...process.env, PORT: String(4300 + Math.floor(Math.random() * 500)) },
  })
const out = join(tmp, "out")
r = drive(out)
assert.equal(r.status, 0, r.stdout + r.stderr)
const att = JSON.parse(readFileSync(join(out, "statement-attestation.json"), "utf8"))
eq(checkAttestation(att), [])
const by = Object.fromEntries(att.problems.map((p) => [p.id, p]))
eq([by.p1.verdict, by.p1.name, by.p1.oldId], ["pass", "Problem1.good", "k/FATEX.«1»"])
assert.equal(by.p1.exportSha256, sha256(`{"export":1}\n`), "the export's hash is recorded")
eq([by.p2.verdict, by.p2.reason], ["fail", "rejected"])
eq([by.p3.verdict, by.p3.reason], ["fail", "no_export_for_module"])
eq([by.p4.verdict, by.p4.reason, by.p4.port], ["fail", "target_decl_not_found", "modifier"])
eq(att.counts, { total: 4, pass: 1, fail: 3, failReasons: { rejected: 1, no_export_for_module: 1, target_decl_not_found: 1 } })
eq([att.kind, att.admissible, att.upstream.commit], ["statement-only", false, "abc"])
assert.equal(att.inputs.translatedSha256, sha256(readFileSync(join(tmp, "problems.json"))))
assert.equal(readFileSync(join(out, "results.jsonl"), "utf8").trim().split("\n").length, 4)
r = drive(join(tmp, "out2"), ["--only", "p1"])
assert.equal(r.status, 0, r.stderr)
eq(JSON.parse(readFileSync(join(tmp, "out2", "statement-attestation.json"), "utf8")).counts.total, 1, "--only")
r = drive(join(tmp, "out3"), ["--export-mode", "full-closure"])
assert.equal(r.status, 0, r.stderr)
const full = JSON.parse(readFileSync(join(tmp, "out3", "statement-attestation.json"), "utf8"))
eq([full.inputs.exportMode, att.inputs.exportMode], ["full-closure", "library-only"], "the export mode is recorded, library-only by default")
assert.ok(full.limits.some((l) => /full-closure|without --only-listed/.test(l)) && !full.limits.some((l) => /are not in the original's export/.test(l)), "the Mathlib limit says what the export held")
assert.ok(att.limits.some((l) => /are not in the original's export/.test(l)))
eq(EXPORT_MODES, ["library-only", "full-closure"])
assert.notEqual(drive(join(tmp, "out4"), ["--export-mode", "everything"]).status, 0, "an unknown export mode is refused")
r = drive(join(ROOT, "data", "bank", "attest-test"))
assert.notEqual(r.status, 0, "the driver refuses an output directory under data/bank")
assert.match(r.stderr, /refusing to write a statement attestation under data\/bank/)
ok("driver end to end: pass, kernel refusal, no export, declaration not found; --only; refuses data/bank")

// ---- the workflow ------------------------------------------------------------------------------
const wf = readFileSync(join(ROOT, ".github/workflows/attest-statements.yml"), "utf8")
const active = wf.split("\n").filter((l) => !/^\s*#/.test(l)).join("\n")
for (const bad of [/TENGOKU_BOT_TOKEN/, /secrets\./, /bank-flush/, /git (?:push|commit)/, /gh pr /, /gh workflow run/, /contents:\s*write/, /actions:\s*write/, /data\/(?:bank|staging|translate)/, /--bridge/])
  assert.ok(!bad.test(active), `the workflow must not contain ${bad}`)
const job = (name) => {
  const m = active.match(new RegExp(`\\n  ${name}:\\n([\\s\\S]*?)(?=\\n  [a-z]+:\\n|$)`))
  assert.ok(m, `job ${name}`)
  return m[1]
}
const perm = (name) => (job(name).match(/permissions:\s*(\{[^}]*\})/) || [])[1]
assert.match(perm("old"), /contents: read/)
assert.ok(!/id-token|attestations/.test(perm("old")), "the job that builds the library cannot sign")
assert.ok(!/id-token|attestations/.test(perm("gate")), "the job that elaborates the translations cannot sign")
assert.match(perm("attest"), /id-token: write/)
assert.match(perm("attest"), /attestations: write/)
assert.ok(!/\blake\b|setup-source|elan|lean /.test(job("attest").replace(/lean4|"lean/g, "")), "the signing job compiles nothing")
assert.match(job("attest"), /bump-library/, "the signing job asserts tengoku's workflows would refuse the file")
assert.match(job("attest"), /refs\/heads\/main/)
assert.match(job("attest"), /checkAttestation/)
assert.equal((active.match(/actions\/attest-build-provenance@[0-9a-f]{40}/g) || []).length, 3, "three tries, as bump-library.yml")
assert.match(active, /github\.repository == 'competemath\/emissary-archangel'/, "a fork does not run it")
assert.match(wf, /pull_request:/)
ok("workflow: no way to bank or publish, signs only in a job that compiles nothing, asserts the refusal")

console.log(`\nall ok (${n} comparisons)`)
process.exit(0)
