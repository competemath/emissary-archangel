#!/usr/bin/env node
// Statement attestation: Archangel (Gate 2) over a set of translated statements, against exports of the originals made on their own toolchain.
//
//   node scripts/attest/attest-statements.mjs --problems data/attest/fate-x/translated.json --exports data/exports/fate-x --key fate-x --root FATEX \
//        --gate2 http://127.0.0.1:7872/sse --source data/attest/fate-x/source.json --out out [--tree tree] [--limit N] [--only fatex_009,fatex_016]
//
// For each problem it calls the SAME harness function a translation goes through (gate2ForScript in public/local-claude-bridge.mjs: it renames the translated theorem
// to <name>_archangel, asks the Gate 2 daemon for `fun h => h : new -> old` and reads the kernel's answer). It does NOT run Gate 1 (Leak IV refuses any `sorry`), because
// the statements' proofs are `sorry`; and it never calls the banking code: its only output is `out/results.jsonl` and `out/statement-attestation.json`, a file
// marked `admissible: false`, which the workflow signs under its own identity (.github/workflows/attest-statements.yml). `--out` may not be a directory a record
// could be banked from (lib.mjs ADMISSION_DIRS).
import { existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync, appendFileSync } from "node:fs"
import { execFileSync } from "node:child_process"
import { join, resolve } from "node:path"
import { pathToFileURL } from "node:url"
import { ADMISSION_DIRS, assertNotAdmissionPath, buildAttestation, checkAttestation, exportCandidates, problemEntry, readVerdict, sha256 } from "./lib.mjs"

const argv = process.argv.slice(2)
const opt = (n, d = null) => (argv.includes(`--${n}`) ? argv[argv.indexOf(`--${n}`) + 1] : d)
const need = (n) => opt(n) ?? (console.error(`attest-statements: --${n} is required`), process.exit(2))
const ROOT = resolve(new URL("../..", import.meta.url).pathname)

const problemsFile = need("problems")
const exportsDir = resolve(need("exports"))
const key = need("key")
const libRoot = need("root")
const gate2Url = need("gate2")
const sourceFile = need("source")
const outDir = resolve(need("out"))
const treeDir = opt("tree")
const limit = Number(opt("limit", "0")) || 0
const only = (opt("only", "") || "").split(",").filter(Boolean)
assertNotAdmissionPath(outDir, ROOT)
mkdirSync(outDir, { recursive: true })

const ts = () => new Date().toISOString().slice(11, 19)
const log = (s) => console.log(`[${ts()}] ${s}`)
const git = (cwd, ...args) => {
  try {
    return execFileSync("git", args, { cwd, encoding: "utf8" }).trim()
  } catch {
    return null
  }
}

// The harness module starts a local HTTP server when it is imported (the bridge): a port of its own, a token that is not a secret, and an explicit exit at the end.
process.env.PORT = process.env.PORT || "4199"
process.env.BRIDGE_TOKEN = process.env.BRIDGE_TOKEN || "statement-attestation"
// --bridge: another module with the same two functions (the tests' stand-in for the Gate 2 daemon); the default is the real harness.
const bridgeFile = opt("bridge")
const bridge = await import(bridgeFile ? pathToFileURL(resolve(bridgeFile)).href : new URL("../../public/local-claude-bridge.mjs", import.meta.url).href)

let problems = JSON.parse(readFileSync(problemsFile, "utf8"))
if (only.length) problems = problems.filter((p) => only.includes(p.id))
if (limit) problems = problems.slice(0, limit)
const source = JSON.parse(readFileSync(sourceFile, "utf8"))
const available = existsSync(exportsDir) ? readdirSync(exportsDir) : []
log(`${problems.length} problems, ${available.filter((f) => f.endsWith(".ndjson")).length} exports in ${exportsDir}`)

const resultsPath = join(outDir, "results.jsonl")
writeFileSync(resultsPath, "")
const entries = []
for (const problem of problems) {
  const spelled = exportCandidates(libRoot, problem.index).map((m) => `${m}.ndjson`)
  const file = spelled.find((f) => available.includes(f))
  const { found, hits } = bridge.findTargetDecl(problem.statement, "")
  const mine = found.filter((f) => f.declared === problem.name || f.qualified === problem.name || f.qualified.endsWith(`.${problem.name}`))
  let entry
  if (!file) {
    entry = problemEntry({ problem, qualifiedName: null, verdict: { ok: false, reason: "no_export_for_module", identical: null }, gate2Text: `no export among ${spelled.join(", ")}` })
  } else if (mine.length !== 1) {
    entry = problemEntry({ problem, qualifiedName: null, verdict: { ok: false, reason: "target_decl_not_found", identical: null }, gate2Text: `declarations found: ${found.map((f) => f.qualified).join(", ") || "none"}` })
  } else {
    const qualifiedName = mine[0].qualified
    const oldId = `${key}/${file.replace(/\.ndjson$/, "")}`
    const exportSha256 = sha256(readFileSync(join(exportsDir, file)))
    const t0 = Date.now()
    const r = await bridge.gate2ForScript(problem.statement, { old_id: oldId, old_export_names: qualifiedName, bare_name: problem.name }, { archangelUrl: gate2Url })
    const verdict = readVerdict(r)
    log(`${problem.id} ${qualifiedName}: ${verdict.ok ? "PASS" : `FAIL ${verdict.reason}`} (${Math.round((Date.now() - t0) / 1000)} s)`)
    entry = problemEntry({ problem, qualifiedName, oldId, exportSha256, verdict, gate2Text: r?.text })
    appendFileSync(resultsPath, JSON.stringify({ ...entry, gate2: String(r?.text || "").slice(0, 4000) }) + "\n")
    entries.push(entry)
    continue
  }
  log(`${problem.id}: not run (${entry.reason})`)
  appendFileSync(resultsPath, JSON.stringify(entry) + "\n")
  entries.push(entry)
}

const sha = (p) => (existsSync(p) ? sha256(readFileSync(p)) : null)
const attestation = buildAttestation({
  subject: `${source.label}: ${problems.length} translated statements against their originals`,
  upstream: { repo: source.repo, commit: source.commit, toolchain: source.toolchain, licence: source.licence },
  target: { tree: treeDir ? git(treeDir, "remote", "get-url", "origin") : null, treeCommit: treeDir ? git(treeDir, "rev-parse", "HEAD") : null, toolchain: treeDir && existsSync(join(treeDir, "lean-toolchain")) ? readFileSync(join(treeDir, "lean-toolchain"), "utf8").trim() : null },
  inputs: { translatedSha256: sha(problemsFile), sourceSha256: sha(sourceFile) },
  gate2: {
    check: "kernel accepts `fun h => h : T_translated -> T_original` (Archangel, gate2/Vendor/Gate2.lean), original replayed from its export on its own toolchain",
    serverSha256: sha(join(ROOT, "gate2", "server.py")),
    gate2LeanSha256: sha(join(ROOT, "gate2", "Vendor", "Gate2.lean")),
    harnessSha256: sha(join(ROOT, "public", "local-claude-bridge.mjs")),
    emissaryCommit: git(ROOT, "rev-parse", "HEAD"),
  },
  problems: entries,
  run: { repository: process.env.GITHUB_REPOSITORY || null, workflow: process.env.GITHUB_WORKFLOW_REF || null, runId: process.env.GITHUB_RUN_ID || null, sha: process.env.GITHUB_SHA || null, ref: process.env.GITHUB_REF || null },
})
const bad = checkAttestation(attestation)
if (bad.length) {
  console.error(`attest-statements: the attestation breaks its own invariants: ${bad.join("; ")}`)
  process.exit(1)
}
writeFileSync(join(outDir, "statement-attestation.json"), JSON.stringify(attestation, null, 2) + "\n")
log(`attestation: ${JSON.stringify(attestation.counts)} -> ${join(outDir, "statement-attestation.json")}`)
log(`not written under: ${ADMISSION_DIRS.join(", ")}`)
process.exit(0)
