#!/usr/bin/env node
// Statement attestation, batch checker: ONE Lean process per chunk of problems, Gate 2's batch check with the statement-only rule (Vendor/Attest.lean, scripts/attest/emit_attest_vendor.py).
//
//   node scripts/attest/attest-batch.mjs --problems data/attest/fate-x/translated.json --exports data/exports/fate-x --key fate-x --root FATEX --source data/attest/fate-x/source.json \
//        --out out --tree tree --lean /path/to/lean --lean-path "<LEAN_PATH>" --vendor vendorproj [--chunk 25] [--parallel 2] [--limit N] [--only ids] [--export-mode full-closure]
//
// Why not the daemon (attest-statements.mjs, round 1 and 2 of PR 162): the daemon refuses to replay an original around ANY Mathlib definition the tree has with another structure, and 6
// versions of Mathlib change a great many instances (round 2: 92 refusals of 100). The batch check decides sameness of definitions with the kernel (the original's replayed beside the native one,
// `native = original` by `Eq.refl`), which is what a bump of a whole library is judged by. It refuses `sorry` anywhere; the statement-only variant refuses it in everything but the
// PROOF of the theorem being checked.
//
// Each problem: the original's export is parsed, the translation is elaborated in a section of its own (under its own names, in the tree), and the check compares the two. A chunk that dies (memory,
// time) is run again problem by problem; a problem whose own elaboration fails is a failure with its first Lean error. Nothing is written but `--out`, and never under a directory a record is banked from.
import { spawn } from "node:child_process"
import { existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync, appendFileSync } from "node:fs"
import { execFileSync } from "node:child_process"
import { join, resolve } from "node:path"
import { ADMISSION_DIRS, EXPORT_MODES, assertNotAdmissionPath, buildAttestation, checkAttestation, checkFileText, exportCandidates, problemBlock, problemEntry, qualifiedTarget, readBatchVerdict, sha256, splitLog } from "./lib.mjs"

const argv = process.argv.slice(2)
const opt = (n, d = null) => (argv.includes(`--${n}`) ? argv[argv.indexOf(`--${n}`) + 1] : d)
const need = (n) => opt(n) ?? (console.error(`attest-batch: --${n} is required`), process.exit(2))
const ROOT = resolve(new URL("../..", import.meta.url).pathname)
const problemsFile = need("problems")
const exportsDir = resolve(need("exports"))
const key = need("key")
const libRoot = need("root")
const sourceFile = need("source")
const outDir = resolve(need("out"))
const treeDir = opt("tree")
const lean = need("lean")
const leanPath = need("lean-path")
const vendorDir = opt("vendor")
const treeImport = opt("tree-import", "Tengoku.All")
// the checker may run as another user, to whom git calls on the runner's checkouts fail ("dubious ownership"): the workflow passes the commits
const treeCommitArg = opt("tree-commit")
const emissaryCommitArg = opt("emissary-commit")
const chunkSize = Math.max(1, Number(opt("chunk", "25")))
const parallel = Math.max(1, Number(opt("parallel", "2")))
const timeoutMin = Number(opt("timeout-min", "100"))
const limit = Number(opt("limit", "0")) || 0
const only = (opt("only", "") || "").split(",").filter(Boolean)
const exportMode = opt("export-mode", "full-closure")
// the hand-written migration table (data/attest/fate-x/migration.json + .lean): old-library names defined by the tree's own constants, for the check of one problem at a time
const migrationFile = opt("migration")
const migration = migrationFile
  ? (() => {
      const spec = JSON.parse(readFileSync(migrationFile, "utf8"))
      const text = readFileSync(join(resolve(migrationFile, ".."), spec.file), "utf8")
      return { names: spec.names, renames: spec.renames || {}, text, sha256: sha256(text), file: spec.file, oldToolchain: spec.oldToolchain, newToolchain: spec.newToolchain }
    })()
  : null
if (!EXPORT_MODES.includes(exportMode)) (console.error(`attest-batch: --export-mode is one of ${EXPORT_MODES.join(", ")}`), process.exit(2))
assertNotAdmissionPath(outDir, ROOT)
mkdirSync(join(outDir, "chunks"), { recursive: true })

const ts = () => new Date().toISOString().slice(11, 19)
const log = (s) => console.log(`[${ts()}] ${s}`)
const sh = (cmd, args, cwd) => {
  try {
    return execFileSync(cmd, args, { cwd, encoding: "utf8" }).trim()
  } catch {
    return null
  }
}

let problems = JSON.parse(readFileSync(problemsFile, "utf8"))
if (only.length) problems = problems.filter((p) => only.includes(p.id))
if (limit) problems = problems.slice(0, limit)
const source = JSON.parse(readFileSync(sourceFile, "utf8"))
const available = existsSync(exportsDir) ? readdirSync(exportsDir) : []

// what each problem needs: its export file and its qualified name; a problem without either is a failure that never reaches Lean
const prepared = new Map()
const entries = new Map()
const results = join(outDir, "results.jsonl")
writeFileSync(results, "")
const settle = (problem, entry, extra = {}) => {
  entries.set(problem.id, entry)
  appendFileSync(results, JSON.stringify({ ...entry, ...extra }) + "\n")
}
for (const problem of problems) {
  const file = exportCandidates(libRoot, problem.index).map((m) => `${m}.ndjson`).find((f) => available.includes(f))
  const qualified = qualifiedTarget(problem.statement, problem.name)
  if (!file) settle(problem, problemEntry({ problem, verdict: { ok: false, reason: "no_export_for_module", via: null }, gate2Text: "no export for this module" }))
  else if (!qualified) settle(problem, problemEntry({ problem, verdict: { ok: false, reason: "target_decl_not_found", via: null }, gate2Text: `theorem ${problem.name} is not declared exactly once` }))
  else prepared.set(problem.id, { problem, file, qualified, exportPath: join(exportsDir, file), oldId: `${key}/${file.replace(/\.ndjson$/, "")}`, exportSha256: sha256(readFileSync(join(exportsDir, file))) })
}
log(`${problems.length} problems, ${prepared.size} ready for Lean, ${entries.size} already failed`)

// a problem the plain bridge `fun h => h` refuses is tried once more, alone, with these terms in turn (the kernel checks each like any other)
const BRIDGES = ["fun h => by with_unfolding_all exact h", "fun h => by convert h", "fun h => by convert h <;> first | rfl | exact Subsingleton.elim _ _ | exact proof_irrel _ _"]
const runLean = (name, items, bridge = null) =>
  new Promise((done) => {
    const file = join(outDir, "chunks", `${name}.lean`)
    writeFileSync(file, checkFileText(treeImport, items.map((p) => problemBlock({ id: p.problem.id, exportPath: p.exportPath, statement: p.problem.statement, qualified: p.qualified, migration })), bridge))
    const logFile = join(outDir, "chunks", `${name}.log`)
    const t0 = Date.now()
    const child = spawn(lean, [file], { env: { ...process.env, LEAN_PATH: leanPath }, cwd: outDir, stdio: ["ignore", "pipe", "pipe"] })
    let text = ""
    child.stdout.on("data", (d) => (text += d))
    child.stderr.on("data", (d) => (text += d))
    let timedOut = false
    const timer = setTimeout(() => ((timedOut = true), child.kill("SIGKILL")), timeoutMin * 60 * 1000)
    child.on("close", (code, signal) => {
      clearTimeout(timer)
      writeFileSync(logFile, text)
      log(`chunk ${name}: ${items.length} problems, exit ${code ?? signal}${timedOut ? " (timeout)" : ""}, ${Math.round((Date.now() - t0) / 1000)} s`)
      done({ text, code, signal, timedOut })
    })
  })

// a chunk's problems that got a verdict are settled; the others are returned (the process died before them, or a segment holds nothing readable)
const runChunk = async (name, items, bridge = null) => {
  const r = await runLean(name, items, bridge)
  const segments = splitLog(r.text)
  const left = []
  for (const p of items) {
    const seg = segments[p.problem.id]
    const v = seg === undefined ? { ok: null, reason: "not_reached", via: null, errors: [] } : readBatchVerdict(seg)
    if (v.ok === null && (seg === undefined || r.timedOut || r.signal)) {
      left.push(p)
      continue
    }
    const ok = v.ok === true
    settle(p.problem, problemEntry({ problem: p.problem, qualifiedName: p.qualified, oldId: p.oldId, exportSha256: p.exportSha256, verdict: ok ? { ...v, ...(bridge ? { bridge } : {}) } : { ...v, ok: false }, gate2Text: null }), { checker: "batch-statement-only", segment: (seg || "").replace(/\s+/g, " ").slice(0, 3000) })
    log(`${p.problem.id} ${p.qualified}: ${ok ? `PASS via=${v.via}` : `FAIL ${v.reason}`}`)
  }
  return left
}

const todo = [...prepared.values()]
const chunks = []
for (let i = 0; i < todo.length; i += chunkSize) chunks.push(todo.slice(i, i + chunkSize))
const queue = chunks.map((c, i) => ({ name: `chunk-${String(i).padStart(2, "0")}`, items: c }))
let again = []
await Promise.all(
  Array.from({ length: Math.min(parallel, queue.length) }, async () => {
    while (queue.length) {
      const job = queue.shift()
      again.push(...(await runChunk(job.name, job.items)))
    }
  }),
)
if (again.length) {
  log(`${again.length} problems were not reached or their process died: each in a process of its own`)
  const singles = again.map((p) => ({ name: `single-${p.problem.id}`, items: [p] }))
  const stuck = []
  await Promise.all(
    Array.from({ length: Math.min(parallel, singles.length) }, async () => {
      while (singles.length) {
        const job = singles.shift()
        stuck.push(...(await runChunk(job.name, job.items)))
      }
    }),
  )
  for (const p of stuck) settle(p.problem, problemEntry({ problem: p.problem, qualifiedName: p.qualified, oldId: p.oldId, exportSha256: p.exportSha256, verdict: { ok: false, reason: "process_died", via: null }, gate2Text: "Lean was killed (memory or time) alone on this problem" }))
}

// second pass: the problems refused by the plain bridge, each in a process of its own, with the other bridge terms in turn. Only a pass replaces the first verdict.
const refused = [...prepared.values()].filter((p) => entries.get(p.problem.id)?.verdict === "fail" && entries.get(p.problem.id)?.reason === "rejected")
if (refused.length) {
  log(`${refused.length} problems were refused by the plain bridge: each once more with ${BRIDGES.map((b) => `\`${b}\``).join(", then ")}`)
  const jobs = refused.map((p) => ({ p }))
  await Promise.all(
    Array.from({ length: Math.min(parallel, jobs.length) }, async () => {
      while (jobs.length) {
        const { p } = jobs.shift()
        const before = entries.get(p.problem.id)
        for (const [i, bridge] of BRIDGES.entries()) {
          await runChunk(`bridge${i + 2}-${p.problem.id}`, [p], bridge)
          if (entries.get(p.problem.id)?.verdict === "pass") break
          entries.set(p.problem.id, before) // a second-pass failure keeps the first verdict (its reason and difference are the ones to read)
        }
      }
    }),
  )
}

const sha = (p) => (p && existsSync(p) ? sha256(readFileSync(p)) : null)
const ordered = problems.map((p) => entries.get(p.id)).filter(Boolean)
const attestation = buildAttestation({
  subject: `${source.label}: ${problems.length} translated statements against their originals`,
  upstream: { repo: source.repo, commit: source.commit, toolchain: source.toolchain, licence: source.licence },
  target: { tree: treeDir ? sh("git", ["remote", "get-url", "origin"], treeDir) : null, treeCommit: treeCommitArg || (treeDir ? sh("git", ["rev-parse", "HEAD"], treeDir) : null), toolchain: treeDir && existsSync(join(treeDir, "lean-toolchain")) ? readFileSync(join(treeDir, "lean-toolchain"), "utf8").trim() : null, lean: sh(lean, ["--version"]) },
  inputs: { translatedSha256: sha(problemsFile), sourceSha256: sha(sourceFile) },
  gate2: {
    checker: "batch-statement-only",
    check: "Gate 2's batch check (gate2_batch.py) with the statement-only rule: the kernel accepts `native = original` for every definition the statements reach, and the statements are equal or `fun h => h : T_translated -> T_original`; sorry only in the proof of the theorem checked",
    attestLeanSha256: vendorDir ? sha(join(vendorDir, "Vendor", "Attest.lean")) : null,
    batchLeanSha256: vendorDir ? sha(join(vendorDir, "Vendor", "Batch.lean")) : null,
    coreLeanSha256: vendorDir ? sha(join(vendorDir, "Vendor", "Core.lean")) : null,
    emissaryCommit: emissaryCommitArg || sh("git", ["rev-parse", "HEAD"], ROOT),
  },
  problems: ordered,
  exportMode,
  checker: "batch-statement-only",
  interpretation: migration ? { kind: "hand-written-migration-table", file: migration.file, sha256: migration.sha256, names: migration.names, renames: migration.renames, oldToolchain: migration.oldToolchain, newToolchain: migration.newToolchain, text: migration.text } : null,
  run: { repository: process.env.GITHUB_REPOSITORY || null, workflow: process.env.GITHUB_WORKFLOW_REF || null, runId: process.env.GITHUB_RUN_ID || null, sha: process.env.GITHUB_SHA || null, ref: process.env.GITHUB_REF || null },
})
const bad = checkAttestation(attestation)
if (bad.length) {
  console.error(`attest-batch: the attestation breaks its own invariants: ${bad.join("; ")}`)
  process.exit(1)
}
writeFileSync(join(outDir, "statement-attestation.json"), JSON.stringify(attestation, null, 2) + "\n")
log(`attestation: ${JSON.stringify(attestation.counts)} -> ${join(outDir, "statement-attestation.json")}`)
log(`not written under: ${ADMISSION_DIRS.join(", ")}`)
process.exit(0)
