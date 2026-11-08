// node scripts/test-setup-seed-memory.mjs — the seed step keeps the files it reads within a budget, so a library of very large sources is seeded under Node's heap limit.
//
// The real case: leanbridge (7 Nov 2026) has 1.5 GB of Lean sources (LMFDB q-expansion tables, up to 53 MB a file) and 15 tentative files whose records come file by file
// (leanbridge-001: 1,645 records in 341 files, 340 changes of file). The seed step kept every file's lines for the whole run and Node died at its 4 GB heap in every phase
// ("Reached heap limit Allocation failed - JavaScript heap out of memory", setup runs 42386199526, 42387020776). Here a library of 12 files of 12 MB of non-Latin-1 text
// (two bytes a character in memory, as the LMFDB tables are) is seeded with Node's heap capped at 200 MB: more than the heap if every file is kept, about one file if not.
// Records have the real shape (keys of a leanbridge record). Invariants: the seed finishes under the cap with a small budget; the queue is byte for byte the one an unbounded
// cache gives (same entries, same order, same names and lines); with the records interleaved across files (the worst order) the queue is still the same.
import { execFileSync, spawnSync } from "node:child_process"
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import os from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const tmp = mkdtempSync(join(os.tmpdir(), "seed-memory-"))
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) {
    bad++
    console.log("FAIL", name, detail ?? "")
  } else console.log("ok", name)
}
const sh = (cmd, args, opts = {}) => execFileSync(cmd, args, { stdio: ["ignore", "pipe", "pipe"], maxBuffer: 1 << 26, ...opts }).toString()

// the library: FILES files, each a theorem every PER lines and a large table in between
const FILES = 12
const MB = 12
const lib = join(tmp, "lib-src")
mkdirSync(join(lib, "Lib"), { recursive: true })
const TC = "leanprover/lean4:v4.0.0"
writeFileSync(join(lib, "lean-toolchain"), TC + "\n")
const records = []
const row = "-- q-expansion: " + "∑ₙ aₙ qⁿ ℤ ".repeat(8) + "\n" // non-Latin-1: two bytes a character in Node's memory
for (let f = 0; f < FILES; f++) {
  const parts = []
  let line = 1
  let size = 0
  let k = 0
  while (size < MB * 1024 * 1024) {
    const thm = `theorem t${f}_${k} : ${k} = ${k} := rfl\n`
    parts.push(thm)
    records.push({ name: `t${f}_${k}`, statement: `theorem t${f}_${k} : ${k} = ${k}`, proof: ":= rfl", status: "tentative", library: "t", source_url: `PATH:Lib/F${f}.lean#L${line}`, toolchain: TC })
    line += 1
    const block = row.repeat(2000)
    parts.push(block)
    line += 2000
    size += thm.length + block.length
    k++
  }
  writeFileSync(join(lib, "Lib", `F${f}.lean`), parts.join(""))
}
const git = (...a) => sh("git", ["-c", "user.name=t", "-c", "user.email=t@t", ...a], { cwd: lib })
git("init", "-q")
git("add", ".")
git("commit", "-q", "-m", "lib")
const commit = git("rev-parse", "HEAD").trim()
for (const r of records) r.source_url = r.source_url.replace("PATH:", `https://github.com/o/lib/blob/${commit}/`)

const root = join(tmp, "root")
mkdirSync(join(root, "scripts"), { recursive: true })
mkdirSync(join(root, "data"), { recursive: true })
for (const f of ["setup-source.mjs", "setup-tools.mjs", "bisect.mjs", "memory-rules.mjs", "pinned-deps.mjs"]) cpSync(join(here, f), join(root, "scripts", f))
writeFileSync(join(root, "sources.json"), JSON.stringify({ sources: { t: { repo: lib, commit, toolchain: TC, roots: ["Lib"] } } }))
const tent = join(tmp, "tentative")
mkdirSync(tent)
const home = join(tmp, "home")
mkdirSync(join(home, ".elan", "bin"), { recursive: true })
writeFileSync(join(home, ".elan", "bin", "elan"), `#!/bin/sh\necho "${TC} (default)"\n`)
sh("chmod", ["+x", join(home, ".elan", "bin", "elan")])

const seed = (recs, env, heapMb = 200) => {
  writeFileSync(join(tent, "t.jsonl"), recs.map((r) => JSON.stringify(r)).join("\n") + "\n")
  rmSync(join(root, "data", "queue-t.json"), { force: true })
  const r = spawnSync("node", [`--max-old-space-size=${heapMb}`, join(root, "scripts", "setup-source.mjs"), "t", "--only", "seed"], {
    env: { ...process.env, HOME: home, EMISSARY_TENTATIVE_DIR: tent, ...env },
    encoding: "utf8",
    maxBuffer: 1 << 26,
  })
  let queue = null
  try {
    queue = readFileSync(join(root, "data", "queue-t.json"), "utf8")
  } catch {}
  return { code: r.status, out: (r.stdout || "") + (r.stderr || ""), queue }
}

const total = FILES * MB
const small = seed(records, { EMISSARY_SEED_CACHE_MB: "16" })
check(`the seed of ${FILES} files (${total} MB of two-byte text) finishes under a 200 MB heap`, small.code === 0 && small.queue, small.out.slice(-600))
const n = small.queue ? JSON.parse(small.queue).length : 0
check(`every record became an entry (${records.length})`, n === records.length, `${n}`)

// the same queue as a cache that keeps everything (a heap big enough for it); the queue file is removed first, or setup-source keeps it and seeds nothing
rmSync(join(root, "data", "queue-t.json"), { force: true })
const keepAll = spawnSync("node", ["--max-old-space-size=4096", join(root, "scripts", "setup-source.mjs"), "t", "--only", "seed"], {
  env: { ...process.env, HOME: home, EMISSARY_TENTATIVE_DIR: tent, EMISSARY_SEED_CACHE_MB: "100000" },
  encoding: "utf8",
  maxBuffer: 1 << 26,
})
const fullQueue = readFileSync(join(root, "data", "queue-t.json"), "utf8")
check("the queue is byte for byte the one an unbounded cache gives", keepAll.status === 0 && fullQueue === small.queue)

// a budget smaller than one file: no file is kept (each is read for its records and let go), the queue is the same, and the heap holds
// one record names a file the library does not have: it is cached as "no file", which is not a file kept
const missing = { ...records[0], name: "gone", source_url: records[0].source_url.replace(/F0\.lean#L\d+$/, "Gone.lean#L1") }
const tiny = seed([...records, missing], { EMISSARY_SEED_CACHE_MB: "1" })
check("a budget smaller than any file: nothing is kept (a missing file is no file kept), and the queue is the same", tiny.code === 0 && tiny.queue === fullQueue && /seed: 0 source file\(s\) kept at the end/.test(tiny.out), tiny.out.slice(-300))
// a budget that is no finite number falls back to the default (256 MB): it never means 'keep everything'
for (const v of ["Infinity", "1e309", "NaN", "-5", "0"]) {
  const r = seed(records.slice(0, 5), { EMISSARY_SEED_CACHE_MB: v })
  check(`EMISSARY_SEED_CACHE_MB=${v} falls back to the default budget`, r.code === 0 && /kept within 256 MB of text/.test(r.out), r.out.slice(-300))
}

// the worst order: records interleaved across files, so every record evicts the file the next one needs
const inter = []
const byFile = Array.from({ length: FILES }, (_, f) => records.filter((r) => r.source_url.includes(`/F${f}.lean#`)))
for (let i = 0; byFile.some((l) => i < l.length); i++) for (const l of byFile) if (i < l.length) inter.push(l[i])
const a = seed(inter.slice(0, 200), { EMISSARY_SEED_CACHE_MB: "16" })
const b = seed(inter.slice(0, 200), { EMISSARY_SEED_CACHE_MB: "100000" }, 4096) // the reference keeps every file: it needs the large heap
check("records interleaved across files: the same queue with a small budget as with no limit", a.code === 0 && a.queue && a.queue === b.queue, a.out.slice(-300))

// the fixture is shown to need the budget: with no limit under the same 200 MB heap the seed dies
const unbounded = seed(records, { EMISSARY_SEED_CACHE_MB: "100000" })
check("the fixture reproduces the failure: with every file kept, the seed dies at the heap limit", unbounded.code !== 0 && /heap out of memory|Allocation failed/.test(unbounded.out), `${unbounded.code} ${unbounded.out.slice(-300)}`)

// leanbridge's other half (setup run 42411218917, 7 Nov): 15 tentative files of ~40 MB (records whose proofs run to tens of KB), all read at once, and the queue written as
// one JSON string, did not fit next to the entries either. 6 tentative files of 12 MB of long proofs are seeded under a 300 MB heap: the files are read one at a time and the
// queue is written entry by entry; its bytes are exactly JSON.stringify(entries, null, 2) (parsed and written again, the same bytes).
{
  // every record of the library once, each pointing at its own declaration (so no record takes the unverified-line fallback), its proof made long
  const proof = ":= by\n" + "  simp [Finset.sum_range_succ, ℤ, ∑]\n".repeat(2800) // ~100 KB, non-Latin-1 like the real proofs
  const tfiles = []
  const per = Math.ceil(records.length / 6)
  for (let t = 0; t < 6; t++) {
    const rows = records.slice(t * per, (t + 1) * per).map((r) => JSON.stringify({ ...r, proof }))
    const name = `t-${String(t + 1).padStart(3, "0")}.jsonl`
    writeFileSync(join(tent, name), rows.join("\n") + "\n")
    tfiles.push(name)
  }
  writeFileSync(join(root, "sources.json"), JSON.stringify({ sources: { t: { repo: lib, commit, toolchain: TC, roots: ["Lib"], tentative: tfiles } } }))
  rmSync(join(root, "data", "queue-t.json"), { force: true })
  const r = spawnSync("node", ["--max-old-space-size=300", join(root, "scripts", "setup-source.mjs"), "t", "--only", "seed"], {
    env: { ...process.env, HOME: home, EMISSARY_TENTATIVE_DIR: tent, EMISSARY_SEED_CACHE_MB: "16" },
    encoding: "utf8",
    maxBuffer: 1 << 26,
  })
  check(`six tentative files of long proofs (${records.length} records, ~${Math.round((records.length * proof.length) / 1e6)} MB) are seeded under a 300 MB heap`, r.status === 0, (r.stdout + r.stderr).slice(-400))
  const stats = JSON.parse(((r.stdout || "").match(/seeded \S+: (\{.*\})/) || [, "{}"])[1])
  check("no record took the unverified-line fallback: each line was checked against its declaration", stats.kept === records.length && stats.lineUnverified === 0, JSON.stringify(stats))
  const text = r.status === 0 ? readFileSync(join(root, "data", "queue-t.json"), "utf8") : ""
  const parsed = text ? JSON.parse(text) : []
  check("the queue's bytes are JSON.stringify(entries, null, 2) exactly", text !== "" && text === JSON.stringify(parsed, null, 2))
  const want = records.map((r) => r.name)
  check("every record of the six files became an entry, in order, once", JSON.stringify(parsed.map((e) => e.name)) === JSON.stringify(want), `${parsed.length} of ${want.length}`)
}

// leanbridge's third half (setup run 42427677819 and the five rounds after it, 7-8 Nov): with the files read one at a time and the queue written entry by entry, the seed still
// died at the 4 GB heap in every round, in the build and in build-status: every entry kept its statement and proof until the end (the 1,645 records of leanbridge-001 take 118 MB
// of heap, ~1.7 GB for the 15 files), and the queue it wrote (~600 million characters) is longer than the longest string Node can make, so the next step could not read it.
// The records here have the REAL sizes of leanbridge-001's 1,645 records (fixtures/real-leanbridge-001-sizes.json: statement and proof lengths, two-byte text where the real one
// is, the real 341 files), twice (as leanbridge-001 and -002), ~80 MB of text, ~240 MB as entries: more than the 128 MB heap the seed and build-status run under here.
// Invariants: the seed finishes under the cap; the queue holds every record whole (statement and proof), in order, and its bytes are JSON.stringify(entries, null, 2); build-status
// reads that queue back under the same cap and counts every module; a queue of another shape (minified, empty) is still read; a cut-off queue is refused, not half-read.
{
  const real = JSON.parse(readFileSync(join(here, "fixtures", "real-leanbridge-001-sizes.json"), "utf8"))
  check("the fixture is leanbridge-001's 1,645 records in 341 files", real.records === 1645 && real.rows.length === 1645 && real.files === 341)
  const lib2 = join(tmp, "lib-lb")
  mkdirSync(join(lib2, "LB"), { recursive: true })
  writeFileSync(join(lib2, "lean-toolchain"), TC + "\n")
  const pad = (n, wide) => (wide ? "ℚ∑ₙ" : "abc").repeat(Math.ceil(n / 3)).slice(0, Math.max(0, n))
  const files = new Map() // file -> lines
  const recs = []
  for (const copy of [0, 1])
    for (const [i, [f, st, pr, wide]] of real.rows.entries()) {
      const file = `LB/F${copy}_${f}.lean`
      if (!files.has(file)) files.set(file, [])
      const lines = files.get(file)
      const name = `r${copy}_${i}`
      const head = `theorem ${name} : ${i} = ${i}`
      lines.push(head + " := rfl", "")
      const statement = head + "\n" + pad(st - head.length - 1, wide) // the real length; the first line is the declaration's
      const proof = ":= by\n" + pad(pr - 6, wide)
      recs.push({ name, statement, proof, status: "tentative", library: "lb", source_url: `PATH:${file}#L${lines.length - 1}`, toolchain: TC })
    }
  for (const [file, lines] of files) writeFileSync(join(lib2, file), lines.join("\n"))
  const git2 = (...a) => sh("git", ["-c", "user.name=t", "-c", "user.email=t@t", ...a], { cwd: lib2 })
  git2("init", "-q")
  git2("add", ".")
  git2("commit", "-q", "-m", "lib")
  const c2 = git2("rev-parse", "HEAD").trim()
  for (const r of recs) r.source_url = r.source_url.replace("PATH:", `https://github.com/o/lb/blob/${c2}/`)
  const half = recs.length / 2
  writeFileSync(join(tent, "lb-001.jsonl"), recs.slice(0, half).map((r) => JSON.stringify(r)).join("\n") + "\n")
  writeFileSync(join(tent, "lb-002.jsonl"), recs.slice(half).map((r) => JSON.stringify(r)).join("\n") + "\n")
  writeFileSync(join(root, "sources.json"), JSON.stringify({ sources: { lb: { repo: lib2, commit: c2, toolchain: TC, roots: ["LB"], tentative: ["lb-001.jsonl", "lb-002.jsonl"] } } }))
  const textMB = Math.round(recs.reduce((a, r) => a + r.statement.length + r.proof.length, 0) / 1048576)
  const qfile = join(root, "data", "queue-lb.json")
  const statusFile = join(root, "infra", "lb", "build-status.json")
  const run = (args, heapMb = 128) =>
    spawnSync("node", [`--max-old-space-size=${heapMb}`, join(root, "scripts", "setup-source.mjs"), "lb", ...args], {
      env: { ...process.env, HOME: home, EMISSARY_TENTATIVE_DIR: tent, EMISSARY_SEED_CACHE_MB: "8" },
      encoding: "utf8",
      maxBuffer: 1 << 26,
    })
  rmSync(qfile, { force: true })
  const s = run(["--only", "seed"])
  check(`${recs.length} records of leanbridge's real sizes (${textMB} MB of text) are seeded under a 128 MB heap`, s.status === 0, (s.stdout + s.stderr).slice(-400))
  const text = s.status === 0 ? readFileSync(qfile, "utf8") : ""
  const parsed = text ? JSON.parse(text) : []
  check("the queue's bytes are JSON.stringify(entries, null, 2) exactly", text !== "" && text === JSON.stringify(parsed, null, 2))
  check(
    "every record is in the queue whole, in order: its name, statement and proof",
    parsed.length === recs.length && parsed.every((e, i) => e.name === recs[i].name && e.oldStatement === recs[i].statement && e.oldProofText === recs[i].proof && e.id === i + 1),
    `${parsed.length} of ${recs.length}`,
  )
  const modules = new Set(recs.map((r) => r.source_url.match(/blob\/[0-9a-f]+\/(.+)\.lean#/)[1].replace(/\//g, "."))).size
  // the next step of the same job: the queue exists, and is read back
  rmSync(statusFile, { force: true })
  const b = run(["--phase", "build-status"])
  const st = existsSync(statusFile) ? JSON.parse(readFileSync(statusFile, "utf8")) : {}
  check(`build-status reads the queue back under the same heap and counts all ${modules} modules`, b.status === 0 && st.modules === modules && st.built === 0 && /queue exists: .* \(3290 entries\)/.test(b.stdout), `${b.status} ${JSON.stringify(st).slice(0, 200)} ${(b.stdout + b.stderr).slice(-300)}`)
  // a queue of another shape is parsed whole, as before: minified, and empty
  writeFileSync(qfile, JSON.stringify(parsed.slice(0, 50)))
  rmSync(statusFile, { force: true })
  const m = run(["--phase", "build-status"], 1024)
  const m50 = new Set(parsed.slice(0, 50).map((e) => e.sourcePath)).size
  check(`a minified queue is still read (${m50} modules of its 50 entries)`, m.status === 0 && JSON.parse(readFileSync(statusFile, "utf8")).modules === m50, (m.stdout + m.stderr).slice(-300))
  writeFileSync(qfile, "[]")
  const e = run(["--phase", "build-status"], 1024)
  check("an empty queue is read as no entries", e.status === 0 && /queue exists: .* \(0 entries\)/.test(e.stdout), (e.stdout + e.stderr).slice(-300))
  // a queue cut off in the middle (a full disk, a killed job) is refused, never read as the entries before the cut
  writeFileSync(qfile, text.slice(0, Math.floor(text.length / 2)))
  const cut = run(["--phase", "build-status"], 1024)
  check("a queue cut off in the middle is refused, not half-read", cut.status !== 0 && /ends before its closing \]|not the start of an entry/.test(cut.stdout + cut.stderr), `${cut.status} ${(cut.stdout + cut.stderr).slice(-300)}`)
  writeFileSync(qfile, text + "\n[]")
  const extra = run(["--phase", "build-status"], 1024)
  check("text after the closing ] is refused", extra.status !== 0 && /text after the closing \]/.test(extra.stdout + extra.stderr), `${extra.status} ${(extra.stdout + extra.stderr).slice(-300)}`)
}

rmSync(tmp, { recursive: true, force: true })
if (bad) {
  console.log(`${bad} FAILED`)
  process.exit(1)
}
console.log("all seed-memory checks passed")
