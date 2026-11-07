// node scripts/test-setup-seed-memory.mjs — the seed step keeps the files it reads within a budget, so a library of very large sources is seeded under Node's heap limit.
//
// The real case: leanbridge (7 Nov 2026) has 1.5 GB of Lean sources (LMFDB q-expansion tables, up to 53 MB a file) and 15 tentative files whose records come file by file
// (leanbridge-001: 1,645 records in 341 files, 340 changes of file). The seed step kept every file's lines for the whole run and Node died at its 4 GB heap in every phase
// ("Reached heap limit Allocation failed - JavaScript heap out of memory", setup runs 42386199526, 42387020776). Here a library of 12 files of 12 MB of non-Latin-1 text
// (two bytes a character in memory, as the LMFDB tables are) is seeded with Node's heap capped at 200 MB: more than the heap if every file is kept, about one file if not.
// Records have the real shape (keys of a leanbridge record). Invariants: the seed finishes under the cap with a small budget; the queue is byte for byte the one an unbounded
// cache gives (same entries, same order, same names and lines); with the records interleaved across files (the worst order) the queue is still the same.
import { execFileSync, spawnSync } from "node:child_process"
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
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

rmSync(tmp, { recursive: true, force: true })
if (bad) {
  console.log(`${bad} FAILED`)
  process.exit(1)
}
console.log("all seed-memory checks passed")
