// node scripts/test-setup-seed-roots.mjs — the seed step keeps the records of a root that is one file at the top of the repository, and a seed that keeps nothing stops.
//
// The real case: PrimeGaps186.lean, LongGapsBetweenPrimes.lean and ten-proofs' MetricCodes.lean (and nine more) sit at the top of their repositories. The check compared
// `PrimeGaps186.lean` with the root `PrimeGaps186`, every record fell outside the roots, and setup-source reported success with 0 modules: 21,971 records of three libraries,
// and 13,326 of classfieldtheory-yamaguchi for a layout reason, gone without a word until 8 Nov 2026 (setup runs 42494622728, 42494610153, 42494615922).
// Cases: fixtures/real-seed-paths.json.gz, every source path of the records of 152 libraries of the registry (36,674 paths, 509,833 records), then real seeds of a throwaway
// repository of each layout. Invariants: nothing the old rule kept is lost; the rule differs from the old one only on a top-level file whose name is a root; a top-level file
// that is not a root stays out; a seed with every record outside the roots exits non-zero, names what the paths start with and leaves no queue; a partial seed still passes.
import { execFileSync, spawnSync } from "node:child_process"
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import os from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { gunzipSync } from "node:zlib"
import { rootOfRepoPath } from "./setup-tools.mjs"

const here = dirname(fileURLToPath(import.meta.url))
const tmp = mkdtempSync(join(os.tmpdir(), "seed-roots-"))
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) {
    bad++
    console.log("FAIL", name, detail ?? "")
  } else console.log("ok", name)
}

// 1. the rule against every real path
const real = JSON.parse(gunzipSync(readFileSync(join(here, "bump", "tests", "fixtures", "real-seed-paths.json.gz"))).toString())
const oldKept = (roots, p) => roots.has(p.split("/")[0])
let paths = 0
let records = 0
let lost = 0
let changedElsewhere = 0
let keptOld = 0
const recovered = {}
const topNotRoot = new Set()
for (const [key, { roots: list, paths: byPath }] of Object.entries(real)) {
  const roots = new Set(list)
  for (const [p, n] of Object.entries(byPath)) {
    paths++
    records += n
    const was = oldKept(roots, p)
    const now = roots.has(rootOfRepoPath(p))
    if (was) keptOld += n
    if (was && !now) lost++
    if (now !== was) {
      if (p.includes("/") || !p.endsWith(".lean") || !roots.has(p.slice(0, -5))) changedElsewhere++
      recovered[key] = (recovered[key] || 0) + n
    }
    if (!p.includes("/") && !now) topNotRoot.add(p)
    if (p.includes("/") && rootOfRepoPath(p) !== p.split("/")[0]) changedElsewhere++
  }
}
check(`real paths read: ${paths} of ${records} records in ${Object.keys(real).length} libraries`, paths === 36674 && records === 509833 && Object.keys(real).length === 152, `${paths} ${records}`)
check(`nothing the old rule kept is lost (${keptOld} records)`, lost === 0, `${lost}`)
check("the rule differs from the old one only on a top-level file named after a root", changedElsewhere === 0, `${changedElsewhere}`)
check("the single-file libraries get all their records back", recovered["ten-proofs"] === 18223 && recovered["prime-gaps-186"] === 3504 && recovered["long-gaps-between-primes"] === 244, JSON.stringify(recovered))
check("classfieldtheory-yamaguchi (under Lean4/) is not touched by this rule", !recovered["classfieldtheory-yamaguchi"], JSON.stringify(recovered))
console.log(`  top-level files that are no root stay out: ${topNotRoot.size}; libraries gaining records: ${Object.keys(recovered).length}`)
for (const [p, want] of [["A.lean", "A"], ["A/B.lean", "A"], ["A.lean/B.lean", "A.lean"], ["A", "A"], ["A.lean.lean", "A.lean"], [".lean", ""], ["Lean4/A/B.lean", "Lean4"]])
  check(`rootOfRepoPath(${p}) = ${want}`, rootOfRepoPath(p) === want, rootOfRepoPath(p))

// 2. real seeds: one repository, three kinds of record
const sh = (cmd, args, opts = {}) => execFileSync(cmd, args, { stdio: ["ignore", "pipe", "pipe"], maxBuffer: 1 << 26, ...opts }).toString()
const TC = "leanprover/lean4:v4.0.0"
const lib = join(tmp, "lib-src")
mkdirSync(join(lib, "Sub"), { recursive: true })
mkdirSync(join(lib, "Lean4", "Deep"), { recursive: true })
writeFileSync(join(lib, "lean-toolchain"), TC + "\n")
writeFileSync(join(lib, "Single.lean"), "theorem t0 : 0 = 0 := rfl\n\ntheorem t1 : 1 = 1 := rfl\n")
writeFileSync(join(lib, "Other.lean"), "theorem o0 : 0 = 0 := rfl\n")
writeFileSync(join(lib, "Sub", "F.lean"), "theorem s0 : 0 = 0 := rfl\n")
writeFileSync(join(lib, "Lean4", "Deep", "G.lean"), "theorem g0 : 0 = 0 := rfl\n")
const git = (...a) => sh("git", ["-c", "user.name=t", "-c", "user.email=t@t", ...a], { cwd: lib })
git("init", "-q")
git("add", ".")
git("commit", "-q", "-m", "lib")
const commit = git("rev-parse", "HEAD").trim()
const rec = (name, path, line) => ({ name, statement: `theorem ${name} : 0 = 0`, proof: ":= rfl", status: "tentative", library: "t", source_url: `https://github.com/o/lib/blob/${commit}/${path}#L${line}` })
const root = join(tmp, "root")
mkdirSync(join(root, "scripts"), { recursive: true })
mkdirSync(join(root, "data"), { recursive: true })
for (const f of ["setup-source.mjs", "setup-tools.mjs", "bisect.mjs", "memory-rules.mjs", "pinned-deps.mjs"]) cpSync(join(here, f), join(root, "scripts", f))
mkdirSync(join(root, "scripts", "bump"), { recursive: true })
cpSync(join(here, "bump", "link_srcdir.py"), join(root, "scripts", "bump", "link_srcdir.py"))
const tent = join(tmp, "tentative")
mkdirSync(tent)
const home = join(tmp, "home")
mkdirSync(join(home, ".elan", "bin"), { recursive: true })
writeFileSync(join(home, ".elan", "bin", "elan"), `#!/bin/sh\necho "${TC} (default)"\n`)
sh("chmod", ["+x", join(home, ".elan", "bin", "elan")])
const seed = (roots, recs, extra = {}) => {
  writeFileSync(join(root, "sources.json"), JSON.stringify({ sources: { t: { repo: lib, commit, toolchain: TC, roots, ...extra } } }))
  writeFileSync(join(tent, "t.jsonl"), recs.map((r) => JSON.stringify(r)).join("\n") + "\n")
  rmSync(join(root, "data", "queue-t.json"), { force: true })
  const r = spawnSync("node", [join(root, "scripts", "setup-source.mjs"), "t", "--only", "seed"], { env: { ...process.env, HOME: home, EMISSARY_TENTATIVE_DIR: tent }, encoding: "utf8", maxBuffer: 1 << 26 })
  const q = join(root, "data", "queue-t.json")
  return { code: r.status, out: (r.stdout || "") + (r.stderr || ""), queue: existsSync(q) ? JSON.parse(readFileSync(q, "utf8")) : null }
}
const single = seed(["Single"], [rec("t0", "Single.lean", 1), rec("t1", "Single.lean", 3)])
check("a root that is one top-level file: every record is seeded", single.code === 0 && single.queue?.length === 2, single.out.slice(-400))
check("its entries read the file at the top of the repository", single.queue?.every((e) => e.sourcePath === "Single.lean"), JSON.stringify(single.queue?.[0]))
const mixed = seed(["Single", "Sub"], [rec("t0", "Single.lean", 1), rec("s0", "Sub/F.lean", 1), rec("o0", "Other.lean", 1)])
check("a top-level file that is no root stays out, the others are kept, the seed passes", mixed.code === 0 && mixed.queue?.map((e) => e.sourcePath).sort().join() === "Single.lean,Sub/F.lean" && /"skippedRoot":1/.test(mixed.out), mixed.out.slice(-400))
const none = seed(["Single"], [rec("g0", "Lean4/Deep/G.lean", 1), rec("o0", "Other.lean", 1)])
check("every record outside the roots: the setup stops", none.code !== 0, none.out.slice(-400))
check("the message names the roots and what the paths start with", /none of the 2 records was kept \(outside the roots Single: 2/.test(none.out) && /Lean4 \(1\)/.test(none.out) && /Other\.lean \(1\)/.test(none.out), none.out.slice(-400))
check("no empty queue is left for the next run to keep", none.queue === null)
const noFile = seed(["Single"], [rec("t0", "Single/Gone.lean", 1)])
check("every record names a file the repository does not have: the setup stops and says so", noFile.code !== 0 && /none of the 1 records was kept/.test(noFile.out) && /no file: 1/.test(noFile.out) && noFile.queue === null, noFile.out.slice(-400))
const badUrl = seed(["Single"], [{ ...rec("t0", "Single.lean", 1), source_url: "https://example.org/not-a-blob" }])
check("every record has a link that is no repository link: the setup stops", badUrl.code !== 0 && /none of the 1 records was kept/.test(badUrl.out) && badUrl.queue === null, badUrl.out.slice(-400))
// a source folder (classfieldtheory-yamaguchi's Lean4/): the record's path is read from inside it, the root is linked at the top
const inFolder = seed(["Deep"], [rec("g0", "Lean4/Deep/G.lean", 1)], { srcdir: "Lean4" })
check("a source folder: the record is seeded under its module's own path", inFolder.code === 0 && inFolder.queue?.[0]?.sourcePath === "Deep/G.lean", inFolder.out.slice(-500))
check("a source folder: the setup says what it linked", /t: linked at the top of the project: Deep/.test(inFolder.out), inFolder.out.slice(-500))
const twoRuns = seed(["Deep"], [rec("g0", "Lean4/Deep/G.lean", 1)], { srcdir: "Lean4" })
check("a source folder: a second run over the same clone passes", twoRuns.code === 0 && twoRuns.queue?.length === 1, twoRuns.out.slice(-500))
const wrongFolder = seed(["Deep"], [rec("g0", "Lean4/Deep/G.lean", 1)], { srcdir: "Nope" })
check("a source folder the repository does not have: the setup stops", wrongFolder.code !== 0 && /not a folder of the project/.test(wrongFolder.out), wrongFolder.out.slice(-500))
rmSync(join(root, "infra"), { recursive: true, force: true })
// a list of source folders (aintlib): each record is read from inside its own, and of two that overlap the longest wins: an unsorted resolver would read Lean4/Deep/G.lean as Deep/G.lean
const inList = seed(["G"], [rec("g0", "Lean4/Deep/G.lean", 1)], { srcdir: ["Lean4", "Lean4/Deep"] })
check("a list of source folders: of two that overlap, the longest gives the module's path", inList.code === 0 && inList.queue?.[0]?.sourcePath === "G.lean", inList.out.slice(-500))
rmSync(join(root, "infra"), { recursive: true, force: true })
const empty = seed(["Single"], [])
check("a library with no records at all is not that error", empty.code === 0 && empty.queue?.length === 0, empty.out.slice(-400))

rmSync(tmp, { recursive: true, force: true })
if (bad) {
  console.log(`${bad} check(s) FAILED`)
  process.exit(1)
}
console.log("all seed-root checks passed")
