#!/usr/bin/env node
// Re-export each module of a set-up source WITH the Mathlib constants its statements reach (lean4export without --only-listed).
//
//   node scripts/attest/export-full.mjs --key fate-x --toolchain leanprover/lean4:v4.28.0 --repo infra/fate-x/repo --names data/exports/fate-x --out data/exports-full [--concurrency 3]
//
// setup-source.mjs exports the library's OWN constants only (--only-listed), which is right for a translation, where the translator keeps the original's names. For a
// statement attestation it left Gate 2 unable to read an original whose statement mentions an instance the tree has since renamed (`Monoid.toNatPow`,
// `MvPolynomial.instCommRingMvPolynomial`, `algebraMap`: 33 of the 49 refusals of the first run). With those constants in the export, Gate 2 replays them (it follows a statement through
// definitions and instances, never through proofs) and the kernel decides whether the two statements are the same under them. Needs the build setup-source.mjs leaves
// with --keep-build, and the lean4export it built for this toolchain.
import { spawn } from "node:child_process"
import { closeSync, existsSync, mkdirSync, openSync, readFileSync, readdirSync, renameSync, rmSync, statSync } from "node:fs"
import { join, resolve } from "node:path"

const argv = process.argv.slice(2)
const opt = (n, d = null) => (argv.includes(`--${n}`) ? argv[argv.indexOf(`--${n}`) + 1] : d)
const need = (n) => opt(n) ?? (console.error(`export-full: --${n} is required`), process.exit(2))
const toolchain = need("toolchain")
const repo = resolve(need("repo"))
const namesDir = resolve(need("names"))
const outDir = resolve(need("out"))
const concurrency = Math.max(1, Number(opt("concurrency", "3")))
const slug = toolchain.replace(/[^A-Za-z0-9.-]+/g, "_") // setup-source.mjs TC_SLUG
const l4e = resolve("infra", "lean4export", slug, ".lake", "build", "bin", "lean4export")
if (!existsSync(l4e)) (console.error(`export-full: no lean4export at ${l4e}`), process.exit(1))
mkdirSync(outDir, { recursive: true })

const modules = readdirSync(namesDir).filter((f) => f.endsWith(".names.json")).map((f) => f.replace(/\.names\.json$/, "")).sort()
console.log(`export-full: ${modules.length} modules`)
let next = 0
let failed = 0
const one = (m) =>
  new Promise((done) => {
    const names = JSON.parse(readFileSync(join(namesDir, `${m}.names.json`), "utf8")).names
    const tmp = join(outDir, `${m}.ndjson.tmp`)
    const fd = openSync(tmp, "w")
    // spawn, not execFile: the export is tens of megabytes and goes straight to the file, never through a buffer
    const p = spawn("lake", ["env", l4e, m, "--", ...names], { cwd: repo, stdio: ["ignore", fd, "pipe"] })
    let err = ""
    p.stderr.on("data", (d) => (err = (err + d).slice(-400)))
    const timer = setTimeout(() => p.kill("SIGKILL"), 30 * 60 * 1000)
    p.on("close", (code) => {
      clearTimeout(timer)
      closeSync(fd)
      if (code === 0 && statSync(tmp).size > 0) {
        renameSync(tmp, join(outDir, `${m}.ndjson`))
        console.log(`export-full: ${m} ${Math.round(statSync(join(outDir, `${m}.ndjson`)).size / 1024)} KB`)
      } else {
        failed++
        rmSync(tmp, { force: true })
        console.log(`export-full: ${m} FAILED (${code}) ${err.replace(/\s+/g, " ")}`)
      }
      done()
    })
  })
await Promise.all(Array.from({ length: concurrency }, async () => { while (next < modules.length) await one(modules[next++]) }))
console.log(`export-full: ${modules.length - failed}/${modules.length} exported, ${failed} failed`)
process.exit(failed ? 1 : 0)
