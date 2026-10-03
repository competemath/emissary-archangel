#!/usr/bin/env node
// Download a library's machine exports (.ndjson, .names.json) from the release archive its setup.ci.json names, check
// the archive against its sha256 and unpack it into data/exports/<key>/. Libraries set up across runners
// (.github/workflows/setup-sharded.yml) keep these exports in a release, not in git; the bridge does the same the
// first time a translation needs the library. Idempotent: a marker records which archive is unpacked.
//   node scripts/fetch-exports.mjs <key> [--force] [--modules FILE]
// --modules FILE (module names, one per line or comma separated): unpack only those modules' files. A shard of a library bumped across
// runners (.github/workflows/bump-shard.yml) needs the exports of its own targets and nothing else: the archive is read once, only
// those files are written (lean-pool's exports are 19 GB unpacked).
import { execFileSync } from "node:child_process"
import { createHash } from "node:crypto"
import { createReadStream, existsSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { dirname, join, resolve } from "node:path"
import { fileURLToPath } from "node:url"

const APP_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..")
const key = process.argv[2]
if (!key || key.startsWith("--")) {
  console.error("usage: node scripts/fetch-exports.mjs <key> [--force]")
  process.exit(2)
}
const dir = join(process.env.GATE2_EXPORTS_DIR || join(APP_ROOT, "data", "exports"), key)
const recPath = join(dir, "setup.ci.json")
if (!existsSync(recPath)) {
  console.error(`${recPath} does not exist: ${key} has no runner setup record`)
  process.exit(1)
}
const a = JSON.parse(readFileSync(recPath, "utf8")).archive
if (!a?.sha256) {
  console.log(`${key} keeps its exports in git: nothing to download`)
  process.exit(0)
}
const modIdx = process.argv.indexOf("--modules")
const only = modIdx > 0 ? readFileSync(process.argv[modIdx + 1], "utf8").split(/[\n,]+/).map((x) => x.trim()).filter(Boolean) : null
const marker = join(dir, `.archive-${a.sha256.slice(0, 16)}`)
if (existsSync(marker) && !process.argv.includes("--force")) {
  console.log(`${key}: ${a.asset} is already unpacked`)
  process.exit(0)
}
const urls = a.parts?.length ? a.parts.map((p) => p.url) : [a.url]
const tmp = join(dir, `.archive-download-${process.pid}`)
const sha256 = (p) =>
  new Promise((res, rej) => {
    const h = createHash("sha256")
    createReadStream(p).on("data", (d) => h.update(d)).on("end", () => res(h.digest("hex"))).on("error", rej)
  })
try {
  rmSync(tmp, { force: true })
  console.log(`${key}: downloading ${a.asset} (${(a.bytes / 1048576).toFixed(0)} MB${urls.length > 1 ? `, ${urls.length} parts` : ""})`)
  for (const u of urls) execFileSync("sh", ["-c", 'curl -fL --retry 3 --progress-bar "$1" >> "$2"', "sh", u, tmp], { stdio: "inherit" })
  const got = await sha256(tmp)
  if (got !== a.sha256) throw new Error(`the download's sha256 is ${got}, the record says ${a.sha256}`)
  if (only) {
    // the members' names (with or without a leading ./): the files of the wanted modules, under either spelling of a module name
    const members = new Set(execFileSync("tar", ["--zstd", "-tf", tmp], { maxBuffer: 1 << 30 }).toString().split("\n").filter(Boolean))
    const wanted = []
    for (const m of only) {
      for (const name of new Set([m, m.replace(/[«»]/g, "")])) {
        for (const f of [`${name}.ndjson`, `${name}.names.json`]) for (const c of [f, `./${f}`]) if (members.has(c)) wanted.push(c)
      }
    }
    const listFile = `${tmp}.list`
    writeFileSync(listFile, wanted.join("\n") + "\n")
    if (wanted.length) execFileSync("tar", ["--zstd", "-xf", tmp, "-C", dir, "-T", listFile], { stdio: "inherit" })
    rmSync(listFile, { force: true })
    console.log(`${key}: unpacked ${wanted.length} files of ${only.length} modules into ${dir}`)
  } else {
    execFileSync("tar", ["--zstd", "-xf", tmp, "-C", dir], { stdio: "inherit" })
    writeFileSync(marker, `${a.asset}\n`)
    console.log(`${key}: unpacked ${a.files} files into ${dir}`)
  }
} finally {
  rmSync(tmp, { force: true })
}
