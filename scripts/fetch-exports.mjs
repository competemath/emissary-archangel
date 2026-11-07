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
const mineRecord = JSON.parse(readFileSync(recPath, "utf8"))
let a = mineRecord.archive
// The record in this checkout can be older than the archive it names: a setup round that republishes the library's archive (the same asset name, new bytes and a new sha256) while a long run is in flight
// leaves the run's checkout pointing at an archive that no longer exists (flt-anthropic, 6 Nov 2026: the shards of a pilot that started after the 86's export round republished the archive all failed with
// "the download's sha256 is c335..., the record says bcbf..."). So the current record of the default branch is read first (EMISSARY_RECORD_URL, or GITHUB_REPOSITORY's main); when it names another archive, that
// one is used, but only when it is the record of the SAME library commit (a re-pin on main must never replace the exports this checkout is pinned to). Unreachable or unreadable: the checkout's own record,
// as before. The lookup retries as the download does (--retry 8 --retry-delay 15: a minute's outage of raw.githubusercontent.com must not leave the stale record in use).
function currentArchive(mine) {
  const url = process.env.EMISSARY_RECORD_URL || (process.env.GITHUB_REPOSITORY ? `https://raw.githubusercontent.com/${process.env.GITHUB_REPOSITORY}/main/data/exports/${key}/setup.ci.json` : "")
  if (!url) return mine
  try {
    const rec = JSON.parse(execFileSync("curl", ["-fsSL", "--retry", "8", "--retry-delay", "15", "--max-time", "60", url], { stdio: ["ignore", "pipe", "ignore"], maxBuffer: 64 << 20 }).toString())
    const fresh = rec.archive
    if (fresh?.sha256 && fresh.sha256 !== mine?.sha256) {
      if (rec.commit !== mineRecord.commit) {
        console.log(`${key}: the current record is for library commit ${String(rec.commit).slice(0, 12)}, this checkout's for ${String(mineRecord.commit).slice(0, 12)}: not used`)
        return mine
      }
      console.log(`${key}: this checkout's record names ${mine?.sha256?.slice(0, 12)}, the current record ${fresh.sha256.slice(0, 12)}: the archive was republished; using the current one`)
      return fresh
    }
  } catch {
    /* unreachable or not a record: the checkout's own */
  }
  return mine
}
a = currentArchive(a)
if (!a?.sha256) {
  console.log(`${key} keeps its exports in git: nothing to download`)
  process.exit(0)
}
const modIdx = process.argv.indexOf("--modules")
const only = modIdx > 0 ? readFileSync(process.argv[modIdx + 1], "utf8").split(/[\n,]+/).map((x) => x.trim()).filter(Boolean) : null
// --names FILE (with --modules): the .names.json of these modules too, without their .ndjson. A shard's Gate 2 tells a module's own declarations from the ones it uses by the names
// of everything the module imports (gate2_batch.qualify), and those are the shard's build list, far more than its targets.
const namesIdx = process.argv.indexOf("--names")
const namesOnly = namesIdx > 0 ? readFileSync(process.argv[namesIdx + 1], "utf8").split(/[\n,]+/).map((x) => x.trim()).filter(Boolean) : []
const markerOf = (x) => join(dir, `.archive-${x.sha256.slice(0, 16)}`)
if (existsSync(markerOf(a)) && !process.argv.includes("--force")) {
  console.log(`${key}: ${a.asset} is already unpacked`)
  process.exit(0)
}
const tmp = join(dir, `.archive-download-${process.pid}`)
const sha256 = (p) =>
  new Promise((res, rej) => {
    const h = createHash("sha256")
    createReadStream(p).on("data", (d) => h.update(d)).on("end", () => res(h.digest("hex"))).on("error", rej)
  })
try {
  rmSync(tmp, { force: true })
  // each part into a file of its own, appended only once curl has succeeded: a transfer that dies half way must not leave its bytes in the archive. --retry 8 --retry-delay 15: curl retries 408, 429 and
  // 5xx (a 504 included) for about two minutes; the default, 3 retries 1, 2 and 4 seconds apart, gave up on a 504 that was gone a minute later and cost a bump shard its three hours of build.
  const part = `${tmp}.part`
  for (let attempt = 0; ; attempt++) {
    const urls = a.parts?.length ? a.parts.map((p) => p.url) : [a.url]
    console.log(`${key}: downloading ${a.asset} (${(a.bytes / 1048576).toFixed(0)} MB${urls.length > 1 ? `, ${urls.length} parts` : ""})`)
    for (const u of urls) {
      rmSync(part, { force: true })
      execFileSync("sh", ["-c", 'curl -fL --retry 8 --retry-delay 15 --progress-bar -o "$2" "$1"', "sh", u, part], { stdio: "inherit" })
      execFileSync("sh", ["-c", 'cat "$1" >> "$2"', "sh", part, tmp], { stdio: "inherit" })
      rmSync(part, { force: true })
    }
    const got = await sha256(tmp)
    if (got === a.sha256) break
    // the archive may have been republished between reading the record and downloading: read the record again, and when it names another archive, download that one (twice at most)
    const next = attempt < 2 ? currentArchive(a) : a
    if (next.sha256 === a.sha256) throw new Error(`the download's sha256 is ${got}, the record says ${a.sha256} (the archive may have been republished since the record was read; the current record could not be used to tell)`)
    a = next
    rmSync(tmp, { force: true })
  }
  if (only) {
    // the members' names (with or without a leading ./): the files of the wanted modules, under either spelling of a module name
    const members = new Set(execFileSync("tar", ["--zstd", "-tf", tmp], { maxBuffer: 1 << 30 }).toString().split("\n").filter(Boolean))
    const wanted = new Set()
    for (const [list, kinds] of [[only, [".ndjson", ".names.json"]], [namesOnly, [".names.json"]]]) {
      for (const m of list) {
        for (const name of new Set([m, m.replace(/[«»]/g, "")])) {
          for (const k of kinds) for (const c of [`${name}${k}`, `./${name}${k}`]) if (members.has(c)) wanted.add(c)
        }
      }
    }
    const listFile = `${tmp}.list`
    writeFileSync(listFile, [...wanted].join("\n") + "\n")
    if (wanted.size) execFileSync("tar", ["--zstd", "-xf", tmp, "-C", dir, "-T", listFile], { stdio: "inherit" })
    rmSync(listFile, { force: true })
    console.log(`${key}: unpacked ${wanted.size} files of ${only.length} modules (and the names of ${namesOnly.length}) into ${dir}`)
  } else {
    execFileSync("tar", ["--zstd", "-xf", tmp, "-C", dir], { stdio: "inherit" })
    writeFileSync(markerOf(a), `${a.asset}\n`)
    console.log(`${key}: unpacked ${a.files} files into ${dir}`)
  }
} finally {
  rmSync(tmp, { force: true })
  rmSync(`${tmp}.part`, { force: true })
}
