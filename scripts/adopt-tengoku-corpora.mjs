#!/usr/bin/env node
// node scripts/adopt-tengoku-corpora.mjs [--dry-run] [--tengoku-sources FILE] [--toolchain KEY=TOOLCHAIN]...
//
// A library is registered in one place: tengoku's schemas/sources.json (`corpora`), in a tooling PR anyone can
// open. This adopts every registered library Emissary does not know yet: its entry in sources.json (repo, commit,
// roots, the Lake project's `subdir`, the toolchain read from the library's own lean-toolchain at that commit, the
// licence tengoku records for it). Prints one line per adopted key ("adopted <key> <toolchain> <tengoku PR or ->")
// for the workflow, which commits sources.json, starts the setup and tells the registering PR.
// A library whose toolchain cannot be read yet is skipped and retried on the next run. The legacy corpus
// (equational-theories) is Emissary's own. --tengoku-sources and --toolchain replace the network (tests).

import { execFileSync } from "node:child_process"
import { readFileSync, writeFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const ROOT = join(dirname(fileURLToPath(import.meta.url)), "..")
const args = process.argv.slice(2)
const DRY = args.includes("--dry-run")
const opt = (name) => {
  const i = args.indexOf(name)
  return i >= 0 ? args[i + 1] : null
}
const toolchainOverride = Object.fromEntries(
  args.flatMap((a, i) => (a === "--toolchain" ? [args[i + 1].split("=", 2)] : [])),
)
const TENGOKU = "competemath/tengoku"

async function tengokuSources() {
  const file = opt("--tengoku-sources")
  if (file) return JSON.parse(readFileSync(file, "utf8"))
  const res = await fetch(`https://raw.githubusercontent.com/${TENGOKU}/main/schemas/sources.json`)
  if (!res.ok) throw new Error(`tengoku sources.json: HTTP ${res.status}`)
  return res.json()
}

async function toolchainOf(key, c) {
  if (toolchainOverride[key]) return toolchainOverride[key]
  const m = String(c.repo).match(/^https:\/\/github\.com\/([^/]+\/[^/.]+)(?:\.git)?\/?$/)
  if (!m) return null
  const path = [c.path, "lean-toolchain"].filter(Boolean).join("/")
  const res = await fetch(`https://raw.githubusercontent.com/${m[1]}/${c.commit}/${path}`)
  if (!res.ok) return null
  const t = (await res.text()).trim()
  return /^leanprover\/lean4:\S+$/.test(t) ? t : null
}

// The tengoku PR that registered a key: the oldest commit of schemas/sources.json that added it (squash subject "(#N)").
function registeringPr(key) {
  if (opt("--tengoku-sources")) return null
  try {
    const dir = execFileSync("mktemp", ["-d"], { encoding: "utf8" }).trim()
    execFileSync("git", ["clone", "-q", "--filter=blob:none", "--no-checkout", `https://github.com/${TENGOKU}.git`, dir])
    const log = execFileSync("git", ["-C", dir, "log", "--format=%s", "-S", `"${key}":`, "--", "schemas/sources.json"], { encoding: "utf8" })
    const found = [...log.matchAll(/\(#(\d+)\)\s*$/gm)].map((m) => m[1])
    return found.length ? found[found.length - 1] : null
  } catch {
    return null
  }
}

function licenceOf(repo, licences) {
  const best = Object.keys(licences || {})
    .filter((p) => String(repo).startsWith(p) || String(p).startsWith(String(repo)))
    .sort((a, b) => b.length - a.length)[0]
  return best ? licences[best] : null
}

const registry = JSON.parse(readFileSync(join(ROOT, "sources.json"), "utf8"))
const tengoku = await tengokuSources()
const adopted = []
for (const [key, c] of Object.entries(tengoku.corpora || {})) {
  if (registry.sources[key] || c.generator === "legacy") continue
  if (!c.repo || !c.commit || !Array.isArray(c.roots) || !c.roots.length) {
    console.error(`skip ${key}: tengoku's entry lacks repo, commit or roots`)
    continue
  }
  const toolchain = await toolchainOf(key, c)
  if (!toolchain) {
    console.error(`skip ${key}: no lean-toolchain readable at ${c.repo}@${c.commit}${c.path ? ` (${c.path})` : ""}; retried next run`)
    continue
  }
  const entry = { label: key, repo: c.repo, commit: c.commit, toolchain, roots: c.roots }
  if (c.path) entry.subdir = c.path
  const licence = licenceOf(c.repo, tengoku.licences)
  if (licence) entry.licence = licence
  registry.sources[key] = entry
  adopted.push([key, toolchain, registeringPr(key) || "-"])
}
if (adopted.length && !DRY) writeFileSync(join(ROOT, "sources.json"), JSON.stringify(registry, null, 2) + "\n")
for (const [key, toolchain, pr] of adopted) console.log(`adopted ${key} ${toolchain} ${pr}`)
if (!adopted.length) console.error("every library registered in tengoku is known here")
