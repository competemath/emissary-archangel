// pinned-deps.mjs — a dependency pinned to a commit that no branch holds any more is fetched by its hash, so that Lake can check it out.
//
// padic-l-functions (2026-11-07, setup run 42383040195): its lake-manifest.json pins CBirkbeck/LeanModularForms at 512911ce. GitHub still serves that commit (the API
// returns it), but no branch holds it, so the clone Lake makes does not have it: "LeanModularForms: checking out revision '512911ce…'", then "fatal: unable to read tree
// (512911ce…)", and every build of the library failed. GitHub lets a fetch name a commit by its hash; this reads the package and the commit from Lake's own lines, fetches
// that commit into the clone Lake made, and the caller runs Lake again. Nothing else is touched: a dependency Lake can check out is never fetched here.

import { execFileSync } from "node:child_process"
import { existsSync, readFileSync } from "node:fs"
import { join } from "node:path"

const CHECKOUT = /^info: (?<pkg>[^\s:]+): checking out revision '(?<rev>[0-9a-f]{40})'/gm
const UNREADABLE = /fatal: unable to read tree \(?(?<rev>[0-9a-f]{40})\)?/g

// The packages Lake could not check out: [{pkg, rev}], from Lake's output (each package once).
export function unreadablePins(output) {
  const bad = new Set([...output.matchAll(UNREADABLE)].map((m) => m.groups.rev))
  const seen = new Map()
  for (const m of output.matchAll(CHECKOUT)) if (bad.has(m.groups.rev) && !seen.has(m.groups.pkg)) seen.set(m.groups.pkg, m.groups.rev)
  return [...seen].map(([pkg, rev]) => ({ pkg, rev }))
}

// Where Lake keeps the packages of `repo` (lake-manifest.json `packagesDir`, `.lake/packages` by default).
export function packagesDir(repo) {
  const f = join(repo, "lake-manifest.json")
  if (!existsSync(f)) return join(repo, ".lake", "packages")
  try {
    return join(repo, JSON.parse(readFileSync(f, "utf8")).packagesDir || ".lake/packages")
  } catch {
    return join(repo, ".lake", "packages")
  }
}

const gitDefault = (args, cwd) => execFileSync("git", args, { cwd, stdio: ["ignore", "pipe", "pipe"], timeout: 30 * 60 * 1000 })

function hasCommit(git, dir, rev) {
  try {
    git(["cat-file", "-e", `${rev}^{commit}`], dir)
    return true
  } catch {
    return false
  }
}

// Fetches each unreadable pin of `output` by its hash into the package's clone. Returns {fetched, failed}: fetched = the pins that are now in the clone (run Lake again),
// failed = [{pkg, rev, why}] (no clone to fetch into, or the remote refused the hash).
export function repairPins(repo, output, { git = gitDefault, log = () => {} } = {}) {
  const fetched = []
  const failed = []
  for (const { pkg, rev } of unreadablePins(output)) {
    const dir = join(packagesDir(repo), pkg)
    if (!existsSync(join(dir, ".git"))) {
      failed.push({ pkg, rev, why: `no clone at ${dir}` })
      continue
    }
    if (!hasCommit(git, dir, rev)) {
      try {
        git(["fetch", "--quiet", "origin", rev], dir)
      } catch (e) {
        failed.push({ pkg, rev, why: `the remote refused the commit: ${String(e.stderr || e.message).trim().slice(-200)}` })
        continue
      }
    }
    if (hasCommit(git, dir, rev)) {
      log(`dependency ${pkg}: commit ${rev.slice(0, 12)} is on no branch of its repository; fetched it by its hash`)
      fetched.push({ pkg, rev })
    } else failed.push({ pkg, rev, why: "fetched, but the commit is still not in the clone" })
  }
  return { fetched, failed }
}
