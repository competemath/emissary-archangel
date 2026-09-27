// Send banked records to the tree as content PRs. All of a library's pending data/bank/<key>/*.jsonl (the cloud
// translation's output, scripts/translate-finish.mjs) are pooled and sent as PRs of at most --batch records: each a per-PR staging file
// data/staging/<key>/<batch>.jsonl on a fresh branch of the tree, signed off, queued with auto-merge — the same PR
// the app opens in PR mode (lib/tengoku-pr.ts). Records whose names are already on the tree's main are dropped.
// A sent bank file moves to data/bank/<key>/sent/, with <file>.prs.json listing its PRs.
//
//   GH_TOKEN=<a token that can push branches and open PRs on the tree> node scripts/bank-flush.mjs
//        [--repo competemath/tengoku] [--batch 500] [--key <key>] [--dry-run]
// The commits are authored and signed off by the token's own account (its GitHub noreply address).
import { execFileSync } from "node:child_process"
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, renameSync, rmSync, writeFileSync } from "node:fs"
import os from "node:os"
import { join } from "node:path"

const argv = process.argv.slice(2)
const opt = (n, d = null) => (argv.includes(`--${n}`) ? argv[argv.indexOf(`--${n}`) + 1] : d)
const REPO = opt("repo", "competemath/tengoku")
const BATCH = Number(opt("batch", "500"))
const ONLY = opt("key")
const DRY = argv.includes("--dry-run")
const ROOT = new URL("..", import.meta.url).pathname
const BANK = join(ROOT, "data", "bank")
const sh = (cmd, args, cwd) => execFileSync(cmd, args, { cwd, encoding: "utf8", maxBuffer: 256 * 1024 * 1024 }).trim()
const token = process.env.GH_TOKEN
if (!token && !DRY) {
  console.log("bank-flush: no GH_TOKEN — nothing sent (the bank stays committed until a token exists)")
  process.exit(0)
}

const keys = existsSync(BANK) ? readdirSync(BANK).filter((k) => (!ONLY || k === ONLY) && existsSync(join(BANK, k))) : []
const pending = keys
  .map((k) => ({ key: k, files: readdirSync(join(BANK, k)).filter((f) => f.endsWith(".jsonl")).sort() }))
  .filter((p) => p.files.length)
if (!pending.length) {
  console.log("bank-flush: nothing banked")
  process.exit(0)
}

// the tree's main: only the names (staging and trusted), for the duplicate check
const tree = mkdtempSync(join(os.tmpdir(), "tengoku-flush-"))
const remote = token ? `https://x-access-token:${token}@github.com/${REPO}.git` : `https://github.com/${REPO}.git`
sh("git", ["clone", "-q", "--filter=blob:none", "--no-checkout", remote, tree])
sh("git", ["-C", tree, "sparse-checkout", "set", "--no-cone", ...keys.flatMap((k) => [`data/staging/${k}.jsonl`, `data/staging/${k}/`, `data/trusted/${k}.jsonl`])])
sh("git", ["-C", tree, "checkout", "-q", "main"])
const onMain = (key) => {
  const names = new Set()
  const files = [join(tree, "data", "staging", `${key}.jsonl`), join(tree, "data", "trusted", `${key}.jsonl`)]
  if (existsSync(join(tree, "data", "staging", key))) for (const f of readdirSync(join(tree, "data", "staging", key))) files.push(join(tree, "data", "staging", key, f))
  for (const f of files) {
    if (!existsSync(f) || !f.endsWith(".jsonl")) continue
    for (const l of readFileSync(f, "utf8").split("\n")) if (l.trim()) try { names.add(JSON.parse(l).name) } catch { /* the gate's problem */ }
  }
  return names
}

let who = { name: "emissary-archangel", email: "emissary-archangel@users.noreply.github.com" }
if (token) {
  const u = JSON.parse(sh("gh", ["api", "user"]))
  who = { name: u.login, email: `${u.id}+${u.login}@users.noreply.github.com` }
}
const git = (...a) => sh("git", ["-C", tree, "-c", `user.name=${who.name}`, "-c", `user.email=${who.email}`, ...a])

const stamp = new Date().toISOString().replace(/[-:]/g, "").replace(/\.\d+Z$/, "Z")
for (const { key, files } of pending) {
  const have = onMain(key)
  const records = files.flatMap((f) => readFileSync(join(BANK, key, f), "utf8").split("\n").filter((l) => l.trim()))
  const seen = new Set()
  const fresh = records.filter((l) => {
    const n = JSON.parse(l).name
    if (have.has(n) || seen.has(n)) return false
    seen.add(n)
    return true
  })
  const prs = []
  for (let i = 0; i < fresh.length; i += BATCH) {
    const batch = fresh.slice(i, i + BATCH)
    const id = `${stamp}-${String(i / BATCH).padStart(3, "0")}`
    const branch = `bank/${key}/${id}`
    const title = `Stage ${key}: ${batch.length} record${batch.length === 1 ? "" : "s"} (${id})`
    const body = `Banked by Emissary-Archangel's cloud translation (runs ${files.map((f) => f.replace(/\.jsonl$/, "")).join(", ")}). One per-PR staging file; the merge queue compiles exactly these records.`
    if (DRY) {
      console.log(`[dry-run] ${title}`)
      continue
    }
    git("switch", "-q", "-C", branch, "origin/main")
    const rel = join("data", "staging", key, `${id}.jsonl`)
    mkdirSync(join(tree, "data", "staging", key), { recursive: true })
    writeFileSync(join(tree, rel), batch.join("\n") + "\n")
    git("add", "--sparse", "--", rel)
    git("commit", "-q", "-s", "-m", `${title}\n\n${body}`)
    git("push", "-q", "-f", "origin", branch)
    const url = sh("gh", ["pr", "create", "-R", REPO, "--head", branch, "--title", title, "--body", body]).split("\n").pop()
    try {
      sh("gh", ["pr", "merge", url, "-R", REPO, "--auto"])
    } catch (e) {
      console.log(`  (auto-merge not enabled for ${url}: ${String(e.message).split("\n")[0]})`)
    }
    prs.push(url)
    console.log(`${title}: ${url}`)
  }
  if (DRY) continue
  mkdirSync(join(BANK, key, "sent"), { recursive: true })
  for (const f of files) renameSync(join(BANK, key, f), join(BANK, key, "sent", f))
  writeFileSync(join(BANK, key, "sent", `${stamp}.prs.json`), JSON.stringify({ files, records: records.length, duplicates: records.length - fresh.length, prs }, null, 2) + "\n")
  console.log(`${key}: ${fresh.length} of ${records.length} records from ${files.length} bank file(s) sent in ${prs.length} PR(s)`)
}
rmSync(tree, { recursive: true, force: true })
