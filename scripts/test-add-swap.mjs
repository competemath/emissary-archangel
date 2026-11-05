// node scripts/test-add-swap.mjs — scripts/add-swap.sh: the swap a big-memory round adds is what the disk can spare, never the whole 48 GB that took the space the earlier build needs.
// (flt-anthropic, 5 Nov 2026: the first retry added 48 GB of swap, then unpacked a 16.5 GB archive into a build of 50+ GB on a runner with 113 GB free: "No space left on device", four minutes in.)
// The script is run for real with df, sudo and free replaced by recorders, over 31 sampled free-space values from 0 to 200 GB (113 GB is what the real runner had after its disk was cleaned: the
// figure in the logs of the failed round) including the boundaries (7, 8 and 9 GB to spare), five maxima and three kept sizes, and the rules are checked:
//   1. the swap is min(MAX, free - KEEP) GB when the room (free - KEEP) is at least 8, else there is none and the script still exits 0 (nothing to add, nothing broken);
//   2. it never takes the space KEEP is for (free - size >= KEEP whenever there is swap);
//   3. the free space is read in bytes and rounded DOWN to whole GB (df -BG rounds up: up to 1 GB too much free space, a swap file 1 GB too big or one added with under 8 GB to spare);
//   4. a command that fails (fallocate, chmod, mkswap, swapon) removes the swap file and exits 1: the job stops, it does not go on as if the memory were there;
//   5. a malformed MAX or KEEP exits 2 and touches nothing; an unreadable df adds nothing and does not fail the job.
// Then the same cases run against broken versions of the script, and each must be caught.
import { chmodSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs"
import { spawnSync } from "node:child_process"
import { tmpdir } from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const real = readFileSync(join(here, "add-swap.sh"), "utf8")
let bad = 0
const check = (name, ok, detail) => { if (!ok) { bad++; console.log("FAIL", name, detail ?? "") } else console.log("ok", name) }
const GIB = 1073741824

const box = mkdtempSync(join(tmpdir(), "swap-"))
const calls = join(box, "calls")
const fake = (name, body) => { writeFileSync(join(box, name), `#!/bin/sh\n${body}\n`); chmodSync(join(box, name), 0o755) }
// df -B1 prints bytes (what the script reads); df -BG, which the broken version reads, rounds UP like the real one
fake("df", 'case "$1" in -B1) printf "Avail\\n%s\\n" "$FAKE_BYTES";; -BG) printf "Avail\\n%sG\\n" "$(( (FAKE_BYTES + 1073741823) / 1073741824 ))";; esac')
fake("sudo", 'echo "sudo $*" >> "$CALLS"; if [ -n "$FAIL_ON" ] && [ "$1" = "$FAIL_ON" ]; then exit 1; fi; exit 0')
fake("free", 'echo free >> "$CALLS"')
const run = (script, args, env = {}) => {
  writeFileSync(join(box, "add-swap.sh"), script)
  writeFileSync(calls, "")
  const r = spawnSync("sh", [join(box, "add-swap.sh"), ...args], { encoding: "utf8", timeout: 8000, killSignal: "SIGKILL", env: { PATH: `${box}:${process.env.PATH}`, CALLS: calls, FAKE_BYTES: String(113 * GIB), ...env } })
  const log = readFileSync(calls, "utf8")
  const m = log.match(/fallocate -l (\d+)G \/swapfile/)
  return { code: r.status, text: r.stdout + r.stderr, size: m ? Number(m[1]) : null, on: /swapon \/swapfile/.test(log), removed: /rm -f \/swapfile/.test(log), log }
}

function suite(script, print, full = true) {
  let cases = 0, wrong = 0
  const v = (what, detail) => { wrong++; if (print && wrong <= 6) console.log("FAIL", what, JSON.stringify(detail)) }
  const avails = full ? [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 20, 26, 30, 32, 33, 34, 40, 48, 49, 65, 66, 70, 71, 78, 90, 113, 150, 200] : [0, 7, 8, 33, 70, 113]
  for (const avail of avails) for (const max of full ? [1, 8, 24, 48, 999] : [1, 48]) for (const keep of full ? [0, 25, 70] : [0, 25]) for (const frac of [0, 0.9]) {
    cases++
    const bytes = Math.round((avail + frac) * GIB)
    const r = run(script, [String(max), String(keep)], { FAKE_BYTES: String(bytes) })
    const room = Math.floor(bytes / GIB) - keep  // whole GB, rounded down
    const want = room < 8 ? null : Math.min(max, room)
    if (r.code !== 0) v("exit code", { avail, frac, max, keep, code: r.code, text: r.text })
    else if (r.size !== want) v("size", { avail, frac, max, keep, want, got: r.size })
    else if (want !== null && (!r.on || Math.floor(bytes / GIB) - r.size < keep)) v("takes the space kept for the build, or not switched on", { avail, frac, max, keep, got: r.size, on: r.on })
    else if (want === null && (r.on || r.log.includes("fallocate"))) v("swap added with nothing to spare", { avail, frac, max, keep })
  }
  // the real runner: 113 GB free after cleaning, 25 kept: 48 asked, 48 got; the failed round's 48 at keep 70 would have been 43
  cases += 3
  if (run(script, ["48", "25"]).size !== 48) v("the real runner at keep 25")
  if (run(script, ["48", "70"]).size !== 43) v("the real runner at keep 70")
  // one byte under a whole GB: rounded down, not up
  if (run(script, ["999", "25"], { FAKE_BYTES: String(60 * GIB - 1) }).size !== 34) v("59.999 GB free must count as 59 GB")
  // a failing command removes the file and fails the job, whichever it is
  for (const failing of ["fallocate", "chmod", "mkswap", "swapon"]) {
    cases++
    const r = run(script, ["48", "25"], { FAIL_ON: failing })
    if (r.code !== 1 || !r.removed || /GB of swap \(/.test(r.text)) v("a failing command must remove the swap file, exit 1 and not claim success", { failing, code: r.code, removed: r.removed, text: r.text })
  }
  // swapoff -a failing (no swap on) is fine
  cases++
  if (run(script, ["48", "25"], { FAIL_ON: "swapoff" }).size !== 48) v("a failing swapoff -a must not stop the swap being added")
  // malformed arguments
  for (const args of [[], ["x", "25"], ["48", "y"], ["0", "25"], ["-5", "25"], ["48", "-1"], ["4 8", "25"], ["48;id", "25"], ["", "25"]]) {
    cases++
    const r = run(script, args)
    if (r.code !== 2 || r.log.includes("fallocate") || r.log.includes("swapon")) v("malformed arguments", { args, code: r.code, log: r.log })
  }
  // an unreadable df
  cases++
  fake("df", "echo nonsense")
  const r = run(script, ["48", "25"])
  fake("df", 'case "$1" in -B1) printf "Avail\\n%s\\n" "$FAKE_BYTES";; -BG) printf "Avail\\n%sG\\n" "$(( (FAKE_BYTES + 1073741823) / 1073741824 ))";; esac')
  if (r.code !== 0 || r.size !== null) v("an unreadable df adds swap or fails the job", { code: r.code, size: r.size })
  return { cases, wrong }
}

const good = suite(real, true)
console.log(`add-swap: ${good.cases} cases (31 sampled free-space values from 0 to 200 GB with and without a 0.9 GB remainder x 5 maxima x 3 kept sizes, failing commands, malformed arguments): ${good.wrong} violations`)
check("the real script holds on every case", good.wrong === 0, good.wrong)

const mutants = [
  ["keep is ignored", 'room=$((avail - keep))', 'room=$avail'],
  ["the maximum is ignored", '[ "$size" -le "$max" ] || size=$max', ":"],
  ["a swap under 8 GB is added", 'if [ "$room" -lt 8 ]; then', 'if [ "$room" -lt 0 ]; then'],
  ["the free space is read rounded up (df -BG, multiplied back to bytes)", "df -B1 --output=avail / | tail -n 1 | tr -dc '0-9')", "df -BG --output=avail / | tail -n 1 | tr -dc '0-9'); bytes=$((${bytes:-0} * 1073741824))"],
  ["a failing fallocate is ignored", 'sudo fallocate -l "${size}G" /swapfile || fail fallocate', 'sudo fallocate -l "${size}G" /swapfile || true'],
  ["a failing mkswap is ignored", "sudo mkswap /swapfile || fail mkswap", "sudo mkswap /swapfile || true"],
  ["a failing swapon is ignored", "sudo swapon /swapfile || fail swapon", "sudo swapon /swapfile || true"],
  ["a failure leaves the swap file behind", "  sudo rm -f /swapfile\n  exit 1", "  exit 1"],
  ["a failure exits 0", "  sudo rm -f /swapfile\n  exit 1", "  sudo rm -f /swapfile\n  exit 0"],
  ["swap is not switched on", "sudo swapon /swapfile || fail swapon\n", "\n"],
  ["a malformed maximum is accepted", "case $max in ''|*[!0-9]*|0)", "case $max in NEVER)"],
  ["an unreadable df is an error", "cannot read the free space; no swap\" >&2; exit 0", "cannot read the free space\" >&2; exit 1"],
]
let caught = 0
for (const [name, from, to] of mutants) {
  if (!real.includes(from)) { check(`mutant: ${name}`, false, "pattern not found"); continue }
  const mutated = real.replace(from, to)
  writeFileSync(join(box, "syntax.sh"), mutated)
  const syn = spawnSync("sh", ["-n", join(box, "syntax.sh")], { encoding: "utf8" })
  if (syn.status !== 0) { check(`mutant: ${name} is valid shell (a mutant that does not parse is "caught" by every run failing, not by the rule it breaks)`, false, syn.stderr); continue }
  const r = suite(mutated, false, false)
  if (r.wrong > 0) caught++
  check(`the broken version "${name}" is caught (${r.wrong} violations in ${r.cases} cases)`, r.wrong > 0, "")
}
check("every broken version was caught", caught === mutants.length, `${caught}/${mutants.length}`)
process.exit(bad ? 1 : 0)
