// node scripts/test-add-swap.mjs — scripts/add-swap.sh: the swap a big-memory round adds is what the disk can spare, never the whole 48 GB that took the space the earlier build needs.
// (flt-anthropic, 5 Nov 2026: the first retry added 48 GB of swap, then unpacked a 16.5 GB archive into a build of 50+ GB on a runner with 113 GB free: "No space left on device", four minutes in.)
// The script is run for real with df, sudo, fallocate, mkswap, swapon, swapoff and free replaced by recorders, over every free space from 0 to 200 GB (113 GB is what the real runner had after
// its disk was cleaned: the figure in the logs of the failed round), and the boundaries (7, 8, 9 GB to spare), maxima and kept sizes, and the rules are checked:
//   1. the swap is min(MAX, free - KEEP) GB when the room (free - KEEP) is at least 8, else there is none and the script still exits 0 (the build goes on without swap);
//   2. it never takes the space KEEP is for (free - size >= KEEP whenever there is swap);
//   3. with a WAIT_FILE it adds nothing while the file exists, adds the swap once it is gone, and gives up (no swap, exit 0) when it never goes;
//   4. a malformed MAX or KEEP exits 2 and touches nothing.
// Then the same cases run against broken versions of the script, and each must be caught.
import { chmodSync, existsSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs"
import { spawnSync } from "node:child_process"
import { tmpdir } from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const real = readFileSync(join(here, "add-swap.sh"), "utf8")
let bad = 0
const check = (name, ok, detail) => { if (!ok) { bad++; console.log("FAIL", name, detail ?? "") } else console.log("ok", name) }

const box = mkdtempSync(join(tmpdir(), "swap-"))
const calls = join(box, "calls")
const fake = (name, body) => { writeFileSync(join(box, name), `#!/bin/sh\n${body}\n`); chmodSync(join(box, name), 0o755) }
fake("df", 'printf "Avail\\n%sG\\n" "$FAKE_AVAIL"')
fake("sudo", 'echo "sudo $*" >> "$CALLS"; exit 0')
fake("free", 'echo free >> "$CALLS"')
const run = (script, args, env = {}) => {
  writeFileSync(join(box, "add-swap.sh"), script)
  writeFileSync(calls, "")
  const r = spawnSync("sh", [join(box, "add-swap.sh"), ...args], { encoding: "utf8", timeout: 8000, killSignal: "SIGKILL", env: { PATH: `${box}:${process.env.PATH}`, CALLS: calls, FAKE_AVAIL: "113", ADD_SWAP_POLL_S: "0", ADD_SWAP_MAX_POLLS: "3", ...env } })
  const log = readFileSync(calls, "utf8")
  const m = log.match(/fallocate -l (\d+)G \/swapfile/)
  return { code: r.status, text: r.stdout + r.stderr, size: m ? Number(m[1]) : null, on: /swapon \/swapfile/.test(log), log }
}

function suite(script, print, full = true) {
  let cases = 0, wrong = 0
  const v = (what, detail) => { wrong++; if (print && wrong <= 6) console.log("FAIL", what, JSON.stringify(detail)) }
  const avails = full ? [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 20, 26, 30, 32, 33, 34, 40, 48, 49, 65, 66, 70, 71, 78, 90, 113, 150, 200] : [0, 7, 8, 33, 70, 113]
  for (const avail of avails) for (const max of full ? [1, 8, 24, 48, 999] : [1, 48]) for (const keep of full ? [0, 25, 70] : [0, 25]) {
    cases++
    const r = run(script, [String(max), String(keep)], { FAKE_AVAIL: String(avail) })
    const room = avail - keep
    const want = room < 8 ? null : Math.min(max, room)
    if (r.code !== 0) v("exit code", { avail, max, keep, code: r.code, text: r.text })
    else if (r.size !== want) v("size", { avail, max, keep, want, got: r.size })
    else if (want !== null && (!r.on || avail - r.size < keep)) v("takes the space kept for the build, or not switched on", { avail, max, keep, got: r.size, on: r.on })
    else if (want === null && (r.on || r.log.includes("fallocate"))) v("swap added with nothing to spare", { avail, max, keep })
  }
  // the real runner: 113 GB free after cleaning, 25 kept: 48 asked, 48 got; the failed round's 48 at keep 70 would have been 43
  cases += 2
  if (run(script, ["48", "25"]).size !== 48) v("the real runner at keep 25")
  if (run(script, ["48", "70"]).size !== 43) v("the real runner at keep 70")
  // wait file
  const marker = join(box, "build.tar.zst")
  cases++
  writeFileSync(marker, "x")
  let r = run(script, ["48", "25", marker])
  if (r.size !== null || r.code !== 0) v("waits for the file: swap added while it is still there, or an error", { size: r.size, code: r.code })
  // the file goes away after two polls: swap follows
  fake("sleep", `n=$(cat "${box}/n" 2>/dev/null || echo 0); n=$((n+1)); echo $n > "${box}/n"; [ $n -ge 2 ] && rm -f "${marker}"; exit 0`)
  writeFileSync(join(box, "n"), "0"); writeFileSync(marker, "x")
  cases++
  r = run(script, ["48", "25", marker], { ADD_SWAP_MAX_POLLS: "10" })
  if (r.size !== 48 || r.code !== 0) v("the swap is not added once the file is gone", { size: r.size, code: r.code, text: r.text })
  fake("sleep", "exit 0")
  // no wait file given and none present: immediate
  cases++
  r = run(script, ["48", "25", join(box, "does-not-exist")])
  if (r.size !== 48) v("a wait file that does not exist must not delay or prevent the swap", r.size)
  // malformed arguments
  for (const args of [[], ["x", "25"], ["48", "y"], ["0", "25"], ["-5", "25"], ["48", "-1"], ["4 8", "25"], ["48;id", "25"], ["", "25"]]) {
    cases++
    r = run(script, args)
    if (r.code !== 2 || r.log.includes("fallocate") || r.log.includes("swapon")) v("malformed arguments", { args, code: r.code, log: r.log })
  }
  // an unreadable df
  cases++
  fake("df", 'echo nonsense')
  r = run(script, ["48", "25"])
  fake("df", 'printf "Avail\\n%sG\\n" "$FAKE_AVAIL"')
  if (r.code !== 0 || r.size !== null) v("an unreadable df adds swap or fails the job", { code: r.code, size: r.size })
  return { cases, wrong }
}

const good = suite(real, true)
console.log(`add-swap: ${good.cases} cases (free space 0-200 GB, 31 values x 5 maxima x 3 kept sizes, wait file, malformed arguments): ${good.wrong} violations`)
check("the real script holds on every case", good.wrong === 0, good.wrong)

const mutants = [
  ["keep is ignored", 'room=$((avail - keep))', 'room=$avail'],
  ["the maximum is ignored", '[ "$size" -le "$max" ] || size=$max', ":"],
  ["a swap under 8 GB is added", 'if [ "$room" -lt 8 ]; then', 'if [ "$room" -lt 0 ]; then'],
  ["the wait file is not waited for", '[ -e "$wait_file" ]', "false"],
  ["the wait never ends", '[ "$waited" -le "${ADD_SWAP_MAX_POLLS:-1440}" ] ||', "true ||"],
  ["swap is not switched on", "sudo swapon /swapfile\n", "\n"],
  ["a malformed maximum is accepted", "case $max in ''|*[!0-9]*|0)", "case $max in NEVER)"],
  ["an unreadable df is an error", "cannot read the free space; no swap\" >&2; exit 0", "cannot read the free space\" >&2; exit 1"],
]
let caught = 0
for (const [name, from, to] of mutants) {
  if (!real.includes(from)) { check(`mutant: ${name}`, false, "pattern not found"); continue }
  const r = suite(real.replace(from, to), false, false)
  if (r.wrong > 0) caught++
  check(`the broken version "${name}" is caught (${r.wrong} violations in ${r.cases} cases)`, r.wrong > 0, "")
}
check("every broken version was caught", caught === mutants.length, `${caught}/${mutants.length}`)
process.exit(bad ? 1 : 0)
