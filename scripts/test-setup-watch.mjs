// node scripts/test-setup-watch.mjs — runner-watch.sh writes a header and one line per interval, prints the first line, and
// round-summary.py turns the file into the summary lines that go to the run page.
import { spawn, spawnSync } from "node:child_process"
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import os from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const tmp = mkdtempSync(join(os.tmpdir(), "runner-watch-test-"))
let bad = 0
const check = (name, ok, detail) => { if (!ok) { bad++; console.log("FAIL", name, detail ?? "") } else console.log("ok", name) }

const dir = join(tmp, "lib"); mkdirSync(dir)
writeFileSync(join(dir, "A.olean"), "")
const out = join(tmp, "m.tsv")
const w = spawn("sh", [join(here, "runner-watch.sh"), dir, out, "1"], { stdio: ["ignore", "pipe", "ignore"] })
let printed = ""
w.stdout.on("data", (d) => (printed += d))
await new Promise((r) => setTimeout(r, 400))
writeFileSync(join(dir, "B.olean"), "")
await new Promise((r) => setTimeout(r, 2200))
w.kill()
const rows = readFileSync(out, "utf8").trim().split("\n")
check("the file has a header and at least two samples", rows[0] === "time\tfree_mb\tbuilt\ttop_mb\ttop_name" && rows.length >= 3, rows.join("\n"))
check("the built count follows the .olean files (1, then 2)", rows[1].split("\t")[2] === "1" && rows[rows.length - 1].split("\t")[2] === "2", rows.join("\n"))
check("the first sample is also printed (so the log is not silent)", /^\[watch\] /.test(printed), printed)
const s = spawnSync("python3", ["-I", join(here, "round-summary.py"), out, "Build round 9", "1"], { encoding: "utf8" })
check("the summary names the round and the modules built", s.status === 0 && /### Build round 9/.test(s.stdout) && /modules built .*: 1 at the start, 2 at the end, \+1/.test(s.stdout), s.stdout + s.stderr)
writeFileSync(join(tmp, "empty.tsv"), "time\tfree_mb\tbuilt\ttop_mb\ttop_name\n")
check("an empty metrics file gives a note, not an error", spawnSync("python3", ["-I", join(here, "round-summary.py"), join(tmp, "empty.tsv")], { encoding: "utf8" }).stdout.includes("No samples"), "")
rmSync(tmp, { recursive: true, force: true })
process.exit(bad ? 1 : 0)
