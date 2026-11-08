// node scripts/test-setup-budget-run.mjs — scripts/budget-run.sh tells a budget stop from a crash, on real processes under GNU timeout.
//
// The real case: leanbridge (setup run 42427677819 and the five rounds after it, 7-8 Nov 2026). Node died at its heap limit (exit 134) in every prime build, and the step's
// `|| echo "::notice::the prime build stopped at its budget"` called each crash a budget stop. cubic (#157): exit 137 is no proof of the budget either, since a command the
// runner's out-of-memory killer takes (SIGKILL) also ends with 137. Here each way a command can end is made by a real process: it finishes; it outlives the budget and stops on
// TERM (124); it ignores TERM and is killed after the budget (137, budget); Node runs out of heap (134, early); it is SIGKILLed before the budget (137, early); it fails (1).
// Invariants: only the two budget stops give a ::notice::, every other non-zero end gives an ::error:: naming its exit code; the step goes on (exit 0) either way; a malformed
// budget is refused (exit 2); both build sites of setup-sharded.yml use the script and no bare `|| echo "::notice::... budget"` is left.
import { spawnSync } from "node:child_process"
import { readFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) {
    bad++
    console.log("FAIL", name, detail ?? "")
  } else console.log("ok", name)
}

const wf = readFileSync(join(here, "..", ".github", "workflows", "setup-sharded.yml"), "utf8")
check("the prime build runs under budget-run.sh", /bash scripts\/budget-run\.sh "\$PRIME_MINUTES" "the prime build" "the shards build the rest" node scripts\/setup-source\.mjs "\$KEY" --phase build /.test(wf))
check("each shard runs under budget-run.sh", /bash scripts\/budget-run\.sh 300 "shard \$I" "handing on what it produced" node scripts\/setup-source\.mjs "\$KEY" --phase shard /.test(wf))
check("no step calls a non-zero end of setup-source a budget stop without looking", !/setup-source\.mjs[^\n]*\|\| echo "::notice::/.test(wf))

const hasTimeout = spawnSync("timeout", ["--version"]).status === 0
if (!hasTimeout) {
  if (process.env.CI) check("GNU timeout is on the runner (the script needs it)", false)
  else console.log("skip: no GNU timeout here; the setup-tests workflow runs these cases on the runner")
} else {
  const run = (min, cmd, env = {}) => {
    const r = spawnSync("bash", [join(here, "budget-run.sh"), String(min), "the step", "going on", ...cmd], {
      encoding: "utf8",
      env: { ...process.env, BUDGET_RUN_UNIT: "s", BUDGET_RUN_KILL_AFTER: "1s", ...env },
    })
    return { code: r.status, out: (r.stdout || "") + (r.stderr || "") }
  }
  const notice = (o) => /::notice::the step stopped at its budget \(2s\); going on/.test(o.out) && !/::error::/.test(o.out)
  const error = (o, rc) => new RegExp(`::error::the step ended with exit code ${rc} after \\d+s, not at its budget`).test(o.out) && !/::notice::/.test(o.out)
  const ok = run(2, ["bash", "-c", "exit 0"])
  check("a command that finishes: no line, exit 0", ok.code === 0 && !/::(notice|error)::/.test(ok.out), ok.out)
  const term = run(2, ["sleep", "30"])
  check("outlives the budget and stops on TERM (124): a budget stop", term.code === 0 && notice(term), term.out)
  const stubborn = run(2, ["bash", "-c", "trap '' TERM; sleep 30 & wait; sleep 30"])
  check("ignores TERM and is killed after the budget (137): a budget stop", stubborn.code === 0 && notice(stubborn), stubborn.out)
  const heap = run(60, ["node", "--max-old-space-size=16", "-e", "const a = []; for (;;) a.push('x'.repeat(1e5) + a.length)"])
  check("Node runs out of heap (134), long before the budget: an error naming 134", heap.code === 0 && error(heap, 134), heap.out.slice(-400))
  const oomKill = run(60, ["bash", "-c", "kill -9 $$"])
  check("SIGKILLed before the budget (137, as the out-of-memory killer does): an error, not a budget stop", oomKill.code === 0 && error(oomKill, 137), oomKill.out)
  const fails = run(60, ["bash", "-c", "exit 1"])
  check("fails with exit 1: an error", fails.code === 0 && error(fails, 1), fails.out)
  for (const m of ["", "5m", "-1", "1.5", "99999", "$(id)"]) {
    const r = run(m, ["true"])
    check(`a malformed budget '${m}' is refused (exit 2)`, r.code === 2 && /is not a number of minutes/.test(r.out), r.out)
  }
  const unit = run(2, ["true"], { BUDGET_RUN_UNIT: "h" })
  check("a unit other than m or s is refused", unit.code === 2, unit.out)
}

if (bad) {
  console.log(`${bad} FAILED`)
  process.exit(1)
}
console.log("all budget-run checks passed")
