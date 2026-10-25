// node scripts/test-setup-plan.mjs — the route a library is set up by (exits 1 on a wrong plan)
import { decide, ONE_SHOT_MAX_ENTRIES, MAX_SHARDS } from "./setup-plan.mjs"
let bad = 0
const check = (name, ok, got) => {
  if (!ok) { bad++; console.log("FAIL", name, JSON.stringify(got)) } else console.log("ok", name)
}
const throws = (f) => { try { f(); return false } catch { return true } }

check("a small library is set up in one job", decide({ entries: 394 }).route === "oneshot", decide({ entries: 394 }))
check("exactly at the line is still one job", decide({ entries: ONE_SHOT_MAX_ENTRIES }).route === "oneshot", decide({ entries: ONE_SHOT_MAX_ENTRIES }))
check("one entry over the line is staged", decide({ entries: ONE_SHOT_MAX_ENTRIES + 1 }).route === "staged", decide({ entries: ONE_SHOT_MAX_ENTRIES + 1 }))
const flt = decide({ entries: 48460 })
check("flt-anthropic: staged, 64 shards, 8 modules per expansion process", flt.route === "staged" && flt.shards === 64 && flt.expand_chunk === 8, flt)
check("a mid-size library gets a share of the shards, never fewer than 2", decide({ entries: 4000 }).shards === 6 && decide({ entries: 3001 }).shards === 5, decide({ entries: 3001 }))
check("shards never pass the cap, however many entries", decide({ entries: 10_000_000 }).shards === MAX_SHARDS, decide({ entries: 10_000_000 }))
check("asked for staged, a tiny library is staged (2 shards at least)", decide({ entries: 5, mode: "staged" }).route === "staged" && decide({ entries: 5, mode: "staged" }).shards === 2, decide({ entries: 5, mode: "staged" }))
check("asked for oneshot, a huge library is not second-guessed", decide({ entries: 48460, mode: "oneshot" }).route === "oneshot", decide({ entries: 48460, mode: "oneshot" }))
check("a shard count that was asked for wins", decide({ entries: 48460, shards: 16 }).shards === 16, decide({ entries: 48460, shards: 16 }))
check("the build gets the room it needs: 300-minute rounds, up to 6", decide({ entries: 9000 }).prime_minutes === 300 && decide({ entries: 9000 }).max_build_rounds === 6, decide({ entries: 9000 }))
check("a bad mode is refused", throws(() => decide({ entries: 1, mode: "fast" })), null)
check("a bad entry count is refused", throws(() => decide({ entries: -1 })) && throws(() => decide({ entries: 1.5 })) && throws(() => decide({ entries: "9" })), null)
check("a bad shard count is refused", throws(() => decide({ entries: 1, shards: 65 })) && throws(() => decide({ entries: 1, shards: -2 })), null)
process.exit(bad ? 1 : 0)
