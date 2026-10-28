// node scripts/test-setup-plan.mjs — the route a library is set up by (exits 1 on a wrong plan)
import { decide, roundProgress, MIN_PROGRESS_DEFAULT, ONE_SHOT_MAX_ENTRIES, MAX_SHARDS } from "./setup-plan.mjs"
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

// ---- a build round that did nothing (roundProgress) ----
// An independent statement of the rule, to compare with on random numbers: the first round and a round with no count before it are never stopped; any other stops exactly when it added fewer than min.
const oracle = (round, prev, built, min) => (round === 1 || prev === null ? false : built - prev < min)
let seed = 12345
const rnd = (n) => { // mulberry32: deterministic, and good in its low bits
  seed = (seed + 0x6d2b79f5) | 0
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed)
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
  return (((t ^ (t >>> 14)) >>> 0) % n)
}
let mismatches = 0
let stops = 0
let goes = 0
for (let i = 0; i < 20000; i++) {
  const round = 1 + rnd(8), min = rnd(6), built = rnd(40000), prev = rnd(5) === 0 ? null : rnd(40000)
  const got = roundProgress({ round, prev, built, min }).stop
  if (got !== oracle(round, prev, built, min)) mismatches++
  got ? stops++ : goes++
}
check("roundProgress agrees with the rule on 20,000 random rounds", mismatches === 0, mismatches)
check("the random rounds exercise both outcomes", stops > 1000 && goes > 1000, { stops, goes })
// the boundaries: added exactly min goes on, min - 1 stops, for every min, from every earlier count
let edge = true
for (const min of [0, 1, 2, 7]) for (const prev of [0, 1, 500, 30661]) {
  edge &&= roundProgress({ round: 2, prev, built: prev + min, min }).stop === false
  edge &&= roundProgress({ round: 2, prev, built: prev + min + 1, min }).stop === false
  if (min > 0) edge &&= roundProgress({ round: 2, prev, built: prev + min - 1, min }).stop === true
}
check("exactly min modules added goes on, one fewer stops (and min 0 never stops on a count that did not fall)", edge, null)
check("the default asks for any progress: a round that added 0 stops, one that added 1 goes on", MIN_PROGRESS_DEFAULT === 1 && roundProgress({ round: 3, prev: 100, built: 100 }).stop && !roundProgress({ round: 3, prev: 100, built: 101 }).stop, null)
check("a build that went down (the earlier build was not restored) is no progress, whatever min is above 0", roundProgress({ round: 2, prev: 900, built: 40, min: 1 }).stop === true && roundProgress({ round: 2, prev: 900, built: 40, min: 1 }).added === -860, roundProgress({ round: 2, prev: 900, built: 40 }))
check("the first round is never stopped, nor a round with nothing to compare with", !roundProgress({ round: 1, prev: 500, built: 500 }).stop && !roundProgress({ round: 4, prev: null, built: 0 }).stop && !roundProgress({ round: 4, prev: "", built: 0 }).stop && !roundProgress({ round: 4, built: 0 }).stop, null)
check("flt-anthropic: three rounds at the same count, the second of them already stops", roundProgress({ round: 2, prev: 1234, built: 1234 }).stop && roundProgress({ round: 2, prev: 1234, built: 1234 }).why.includes("1234"), roundProgress({ round: 2, prev: 1234, built: 1234 }))
check("bad numbers are refused", throws(() => roundProgress({ round: 0, built: 1 })) && throws(() => roundProgress({ round: 2, prev: -1, built: 1 })) && throws(() => roundProgress({ round: 2, prev: 1, built: "9" })) && throws(() => roundProgress({ round: 2, prev: 1, built: 2, min: -1 })), null)
// mutants: the check above must fail for each wrong version of the rule
const disagrees = (rule) => {
  for (let i = 0; i < 3000; i++) {
    const round = 1 + rnd(4), min = rnd(4), prev = rnd(3) === 0 ? null : rnd(6), built = rnd(10)
    if (rule({ round, prev, built, min }) !== oracle(round, prev, built, min)) return true
  }
  return false
}
const ref = (a) => roundProgress(a).stop
check("the rule itself is not noticed as a mutant", !disagrees(ref), null)
check("mutant: stopping when added <= min is noticed", disagrees(({ round, prev, built, min }) => (round === 1 || prev === null ? false : built - prev <= min)), null)
check("mutant: judging the first round is noticed", disagrees(({ round, prev, built, min }) => (prev === null ? false : built - prev < min)), null)
check("mutant: reading no count as zero is noticed", disagrees(({ round, prev, built, min }) => (round === 1 ? false : built - (prev ?? 0) < min)), null)
check("mutant: counting a fall as no change is noticed", disagrees(({ round, prev, built, min }) => (round === 1 || prev === null ? false : Math.max(0, built - prev) < min && built >= prev)), null)
check("mutant: comparing with the library's size instead of the round before is noticed", disagrees(({ round, prev, built, min }) => (round === 1 || prev === null ? false : built < min)), null)
process.exit(bad ? 1 : 0)
