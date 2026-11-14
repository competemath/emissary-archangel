// node scripts/test-setup-plan.mjs — the route a library is set up by (exits 1 on a wrong plan)
import { decide, roundProgress, roundsCap, slicedSwitch, SLICE_MODULES_PER_SHARD, SLICE_MIN_SHARDS, SLICE_MAX_MODULES_PER_SHARD, BUILD_ROUNDS_CEILING_FACTOR, MIN_PROGRESS_DEFAULT, ONE_SHOT_MAX_ENTRIES, MAX_SHARDS } from "./setup-plan.mjs"
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
const oracle = (round, prev, built, min) => (round === 1 || prev === null || min === 0 ? false : built - prev < min) // min 0: no such stop, a fall included
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
check("exactly min modules added goes on, one fewer stops (min 0 never stops)", edge, null)
check("the default asks for any progress: a round that added 0 stops, one that added 1 goes on", MIN_PROGRESS_DEFAULT === 1 && roundProgress({ round: 3, prev: 100, built: 100 }).stop && !roundProgress({ round: 3, prev: 100, built: 101 }).stop, null)
check("a build that went down (the earlier build was not restored) is no progress, whatever min is above 0", roundProgress({ round: 2, prev: 900, built: 40, min: 1 }).stop === true && roundProgress({ round: 2, prev: 900, built: 40, min: 1 }).added === -860, roundProgress({ round: 2, prev: 900, built: 40 }))
check("min 0 turns the stop off: a round that added nothing, or whose count fell, goes on", !roundProgress({ round: 3, prev: 100, built: 100, min: 0 }).stop && !roundProgress({ round: 3, prev: 900, built: 40, min: 0 }).stop && roundProgress({ round: 3, prev: 900, built: 40, min: 0 }).added === -860 && roundProgress({ round: 3, prev: 900, built: 40, min: 1 }).stop, roundProgress({ round: 3, prev: 900, built: 40, min: 0 }))
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
check("mutant: stopping on a fall although min is 0 is noticed", disagrees(({ round, prev, built, min }) => (round === 1 || prev === null ? false : built - prev < min || (min === 0 && built < prev))), null)

// roundsCap: the plan's number of build rounds is a budget, not a wall (flt-anthropic, 6 Nov 2026: round 6 of 6 built 85 of 86 modules and the chain stopped until a person raised the cap)
{
  const c = (a) => roundsCap(a).stop
  check("within the plan, another round whatever the counts", [1, 2, 5].every((r) => !c({ round: r, maxRounds: 6, prev: null, built: null })), null)
  check("the real case: round 6 of 6 added 15 modules (70 -> 85): another round", !c({ round: 6, maxRounds: 6, prev: 70, built: 85 }), null)
  check("past the plan with no gain, or a fall, or no count: stop", c({ round: 6, maxRounds: 6, prev: 85, built: 85 }) && c({ round: 7, maxRounds: 6, prev: 85, built: 80 }) && c({ round: 6, maxRounds: 6, prev: null, built: 85 }) && c({ round: 6, maxRounds: 6, prev: 85, built: null }), null)
  check("min_progress counts: 4 added with min 5 stops, 5 added continues, min 0 still needs one", c({ round: 6, maxRounds: 6, prev: 100, built: 104, min: 5 }) && !c({ round: 6, maxRounds: 6, prev: 100, built: 105, min: 5 }) && c({ round: 6, maxRounds: 6, prev: 100, built: 100, min: 0 }) && !c({ round: 6, maxRounds: 6, prev: 100, built: 101, min: 0 }), null)
  check("the ceiling is three times the plan, whatever the gain", !c({ round: 17, maxRounds: 6, prev: 1, built: 999 }) && c({ round: 18, maxRounds: 6, prev: 1, built: 999 }) && BUILD_ROUNDS_CEILING_FACTOR === 3, null)
  let threw = 0
  for (const a of [{ round: 0, maxRounds: 6 }, { round: 1, maxRounds: 0 }, { round: 1.5, maxRounds: 6 }, { round: 1, maxRounds: 6, min: -1 }]) { try { roundsCap(a) } catch { threw++ } }
  check("a round or a plan that is not a count is an error", threw === 4, threw)
}

// ---- a build too slow for rounds is split over runners (slicedSwitch) ----
{
  const sw = (a) => slicedSwitch({ maxBuildRounds: 6, ...a })
  const fsgl = sw({ round: 1, built: 95, modules: 3964 })
  check("finite-simple-groups-lean, 14 Nov 2026: 95 of 3,964 in round 1 is 41 more rounds: 64 slices of about 62 modules instead", fsgl.switch && fsgl.shards === 64 && /41 more rounds/.test(fsgl.why) && /about 62 of the 3964/.test(fsgl.why), fsgl)
  check("the round before the storm rule (13 of 3,964) switches too", sw({ round: 1, built: 13, modules: 3964 }).switch, null)
  check("a build that fits the plan keeps the rounds: 2,900 a round of 8,000 is 3 in all", !sw({ round: 2, prev: 3000, built: 5900, modules: 8000 }).switch && !sw({ round: 1, built: 2000, modules: 8000 }).switch, null)
  check("the line is exact: round + rounds left = the plan keeps rounds, one over switches", !sw({ round: 1, built: 100, modules: 600 }).switch && sw({ round: 1, built: 100, modules: 601 }).switch, [sw({ round: 1, built: 100, modules: 600 }), sw({ round: 1, built: 100, modules: 601 })])
  check("a build that needs only one more round keeps it: flt-anthropic 86 modules, round 6 built 85 (one left, 84 a round)", !sw({ round: 6, prev: 1, built: 85, modules: 86 }).switch && !sw({ round: 6, prev: 100, built: 200, modules: 300 }).switch && sw({ round: 6, prev: 100, built: 200, modules: 301 }).switch, [sw({ round: 6, prev: 1, built: 85, modules: 86 }), sw({ round: 6, prev: 100, built: 200, modules: 301 })])
  // the archive flags alone decide: the same pace that switches (95 of 3,964 in round 1) keeps the rounds with either flag (cubic: the 86-module case would keep its rounds without the guard)
  check("an archive delta is built by rounds (from_release, only_modules): the pace that switches keeps the rounds with either flag", sw({ round: 1, built: 95, modules: 3964 }).switch && !sw({ round: 1, built: 95, modules: 3964, fromRelease: true }).switch && !sw({ round: 1, built: 95, modules: 3964, onlyModules: true }).switch, null)
  check("no count, a finished build and a round that added nothing or fell are not the pace's to judge", [{ built: null, modules: 100 }, { built: 5, modules: null }, { built: "", modules: 100 }, { built: 100, modules: 100 }, { built: 120, modules: 100 }, { round: 3, prev: 50, built: 50, modules: 5000 }, { round: 3, prev: 60, built: 50, modules: 5000 }].every((a) => !sw({ round: 1, ...a }).switch), null)
  check("a round after the first with no count of the round before it is not judged (cubic: not projected from the total)", !sw({ round: 3, prev: null, built: 95, modules: 3964 }).switch && !sw({ round: 3, prev: "", built: 95, modules: 3964 }).switch && sw({ round: 1, prev: null, built: 95, modules: 3964 }).switch, null)
  check("a round after the first is judged on what it added, not on the total: 1,000 added of 3,964 is one more round", !sw({ round: 2, prev: 2000, built: 3000, modules: 3964 }).switch && sw({ round: 2, prev: 2999, built: 3000, modules: 3964 }).switch, null)
  check("a later round at a pace of 95 a round (prev 95, built 190) switches", sw({ round: 2, prev: 95, built: 190, modules: 3964 }).switch, null)
  // cubic: a round that added fewer than min_progress modules is the stall rule's, not the pace's
  check("a round that added fewer than min_progress is the stall rule's: added 1 with min 5 keeps the rounds, added 5 or min 0 slices; round 1 has no stall rule", !sw({ round: 3, prev: 100, built: 101, modules: 3964, min: 5 }).switch && sw({ round: 3, prev: 100, built: 105, modules: 3964, min: 5 }).switch && sw({ round: 3, prev: 100, built: 101, modules: 3964, min: 0 }).switch && sw({ round: 1, built: 1, modules: 3964, min: 5 }).switch, null)
  // cubic: the sliced run starts from nothing, so its shards divide ALL the modules, not the ones left
  check("the shards divide all the modules: 64 for 3,964 whatever is built, and 3,000 of 3,964 built is still 64 (not 16)", sw({ round: 1, built: 95, modules: 3964 }).shards === 64 && sw({ round: 2, prev: 2990, built: 3000, modules: 3964 }).shards === 64, [sw({ round: 2, prev: 2990, built: 3000, modules: 3964 })])
  check("flt-anthropic's 30,662 modules are not sliced (480 a shard in 64 shards is more than a shard's time holds): rounds go on", !sw({ round: 1, built: 9, modules: 30662 }).switch && /480 a shard/.test(sw({ round: 1, built: 9, modules: 30662 }).why), sw({ round: 1, built: 9, modules: 30662 }))
  check("the shards are about 60 modules each, 8 at least, 64 at most, and a slice is at most 150 modules", sw({ round: 1, built: 1, modules: 400, maxBuildRounds: 1 }).shards === SLICE_MIN_SHARDS && sw({ round: 1, built: 10, modules: 1000 }).shards === 17 && sw({ round: 1, built: 1, modules: 64 * SLICE_MAX_MODULES_PER_SHARD }).shards === 64 && !sw({ round: 1, built: 1, modules: 64 * SLICE_MAX_MODULES_PER_SHARD + 1 }).switch && SLICE_MODULES_PER_SHARD === 60, [sw({ round: 1, built: 1, modules: 64 * SLICE_MAX_MODULES_PER_SHARD })])
  // an independent statement of the rule on random numbers
  let ok = true, switched = 0, kept = 0
  for (let i = 0; i < 20000; i++) {
    const modules = 1 + rnd(40000), built = rnd(modules + 1), prevN = rnd(modules + 1), round = 1 + rnd(8), maxBuildRounds = 1 + rnd(8), min = rnd(4) === 0 ? 0 : 1 + rnd(5), prev = rnd(5) === 0 ? null : prevN
    let want = false
    if (built < modules && !(round > 1 && prev === null)) {
      const added = round === 1 ? built : built - prev
      const roundsLeft = added > 0 ? Math.ceil((modules - built) / added) : 0
      const shards = Math.min(64, Math.max(8, Math.ceil(modules / 60)))
      want = added > 0 && !(round > 1 && min > 0 && added < min) && roundsLeft >= 2 && round + roundsLeft > maxBuildRounds && Math.ceil(modules / shards) <= 150
      if (want && slicedSwitch({ round, prev, built, modules, maxBuildRounds, min }).shards !== shards) { ok = false; console.log("  shards", { round, prev, built, modules }); break }
    }
    const got = slicedSwitch({ round, prev, built, modules, maxBuildRounds, min })
    if (got.switch !== want) { ok = false; console.log("  differs", { round, prev, built, modules, maxBuildRounds, min, got, want }); break }
    if (want) switched++; else kept++
  }
  check(`slicedSwitch agrees with an independent statement of the rule on 20,000 random builds (${switched} switch, ${kept} do not)`, ok && switched > 300 && kept > 1000, { switched, kept })
  let threw = 0
  for (const a of [{ round: 0 }, { round: 1.5 }, { round: 1, maxBuildRounds: 0 }, { round: 1, built: -1, modules: 5 }, { round: 1, built: 1, modules: 5.5 }, { round: 1, min: -1 }]) { try { slicedSwitch({ maxBuildRounds: 6, ...a }) } catch { threw++ } }
  check("a round, a plan or a count that is not a count is an error", threw === 6, threw)
}
process.exit(bad ? 1 : 0)
