// The memory rules of scripts/setup-source.mjs that do not need a Lean process to be checked (scripts/test-memory-rules.mjs runs them on real values).

// How long one module killed for its memory may take when built alone: 90 minutes, and for the round that gives such modules swap and a bigger limit
// (setup-sharded.yml, solo_minutes) as long as the job has. A value that is not a positive number of minutes the job can hold is the default
// (a wait longer than the job's 350 minutes would only lose the round).
export const SOLO_BUILD_DEFAULT_MS = 90 * 60 * 1000
export const SOLO_BUILD_MAX_MINUTES = 340
export function soloBuildMs(env = process.env) {
  const v = env.EMISSARY_SOLO_BUILD_MINUTES
  if (typeof v !== "string" || !/^[0-9]+(\.[0-9]+)?$/.test(v.trim())) return SOLO_BUILD_DEFAULT_MS
  const minutes = Number(v)
  const ms = Math.round(minutes * 60 * 1000)
  return minutes <= SOLO_BUILD_MAX_MINUTES && ms > 0 ? ms : SOLO_BUILD_DEFAULT_MS // a sub-millisecond value rounds to 0, which would end every solo build at once
}

// Memory a process can still get, in MB, from the text of /proc/meminfo. With `countSwap` (the job added swap for the modules that do not fit in a runner's RAM,
// EMISSARY_COUNT_SWAP=1) the free swap counts too: those modules are meant to run on swap, and RAM alone is nearly all used then, which the guard would take for a
// shortage and kill the very module the swap was added for. Without it swap is not counted: the 4 GB a hosted runner has by default must not hide a real shortage.
// Infinity when the text has no MemAvailable (not Linux): nothing to judge by.
export function availableFrom(meminfo, countSwap = false) {
  const m = /^MemAvailable:\s+(\d+) kB/m.exec(meminfo)
  if (!m) return Infinity
  const swap = countSwap ? /^SwapFree:\s+(\d+) kB/m.exec(meminfo) : null
  return (Number(m[1]) + (swap ? Number(swap[1]) : 0)) / 1024
}

// The files of a packed build (.lake/build/lib/lean/<path>.* and .lake/build/ir/<path>.*, never *.setup.json) that belong to the modules in `keep`; `listing` is `tar -t` of the archive.
// `keep` holds module paths as setup-source.mjs's pathOfModule writes them (a «guillemet» component is written without the guillemets, dots inside it stay: X.«c.d» is X/c.d).
// A file is <path>.<suffixes>, and a path may itself hold dots, so every dot of the last component is tried as the end of the path. That can take the files of a module X/c.d along with those
// of a module X/c (when both exist): a few files too many, never one too few.
export function membersOf(listing, keep) {
  const out = []
  for (const line of listing.split("\n")) {
    const f = line.replace(/^\.\//, "")
    const m = /^\.lake\/build\/(?:lib\/lean|ir)\/(.+)$/.exec(f)
    if (!m || f.endsWith(".setup.json")) continue
    const parts = m[1].split("/")
    const last = parts.pop()
    for (let i = last.indexOf("."); i > 0; i = last.indexOf(".", i + 1)) {
      if (keep.has([...parts, last.slice(0, i)].join("/"))) {
        out.push(f)
        break
      }
    }
  }
  return out
}
