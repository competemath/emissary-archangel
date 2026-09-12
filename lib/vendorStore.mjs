// Persistent, dedup-aware registry of every declaration Emissary-Archangel has
// already vendored into Tengoku. The actual dedup MECHANISM (closure walk +
// `env.find?` existence check, so only genuinely-missing names get
// transplanted) already exists and is proven — Vendor/Importer.lean +
// Vendor/ReplayCore.lean, exercised all through this session's tautology work.
// What this file adds is PERSISTENCE of that knowledge ACROSS separate process
// runs: each `lake env lean` invocation starts from a fresh environment, so
// without a record living outside that process, every run would "discover"
// the same common definitions as new every single time.
//
// Scope, stated plainly rather than overclaimed: this registry tracks WHICH
// declaration names are already vendored (for cheap membership checks before
// deciding whether a future translation needs to bring something in) and
// records their own source (for the "no external library" audit trail this
// whole vendoring effort is for). It does NOT yet serialize the actual
// compiled content into a single accumulating environment that a later Lean
// process can load back in one shot — each translation's export still needs
// re-deriving the closure content for anything not already tracked. Building
// a real accumulating environment (concatenating/re-exporting the union of
// every vendored declaration's content) is the natural next step once this
// registry has real usage data to design against — not done here.

import { readFileSync, writeFileSync, existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const STORE_PATH = path.join(__dirname, "..", "data", "vendored-definitions.json");

function load() {
  if (!existsSync(STORE_PATH)) return { bySource: {}, byName: {} };
  try {
    return JSON.parse(readFileSync(STORE_PATH, "utf8"));
  } catch {
    return { bySource: {}, byName: {} };
  }
}

function save(store) {
  writeFileSync(STORE_PATH, JSON.stringify(store, null, 2));
}

// Returns only the names NOT already vendored — the actual dedup check a
// caller should run before doing any work to bring a name in.
export function filterAlreadyVendored(names) {
  const store = load();
  return names.filter((n) => !store.byName[n]);
}

export function isVendored(name) {
  const store = load();
  return !!store.byName[name];
}

// Records that `names` are now vendored, attributed to `sourceId` (e.g. a
// Tengoku theorem id, or a source library name for a bulk vendoring pass like
// tautology). Idempotent — re-recording an already-known name updates nothing
// but its lastSeenSourceId, never duplicates it.
export function recordVendored(names, sourceId) {
  const store = load();
  store.bySource[sourceId] = store.bySource[sourceId] || [];
  const now = new Date().toISOString();
  let added = 0;
  for (const n of names) {
    if (!store.byName[n]) {
      store.byName[n] = { firstVendoredBy: sourceId, firstVendoredAt: now };
      added++;
    }
    store.byName[n].lastSeenSourceId = sourceId;
    if (!store.bySource[sourceId].includes(n)) store.bySource[sourceId].push(n);
  }
  save(store);
  return { added, alreadyKnown: names.length - added, total: Object.keys(store.byName).length };
}

export function stats() {
  const store = load();
  return {
    totalVendoredNames: Object.keys(store.byName).length,
    totalSources: Object.keys(store.bySource).length,
  };
}
