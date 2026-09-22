import { NextResponse } from "next/server";
import { readFile, writeFile, rename, mkdir } from "node:fs/promises";
import path from "node:path";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { loadConfig } from "@/lib/pipeline";
import { existingNames, openRecordsPr } from "@/lib/tengoku-pr";

const execFileAsync = promisify(execFile);

// PR mode (config promote.viaPrs, or TENGOKU_VIA_PRS=1): records are banked
// into an ignored batch file under <tree>/.bank/<library>/ and every batch
// becomes one content PR (a per-PR staging file, signed off, auto-merged)
// instead of a commit on main. A batch closes after FLUSH_MAX records or
// FLUSH_AGE_MS, whichever comes first; promotion is the loop's job, in its
// own PRs. Nothing in PR mode runs promote.py from here.
const FLUSH_MAX = Number(process.env.TENGOKU_BANK_FLUSH_MAX || 200);
const FLUSH_AGE_MS = Number(process.env.TENGOKU_BANK_FLUSH_MIN || 10) * 60 * 1000;
function viaPrs(): boolean {
  return process.env.TENGOKU_VIA_PRS === "1" || !!loadConfig().promote.viaPrs;
}
type Batch = { id: string; file: string; startedAt: number; count: number };
// On `globalThis`, not a plain module-level `const`: a dev-mode hot-reload of this route
// re-evaluates the module, which would otherwise hand every open batch a brand-new, empty
// Map with nothing watching it — the age-based flush below skips creating a second interval
// (see its own guard) because it finds one already running, but that surviving interval
// closed over the OLD module instance's map, not this new one. A batch staged between the
// edit and the next server restart then sits forever: found live (a batch went unflushed for
// over an hour after an unrelated fix to this same file). Keyed off `globalThis` instead, the
// map itself survives a reload exactly like the interval does, so there is only ever one.
const batches: Map<string, Batch> = ((globalThis as { __tengokuBanks?: Map<string, Batch> }).__tengokuBanks ??= new Map());
function batchFor(source: string): { id: string; file: string; startedAt: number; count: number } {
  let b = batches.get(source);
  if (!b) {
    const id = new Date().toISOString().replace(/[-:]/g, "").replace(/\.\d+Z$/, "Z");
    b = { id, file: path.join(TENGOKU_REPO, ".bank", sanitizeSegment(source), `${id}.jsonl`), startedAt: Date.now(), count: 0 };
    batches.set(source, b);
  }
  return b;
}
/** Close the batch and open its PR; the batch file moves under .bank/<library>/sent (or /failed). Runs under the git lock. */
async function flushBatch(source: string, why: string): Promise<string> {
  const b = batches.get(source);
  if (!b || b.count === 0) return "nothing to flush";
  batches.delete(source);
  const dir = path.dirname(b.file);
  try {
    const pr = await openRecordsPr({
      repoDir: TENGOKU_REPO,
      library: sanitizeSegment(source),
      batchId: b.id,
      recordsFile: b.file,
      title: `Stage ${source}: ${b.count} record${b.count === 1 ? "" : "s"} (${b.id})`,
      body: `Banked by Emissary-Archangel (${why}). One per-PR staging file; the merge queue compiles exactly these records.`,
    });
    await mkdir(path.join(dir, "sent"), { recursive: true });
    await rename(b.file, path.join(dir, "sent", `${b.id}.jsonl`));
    // eslint-disable-next-line no-console
    console.log(`[bank] PR #${pr.number} for ${source}: ${b.count} records (${why}) ${pr.url}`);
    return `PR #${pr.number} (${b.count} records)`;
  } catch (e) {
    await mkdir(path.join(dir, "failed"), { recursive: true }).catch(() => undefined);
    await rename(b.file, path.join(dir, "failed", `${b.id}.jsonl`)).catch(() => undefined);
    const msg = e instanceof Error ? e.message : String(e);
    // eslint-disable-next-line no-console
    console.error(`[bank] PR for ${source} batch ${b.id} failed (${b.count} records kept in .bank/${sanitizeSegment(source)}/failed):`, msg);
    return `PR failed: ${msg}`;
  }
}
// Age-based flushes happen even when nothing new arrives.
if (typeof setInterval === "function" && !(globalThis as { __tengokuBankTimer?: unknown }).__tengokuBankTimer) {
  (globalThis as { __tengokuBankTimer?: unknown }).__tengokuBankTimer = setInterval(() => {
    for (const [source, b] of batches) {
      if (Date.now() - b.startedAt >= FLUSH_AGE_MS) void withGitLock(() => flushBatch(source, "age"));
    }
  }, 60 * 1000);
}

async function stageViaPr(source: string, name: string, record: Record<string, unknown>): Promise<{ staged: boolean; detail?: string }> {
  return withGitLock(async () => {
    const known = await existingNames(TENGOKU_REPO, sanitizeSegment(source));
    if (known.has(name)) return { staged: false, detail: `${name} is already on main (staging or trusted); append-only data cannot replace it` };
    const b = batchFor(source);
    await mkdir(path.dirname(b.file), { recursive: true });
    let lines: string[] = [];
    try {
      lines = (await readFile(b.file, "utf8")).split("\n").filter((l) => l.trim());
    } catch {
      /* first record of the batch */
    }
    const kept = lines.filter((l) => {
      try {
        return JSON.parse(l).name !== name;
      } catch {
        return true;
      }
    });
    kept.push(JSON.stringify(record));
    await writeFile(b.file, kept.join("\n") + "\n");
    b.count = kept.length;
    let detail = `batch ${b.id}: ${b.count} record${b.count === 1 ? "" : "s"}`;
    if (b.count >= FLUSH_MAX) detail += `; ${await flushBatch(source, "size")}`;
    return { staged: true, detail };
  });
}

// Every distinct translation corpus gets its own file — never merged into
// one, so a bug or corruption in one source's queue can't touch another's,
// and each stays small enough for the existing whole-file read-modify-write
// pattern to remain fine at its scale. `source` is a query param, so it MUST
// be checked against this allowlist before touching the filesystem with it
// — never interpolate it into a path unchecked.
const SOURCES: Record<string, string> = {
  competemath: "queue.json",
  "equational-theories": "queue-equational-theories.json",
};
const DEFAULT_SOURCE = "competemath";

function resolveQueuePath(source: string): string {
  const filename = SOURCES[source];
  if (!filename) throw new Error(`unknown queue source: ${source}`);
  return path.join(process.cwd(), "data", filename);
}

// Multiple theorem translations can finish/update around the same moment —
// with 3+ concurrent runs, concurrent PATCH calls WILL overlap. A plain
// read-modify-write here corrupted the file for real: two writeFile() calls
// interleaved and left the array closed twice (`]]`), which is exactly what
// happened in production and took the whole queue down with
// "Unexpected end of JSON input" on every GET afterward.
//
// Fix has two parts: (1) an in-process mutex so this module never has two
// read-modify-write cycles in flight at once for the SAME source — a promise
// chain is enough since a single Next.js dev/prod server process is what's
// actually racing itself; kept PER-SOURCE (not one global chain) so a write
// to one corpus's queue never waits behind an unrelated one. (2) an atomic
// write (write to a temp file, then rename() over the real path) so even a
// crash mid-write can never leave a half-written or interleaved file on disk
// — rename() is atomic on the same filesystem.
const writeChains = new Map<string, Promise<unknown>>();

function withQueueLock<T>(source: string, fn: () => Promise<T>): Promise<T> {
  const prior = writeChains.get(source) ?? Promise.resolve();
  const result = prior.then(fn, fn);
  // Swallow so one failed write doesn't wedge the chain for every future
  // caller — each caller still gets its own real result/rejection above.
  writeChains.set(source, result.catch(() => {}));
  return result;
}

async function readQueue(source: string): Promise<Array<Record<string, unknown>>> {
  const raw = await readFile(resolveQueuePath(source), "utf8");
  return JSON.parse(raw);
}

async function writeQueueAtomic(source: string, queue: Array<Record<string, unknown>>): Promise<void> {
  const queuePath = resolveQueuePath(source);
  const tmpPath = `${queuePath}.tmp`;
  await writeFile(tmpPath, JSON.stringify(queue, null, 2));
  await rename(tmpPath, queuePath);
}

// Bank every verified theorem into the REAL Tengoku repo (competemath/tengoku
// on GitHub) IMMEDIATELY — per your own reasoning, a proof sitting only in
// queue.json is one crash away from being lost, and the longer it waits
// un-banked, the more exposure to contamination (a later run overwriting it,
// a corrupted queue file, etc.). A prior version of this committed to an
// orphan LOCAL-ONLY repo and never pushed — worthless as a backup and
// invisible to everyone else. This clone has a real `origin` remote and
// every stage both commits AND pushes straight to `main`; nothing here ever
// talks to CompeteMath's own database directly (Tengoku is its own repo).
const TENGOKU_REPO =
  process.env.TENGOKU_STAGING_REPO || path.join(process.cwd(), "..", "compete-math", "tengoku");

function sanitizeSegment(s: string): string {
  return s.replace(/\.\./g, "_").replace(/[^A-Za-z0-9_.\-]/g, "_");
}

// Tengoku's own toolchain convention: `toolchain` records what the PROOF
// given here actually compiles under. Emissary-Archangel entries are
// translations INTO v4.34.0-rc2 (see infra/equational-theories-4291/
// repo-rc2-test); plain CompeteMath entries are proved directly against
// CompeteMath's own production toolchain — no translation involved.
// Where each corpus's ORIGINAL checkout lives — the tree generator reads the
// corpus's definition modules from it (same map as theorem-text/route.ts's
// REPO_ROOTS, duplicated for the same reason: no shared module boundary).
const CORPUS_ROOT_BY_SOURCE: Record<string, string> = {
  "equational-theories": path.join(process.cwd(), "infra", "equational-theories-4291", "repo"),
};

const TOOLCHAIN_BY_SOURCE: Record<string, string> = {
  competemath: "leanprover/lean4:v4.29.1",
  "equational-theories": "leanprover/lean4:v4.34.0-rc2",
};

// Best-effort: a clean source_url if the queue entry already has one
// (CompeteMath entries do, via `sourceUrl`), else try to pull one out of
// equational-theories' own free-text `sourceRef` convention
// ("owner/repo@<commit>:path/to/File.lean ..." — see queue-equational-
// theories.json), else fall back to the raw text so the record still
// carries SOME provenance rather than silently dropping the field.
function resolveSourceUrl(entry: Record<string, unknown>): string | null {
  if (typeof entry.sourceUrl === "string" && entry.sourceUrl) return entry.sourceUrl;
  const ref = typeof entry.sourceRef === "string" ? entry.sourceRef : null;
  if (!ref) return null;
  const m = ref.match(/^([\w.-]+\/[\w.-]+)@([0-9a-f]{7,40}):(\S+?\.lean)/);
  return m ? `https://github.com/${m[1]}/blob/${m[2]}/${m[3]}` : ref;
}

// Tengoku's record shape (see tengoku/README.md "Record shape") splits the
// declaration header from its proof body at the FIRST `:=` — this mirrors
// every other entry already in data/tentative|trusted/*.jsonl.
// A verified script is no longer a single theorem: it carries everything the
// theorem needs to be self-contained (the corpus modules it depends on, its
// own file's earlier declarations), then the theorem. Splitting at the first
// `:=` in the file put a `Magma.op` definition into `proof`. Split at the
// TARGET declaration instead: `context` = everything before it, `statement` =
// its header up to its own `:=`, `proof` = from that `:=` to the end.
function splitStatementAndProof(fullText: string, name: string): { context: string; statement: string; proof: string } | null {
  const bare = name.split(".").pop() ?? name;
  const declRe = new RegExp(
    `^[ \\t]*(?:@\\[[^\\]]*\\][ \\t]*)*(?:(?:private|protected|nonrec)[ \\t]+)*(?:theorem|lemma)[ \\t]+(?:[\\w'.«»]*\\.)?${bare.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![\\w'])`,
    "gm",
  );
  let decl: RegExpExecArray | null = null;
  for (let m = declRe.exec(fullText); m; m = declRe.exec(fullText)) decl = m; // last one: helpers come first
  const start = decl ? decl.index : -1;
  if (start === -1) {
    const idx = fullText.indexOf(":=");
    if (idx === -1) return null;
    return { context: "", statement: fullText.slice(0, idx).trim(), proof: fullText.slice(idx).trim() };
  }
  const idx = fullText.indexOf(":=", start);
  if (idx === -1) return null;
  return {
    context: fullText.slice(0, start).replace(/\s+$/, ""),
    statement: fullText.slice(start, idx).trim(),
    proof: fullText.slice(idx).trim(),
  };
}

// A dedicated mutex for git itself — separate from the per-source queue
// lock above, because it protects a DIFFERENT resource (the one shared git
// working tree) that every source's verified entries commit into. Multiple
// worker-pool slots can verify around the same moment; without this, two
// concurrent `git commit` calls race on the same index/HEAD.
let gitChain: Promise<unknown> = Promise.resolve();

function withGitLock<T>(fn: () => Promise<T>): Promise<T> {
  const result = gitChain.then(fn, fn);
  gitChain = result.catch(() => {});
  return result;
}

async function stageVerifiedTheorem(
  source: string,
  entry: Record<string, unknown>,
): Promise<{ staged: boolean; detail?: string }> {
  const name = String(entry.name ?? entry.id);
  // Tengoku's generator supplies the tree's own root import for every module; a leading
  // `import ...` line here (e.g. `import Tengoku.All`, `import Mathlib`) would land in
  // `context` and fail the gate's content-lint ("no import inside a record"). Found live:
  // it had been silently landing in `context` since before that check existed (50 of 8,920
  // already-trusted equational-theories records carry it, all promoted pre-2026-09-16) —
  // harmless before the gate, a hard failure on every submission since.
  const fullText = String(entry.proof ?? "").replace(/^(?:\s*import\s+\S+\s*\n)+/, "");
  if (!fullText.trim()) return { staged: false, detail: "no proof text on entry" };
  const split = splitStatementAndProof(fullText, name);
  if (!split) return { staged: false, detail: "no ':=' found — can't split into statement/proof" };

  const record = {
    name,
    statement: split.statement,
    proof: split.proof,
    // Everything the theorem needed in front of it to be self-contained
    // (corpus modules it depends on, its file's earlier declarations) — the
    // tree generator folds this into the module for `source_path`.
    context: split.context,
    source_path: typeof entry.sourcePath === "string" ? entry.sourcePath : null,
    status: "staging",
    staged_at: new Date().toISOString(),
    library: source,
    source_url: resolveSourceUrl(entry),
    toolchain: TOOLCHAIN_BY_SOURCE[source] ?? null,
  };

  if (viaPrs()) return stageViaPr(source, name, record);

  // Direct mode (until the ruleset): ONE file per library, matching every
  // other data/**/*.jsonl file in the repo (data/tentative/<library>.jsonl,
  // data/trusted/<library>.jsonl).
  const relPath = path.join("data", "staging", `${sanitizeSegment(source)}.jsonl`);
  const absPath = path.join(TENGOKU_REPO, relPath);

  return withGitLock(async () => {
    await mkdir(path.dirname(absPath), { recursive: true });
    // Upsert by name: re-verifying an already-staged entry (e.g. a retried
    // translation with a cleaner proof) replaces its line instead of
    // duplicating it — same "re-verify with identical/changed content isn't
    // an error" spirit as the old "nothing to commit" handling below.
    let existingLines: string[] = [];
    try {
      existingLines = (await readFile(absPath, "utf8")).split("\n").filter((l) => l.trim());
    } catch {
      /* file doesn't exist yet — first entry for this library */
    }
    const kept = existingLines.filter((l) => {
      try {
        return JSON.parse(l).name !== name;
      } catch {
        return true; // never drop a line we can't parse — surface it, don't silently lose it
      }
    });
    kept.push(JSON.stringify(record));
    await writeFile(absPath, kept.join("\n") + "\n");

    // The record is the source of truth; the tree module is derived from it.
    // Promotion (scripts/promote.py) moves this source file's staging records
    // — only once the file has been quiet for 5 minutes: a file being banked
    // every few seconds would otherwise rebuild its whole module per bank.
    // scripts/promote-loop.sh in the tree does the same for finished files.
    // to data/trusted, regenerates the file's module and `lake build`s it:
    // only a module that builds in the tree becomes trusted — a failed build
    // puts the records back in staging with the error, and the module is
    // regenerated from what IS trusted. Failure here is reported, never
    // fatal: the record is still staged.
    let generated: string[] = [];
    let promotion = "";
    const corpusRoot = CORPUS_ROOT_BY_SOURCE[source];
    if (corpusRoot && record.source_path) {
      const libNs = source.split(/[-_ ]+/).filter(Boolean).map((p) => p[0].toUpperCase() + p.slice(1)).join("");
      generated = [
        path.join("data", "trusted", `${sanitizeSegment(source)}.jsonl`),
        path.join("Tengoku", libNs),
        path.join("Tengoku", `${libNs}.lean`),
        path.join("Tengoku", "All.lean"),
      ];
      try {
        const { stdout } = await execFileAsync(
          "python3",
          ["scripts/promote.py", "--corpus", corpusRoot, "--library", source, "--only", record.source_path, "--quiescent", "300"],
          { cwd: TENGOKU_REPO, maxBuffer: 16 * 1024 * 1024, timeout: 15 * 60 * 1000 },
        );
        promotion = stdout.trim().split("\n").pop() || "";
      } catch (e) {
        // exit 2 = the module did not build (records are back in staging, with the reason)
        const err = e as { stdout?: string; message?: string };
        promotion = (err.stdout || "").trim().split("\n").filter(Boolean).pop() || err.message || String(e);
        // eslint-disable-next-line no-console
        console.error(`[stage] promotion did not complete for ${name}:`, promotion);
      }
    }

    try {
      await execFileAsync("git", ["add", "-A", "--", relPath, ...generated], { cwd: TENGOKU_REPO });
      const verb = /^\S+: promoted [1-9]/.test(promotion) && !/not promoted [1-9]/.test(promotion) ? "Promote" : "Stage";
      await execFileAsync("git", ["commit", "-m", `${verb} ${source}/${name} (#${entry.id})${promotion ? `\n\n${promotion}` : ""}`], { cwd: TENGOKU_REPO });
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      // "nothing to commit" means this exact content is already staged
      // (e.g. a re-verify with an identical proof) — not a real failure.
      if (!/nothing to commit/i.test(msg)) return { staged: false, detail: msg };
    }
    try {
      await execFileAsync("git", ["push", "origin", "main"], { cwd: TENGOKU_REPO });
      return { staged: true };
    } catch (e) {
      // The commit is real and safe either way — only the push failed (e.g.
      // a network blip, or `main` moved upstream). Report it distinctly
      // rather than silently leaving it local again; the NEXT stage's push
      // will carry this commit along too, so nothing is lost.
      const msg = e instanceof Error ? e.message : String(e);
      return { staged: true, detail: `committed locally but push to origin failed (will retry next stage): ${msg}` };
    }
  });
}

export async function GET(req: Request) {
  const source = new URL(req.url).searchParams.get("source") || DEFAULT_SOURCE;
  if (!(source in SOURCES)) {
    return NextResponse.json({ error: "unknown_source", detail: source }, { status: 400 });
  }
  try {
    const queue = await readQueue(source);
    return NextResponse.json(queue);
  } catch (e) {
    // A real error here used to surface as an opaque client-side
    // "Unexpected end of JSON input" (the frontend called .json() on a
    // non-JSON 500 body). Return real, parseable JSON on failure too.
    return NextResponse.json(
      { error: "queue_read_failed", detail: e instanceof Error ? e.message : String(e) },
      { status: 500 },
    );
  }
}

// Local-only persistence — this never writes to CompeteMath's own database,
// and never pushes anywhere. Results (proof text, gate status) are stored
// in this app's own data/*.json files, and a 'verified' entry is ALSO
// immediately committed into compete-math/tengoku's own local git repo (see
// TENGOKU_REPO / stageVerifiedTheorem) — banked as soon as it's known-good,
// not held pending a later manual step. Pushing that repo to any remote
// stays manual and deliberate.
export async function PATCH(req: Request) {
  const source = new URL(req.url).searchParams.get("source") || DEFAULT_SOURCE;
  if (!(source in SOURCES)) {
    return NextResponse.json({ error: "unknown_source", detail: source }, { status: 400 });
  }
  try {
    const update = await req.json();
    return await withQueueLock(source, async () => {
      const queue = await readQueue(source);
      const idx = queue.findIndex((e) => e.id === update.id);
      if (idx === -1) {
        return NextResponse.json({ error: "not_found" }, { status: 404 });
      }
      queue[idx] = { ...queue[idx], ...update };
      await writeQueueAtomic(source, queue);
      // Stage immediately on the transition to 'verified' — never wait for a
      // later, separate promotion step. A staging failure here is reported
      // back but does NOT fail the request: the queue update (the source of
      // truth for "is this verified") already succeeded and persisted above.
      let staging: { staged: boolean; detail?: string } | undefined;
      if (update.status === "verified") {
        staging = await stageVerifiedTheorem(source, queue[idx]).catch((e) => ({
          staged: false,
          detail: e instanceof Error ? e.message : String(e),
        }));
      }
      return NextResponse.json({ ...queue[idx], ...(staging ? { staging } : {}) });
    });
  } catch (e) {
    return NextResponse.json(
      { error: "queue_update_failed", detail: e instanceof Error ? e.message : String(e) },
      { status: 500 },
    );
  }
}
