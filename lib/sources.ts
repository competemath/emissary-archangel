// The translation-source registry: sources.json at the app root, the one place
// "which sources exist, where their checkout is, which queue file is theirs"
// lives. The queue routes, the pipeline panel, the queue console, run-recurse
// and the bridge all read it — nothing per-source is hardcoded anywhere else.
import fs from "node:fs";
import path from "node:path";

export interface SourceSpec {
  label: string;
  /** "prebaked": entries carry oldTheoremText (CompeteMath); otherwise a corpus checkout is read on demand. */
  kind?: "prebaked" | "corpus";
  repo?: string;
  commit?: string;
  /** The source's own toolchain (setup builds it there); translations target `targetToolchain`. */
  toolchain?: string;
  roots?: string[];
  corpusRoot?: string;
  subdir?: string; // the Lake project inside the clone (a repository of several projects)
  queueFile?: string;
  targetToolchain?: string;
  /** scripts/setup-sources.mjs only: extra setup-source.mjs flags, and "last" for a library that takes days. */
  setup?: { args?: string[]; order?: "last" };
}

export interface SourcesDoc {
  targetToolchain: string;
  tentativeDir?: string;
  sources: Record<string, SourceSpec>;
}

export interface SourceInfo {
  key: string;
  label: string;
  kind: "prebaked" | "corpus";
  toolchain: string | null;
  /** The queue file exists and (for a corpus) the checkout is on disk: selectable for a run. */
  ready: boolean;
}

const APP_ROOT = process.cwd();
const KEY_RE = /^[a-z0-9][a-z0-9-]*$/;

export function loadSources(): SourcesDoc {
  const doc = JSON.parse(fs.readFileSync(path.join(APP_ROOT, "sources.json"), "utf8")) as SourcesDoc;
  for (const k of Object.keys(doc.sources)) if (!KEY_RE.test(k)) throw new Error(`sources.json: bad source key ${JSON.stringify(k)}`);
  return doc;
}

export function sourceSpec(source: string): SourceSpec | null {
  return KEY_RE.test(source) ? loadSources().sources[source] ?? null : null;
}

/** data/<file> holding this source's queue, or null for an unknown source. */
export function queuePathFor(source: string): string | null {
  const s = sourceSpec(source);
  return s ? path.join(APP_ROOT, "data", s.queueFile || `queue-${source}.json`) : null;
}

/** The source's checkout (sources only after setup), or null when it has none. */
export function corpusRootFor(source: string): string | null {
  const s = sourceSpec(source);
  if (!s || !s.repo) return null;
  const env = process.env[`CORPUS_ROOT_${source.toUpperCase().replace(/[^A-Z0-9]+/g, "_")}`];
  return env || path.resolve(APP_ROOT, s.corpusRoot || path.join("infra", source, "repo"), s.subdir || "");
}

/** The toolchain a verified entry of this source compiles under (the tree's, unless the source proves directly). */
export function targetToolchainFor(source: string): string | null {
  const doc = loadSources();
  const s = doc.sources[source];
  return s ? s.targetToolchain || doc.targetToolchain : null;
}

export function listSources(): SourceInfo[] {
  const doc = loadSources();
  return Object.entries(doc.sources).map(([key, s]) => {
    const queue = path.join(APP_ROOT, "data", s.queueFile || `queue-${key}.json`);
    const root = s.repo ? corpusRootFor(key) : null;
    return {
      key,
      label: s.label || key,
      kind: s.repo ? "corpus" : "prebaked",
      toolchain: s.toolchain ?? null,
      ready: fs.existsSync(queue) && (!root || fs.existsSync(root)),
    };
  });
}
