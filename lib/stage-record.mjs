// The Tengoku staging record for a verified queue entry: shared by the app's /api/queue route and the
// headless queue server the cloud translation runs (scripts/queue-server.mjs), so both bank the same shape.

// Best-effort: a clean source_url if the queue entry already has one
// (CompeteMath entries do, via `sourceUrl`), else try to pull one out of
// equational-theories' own free-text `sourceRef` convention
// ("owner/repo@<commit>:path/to/File.lean ..." — see queue-equational-
// theories.json), else fall back to the raw text so the record still
// carries SOME provenance rather than silently dropping the field.
export function resolveSourceUrl(entry) {
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
// Where the declaration's header ends: its own `:=`, or — for a theorem proved by pattern matching, which has no
// `:=` of its own — the first `|` alternative. Both only outside brackets; a `:=` inside `(h : a := b)` or inside a
// proof arm's `have … :=` is not it (splitting there put a whole proof into `statement`).
// `| pat, pat => rhs` starts a line; an absolute value `|x| ≤ 1` starting a continuation line has no `=>` before its `:=`
function isAlternative(text, i) {
  if (text[i + 1] === "|") return false;
  const nl = text.indexOf("\n", i);
  const line = text.slice(i + 1, nl === -1 ? text.length : nl);
  const arrow = line.indexOf("=>");
  const assign = line.indexOf(":=");
  return arrow !== -1 && (assign === -1 || arrow < assign);
}

function headerEnd(text, start) {
  let depth = 0;
  for (let i = start; i < text.length; i++) {
    const c = text[i];
    if (c === "-" && text[i + 1] === "-") { const nl = text.indexOf("\n", i); if (nl === -1) return -1; i = nl; continue; }
    if (c === "/" && text[i + 1] === "-") { const e = text.indexOf("-/", i + 2); if (e === -1) return -1; i = e + 1; continue; }
    if ("([{⟨⦃".includes(c)) depth++;
    else if (")]}⟩⦄".includes(c)) depth = Math.max(0, depth - 1);
    else if (depth === 0 && c === ":" && text[i + 1] === "=") return i;
    else if (depth === 0 && c === "|" && /\n[ \t]*$/.test(text.slice(Math.max(start, i - 200), i)) && isAlternative(text, i)) return i;
  }
  return -1;
}

// A record banked before the split was fixed was cut at the first `:=` after its keyword (inside
// `@[to_additive (attr := simp)]`, or in a later theorem's proof for one proved by pattern matching): re-split
// statement + proof at the header's own end. A record already split right comes back unchanged.
export function resplitRecord(r) {
  const text = `${String(r.statement ?? "").trimEnd()} ${String(r.proof ?? "").trimStart()}`;
  const i = headerEnd(text, 0);
  if (i <= 0 || text.slice(0, i).trimEnd() === String(r.statement ?? "").trimEnd()) return r;
  return { ...r, statement: text.slice(0, i).trimEnd(), proof: text.slice(i) };
}

export function splitStatementAndProof(fullText, name) {
  const bare = name.split(".").pop() ?? name;
  const declRe = new RegExp(
    `^[ \\t]*(?:@\\[[^\\]]*\\][ \\t]*)*(?:(?:private|protected|nonrec)[ \\t]+)*(?:theorem|lemma)[ \\t]+(?:[\\w'.«»]*\\.)?${bare.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![\\w'])`,
    "gm",
  );
  let decl = null;
  for (let m = declRe.exec(fullText); m; m = declRe.exec(fullText)) decl = m; // last one: helpers come first
  const start = decl ? decl.index : -1;
  if (start === -1) {
    const idx = fullText.indexOf(":=");
    if (idx === -1) return null;
    return { context: "", statement: fullText.slice(0, idx).trim(), proof: fullText.slice(idx).trim() };
  }
  const idx = headerEnd(fullText, start);
  if (idx === -1) return null;
  return {
    context: fullText.slice(0, start).replace(/\s+$/, ""),
    statement: fullText.slice(start, idx).trim(),
    proof: fullText.slice(idx).trim(),
  };
}

/** The staging record for a verified entry, or { error } when its proof text cannot be split. */
export function stagingRecord(source, entry, toolchain) {
  const name = String(entry.name ?? entry.id);
  // Tengoku's generator supplies the tree's own root import for every module; a leading
  // `import ...` line here (e.g. `import Tengoku.All`, `import Mathlib`) would land in
  // `context` and fail the gate's content-lint ("no import inside a record"). Found live:
  // it had been silently landing in `context` since before that check existed (50 of 8,920
  // already-trusted equational-theories records carry it, all promoted pre-2026-09-16) —
  // harmless before the gate, a hard failure on every submission since.
  const fullText = String(entry.proof ?? "").replace(/^(?:\s*import\s+\S+\s*\n)+/, "");
  if (!fullText.trim()) return { error: "no proof text on entry" };
  const split = splitStatementAndProof(fullText, name);
  if (!split) return { error: "no ':=' found — can't split into statement/proof" };
  return {
    record: {
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
      toolchain,
    },
  };
}
