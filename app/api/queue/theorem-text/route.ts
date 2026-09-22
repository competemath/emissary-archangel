import { NextResponse } from "next/server";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { corpusRootFor, queuePathFor } from "@/lib/sources";

// Which sources exist, where each one's queue and checkout are: sources.json
// (lib/sources.ts). `source` is a query param and is only ever used through
// that registry — never interpolated into a path unchecked.
//
// Sources whose queue entries store sourcePath/sourceLine instead of a
// pre-baked oldTheoremText are reconstructed from their checkout on demand
// (storing the full per-theorem file-prefix context inline blew the
// equational-theories queue up to 524MB, since hundreds of theorems can share
// one file).

// Constructs a theorem's full compilable context on demand — cheap (one
// file read + slice), and only ever done for the ONE theorem actually being
// run, never for the whole queue at once.
export async function GET(req: Request) {
  const url = new URL(req.url);
  const source = url.searchParams.get("source") || "competemath";
  const idParam = url.searchParams.get("id");
  const queuePath = queuePathFor(source);
  if (!queuePath) {
    return NextResponse.json({ error: "unknown_source", detail: source }, { status: 400 });
  }
  const id = Number(idParam);
  if (!Number.isFinite(id)) {
    return NextResponse.json({ error: "invalid_id", detail: idParam }, { status: 400 });
  }

  try {
    const queue = JSON.parse(await readFile(queuePath, "utf8")) as Array<Record<string, unknown>>;
    const entry = queue.find((e) => e.id === id);
    if (!entry) {
      return NextResponse.json({ error: "not_found" }, { status: 404 });
    }

    // Sources that already carry a pre-baked oldTheoremText (CompeteMath's
    // 232 — small enough that redundancy was never a problem) just pass it
    // through, so the frontend can call this one endpoint uniformly
    // regardless of source.
    if (typeof entry.oldTheoremText === "string") {
      return NextResponse.json({ oldTheoremText: entry.oldTheoremText });
    }

    const repoRoot = corpusRootFor(source);
    const sourcePath = entry.sourcePath;
    const sourceLine = entry.sourceLine;
    if (!repoRoot || typeof sourcePath !== "string" || typeof sourceLine !== "number" || sourcePath.includes("..")) {
      return NextResponse.json(
        { error: "no_construction_path", detail: "entry has neither oldTheoremText nor sourcePath/sourceLine" },
        { status: 500 },
      );
    }

    const fileContent = await readFile(path.join(repoRoot, sourcePath), "utf8");
    // `sourceLine` is 1-indexed and IS the declaration's own first line —
    // everything strictly before it (imports, plus every earlier local
    // declaration in the same file) is what makes the target theorem's
    // OWN local dependencies (defs, abbrevs, notations declared earlier in
    // the same file) resolvable, since Lean's visibility within one file is
    // exactly "declared earlier in this file or an imported one."
    const prefix = fileContent.split("\n").slice(0, sourceLine - 1).join("\n") + "\n\n";
    const oldStatement = String(entry.oldStatement ?? "");
    const oldProofText = String(entry.oldProofText ?? "");
    const oldTheoremText = `${prefix}${oldStatement}${oldProofText}`;
    return NextResponse.json({ oldTheoremText });
  } catch (e) {
    return NextResponse.json(
      { error: "theorem_text_failed", detail: e instanceof Error ? e.message : String(e) },
      { status: 500 },
    );
  }
}
