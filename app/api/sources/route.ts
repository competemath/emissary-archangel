// The sources the pipeline knows (sources.json), for the console's pickers.
import { NextResponse } from "next/server";
import { listSources, loadSources } from "@/lib/sources";

export const dynamic = "force-dynamic";

export async function GET() {
  try {
    return NextResponse.json({ targetToolchain: loadSources().targetToolchain, sources: listSources() });
  } catch (e) {
    return NextResponse.json({ error: "sources_unavailable", detail: e instanceof Error ? e.message : String(e) }, { status: 500 });
  }
}
