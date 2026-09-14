// Console control of the local translation pipeline (see lib/pipeline.ts).
// Localhost only: this route starts and stops processes on this machine.
import { NextResponse } from "next/server";
import {
  SERVICE_NAMES, checkTree, loadConfig, saveConfig, startPromote, startRun, startService, startTreeRefresh, status, stopProc,
  type PipelineConfig, type RunScope, type ServiceName,
} from "@/lib/pipeline";

export const dynamic = "force-dynamic";

function localOnly(req: Request): NextResponse | null {
  const host = (req.headers.get("host") || "").replace(/:\d+$/, "");
  if (host === "localhost" || host === "127.0.0.1" || host === "[::1]") return null;
  return NextResponse.json({ error: "local_only" }, { status: 403 });
}

export async function GET(req: Request) {
  const denied = localOnly(req);
  if (denied) return denied;
  const url = new URL(req.url);
  const lines = Math.min(2000, Math.max(10, Number(url.searchParams.get("lines")) || 60));
  return NextResponse.json(await status(lines));
}

export async function POST(req: Request) {
  const denied = localOnly(req);
  if (denied) return denied;
  const body = (await req.json().catch(() => ({}))) as { action?: string; name?: string; scope?: RunScope; config?: Partial<PipelineConfig> };
  try {
    switch (body.action) {
      case "start-service": {
        if (!SERVICE_NAMES.includes(body.name as ServiceName)) return NextResponse.json({ error: "unknown_service" }, { status: 400 });
        return NextResponse.json({ ok: true, pid: await startService(body.name as ServiceName) });
      }
      case "start-all-services": {
        const started: Record<string, number | string> = {};
        for (const name of SERVICE_NAMES) {
          try { started[name] = (await startService(name)) ?? 0; } catch (e) { started[name] = (e as Error).message; }
        }
        return NextResponse.json({ ok: true, started });
      }
      case "stop-service": {
        if (!SERVICE_NAMES.includes(body.name as ServiceName)) return NextResponse.json({ error: "unknown_service" }, { status: 400 });
        return NextResponse.json({ ok: true, stopped: await stopProc(body.name as ServiceName) });
      }
      case "stop-all-services": {
        const stopped: Record<string, boolean> = {};
        for (const name of SERVICE_NAMES) stopped[name] = await stopProc(name);
        return NextResponse.json({ ok: true, stopped });
      }
      case "start-promote":
        return NextResponse.json({ ok: true, pid: startPromote() });
      case "stop-promote":
        return NextResponse.json({ ok: true, stopped: await stopProc("promote") });
      case "start-run": {
        const scope = body.scope && ["all", "file", "one"].includes(body.scope.type) ? body.scope : ({ type: "all" } as RunScope);
        return NextResponse.json({ ok: true, pid: startRun(scope) });
      }
      case "stop-run":
        return NextResponse.json({ ok: true, stopped: await stopProc("run") });
      case "check-tree":
        return NextResponse.json({ ok: true, ...(await checkTree()) });
      case "refresh-tree":
        return NextResponse.json({ ok: true, pid: startTreeRefresh() });
      case "stop-tree-refresh":
        return NextResponse.json({ ok: true, stopped: await stopProc("tree-refresh") });
      case "save-config":
        return NextResponse.json({ ok: true, config: saveConfig(body.config || {}) });
      case "get-config":
        return NextResponse.json({ ok: true, config: loadConfig() });
      default:
        return NextResponse.json({ error: "unknown_action" }, { status: 400 });
    }
  } catch (e) {
    return NextResponse.json({ error: "failed", detail: (e as Error).message }, { status: 500 });
  }
}
