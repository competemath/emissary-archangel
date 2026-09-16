// Opening pull requests on the Tengoku tree from the banking pipeline.
//
// In PR mode nothing here touches `main`: a batch of records is committed on
// its own branch from a throwaway worktree (so the working tree the promote
// loop uses is never switched under it), pushed, opened as a PR with
// auto-merge, and the gate + merge queue take it from there. The commit is
// signed off (the gate's DCO check) with whatever identity the tree's git
// config carries, and the PR is authored by the `gh` login on this machine.
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { mkdtemp, mkdir, copyFile, readFile, readdir, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";

const x = promisify(execFile);

async function git(cwd: string, ...args: string[]): Promise<string> {
  const { stdout } = await x("git", args, { cwd, maxBuffer: 16 * 1024 * 1024 });
  return stdout.trim();
}

/** owner/repo of the tree's `origin`. */
export async function originRepo(repoDir: string): Promise<string> {
  const url = await git(repoDir, "remote", "get-url", "origin");
  const m = url.match(/github\.com[:/]([^/]+\/[^/.]+)(?:\.git)?$/);
  if (!m) throw new Error(`origin is not a GitHub repository: ${url}`);
  return m[1];
}

/** Names already on main (staging, per-PR staging files, trusted) for a library — a second copy would be a duplicate declaration. */
export async function existingNames(repoDir: string, library: string): Promise<Set<string>> {
  const files = [path.join(repoDir, "data", "staging", `${library}.jsonl`), path.join(repoDir, "data", "trusted", `${library}.jsonl`)];
  const nested = path.join(repoDir, "data", "staging", library);
  try {
    for (const f of await readdir(nested)) if (f.endsWith(".jsonl")) files.push(path.join(nested, f));
  } catch {
    /* no per-PR files yet */
  }
  const names = new Set<string>();
  for (const f of files) {
    let text = "";
    try {
      text = await readFile(f, "utf8");
    } catch {
      continue;
    }
    for (const line of text.split("\n")) {
      if (!line.trim()) continue;
      try {
        const r = JSON.parse(line);
        if (typeof r.name === "string") names.add(r.name);
      } catch {
        /* a bad line is the gate's problem, not ours */
      }
    }
  }
  return names;
}

export interface OpenedPr {
  number: number;
  url: string;
  branch: string;
}

/**
 * Commit `recordsFile` as `data/staging/<library>/<batchId>.jsonl` on a fresh
 * branch off `origin/main`, push it, open a PR and enable auto-merge.
 */
export async function openRecordsPr(opts: { repoDir: string; library: string; batchId: string; recordsFile: string; title: string; body: string }): Promise<OpenedPr> {
  const { repoDir, library, batchId, recordsFile, title, body } = opts;
  const repo = await originRepo(repoDir);
  const branch = `bank/${library}/${batchId}`;
  await git(repoDir, "fetch", "-q", "origin", "main");
  const wt = await mkdtemp(path.join(os.tmpdir(), "tengoku-bank-"));
  try {
    await git(repoDir, "worktree", "add", "-q", "--detach", wt, "origin/main");
    await git(wt, "switch", "-q", "-c", branch);
    const rel = path.join("data", "staging", library, `${batchId}.jsonl`);
    await mkdir(path.dirname(path.join(wt, rel)), { recursive: true });
    await copyFile(recordsFile, path.join(wt, rel));
    await git(wt, "add", "--", rel);
    await git(wt, "commit", "-q", "-s", "-m", `${title}\n\n${body}`);
    await git(wt, "push", "-q", "-u", "origin", branch);
    const { stdout } = await x("gh", ["pr", "create", "-R", repo, "--head", branch, "--title", title, "--body", body], { cwd: wt });
    const url = stdout.trim().split("\n").pop() || "";
    const number = Number(url.match(/\/pull\/(\d+)/)?.[1] ?? 0);
    if (number) await x("gh", ["pr", "merge", String(number), "-R", repo, "--squash", "--auto"], { cwd: wt }).catch(() => undefined);
    return { number, url, branch };
  } finally {
    await git(repoDir, "worktree", "remove", "--force", wt).catch(() => undefined);
    await rm(wt, { recursive: true, force: true }).catch(() => undefined);
    await git(repoDir, "branch", "-D", branch).catch(() => undefined);
  }
}
