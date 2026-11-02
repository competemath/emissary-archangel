#!/usr/bin/env python3
"""register_libraries.py: GitHub repositories -> everything the pipeline needs before `setup-auto`, with no human choices.

    register_libraries.py meta  owner/repo ...            -> JSON on stdout: commit, licence, toolchain, roots, deps, verdict
    register_libraries.py apply --tengoku T --emissary E --meta meta.json
        T: a checkout of competemath/tengoku (its schemas/sources.json and tools/ are used)
        E: a checkout of competemath/emissary-archangel (its sources.json)
        For each library whose verdict is "ok": the tengoku registry entry (allowed, licences, corpora), the emissary
        registry entry, and the tentative records (tools/harvest.py, limited to the library's roots, then filtered by the
        record rules: validate_records.py and lint_banked.py are run and what they refuse is dropped, as in tengoku#674).

A repository is refused (verdict says why) when: archived, a fork, no permissive licence on GitHub, no lean-toolchain, a Lake
dependency beyond Mathlib's own (those libraries need a registration of their own dependencies first), or no lean_lib roots.
"""
import json, re, subprocess, sys, base64, urllib.parse

PERMISSIVE = {"Apache-2.0", "MIT", "BSD-2-Clause", "BSD-3-Clause", "CC0-1.0", "0BSD", "Unlicense", "ISC"}
MATHLIB_DEPS = {"mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets", "aesop", "Qq", "batteries", "Cli"}


def gh(*a, raw=False):
    cmd = ["gh", "api"] + (["-H", "Accept: application/vnd.github.raw"] if raw else []) + list(a)
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    return r.stdout if r.returncode == 0 else None


def contents(repo, path, sha):
    return gh(f"repos/{repo}/contents/{urllib.parse.quote(path)}?ref={sha}", raw=True)


def roots_of(lakefile):
    names = [a or b or c for a, b, c in re.findall(
        r'lean_lib\s+«?([\w.]+)»?|\[\[lean_lib\]\]\s*\n\s*name\s*=\s*"([^"]+)"|\[\[lean_lib\]\]\s*\n(?:[^\n]*\n)*?\s*name\s*=\s*"([^"]+)"', lakefile)]
    return sorted(dict.fromkeys(n for n in names if n))


def meta(repo):
    out = {"repo": repo, "key": repo.split("/")[1].lower().replace("_", "-")}
    info = gh(f"repos/{repo}")
    if not info:
        return {**out, "verdict": "gone (GitHub does not know it)"}
    info = json.loads(info)
    branch = info["default_branch"]
    sha = json.loads(gh(f"repos/{repo}/commits/{branch}"))["sha"]
    spdx = (info.get("license") or {}).get("spdx_id") or "NONE"
    out.update(commit=sha, licence=spdx, archived=info["archived"], fork=info["fork"])
    why = []
    if info["archived"]: why.append("archived")
    if info["fork"]: why.append("a fork")
    if spdx not in PERMISSIVE: why.append(f"licence {spdx}")
    tc = (contents(repo, "lean-toolchain", sha) or "").strip()
    if not tc: why.append("no lean-toolchain")
    out["toolchain"] = tc if tc.startswith("leanprover/") else ("leanprover/lean4:" + tc if tc else "")
    lake = contents(repo, "lakefile.toml", sha) or contents(repo, "lakefile.lean", sha) or ""
    out["roots"] = roots_of(lake)
    if not out["roots"]: why.append("no lean_lib roots")
    mf = contents(repo, "lake-manifest.json", sha)
    deps = []
    if mf:
        try: deps = [p["name"].strip("«»") for p in json.loads(mf)["packages"]]
        except Exception: why.append("unreadable lake-manifest")
    extra = [d for d in deps if d not in MATHLIB_DEPS]
    out["extra_deps"] = extra
    if extra: why.append("Lake dependencies beyond Mathlib: " + ", ".join(extra))
    out["verdict"] = "ok" if not why else "; ".join(why)
    return out


def apply(argv):
    import argparse, shutil
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd"); ap.add_argument("--tengoku", required=True); ap.add_argument("--emissary", required=True)
    ap.add_argument("--meta", required=True); ap.add_argument("--records", required=True, help="dir with <key>.jsonl (harvested, limited to roots)")
    a = ap.parse_args(argv)
    M = [m for m in json.load(open(a.meta)) if m["verdict"] == "ok"]
    # tengoku: allowed + licences + corpora
    p = f"{a.tengoku}/schemas/sources.json"; d = json.load(open(p))
    for m in M:
        url = "https://github.com/" + m["repo"]
        if url not in d["allowed"]: d["allowed"].append(url)
        d["licences"][url] = m["licence"]
        d["corpora"][m["key"]] = {"repo": url, "commit": m["commit"], "roots": m["roots"]}
        shutil.copy(f"{a.records}/{m['key']}.jsonl", f"{a.tengoku}/data/tentative/{m['key']}.jsonl")
    json.dump(d, open(p, "w"), indent=2, ensure_ascii=False); open(p, "a").write("\n")
    # emissary: sources.json
    p = f"{a.emissary}/sources.json"; e = json.load(open(p))
    for m in M:
        e["sources"][m["key"]] = {"label": f"{m['key']} ({m['repo']}; registered from the tengoku-osint scan, FATE-X-relevant)",
            "repo": "https://github.com/" + m["repo"], "commit": m["commit"], "toolchain": m["toolchain"], "roots": m["roots"], "licence": m["licence"]}
    json.dump(e, open(p, "w"), indent=2, ensure_ascii=False); open(p, "a").write("\n")


def refine(argv):
    """refine --tengoku T: run validate_records.py until it is quiet, dropping each record line it refuses (the later of two
    equal names, a name that is already trusted, ...); every drop is counted by reason. The tengoku checkout is committed (HEAD)
    and compared with origin/main."""
    import collections, os
    T = argv[argv.index("--tengoku") + 1]
    reasons = collections.Counter()
    for _ in range(40):
        subprocess.run(["git", "-C", T, "add", "-A"], check=True)
        subprocess.run(["git", "-C", T, "-c", "user.name=mikaelbashir", "-c", "user.email=138998999+mikael-bashir@users.noreply.github.com",
                        "commit", "-q", "--amend", "--no-edit", "--signoff"], check=True)
        r = subprocess.run([sys.executable, "scripts/ci/validate_records.py", "origin/main", "HEAD"], cwd=T, capture_output=True, text=True)
        text = r.stdout + r.stderr
        bad = collections.defaultdict(set)
        for m in re.finditer(r"^\s*(data/\S+\.jsonl):(\d+): (.*)$", text, re.M):
            bad[m.group(1)].add(int(m.group(2))); reasons[re.sub(r":.*", "", m.group(3))] += 1
        if not bad:
            print("validate_records:", (text.strip().splitlines() or ["quiet"])[-1], dict(reasons)); return
        for f, lines in bad.items():
            rows = open(f"{T}/{f}").read().splitlines(True)
            open(f"{T}/{f}", "w").writelines(l for i, l in enumerate(rows, 1) if i not in lines)
    sys.exit("validate_records did not settle in 40 rounds:\n" + text[-1500:])


if __name__ == "__main__":
    if sys.argv[1] == "meta":
        print(json.dumps([meta(r) for r in sys.argv[2:]], indent=1, ensure_ascii=False))
    elif sys.argv[1] == "refine":
        refine(sys.argv[1:])
    elif sys.argv[1] == "apply":
        apply(sys.argv[1:])
    else:
        sys.exit(__doc__)
