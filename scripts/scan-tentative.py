#!/usr/bin/env python3
"""scan-tentative.py — every tentative library the tree holds, as a candidate source:
repo, commit, toolchain, record count, licence (GitHub), lean_lib roots (lakefile at the
commit), and whether it can be registered. Shards (<name>-NNN) of one repo are grouped.
Writes data/pipeline/tentative-scan.json."""
import glob, json, os, re, subprocess, sys, collections
T = os.path.join(os.path.dirname(__file__), "..", json.load(open(os.path.join(os.path.dirname(__file__), "..", "sources.json"))).get("tentativeDir", "../compete-math/tengoku/data/tentative"))
reg = json.load(open(os.path.join(os.path.dirname(__file__), "..", "sources.json")))["sources"]
OSS = {"Apache-2.0", "MIT", "BSD-2-Clause", "BSD-3-Clause", "GPL-2.0", "GPL-3.0", "LGPL-2.1", "LGPL-3.0", "MPL-2.0", "CC0-1.0", "CC-BY-4.0", "CC-BY-SA-4.0", "Unlicense", "ISC", "AGPL-3.0", "0BSD", "Zlib", "BSL-1.0", "EPL-2.0"}
groups = collections.defaultdict(list)
for f in sorted(glob.glob(os.path.join(T, "*.jsonl"))):
    key = os.path.basename(f)[:-6]
    groups[re.sub(r"-\d{3}$", "", key)].append(f)
def sh(*a):
    r = subprocess.run(a, capture_output=True, text=True); return r.stdout.strip() if r.returncode == 0 else ""
out = {}
for key, files in sorted(groups.items()):
    if key in reg: continue
    n = 0; first = None; roots_seen = collections.Counter(); toolchains = collections.Counter(); commits = collections.Counter()
    for f in files:
        for line in open(f):
            if not line.strip(): continue
            r = json.loads(line); n += 1
            if first is None: first = r
            m = re.match(r"https://github\.com/([^/]+/[^/]+)/blob/([0-9a-f]+)/(.+?)#L", r["source_url"])
            if m: roots_seen[m.group(3).split("/")[0]] += 1; commits[m.group(2)] += 1
            toolchains[r["toolchain"]] += 1
    m = re.match(r"https://github\.com/([^/]+/[^/]+)/blob/([0-9a-f]+)/", first["source_url"]) if first else None
    row = {"files": [os.path.basename(f) for f in files], "records": n, "toolchain": toolchains.most_common(1)[0][0], "toolchains": len(toolchains)}
    if not m:
        row.update(status="skip", reason="not a GitHub repo: " + first["source_url"][:60]); out[key] = row; continue
    repo, commit = m.group(1), commits.most_common(1)[0][0]
    row.update(repo=f"https://github.com/{repo}", commit=commit, commits=len(commits))
    lic = sh("gh", "api", f"repos/{repo}", "--jq", ".license.spdx_id // \"NONE\"") or "UNKNOWN"
    row["licence"] = lic
    lakefile = ""
    for lf in ("lakefile.toml", "lakefile.lean"):
        t = sh("curl", "-sf", f"https://raw.githubusercontent.com/{repo}/{commit}/{lf}")
        if t: lakefile = t; break
    libs = [a or b for a, b in re.findall(r'lean_lib\s+«?([\w.]+)»?|\[\[lean_lib\]\]\s*\n\s*name\s*=\s*"([^"]+)"', lakefile)]
    default_root = repo.split("/")[1]
    if lakefile and not libs: libs = [default_root]
    roots = [r for r in roots_seen if r in libs] if libs else []
    row.update(lean_libs=libs, roots=roots, roots_seen=dict(roots_seen.most_common(5)), mathlib=("mathlib" in lakefile.lower()), records_in_roots=sum(c for r, c in roots_seen.items() if r in roots))
    tc = sh("curl", "-sf", f"https://raw.githubusercontent.com/{repo}/{commit}/lean-toolchain")
    row["toolchain_pinned"] = tc
    if lic not in OSS: row.update(status="skip", reason=f"licence {lic}")
    elif not lakefile: row.update(status="skip", reason="no lakefile at commit")
    elif not roots: row.update(status="skip", reason=f"no record root is a lean_lib (libs {libs[:4]}, seen {list(roots_seen)[:4]})")
    else: row["status"] = "eligible"
    out[key] = row
    print(f"{key:36s} {row['status']:8s} {n:6d} {row.get('licence','-'):14s} {row['toolchain']:32s} {row.get('reason','')[:70]}", flush=True)
os.makedirs(os.path.join(os.path.dirname(__file__), "..", "data", "pipeline"), exist_ok=True)
json.dump(out, open(os.path.join(os.path.dirname(__file__), "..", "data", "pipeline", "tentative-scan.json"), "w"), indent=2)
el = [k for k, r in out.items() if r["status"] == "eligible"]
print(f"\neligible: {len(el)} of {len(out)} ({sum(out[k]['records_in_roots'] for k in el)} records); skipped: {collections.Counter(r['reason'].split(':')[0].split(' (')[0] for r in out.values() if r['status']=='skip')}")
