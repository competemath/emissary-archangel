#!/usr/bin/env python3
"""register_libraries.py: GitHub repositories -> everything the pipeline needs before `setup-auto`, with no human choices.

    register_libraries.py meta  owner/repo ...            -> JSON on stdout: commit, licence, toolchain, roots, deps, verdict
    register_libraries.py apply --tengoku T --emissary E --meta meta.json
        T: a checkout of competemath/tengoku (its schemas/sources.json and tools/ are used)
        E: a checkout of competemath/emissary-archangel (its sources.json)
        For each library whose verdict is "ok": the tengoku registry entry (allowed, licences, corpora), the emissary
        registry entry, and the tentative records (tools/harvest.py, limited to the library's roots, then filtered by the
        record rules: validate_records.py and lint_banked.py are run and what they refuse is dropped, as in tengoku#674).

A repository is refused (verdict says why) when: archived, a fork, no permissive licence on GitHub, no lean-toolchain, a lean-toolchain
outside v4.31 to v4.34.1 (the lane's range: older ones lose their proofs on the tree's version, newer ones are not built by it), a Lake
dependency beyond Mathlib's own (those libraries need a registration of their own dependencies first), no lean_lib roots, a root with a
generic name (Challenge, Solution, Paper, Main, ...: it would collide in the tree's namespace), or a root another registered library already
has (batch 12: projectionconstants-lean had grunbaum-lean's ProjectionConstants, so its records were the same theorems twice).
"""
import json, re, subprocess, sys, base64, urllib.parse
from pathlib import Path

PERMISSIVE = {"Apache-2.0", "MIT", "BSD-2-Clause", "BSD-3-Clause", "CC0-1.0", "0BSD", "Unlicense", "ISC"}
# the lane's toolchain range (inclusive): v4.31.0 .. v4.34.1, release candidates of those included
TOOLCHAIN_MIN, TOOLCHAIN_MAX = (4, 31, 0), (4, 34, 1)
# root names that say nothing about the library: a module `Challenge.Basic` or `Main` of two libraries is one namespace in the tree
GENERIC_ROOTS = {"challenge", "solution", "paper", "main", "operator", "util", "utils", "lib", "src", "test", "tests", "examples", "scripts", "submission",
                 "erdosproblems", "formalconjectures", "mathlib", "lean", "basic", "common", "shared", "problem", "problems", "proof", "proofs", "checks"}
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


def requires_of(lakefile):
    """the packages a lakefile requires (lean and toml spellings); a library with no manifest is still judged on these"""
    names = [a or b for a, b in re.findall(r'^\s*require\s+«?([\w.-]+)»?|\[\[require\]\]\s*\n(?:[^\n]*\n)*?\s*name\s*=\s*"([^"]+)"', lakefile, re.M)]
    return sorted(dict.fromkeys(names))


def _outside(path):
    """a path that leaves the repository (`../mathlib4`, `/home/x/mathlib4`): CI has only the one checkout, so nothing is there. A folder inside it (`third_party/optlib`, `./vendor/x`) is fine."""
    import posixpath
    p = posixpath.normpath((path or "").strip())
    return p.startswith("/") or p == ".." or p.startswith("../")


def path_dependencies(lakefile, manifest=None):
    """the names of the dependencies that are a folder OUTSIDE the repository (lhymathlib, batch 13: `require mathlib from "../mathlib4"`, `"type": "path", "dir": "../mathlib4"` in its manifest;
    thurston23, batch 8: `../mathlib4-thurston`): setup cannot build such a library (`package directory not found`). A path inside the repository (causalean: `third_party/optlib`) builds and is allowed."""
    names = [m.group(1) for m in re.finditer(r'^\s*require\s+«?([\w.-]+)»?\s+from\s+"([^"]*)"', lakefile or "", re.M) if _outside(m.group(2))]  # `from "path"`; `from git "url"` has a word before the string
    for blk in re.split(r"\[\[require\]\]", lakefile or "")[1:]:
        blk = blk.split("\n[", 1)[0]
        n = re.search(r'^\s*name\s*=\s*"([^"]+)"', blk, re.M)
        pth = re.search(r'^\s*path\s*=\s*"([^"]*)"', blk, re.M)
        if n and pth and _outside(pth.group(1)): names.append(n.group(1))
    try: names += [p["name"].strip("«»") for p in json.loads(manifest or "{}").get("packages", []) if p.get("type") == "path" and _outside(p.get("dir"))]
    except Exception: pass
    return sorted(dict.fromkeys(names))


def key_problems(key):
    """why this key cannot be a library: the generator writes it as a Lean namespace (`namespace Pascal(key)`, `import Tengoku.Pascal(key).…`) without guillemets, so it must start
    with a letter (2dkakeyaconjecture, batch 14: `namespace 2dkakeyaconjecture` does not parse; Gitar on tengoku#973)"""
    return [] if re.fullmatch(r"[a-z][a-z0-9-]*", key or "") else [f"key {key!r} is no Lean namespace (it must start with a letter and hold only a-z, 0-9 and -)"]


def toolchain_in_range(tc):
    """tc: 'leanprover/lean4:v4.33.0', 'leanprover/lean4:v4.33.0-rc2' or 'v4.33.0'. True from v4.31.0 to v4.34.1; anything else is out: v4.36.0, a nightly,
    a spelling that merely contains a version, no version (cubic on #219: the whole string must be a release or release candidate)."""
    m = re.fullmatch(r"(?:leanprover/lean4:)?v(\d+)\.(\d+)\.(\d+)(?:-rc\d+)?", (tc or "").strip())
    return bool(m) and TOOLCHAIN_MIN <= tuple(int(x) for x in m.groups()) <= TOOLCHAIN_MAX


def root_problems(roots, taken, key=None):
    """why these roots cannot be registered: generic names, and roots another registered library already has. taken: {root lower-case: [keys]}"""
    why = []
    generic = [r for r in roots if r.lower() in GENERIC_ROOTS]
    if generic: why.append("generic lean_lib root: " + ", ".join(generic))
    clash = {r: [k for k in taken.get(r.lower(), []) if k != key] for r in roots}
    clash = {r: ks for r, ks in clash.items() if ks}
    if clash: why.append("root already registered by another library: " + "; ".join(f"{r} ({', '.join(ks)})" for r, ks in clash.items()))
    return why


def registered_roots(path=None):
    """{root lower-case: [keys]} from the emissary registry next to this script (sources.json). An unreadable registry raises: a check that cannot look
    must not pass (cubic on #219)."""
    sources = json.load(open(path or Path(__file__).resolve().parent.parent / "sources.json"))["sources"]
    out = {}
    for k, v in sources.items():
        for r in v.get("roots", []): out.setdefault(r.lower(), []).append(k)
    return out


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
    elif not toolchain_in_range(tc): why.append(f"toolchain {tc} outside v4.31 to v4.34.1")
    out["toolchain"] = tc if tc.startswith("leanprover/") else ("leanprover/lean4:" + tc if tc else "")
    lake = contents(repo, "lakefile.toml", sha) or contents(repo, "lakefile.lean", sha) or ""
    out["roots"] = roots_of(lake)
    if not out["roots"]: why.append("no lean_lib roots")
    else:
        try: taken = registered_roots()
        except Exception as e: why.append(f"registry unreadable, roots not checked: {type(e).__name__}: {e}")
        else: why += root_problems(out["roots"], taken, out["key"])
    why += key_problems(out["key"])
    mf = contents(repo, "lake-manifest.json", sha)
    local = path_dependencies(lake, mf)
    if local: why.append("local path dependency (a folder on the author's machine, setup cannot build it): " + ", ".join(local))
    deps = requires_of(lake)
    if mf:
        try: deps += [p["name"].strip("«»") for p in json.loads(mf)["packages"]]
        except Exception: why.append("unreadable lake-manifest")
    extra = sorted(dict.fromkeys(d for d in deps if d not in MATHLIB_DEPS))
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
    keys = [m["key"] for m in M]
    if len(keys) != len(set(keys)):
        sys.exit("two repositories give the same key: " + ", ".join(sorted(k for k in set(keys) if keys.count(k) > 1)))
    try: taken = registered_roots(f"{a.emissary}/sources.json")
    except Exception as e: sys.exit(f"the emissary registry cannot be read, so no root can be checked: {type(e).__name__}: {e}")
    for m in M:
        if not toolchain_in_range(m.get("toolchain")):  # meta checks it too; stale or edited metadata that says ok must not get past here (cubic on #219)
            sys.exit(f"{m['key']} refused: toolchain {m.get('toolchain')} outside v4.31 to v4.34.1")
        why = key_problems(m["key"]) + root_problems(m["roots"], taken, m["key"])
        if why: sys.exit(f"{m['key']} refused: " + "; ".join(why))
        for r in m["roots"]: taken.setdefault(r.lower(), []).append(m["key"])  # two libraries of one batch with one root are caught here too
    # tengoku: allowed + licences + corpora
    p = f"{a.tengoku}/schemas/sources.json"; d = json.load(open(p))
    e = json.load(open(f"{a.emissary}/sources.json"))
    for m in M:
        url = "https://github.com/" + m["repo"]
        old = (d["corpora"].get(m["key"]) or {}).get("repo") or (e["sources"].get(m["key"]) or {}).get("repo")
        if old and old != url: sys.exit(f"key {m['key']} is already registered for {old}, not {url}")
    for m in M:
        url = "https://github.com/" + m["repo"]
        if url not in d["allowed"]: d["allowed"].append(url)
        d["licences"][url] = m["licence"]
        d["corpora"][m["key"]] = {"repo": url, "commit": m["commit"], "roots": m["roots"]}
        shutil.copy(f"{a.records}/{m['key']}.jsonl", f"{a.tengoku}/data/tentative/{m['key']}.jsonl")
    json.dump(d, open(p, "w"), indent=2, ensure_ascii=False); open(p, "a").write("\n")
    # emissary: sources.json
    p = f"{a.emissary}/sources.json"
    for m in M:
        e["sources"][m["key"]] = {"label": f"{m['key']} ({m['repo']}; registered from the tengoku-osint scan, FATE-X-relevant)",
            "repo": "https://github.com/" + m["repo"], "commit": m["commit"], "toolchain": m["toolchain"], "roots": m["roots"], "licence": m["licence"]}
    json.dump(e, open(p, "w"), indent=2, ensure_ascii=False); open(p, "a").write("\n")


def mostly_overlapping(names, new, threshold=0.5):
    """names: {library: set of record names}; new: the libraries being added. Returns (library, other, share) for every new library
    whose records are at least `threshold` another library's (a vendored copy, or a fork's twin: riemann-roch-function-fields was a full
    copy of grothendieck-riemann-roch, magnitude-conjecture vendors quotient-submodule-equidistribution); the later name of two new
    libraries is the one reported."""
    out = []
    for k in new:
        if not names[k]: continue
        for o, other in names.items():
            if o == k or (o in new and o > k): continue
            share = len(names[k] & other) / len(names[k])
            if share >= threshold: out.append((k, o, round(share, 2)))
    return out


RECORD_LINE = re.compile(r"^\s*(data/\S+\.jsonl):(\d+)(?: \([^\n]*?\))?: (.*)$", re.M)


def refused_lines(text):
    """(file, line, reason) of every record a rule refuses: validate_records.py prints `data/x.jsonl:7: reason`, lint_banked.py
    `data/x.jsonl:7 (Name.of.record): reason` (batch 7, 13 Nov 2026: the first lint refusals refine met, `native_decide` in
    palomar-qseries-row-factorization, were not read, and refine stopped as if the rule had failed without naming a line)"""
    return [(m.group(1), int(m.group(2)), m.group(3)) for m in RECORD_LINE.finditer(text)]


REFINE_ROUNDS = 2000  # the rules name about 25 refused lines per run (27 and 18 lines of output in batch 10): 40 rounds dropped at most ~1,000; batch 10 had 1,993 duplicate names alone (17 Nov 2026)


def stage_and_amend(T):
    """Stage everything in the tengoku checkout and fold it into HEAD. `--sparse`: the checkout is sparse (data/ is left out), and a plain `git add -A` skips every path outside
    it, so the records the rules had just cut lines from never reached the commit and the rules never settled (17 Nov 2026, batch 10: two runs of 40 and 3,000 rounds)."""
    subprocess.run(["git", "-C", T, "add", "--sparse", "-A"], check=True)
    subprocess.run(["git", "-C", T, "-c", "user.name=mikaelbashir", "-c", "user.email=138998999+mikael-bashir@users.noreply.github.com",
                    "commit", "-q", "--amend", "--no-edit", "--signoff"], check=True)


def refine(argv):
    """refine --tengoku T: run the record rules (validate_records.py, lint_banked.py in strict mode) until both are quiet, dropping
    each record line they refuse (the later of two equal names, a name that is already trusted, a banned command, ...); every drop is
    counted by reason. The tengoku checkout is committed (HEAD) and compared with origin/main. A rule that fails without naming a
    record line is an error, never a pass."""
    import collections, os
    T = argv[argv.index("--tengoku") + 1]
    reasons = collections.Counter()
    trusted = trusted_names(T)
    for _ in range(REFINE_ROUNDS):
        stage_and_amend(T)
        bad = collections.defaultdict(set)
        for script in ("validate_records.py", "lint_banked.py"):
            r = subprocess.run([sys.executable, f"scripts/ci/{script}", "origin/main", "HEAD"], cwd=T, capture_output=True, text=True,
                               env={**os.environ, "TENGOKU_INTAKE_LINT": "strict"})
            text = r.stdout + r.stderr
            found = False
            for f, n, why in refused_lines(text):
                bad[f].add(n); reasons[re.sub(r":.*", "", why)] += 1; found = True
            if r.returncode != 0 and not found:
                sys.exit(f"{script} failed without naming a record line:\n" + text[-1500:])
        for f, lines in trusted_clashes(T, trusted).items():  # the rule the gate applies and the sparse checkout cannot show the two scripts above
            bad[f] |= lines; reasons["already trusted name"] += len(lines)
        if not bad:
            print("record rules quiet:", dict(reasons))
            twins = overlap_check(T)
            if twins: sys.exit("refused, most records of a library are another's: " + "; ".join(f"{k} is {s:.0%} {o}" for k, o, s in twins))
            return
        for f, lines in bad.items():
            rows = open(f"{T}/{f}").read().splitlines(True)
            open(f"{T}/{f}", "w").writelines(l for i, l in enumerate(rows, 1) if i not in lines)
    sys.exit(f"the record rules did not settle in {REFINE_ROUNDS} rounds")


def names_of(text):
    got = set()
    for l in text.splitlines():
        try: got.add(json.loads(l)["name"])
        except Exception: pass
    return got


def trusted_names(T):
    """the names of every trusted record on origin/main, read with `git show` so that the checkout need not hold data/trusted (a sparse checkout has none: 15 Nov 2026,
    batch 8, refine ran without it and let symmmoncoherence's `exchange` through; the gate refuses a record whose name is already trusted)"""
    import os
    names = set()
    for f in subprocess.run(["git", "-C", T, "ls-tree", "-r", "--name-only", "origin/main", "data/trusted/"], capture_output=True, text=True).stdout.split():
        if f.endswith(".jsonl"):
            names |= names_of(subprocess.run(["git", "-C", T, "show", f"origin/main:{f}"], capture_output=True, text=True).stdout)
    return names


def trusted_clashes(T, trusted):
    """{file: {line numbers}} of the records the checkout adds to data/tentative whose name is already trusted (a record already on origin/main is not new, so it is not judged)"""
    out = {}
    changed = subprocess.run(["git", "-C", T, "diff", "--name-only", "origin/main", "HEAD", "--", "data/tentative/"], capture_output=True, text=True).stdout.split()
    for f in changed:
        if not f.endswith(".jsonl"): continue
        old = names_of(subprocess.run(["git", "-C", T, "show", f"origin/main:{f}"], capture_output=True, text=True).stdout)
        for i, l in enumerate(open(f"{T}/{f}", encoding="utf-8").read().splitlines(), 1):
            try: n = json.loads(l)["name"]
            except Exception: continue
            if n in trusted and n not in old: out.setdefault(f, set()).add(i)
    return out


def overlap_check(T):
    """the record names of every library on origin/main and in the checkout; the libraries the checkout adds are compared with all"""
    import glob, os
    def names_of(text):
        got = set()
        for l in text.splitlines():
            try: got.add(json.loads(l)["name"])
            except Exception: pass
        return got
    names = {}
    for f in subprocess.run(["git", "-C", T, "ls-tree", "--name-only", "origin/main", "data/tentative/"], capture_output=True, text=True).stdout.split():
        if f.endswith(".jsonl"):
            names[os.path.basename(f)[:-6]] = names_of(subprocess.run(["git", "-C", T, "show", f"origin/main:{f}"], capture_output=True, text=True).stdout)
    new = []
    for f in glob.glob(f"{T}/data/tentative/*.jsonl"):
        k = os.path.basename(f)[:-6]
        cur = names_of(open(f).read())
        if cur != names.get(k): new.append(k)
        names[k] = cur
    return mostly_overlapping(names, new)


if __name__ == "__main__":
    if sys.argv[1] == "meta":
        print(json.dumps([meta(r) for r in sys.argv[2:]], indent=1, ensure_ascii=False))
    elif sys.argv[1] == "refine":
        refine(sys.argv[1:])
    elif sys.argv[1] == "apply":
        apply(sys.argv[1:])
    else:
        sys.exit(__doc__)
