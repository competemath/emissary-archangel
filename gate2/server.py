import asyncio
import logging
import os
import re
import subprocess
import tempfile
import uuid

import uvicorn
from lsp_driver import ResidentElaborator
from mcp.server.fastmcp import FastMCP
from mcp.server.transport_security import TransportSecuritySettings
from starlette.middleware.cors import CORSMiddleware

# =============================================================================
# Emissary-Archangel Gate 2 — Statement Entailment Daemon
# -----------------------------------------------------------------------------
# Deterministically checks "does the translated proof establish at least as
# much as the original" — NewType -> OldType, kernel-verified via Lean.addDecl
# (Vendor/Gate2.lean). Mirrors Leak-IV's server.py shape deliberately (FastMCP,
# SSE transport, CORS-open, no auth, one plain-text tool, deterministic verdict
# string) for operator familiarity, but the actual check-per-call mechanism is
# simpler: each call shells out to `lake env lean` on a freshly generated file,
# rather than Leak-IV's persistent LSP daemon. Correct and simple beats fast
# and fragile for a v0.0.1 — a persistent-process optimization is a documented
# later step, not a blocker now.
# =============================================================================

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger("emissary-gate2")

GATE2_PROJECT_DIR = os.path.dirname(os.path.abspath(__file__))
# Lives inside this project's own data/ dir, not a scratch directory
# (~/tengoku-232-run) elsewhere — that's exactly what broke Gate 2 entirely
# once already: this project's own .lake was a symlink INTO that scratch
# dir, and cleaning it up (reasonably, as scratch) took Gate 2 down with it
# with no warning. A project's real dependencies should live under the
# project itself, not be borrowed from somewhere that looks disposable.
OLD_EXPORT_PATH = os.environ.get(
    "EMISSARY_OLD_EXPORT", os.path.join(GATE2_PROJECT_DIR, "data", "export.ndjson")
)
# A Gate 2 run re-imports Mathlib and elaborates the candidate; ~90 s when the
# machine is idle, several minutes under load. 180 s turned load into
# spurious FAILs (reason=timeout) that the harness then escalated.
VERIFY_TIMEOUT = 900.0

mcp = FastMCP(
    "Emissary-Archangel-Gate2",
    transport_security=TransportSecuritySettings(enable_dns_rebinding_protection=False),
)

# The environment Gate 2 elaborates in is the Tengoku tree. `Tengoku.All` is
# root + every library of verified additions; a narrower module can be set
# for a partial local build.
GATE2_TREE_IMPORT = os.environ.get("GATE2_TREE_IMPORT", "Tengoku.All")

_HEADER = """import Lean
import Mathlib
import Vendor.Importer
import Vendor.ReplayCore
import Vendor.DriverState
import Vendor.Gate2

set_option maxErrors 0

open Lean Elab Command TengokuImport

partial def reachableFrom (all : Std.HashMap Name ConstantInfo) (roots : List Name) :
    Std.HashMap Name ConstantInfo :=
  go roots {} {}
where
  go (stack : List Name) (visited : NameSet) (result : Std.HashMap Name ConstantInfo) :
      Std.HashMap Name ConstantInfo :=
    match stack with
    | [] => result
    | n :: rest =>
      if visited.contains n then
        go rest visited result
      else
        let visited := visited.insert n
        match all[n]? with
        | none => go rest visited result
        | some ci =>
          let result := result.insert n ci
          let newDeps := ci.getUsedConstantsAsSet.toList.filter (fun d => !visited.contains d)
          go (newDeps ++ rest) visited result

/-- What Gate 2 actually needs from the export: the original's STATEMENT and
everything that gives that statement its meaning — definitions, inductives,
instances, followed through their bodies — but never the original's proof, nor
any proof. Theorems reached this way (the original first of all) are replayed as
statement-only axioms. Following proofs used to drag in whatever core internals
a helper lemma happened to recurse over (`List.Sublist.below` and friends),
and a core change to one of those between toolchains then read as a name
collision on an entry whose statement never mentioned it. -/
partial def statementReach (all : Std.HashMap Name ConstantInfo) (roots : List Name) :
    Std.HashMap Name ConstantInfo :=
  go roots {} {}
where
  go (stack : List Name) (visited : NameSet) (result : Std.HashMap Name ConstantInfo) :
      Std.HashMap Name ConstantInfo :=
    match stack with
    | [] => result
    | n :: rest =>
      if visited.contains n then
        go rest visited result
      else
        let visited := visited.insert n
        match all[n]? with
        | none => go rest visited result
        | some ci =>
          let (ci', deps) := match ci with
            | .thmInfo t =>
              (ConstantInfo.axiomInfo { toConstantVal := t.toConstantVal, isUnsafe := false },
               t.type.getUsedConstants.toList)
            | other => (other, other.getUsedConstantsAsSet.toList)
          let result := result.insert n ci'
          go ((deps.filter (fun d => !visited.contains d)) ++ rest) visited result

/-- "Same thing" test for a name the target environment already has: same kind,
same universe arity, structurally equal type (up to universe-param renaming), and
for inductives/constructors/recursors the same constructor shape. Values are NOT
compared (a definition body may legitimately differ across toolchains while its
type — the contract every dependent proof relies on — is unchanged). -/
-- lean4export has no encoding for `mdata`, so an exported type arrives with
-- every annotation stripped, while the native declaration keeps its own —
-- e.g. `Nat.beq : (@& Nat) → (@& Nat) → Bool` carries borrow annotations as
-- mdata on the binder domains. `Expr.eqv` is structural and would call those
-- two types different, flagging a perfectly compatible core definition as a
-- collision. Annotations carry no logical content: compare with them gone.
partial def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | .app f a => .app (stripMData f) (stripMData a)
  | .lam n t b bi => .lam n (stripMData t) (stripMData b) bi
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .letE n t v b nd => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .proj s i e => .proj s i (stripMData e)
  | e => e

-- `strict`: the name is a ROOT — the very theorem Gate 2 reads back from the
-- environment by name — so its native statement must equal the export's, or
-- the entailment would be proved against the wrong statement. A non-root
-- theorem/axiom that a replayed proof merely USES needs no statement check:
-- the kernel type-checks that use against the native statement when the
-- proof is replayed, and the replayed theorem's own statement comes from the
-- export regardless (core lemmas get reformulated between toolchains all the
-- time — `Nat.eq_or_lt_of_le` did — and each such reformulation is either
-- accepted or rejected by the kernel, never silently absorbed).
-- `fromScript`: the native declaration was made by the SCRIPT UNDER TEST (it
-- has no module index), not by Mathlib/core. Such a name is the script's own
-- reproduction of one of the original's definitions, so its BODY must be the
-- original's body too: a definition that merely shares the name and type
-- (a guessed `Equation1443`, say) would otherwise be silently substituted
-- for the original's, and the replayed theorem would be "about" the wrong
-- thing while every type still lined up. Mathlib-native names keep the
-- type-level check — their bodies legitimately differ between toolchains.
-- Private names are mangled per module (`_private.<module>.0.foo`), so the
-- candidate's `private abbrev C := @congr_op` and the export's are the same
-- source declaration under two different mangled names. Erase the mangling
-- on both sides before comparing bodies.
def canonPrivate (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => match privateToUserName? n with
      | some u => some (.const u ls)
      | none => none
    | _ => none

def tengokuCompatible (strict fromScript : Bool) (exported native : ConstantInfo) : Bool :=
  if exported.levelParams.length != native.levelParams.length then false else
  let usedProofOnly := match exported, native with
    | .thmInfo _, .thmInfo _ => true
    | .axiomInfo _, .axiomInfo _ => true
    | _, _ => false
  if usedProofOnly && !strict then true else
  let inst (e : Expr) : Expr := canonPrivate (stripMData (e.instantiateLevelParams exported.levelParams (native.levelParams.map Level.param)))
  if !((inst exported.type).eqv (canonPrivate (stripMData native.type))) then false else
  match exported, native with
  | .inductInfo a, .inductInfo b => a.ctors == b.ctors && a.numParams == b.numParams && a.numIndices == b.numIndices
  | .ctorInfo a, .ctorInfo b => a.induct == b.induct && a.cidx == b.cidx && a.numFields == b.numFields
  | .recInfo a, .recInfo b => a.numParams == b.numParams && a.numMotives == b.numMotives && a.numMinors == b.numMinors
  -- Bodies are compared only for `abbrev`s the candidate defined: those are
  -- the guessable ones (an `Equation1443` written from memory) and their
  -- bodies are plain terms that elaborate identically across toolchains. A
  -- regular `def`'s elaborated body (matchers, auxiliary lemmas, instance
  -- paths) legitimately differs between toolchains even from identical
  -- source, so for those only the type is held fixed.
  | .defnInfo a, .defnInfo b =>
    match a.hints with
    | .abbrev => !fromScript || (inst a.value).eqv (canonPrivate (stripMData b.value))
    | _ => true
  | .thmInfo _, .thmInfo _ => true
  | .axiomInfo _, .axiomInfo _ => true
  | .opaqueInfo _, .opaqueInfo _ => true
  | .quotInfo _, .quotInfo _ => true
  | _, _ => false

elab "#tengoku_import_parse " path:str : command => do
  let contents <- IO.FS.readFile path.getString
  match TengokuImport.runImport contents with
  | .error e => throwError "parse failed: {e}"
  | .ok newConstants => importedConstantsRef.set newConstants

elab "#tengoku_replay_entry " id:str names:str : command => do
  let all <- importedConstantsRef.get
  let roots := ((names.getString.splitOn ",").filter (· != "")).map parseDottedName
  -- A root the export doesn't contain used to be skipped SILENTLY by
  -- reachableFrom (an empty replay looks identical to a successful one),
  -- which is how 31 translations got "verified" against nothing. Fail loudly
  -- here, with the GATE2_FAIL marker the daemon keys its verdict on, so an
  -- unqualified name (`IsRed_nil` vs `ThreeC2.IsRed_nil`) or a missing
  -- per-id export can never again pass as a replay.
  let missing := roots.filter (fun n => (all[n]?).isNone)
  if !missing.isEmpty then
    let shown := String.intercalate "," (missing.map toString)
    logInfo m!"GATE2_FAIL reason=old_name_not_in_export id={id.getString} names={shown} — nothing was replayed; the export loaded for this id does not contain these names"
    throwError "tengoku_replay_entry: names not in export: {shown}"
  let closure := statementReach all roots
  let env <- getEnv
  -- A closure name that ALREADY exists in the target environment used to be
  -- skipped on name alone, silently binding the original theorem's references
  -- to whatever native declaration happens to share the name. That is exactly
  -- how FreeMagma.Fin0_impossible got "verified" against Mathlib's FreeMagma
  -- (constructors of/mul) instead of the corpus's own (Leaf/Fork): same name,
  -- different type. A name may be reused from the environment ONLY if the
  -- native declaration is structurally the same thing as the exported one;
  -- anything else is a collision and the replay refuses, loudly.
  let delta := closure.filter (fun n _ => (env.find? n).isNone)
  -- Only the BOUNDARY matters: native names that a declaration we are about
  -- to replay references directly (in its statement or its proof), plus any
  -- root that already exists natively. A name reachable only through the
  -- proofs of native declarations is the target toolchain's own business —
  -- checking it too flagged private core matchers and reformulated core
  -- lemmas that no replayed declaration ever touches.
  let mut boundary : NameSet := {}
  for (_, ci) in delta.toList do
    for c in ci.type.getUsedConstants do
      if (env.find? c).isSome then boundary := boundary.insert c
    if let some v := ci.value? then
      for c in v.getUsedConstants do
        if (env.find? c).isSome then boundary := boundary.insert c
  for r in roots do
    if (env.find? r).isSome then boundary := boundary.insert r
  let mut collisions : List String := []
  let mut details : List MessageData := []
  for n in boundary.toList do
    match all[n]?, env.find? n with
    | some ci, some native =>
      if !(tengokuCompatible (roots.contains n) ((env.getModuleIdxFor? n).isNone) ci native) then
        collisions := s!"{n}" :: collisions
        -- Show the first few actual differences so a false positive (e.g. an
        -- annotation-only type difference) is diagnosable from the log alone.
        if details.length < 3 then
          details := m!"{n}: export type = {ci.type} | native type = {native.type}" :: details
    | _, _ => pure ()
  if !collisions.isEmpty then
    let shown := String.intercalate "," collisions
    logInfo m!"GATE2_FAIL reason=name_collision names={shown} — these names already exist in the target environment with a DIFFERENT definition than the original's export; the original cannot be replayed faithfully without renaming them. First differences: {MessageData.joinSep details.reverse m!" ;; "}"
    throwError "tengoku_replay_entry: name collision with the target environment: {shown}"
  liftCoreM (TengokuImport.replayIntoCoreEnv delta)
"""

# The environment is the tree, not a Mathlib checkout.
_HEADER = _HEADER.replace("import Mathlib\n", f"import {GATE2_TREE_IMPORT}\n", 1)


def _escape_lean_string(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


# The shared export.ndjson is one combined lean4export invocation covering
# the original 220 CompeteMath entries — its internal name/level/expr indices
# are only unique WITHIN that single file, not globally. A theorem exported
# later in a SEPARATE lean4export run starts its own indices back at 0, so
# blindly appending a new export's lines to the shared file would silently
# collide with existing indices and corrupt lookups for entries that already
# work. Per-id override files avoid that entirely: each stays a fully
# self-contained lean4export output, loaded on its own instead of merged.
# Falls back to the shared file for every id that doesn't have one — the
# original 220 are untouched by this.
def _resolve_export_path(old_id: str) -> str:
    override = os.path.join(os.path.dirname(OLD_EXPORT_PATH), "exports", f"{old_id}.ndjson")
    return override if os.path.isfile(override) else OLD_EXPORT_PATH


# _HEADER above already imports Lean/Mathlib/Vendor before the replay commands
# run — an `import` anywhere but the very start of the file is illegal in Lean,
# so an agent-submitted new_script that ALSO opens with its own `import Mathlib`
# (agents do this — it's a normal habit for a "full standalone script") lands
# mid-file and Lean rejects it outright, with the real cause buried under a
# cascade of unrelated-looking "unknown constant"/"incorrect universe levels"
# errors from everything after it failing to elaborate. Strip a leading import
# of something _HEADER already provides rather than let every submission
# rediscover this the hard way.
_LEADING_IMPORT_RE = re.compile(r"^\s*(?:import\s+[\w.«»]+\s*\n)+", re.MULTILINE)  # the tree's root import covers them all


def _build_verification_file(
    old_id: str,
    old_export_names: str,
    new_script: str,
    bridge_decl_name: str,
    proof_text: str,
) -> str:
    export_path = _resolve_export_path(old_id)
    cleaned_script = _LEADING_IMPORT_RE.sub("", new_script.strip())
    # Candidate FIRST, replay SECOND. The replay only adds closure names the
    # environment does not already have, and checks every one it finds
    # (type-level for Mathlib natives, type AND body for names the candidate
    # itself defined). That is what lets a self-contained candidate reproduce
    # the original's definitions under their original names — `Magma`,
    # `Equation1443`, the private abbrevs — and have the replayed theorem
    # genuinely share them, instead of colliding with them: with the replay
    # first, every such definition in the candidate was "already declared"
    # and the candidate never elaborated at all.
    parts = [
        _HEADER,
        f'#tengoku_import_parse "{_escape_lean_string(export_path)}"\n',
        "\n-- Candidate translation, submitted verbatim:\n",
        cleaned_script.strip() + "\n",
        "\n-- Original, replayed from its export around the candidate's definitions:\n",
        f'#tengoku_replay_entry "{_escape_lean_string(old_id)}" "{_escape_lean_string(old_export_names)}"\n',
        "\n-- Gate 2 check:\n",
    ]
    return "".join(parts)


# `.*$` with MULTILINE stops at the first newline — wrong here, since Lean's
# pretty-printer wraps long expressions (exactly what `goal=`/`new_statement=`
# now include) across multiple indented lines. #gate2_verify is always the
# LAST command we generate, so there is nothing meaningful after its message —
# capture everything from the marker to the end of output instead of trying
# to bound it by line. (DOTALL makes `.` match newlines too.)
_PASS_RE = re.compile(r"GATE2_PASS\b.*\Z", re.DOTALL)
_FAIL_RE = re.compile(r"GATE2_FAIL\b.*\Z", re.DOTALL)


# One resident `lake serve` keeps the tree's imports loaded; each check is a
# didChange of a sandbox file + waitForDiagnostics (see lsp_driver.py). The
# verification text is still written to `file_path` for inspection; what
# gets elaborated is that text, in the resident process.
elaborator = ResidentElaborator(GATE2_PROJECT_DIR)


async def _run_lean(file_path: str) -> tuple[int, str]:
    with open(file_path, "r", encoding="utf-8") as f:
        text = f.read()
    return await elaborator.elaborate(text, VERIFY_TIMEOUT)


@mcp.tool()
async def gate2_verify_entailment(
    old_id: str,
    old_export_names: str,
    new_script: str,
    new_theorem_name: str,
    old_theorem_name: str,
    bridge_decl_name: str,
    proof_text: str,
) -> str:
    """Emissary-Archangel Gate 2 — statement entailment check.

    Verifies that `new_theorem_name` (defined inside `new_script`, which you
    submit verbatim — a full, self-contained candidate translation) proves at
    least as much as `old_theorem_name` (an original theorem replayed
    unmodified from the pre-translation export, identified by `old_id` +
    `old_export_names`, exactly as recorded in Tengoku) — i.e. it kernel-checks
    `new_theorem_name's type -> old_theorem_name's type`.

    You do NOT write `new_theorem_name -> old_theorem_name` as Lean syntax —
    that is a category error (a theorem's name in term position denotes its
    PROOF, not its statement). Instead, submit only `proof_text`: a raw Lean
    term/tactic proof (e.g. "fun h => h" or "by intro h; exact h") of the
    entailment. The harness builds the actual goal type directly from the two
    theorems' already-elaborated types and elaborates your proof against
    that — you cannot fake or bypass this from the agent side.

    Returns a plain-text verdict: "GATE2_PASS ..." on success, or
    "GATE2_FAIL reason=<reason> ..." with the real elaborator/kernel error on
    failure. This is deterministic and kernel-backed — same guarantee as
    verify_full_script, applied to a different question (sameness of claim,
    not mere compilability).
    """
    run_id = uuid.uuid4().hex[:12]
    file_path = os.path.join(tempfile.gettempdir(), f"gate2_{run_id}.lean")
    content = _build_verification_file(
        old_id, old_export_names, new_script, bridge_decl_name, proof_text
    )
    content += (
        f'#gate2_verify "{_escape_lean_string(new_theorem_name)}" '
        f'"{_escape_lean_string(old_theorem_name)}" '
        f'"{_escape_lean_string(bridge_decl_name)}" '
        f'"{_escape_lean_string(proof_text)}"\n'
    )
    with open(file_path, "w") as f:
        f.write(content)

    logger.info("gate2 run %s: old_id=%s new=%s old=%s", run_id, old_id, new_theorem_name, old_theorem_name)
    try:
        rc, output = await _run_lean(file_path)
    finally:
        try:
            os.remove(file_path)
        except OSError:
            pass

    pass_match = _PASS_RE.search(output)
    fail_match = _FAIL_RE.search(output)
    if pass_match and not fail_match:
        logger.info("gate2 run %s: PASS", run_id)
        return f"✅ {pass_match.group(0)}"
    if fail_match:
        logger.info("gate2 run %s: FAIL", run_id)
        return f"❌ {fail_match.group(0)}"
    logger.warning("gate2 run %s: no verdict line found, rc=%s output=%s", run_id, rc, " ".join(output.split())[-600:])
    return f"❌ GATE2_FAIL reason=no_verdict rc={rc} output={output[-2000:]}"


_DEPS_RE = re.compile(r"GATE2_DEPS\b.*\Z", re.DOTALL)
_DEPS_FAIL_RE = re.compile(r"GATE2_DEPS_FAIL\b.*\Z", re.DOTALL)


@mcp.tool()
async def gate2_list_dependencies(
    old_id: str,
    old_export_names: str,
    new_script: str,
    theorem_name: str,
) -> str:
    """Dedup support for the vendoring registry — NOT a gate.

    Lists the full transitive closure of `theorem_name`'s dependencies
    (everything it needs, directly or indirectly), one comma-separated list.
    Call this ONLY after both gates have already passed for `new_script`, so
    the harness knows exactly which declarations to record in Tengoku's
    vendoring registry — and can skip re-recording anything already known
    from an earlier translation, which is the whole point of asking.

    Returns "GATE2_DEPS name1,name2,..." — feed this list straight into the
    registry's dedup check; do not try to interpret or filter it yourself.
    """
    run_id = uuid.uuid4().hex[:12]
    file_path = os.path.join(tempfile.gettempdir(), f"gate2deps_{run_id}.lean")
    content = _build_verification_file(old_id, old_export_names, new_script, "_unused", "_unused")
    content += f'#gate2_list_dependencies "{_escape_lean_string(theorem_name)}"\n'
    with open(file_path, "w") as f:
        f.write(content)

    try:
        rc, output = await _run_lean(file_path)
    finally:
        try:
            os.remove(file_path)
        except OSError:
            pass

    deps_match = _DEPS_RE.search(output)
    fail_match = _DEPS_FAIL_RE.search(output)
    if deps_match and not fail_match:
        return deps_match.group(0)
    if fail_match:
        return fail_match.group(0)
    return f"GATE2_DEPS_FAIL reason=no_verdict rc={rc} output={output[-2000:]}"


def _tree_dir() -> str:
    """The Tengoku checkout this daemon elaborates in: TENGOKU_DIR, else the
    `tengoku` package of lake-manifest.json (a path require locally, the git
    checkout under .lake/packages in deployment)."""
    env = os.environ.get("TENGOKU_DIR")
    if env:
        return env
    import json as _json
    try:
        with open(os.path.join(GATE2_PROJECT_DIR, "lake-manifest.json"), encoding="utf-8") as f:
            for p in _json.load(f).get("packages", []):
                if p.get("name") == "tengoku" and p.get("type") == "path":
                    return p["dir"]
    except Exception:
        pass
    return os.path.join(GATE2_PROJECT_DIR, ".lake", "packages", "tengoku")


async def _sh(cmd: list[str], cwd: str, timeout: float) -> tuple[int, str, float]:
    import time as _time
    t0 = _time.time()
    p = await asyncio.create_subprocess_exec(*cmd, cwd=cwd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT)
    try:
        out, _ = await asyncio.wait_for(p.communicate(), timeout)
    except asyncio.TimeoutError:
        p.kill()
        return 124, f"timed out after {timeout:.0f}s", _time.time() - t0
    return p.returncode or 0, out.decode("utf-8", "replace"), _time.time() - t0


@mcp.tool()
async def gate2_sync(pull: bool = True, fetch_cache: bool = True) -> str:
    """Bring this daemon's Tengoku tree up to date and restart the resident
    elaborator, so the next check runs on the tree as it is now.

    Steps: `git pull --ff-only` in the tree checkout, `scripts/cache.sh get`
    (the tree's build cache for the current commit, if one is published),
    `lake build` of the module the checks import, then a restart of the
    resident `lake serve` — the running worker keeps the oleans it loaded, so
    without the restart a rebuilt tree is not what gets checked. Checks are
    held while the sync runs.
    """
    tree = _tree_dir()
    report = []
    async with elaborator.lock:
        if pull:
            rc, out, dt = await _sh(["git", "pull", "--ff-only"], tree, 300)
            report.append(f"git pull: rc={rc} {dt:.0f}s {' '.join(out.split())[-300:]}")
            if rc != 0:
                return "GATE2_SYNC_FAIL step=pull\n" + "\n".join(report)
        cache = os.path.join(tree, "scripts", "cache.sh")
        if fetch_cache and os.path.isfile(cache):
            rc, out, dt = await _sh(["bash", cache, "get"], tree, 3600)
            report.append(f"cache get: rc={rc} {dt:.0f}s {' '.join(out.split())[-300:]}")
        rc, out, dt = await _sh(["lake", "build", GATE2_TREE_IMPORT], tree, 4 * 3600)
        report.append(f"lake build {GATE2_TREE_IMPORT}: rc={rc} {dt:.0f}s {' '.join(out.split())[-300:]}")
        if rc != 0:
            return "GATE2_SYNC_FAIL step=build\n" + "\n".join(report)
        vendor_mods = re.findall(r"^import (Vendor\.\S+)", _HEADER, re.M)  # no Vendor.lean root: build the modules the header imports
        rc, out, dt = await _sh(["lake", "build", *vendor_mods], GATE2_PROJECT_DIR, 3600)
        report.append(f"lake build {' '.join(vendor_mods)}: rc={rc} {dt:.0f}s {' '.join(out.split())[-200:]}")
        if rc != 0:
            return "GATE2_SYNC_FAIL step=vendor\n" + "\n".join(report)
        await elaborator.restart()
        report.append("resident elaborator restarted")
    rc, out, _ = await _sh(["git", "rev-parse", "--short", "HEAD"], tree, 30)
    return f"GATE2_SYNC_OK tree={out.strip()}\n" + "\n".join(report)


async def main_serve():
    logger.info("=" * 60)
    logger.info("Booting Emissary-Archangel Gate 2 daemon...")
    logger.info("=" * 60)

    http_app = mcp.sse_app()
    http_app.add_middleware(
        CORSMiddleware,
        allow_origins=["*"],
        allow_methods=["*"],
        allow_headers=["*", "mcp-protocol-version", "mcp-session-id"],
        expose_headers=["mcp-session-id"],
    )

    port = int(os.environ.get("PORT", "7861"))
    logger.info(f"Serving MCP (SSE) on 0.0.0.0:{port}")
    config = uvicorn.Config(
        http_app, host="0.0.0.0", port=port,
        proxy_headers=True, forwarded_allow_ips="*",
        log_level="info", loop="asyncio",
    )
    await uvicorn.Server(config).serve()


if __name__ == "__main__":
    asyncio.run(main_serve())
