#!/usr/bin/env python3
"""emit_attest_vendor.py: Gate 2's own Lean modules for a STATEMENT attestation, in a Lake project of their own.

  emit_attest_vendor.py --out vendorproj      (after:  cp -r gate2/Vendor.lean gate2/Vendor vendorproj/)

It writes what scripts/bump/gate2_batch.py `emit-vendor` writes (Vendor/Core.lean, Vendor/Batch.lean: Gate 2's checks, taken from gate2/server.py and gate2_batch.py, one
source of truth), then Vendor/Attest.lean: the batch check `gate2bCheck` re-derived by TEXT TRANSFORMATION from gate2_batch.BATCH_LEAN, with exactly these differences
(every anchor must be found exactly once, or this script stops, so a change to the batch check can never be missed silently):

  * the check's `uses_sorry` / `nonstandard_axiom` refusal is replaced by the STATEMENT-ONLY rule. The new declaration must be a theorem. Its PROOF may stand on `sorryAx` (these are
    statements); nothing that gives its STATEMENT meaning may: every constant its type mentions must stand on the three standard axioms only, and the proof may use no axiom
    besides those and `sorryAx`;
  * a definition the original's statement reaches must not stand on `sorryAx` either (a statement about a hole is not a statement);
  * every verdict is `GATE2S_PASS` / `GATE2S_FAIL`, never `GATE2B_*`: nothing that reads the batch's verdicts (scripts/bump/gate2_batch.py parse, the bump bundles' records) can mistake one for the other.

Everything else (the replay of the original around the tree's own declarations, the kernel-checked sameness of definitions, `equal` or the bridge `fun h => h`) is the batch check's own code.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUMP = HERE.parent / "bump"

SORRY_BLOCK = re.compile(
    r"      -- the tolerant build keeps a module whose declaration failed.*?"
    r"      if !extra\.isEmpty then\n"
    r"        logInfo m!\"GATE2B_FAIL old=\{oldN\} new=\{newN\} reason=nonstandard_axiom axioms=\{extra\.toList\}\"\n"
    r"        return\n",
    re.S,
)

STATEMENT_ONLY = '''      -- STATEMENT-ONLY (scripts/attest/emit_attest_vendor.py). The new declaration is a theorem whose PROOF may stand on `sorryAx`; its STATEMENT may not, nor anything the
      -- statement mentions, and the proof may use no axiom besides the three standard ones and `sorryAx`.
      let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
      if !(match newCi with | .thmInfo _ => true | _ => false) then
        logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=not_a_theorem"
        return
      let mut sorryIn : List Name := []
      for c in newCi.type.getUsedConstants do
        let a ← collectAxioms c
        if a.any (fun x => !(std.contains x)) then sorryIn := c :: sorryIn
      if !sorryIn.isEmpty then
        logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=statement_uses_sorry names={String.intercalate "," (sorryIn.map toString)}"
        return
      let proofAxs ← collectAxioms newN
      let extra := proofAxs.filter (fun a => !(std.contains a) && a != ``sorryAx)
      if !extra.isEmpty then
        logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=nonstandard_axiom axioms={extra.toList}"
        return
'''

CLOSURE_ANCHOR = "      let closure := statementReach all [oldN]\n"
ORIGINAL_SORRY = '''      let origSorry := closure.toList.filter (fun (_, ci) => match ci with
        | .defnInfo d => d.value.getUsedConstants.contains ``sorryAx
        | .opaqueInfo d => d.value.getUsedConstants.contains ``sorryAx
        | _ => false)
      if !origSorry.isEmpty then
        logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=original_definition_uses_sorry names={String.intercalate "," (origSorry.map (fun (n, _) => toString n))}"
        return
'''

COMMANDS = '''
/-- Every name in `names`, original and new under the same name: a STATEMENT check (`GATE2S_*` verdicts). -/
elab "#gate2_statements " names:str : command => do
  for s in (names.getString.splitOn ",").filter (· != "") do
    let n := parseDottedName s
    gate2sCheck n n

/-- A marker the driver splits the log by: what follows, up to the next marker, is one problem's. -/
elab "#attest_begin " id:str : command => logInfo m!"ATTEST_BEGIN {id.getString}"
'''


def batch_lean() -> str:
    sys.path.insert(0, str(BUMP))
    import gate2_batch  # noqa: E402

    return gate2_batch.BATCH_LEAN


def derive(batch: str) -> str:
    """The text of Vendor/Attest.lean, from gate2_batch.BATCH_LEAN."""
    a = batch.index("/-- One check:")
    e = batch.index("/-- Every name in `names`")
    chk = batch[a:e]
    if len(SORRY_BLOCK.findall(chk)) != 1:
        sys.exit("emit_attest_vendor: the batch check's sorry/axiom block was not found exactly once; the transformation needs updating for this gate2_batch.py")
    chk = SORRY_BLOCK.sub(lambda _m: STATEMENT_ONLY, chk)
    if chk.count(CLOSURE_ANCHOR) != 1:
        sys.exit("emit_attest_vendor: `let closure := statementReach all [oldN]` not found exactly once")
    chk = chk.replace(CLOSURE_ANCHOR, CLOSURE_ANCHOR + ORIGINAL_SORRY, 1)
    if chk.count("def gate2bCheck (oldN newN : Name)") != 1:
        sys.exit("emit_attest_vendor: `def gate2bCheck` not found exactly once")
    chk = chk.replace("def gate2bCheck (oldN newN : Name)", "def gate2sCheck (oldN newN : Name)", 1)
    chk = chk.replace("GATE2B_", "GATE2S_")
    if "GATE2B_" in chk or "uses_sorry\"" in chk.replace("statement_uses_sorry", "").replace("original_definition_uses_sorry", ""):
        sys.exit("emit_attest_vendor: a batch verdict or the batch sorry refusal is left in the statement check")
    # the helpers it calls (gate2bSameDef, gate2bKind, ...) stay the batch's own: they are in Vendor.Batch
    header = "import Lean\nimport Vendor.Importer\nimport Vendor.ReplayCore\nimport Vendor.DriverState\nimport Vendor.Gate2\nimport Vendor.Core\nimport Vendor.Batch\n\nset_option Elab.async false\nopen Lean Elab Command TengokuImport Meta\n\n"
    return header + chk + COMMANDS


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    a = ap.parse_args(argv)
    sys.path.insert(0, str(BUMP))
    import gate2_batch

    out = Path(a.out)
    gate2_batch.emit_vendor(argparse.Namespace(out=str(out)))
    (out / "Vendor" / "Attest.lean").write_text(derive(batch_lean()))
    root = (out / "Vendor.lean").read_text()
    if "import Vendor.Attest" not in root:
        (out / "Vendor.lean").write_text(root + "import Vendor.Attest\n")
    print(f"wrote {out}/Vendor/Attest.lean")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
