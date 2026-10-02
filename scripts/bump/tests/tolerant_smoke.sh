#!/bin/bash
# Smoke test of scripts/bump/tolerant_build.py + TolerantBuild.lean on a three-module project (no Mathlib, needs only the toolchain):
#   T/A.lean  clean
#   T/B.lean  imports A; one theorem whose proof fails, one that is fine
#   T/C.lean  imports B; uses the fine one (must stay clean), proves one theorem BY the failing one (must carry sorryAx)
#   T/E.lean  a multi-line copyright block, then `import T.C` (the scheduler must see that import: E needs C's olean)
#   T/D.lean  imports a module that does not exist (bad import: must not build, must be reported as such)
# Expect: A clean, B errors, C clean, D bad_import; oleans for A, B, C; `lake build` would have produced only A;
# `#print axioms` in a file importing C: fine theorems have none, the failing one and its user have sorryAx.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
work=${1:-$(mktemp -d)}
rm -rf "$work/proj" && mkdir -p "$work/proj/T" && cd "$work/proj"
printf 'name = "T"\ndefaultTargets = ["T"]\n[[lean_lib]]\nname = "T"\n' > lakefile.toml
printf 'def one : Nat := 1\ntheorem one_eq : one = 1 := rfl\n' > T/A.lean
printf 'import T.A\ntheorem fine : one + 0 = 1 := by simp [one]\ntheorem broken : one = 2 := by simp [one]\ntheorem after_broken : one + 1 = 2 := rfl\n' > T/B.lean
printf 'import T.B\ntheorem uses_fine : one + 0 = 1 := fine\ntheorem uses_broken : one = 2 := broken\n' > T/C.lean
printf '/-\nCopyright (c) test. All rights reserved.\nSecond line of the copyright block.\n-/\nimport T.C\ntheorem e : True := trivial\n' > T/E.lean
printf 'import T.A\nimport Nonexistent.Module\ntheorem d : True := trivial\n' > T/D.lean
lake update >/dev/null 2>&1 || true
python3 "$here/tolerant_build.py" --lib . --roots T --log build.log --report tb.json --jobs 2 --cache .bump-cache
cat build.log
python3 - <<'PY'
import json, sys
tb = json.load(open("tb.json"))
st = {m: s["state"] for m, s in tb["status"].items()}
print(st)
want = {"T.A": "clean", "T.B": "errors", "T.C": "clean", "T.D": "bad_import", "T.E": "clean"}
bad = {m: (st.get(m), w) for m, w in want.items() if st.get(m) != w}
assert not bad, f"unexpected module states (got, want): {bad}"
assert tb["lake_would_build"] == 1, tb["lake_would_build"]
PY
for m in A B C E; do test -f ".lake/build/lib/lean/T/$m.olean" || { echo "missing olean for T.$m"; exit 1; }; done
test ! -f .lake/build/lib/lean/T/D.olean || { echo "T.D must not have an olean"; exit 1; }
grep -q "error: T/B.lean:3" build.log || { echo "the failing proof was not reported at T/B.lean:3"; exit 1; }
grep -q "bad import 'Nonexistent.Module'" build.log || { echo "the bad import was not reported"; exit 1; }
cat > check.lean <<'LEAN'
import T.C
#print axioms fine
#print axioms uses_fine
#print axioms broken
#print axioms uses_broken
#print axioms after_broken
LEAN
lake env lean check.lean | tee axioms.log
# `fine` and `uses_fine` use propext (simp) but never sorryAx; `after_broken`, written after the failing proof, is untouched by it
for n in fine uses_fine after_broken; do
  line=$(grep "^'$n' " axioms.log) || { echo "no axioms line for $n"; exit 1; }
  case "$line" in *sorryAx*) echo "$n must not stand on sorryAx: $line"; exit 1;; esac
done
grep -q "^'broken' depends on axioms:.*sorryAx" axioms.log || { echo "broken must stand on sorryAx"; exit 1; }
grep -q "^'uses_broken' depends on axioms:.*sorryAx" axioms.log || { echo "uses_broken must stand on sorryAx"; exit 1; }
# the cache: a second run rebuilds nothing
python3 "$here/tolerant_build.py" --lib . --roots T --log build2.log --report tb2.json --jobs 2 --cache .bump-cache
python3 - <<'PY'
import json
tb = json.load(open("tb2.json"))
cached = [m for m, s in tb["status"].items() if s.get("cached")]
print("cached on the second run:", sorted(cached))
assert set(cached) == {"T.A", "T.B", "T.C", "T.E"}, cached
PY
# Gate 2's own Lean modules (they import Lean only) build in a project of their own: a compile error in them breaks every bump run
repo=$(cd "$here/../.." && pwd)
rm -rf "$work/vendor" && mkdir -p "$work/vendor" && cd "$work/vendor"
printf 'name = "V"\ndefaultTargets = ["Vendor"]\n[[lean_lib]]\nname = "Vendor"\n' > lakefile.toml
cp -r "$repo/gate2/Vendor.lean" "$repo/gate2/Vendor" .
lake build Vendor 2>&1 | tail -40
test "${PIPESTATUS[0]}" = 0 || { echo "Vendor does not build"; exit 1; }
# The kernel's refusal must reach the caller of `addDecl` (the batched Gate 2 relies on it): with Elab.async off a theorem the
# kernel rejects raises inside `observing`; with it on the refusal is reported later and the caller sees success.
cd "$work/proj"
cat > kernel.lean <<'LEAN'
import Lean
open Lean Elab Command Meta

def tryBad : CommandElabM String := do
  let r ← liftTermElabM <| observing do
    Lean.addDecl (Declaration.thmDecl {
      name := `badThm, levelParams := []
      type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
      value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1) })
  match r with
  | .ok _ => return "accepted"
  | .error _ => return "rejected"

elab "#bad" : command => do logInfo m!"RESULT {← tryBad}"

set_option Elab.async false
#bad
LEAN
lake env lean kernel.lean | tee kernel.log
grep -q "RESULT rejected" kernel.log || { echo "with Elab.async false the kernel's refusal must raise"; exit 1; }
echo "TOLERANT SMOKE OK"
