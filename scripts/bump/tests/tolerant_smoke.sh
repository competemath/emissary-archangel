#!/bin/bash
# Smoke test of scripts/bump/tolerant_build.py + TolerantBuild.lean on a three-module project (no Mathlib, needs only the toolchain):
#   T/A.lean  clean
#   T/B.lean  imports A; one theorem whose proof fails, one that is fine
#   T/C.lean  imports B; uses the fine one (must stay clean), proves one theorem BY the failing one (must carry sorryAx)
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
printf 'import T.A\nimport Nonexistent.Module\ntheorem d : True := trivial\n' > T/D.lean
lake update >/dev/null 2>&1 || true
python3 "$here/tolerant_build.py" --lib . --roots T --log build.log --report tb.json --jobs 2 --cache .bump-cache
cat build.log
python3 - <<'PY'
import json, sys
tb = json.load(open("tb.json"))
st = {m: s["state"] for m, s in tb["status"].items()}
print(st)
want = {"T.A": "clean", "T.B": "errors", "T.C": "clean", "T.D": "bad_import"}
bad = {m: (st.get(m), w) for m, w in want.items() if st.get(m) != w}
assert not bad, f"unexpected module states (got, want): {bad}"
assert tb["lake_would_build"] == 1, tb["lake_would_build"]
PY
for m in A B C; do test -f ".lake/build/lib/lean/T/$m.olean" || { echo "missing olean for T.$m"; exit 1; }; done
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
grep -q "'fine' does not depend on any axioms" axioms.log || { echo "fine must be axiom-free"; exit 1; }
grep -q "'uses_fine' does not depend on any axioms" axioms.log || { echo "uses_fine must be axiom-free"; exit 1; }
grep -q "'after_broken' does not depend on any axioms" axioms.log || { echo "a theorem after the failing one must survive"; exit 1; }
grep -q "'broken' depends on axioms: \[sorryAx\]" axioms.log || { echo "broken must stand on sorryAx"; exit 1; }
grep -q "'uses_broken' depends on axioms: \[sorryAx\]" axioms.log || { echo "uses_broken must stand on sorryAx"; exit 1; }
# the cache: a second run rebuilds nothing
python3 "$here/tolerant_build.py" --lib . --roots T --log build2.log --report tb2.json --jobs 2 --cache .bump-cache
python3 - <<'PY'
import json
tb = json.load(open("tb2.json"))
cached = [m for m, s in tb["status"].items() if s.get("cached")]
print("cached on the second run:", sorted(cached))
assert set(cached) == {"T.A", "T.B", "T.C"}, cached
PY
echo "TOLERANT SMOKE OK"
