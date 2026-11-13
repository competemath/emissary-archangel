import Mathlib
import Submission.Delta
import Submission.MorseLedger
import Submission.PTAssembly


-- @@ L6-13 verbatim
/-!
# From geometric fiber components to the Morse ledger

This module enumerates any selected union of the canonical flow-orbit components
of a regular framed level set.  The resulting list of frame classes is the
`MorseLedger` consumed by the event calculus, and its ledger `delta` is proved to
be exactly the geometric finite sum `TamedField.deltaOn`.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
namespace Submission


-- @@ L19-19 verbatim
open Set

-- @@ L20-20 verbatim
open scoped BigOperators


-- @@ L22-22 verbatim
variable {n : ℕ}


-- @@ L24-24 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L26-26 verbatim
namespace TamedField


-- @@ L28-28 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L30-32 verbatim
/-- Orbit components selected by a collection of orbit subsets. -/
abbrev SelectedOrbitIndex (A : Set (Set E)) :=
  {O : V.OrbitIndex // (O : Set E) ∈ A}


-- @@ L34-39 verbatim
/-- An arbitrary finite enumeration of the selected components' frame classes.
The order is irrelevant by `MorseLedgerStep.perm`. -/
def selectedFrameLedger (A : Set (Set E)) : MorseLedger := by
  classical
  exact List.ofFn fun i : Fin (Fintype.card (V.SelectedOrbitIndex A)) =>
    V.orbitFrameClass ((Fintype.equivFin (V.SelectedOrbitIndex A)).symm i).1


-- @@ L41-60 verbatim
/-- The enumerated ledger computes exactly the selected geometric delta sum. -/
theorem selectedFrameLedger_delta (A : Set (Set E)) :
    (V.selectedFrameLedger A).delta = V.deltaOn A := by
  classical
  let e := Fintype.equivFin (V.SelectedOrbitIndex A)
  calc
    (V.selectedFrameLedger A).delta =
        ∑ i : Fin (Fintype.card (V.SelectedOrbitIndex A)),
          V.orbitContribution (e.symm i).1 := by
            simp [selectedFrameLedger, MorseLedger.delta,
              TamedField.orbitContribution, List.sum_ofFn, e]
    _ = ∑ O : V.SelectedOrbitIndex A, V.orbitContribution O.1 := by
          exact e.symm.sum_comp (fun O : V.SelectedOrbitIndex A =>
            V.orbitContribution O.1)
    _ = ∑ O : V.OrbitIndex,
        if (O : Set E) ∈ A then V.orbitContribution O else 0 := by
          rw [← Finset.sum_filter]
          exact (Finset.sum_subtype (Finset.univ.filter fun O : V.OrbitIndex =>
            (O : Set E) ∈ A) (by simp) V.orbitContribution).symm
    _ = V.deltaOn A := by rfl


-- @@ L62-62 verbatim
end TamedField


-- @@ L64-64 verbatim
namespace FiberSign


-- @@ L66-66 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L68-70 verbatim
/-- The ledger of the positively labelled components of a signed fiber. -/
def positiveFrameLedger (V : TamedField X) : MorseLedger :=
  V.selectedFrameLedger (S.positiveOrbitCollection V)


-- @@ L72-75 verbatim
/-- The positive ledger computes the signed framed invariant. -/
theorem positiveFrameLedger_delta (V : TamedField X) :
    (S.positiveFrameLedger V).delta = S.positiveFramedDelta V :=
  V.selectedFrameLedger_delta (S.positiveOrbitCollection V)


-- @@ L77-85 verbatim
/-- Equality of positive framed invariants is equivalent to the existence of an
abstract finite Morse schedule between their component ledgers. -/
theorem nonempty_positiveLedgerTrace_iff {Y : FramedLevelSet n}
    (T : FiberSign Y) (V : TamedField X) (W : TamedField Y) :
    Nonempty (MorseLedgerTrace (S.positiveFrameLedger V)
      (T.positiveFrameLedger W)) ↔
      S.positiveFramedDelta V = T.positiveFramedDelta W := by
  rw [MorseLedger.exists_trace_iff_delta_eq,
    S.positiveFrameLedger_delta, T.positiveFrameLedger_delta]


-- @@ L87-87 verbatim
end FiberSign


-- @@ L89-89 verbatim
namespace BridgeData


-- @@ L91-91 verbatim
variable {z : StableSpherePi n} (B : BridgeData n z)


-- @@ L93-95 verbatim
/-- The frame ledger of the northern components of a bridge representative. -/
def northFrameLedger (V : TamedField B.fls) : MorseLedger :=
  B.fiberSign.positiveFrameLedger V


-- @@ L97-100 verbatim
/-- Its ledger value is the bridge's northern delta invariant. -/
theorem northFrameLedger_delta (V : TamedField B.fls) :
    (B.northFrameLedger V).delta = B.northFramedDelta V :=
  B.fiberSign.positiveFrameLedger_delta V


-- @@ L102-111 verbatim
/-- The concrete algebraic contract used by the inverse PT direction: equality of
northern deltas produces a finite standard event trace between the two northern
component ledgers. -/
theorem nonempty_northLedgerTrace_iff {z' : StableSpherePi n}
    (B' : BridgeData n z') (V : TamedField B.fls) (V' : TamedField B'.fls) :
    Nonempty (MorseLedgerTrace (B.northFrameLedger V)
      (B'.northFrameLedger V')) ↔
      B.northFramedDelta V = B'.northFramedDelta V' := by
  rw [MorseLedger.exists_trace_iff_delta_eq,
    B.northFrameLedger_delta, B'.northFrameLedger_delta]


-- @@ L113-113 verbatim
end BridgeData


-- @@ L115-115 verbatim
end Submission
