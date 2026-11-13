import Mathlib
import Submission.SOPositiveDetApproximation


-- @@ L4-21 verbatim
/-!
# Relative smoothing of Cartesian circle homotopies in `SO(m)`

`SOLocalExtension` consumes a jointly smooth map

`R : ℝ → (ℝ × ℝ) → SO(m)`

which starts at the identity and has a prescribed endpoint on the unit
circle.  This file is the relative-smoothing adapter for that contract.  A
continuous Cartesian family which is already smooth near the time-zero plane
and the endpoint unit circle is replaced by a globally smooth `SO(m)` family
without changing either relative locus.

Together with `SOStableCompleteness`, the remaining topological input is now
precisely a continuous Cartesian nullhomotopy with a smooth collar.  All
approximation, determinant control, and retraction back to `SO(m)` are
discharged here and in `SOPositiveDetApproximation`.
-/


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function

-- @@ L26-26 verbatim
open scoped ContDiff Topology


-- @@ L28-28 verbatim
namespace Submission


-- @@ L30-30 verbatim
set_option autoImplicit false


-- @@ L32-32 verbatim
local notation "P" => ℝ × (ℝ × ℝ)


-- @@ L34-38 verbatim
/-- The loci which must be preserved exactly: the whole time-zero plane and
the unit circle at time one. -/
def cartesianSORelativeSet : Set P :=
  {p | p.1 = 0} ∪
    {p | p.1 = 1 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 = 1}


-- @@ L40-46 verbatim
theorem isClosed_cartesianSORelativeSet :
    IsClosed cartesianSORelativeSet := by
  apply IsClosed.union
  · exact isClosed_eq continuous_fst continuous_const
  · apply IsClosed.inter
    · exact isClosed_eq continuous_fst continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const


-- @@ L48-50 verbatim
theorem timeZero_mem_cartesianSORelativeSet (z : ℝ × ℝ) :
    ((0 : ℝ), z) ∈ cartesianSORelativeSet :=
  Or.inl rfl


-- @@ L52-55 verbatim
theorem endpointCircle_mem_cartesianSORelativeSet
    {z : ℝ × ℝ} (hz : z.1 ^ 2 + z.2 ^ 2 = 1) :
    ((1 : ℝ), z) ∈ cartesianSORelativeSet :=
  Or.inr ⟨rfl, hz⟩


-- @@ L57-79 verbatim
/-- A continuous Cartesian `SO(m)` homotopy with a smooth relative collar can
be made globally smooth while fixing both its identity start and its endpoint
on the unit circle. -/
theorem exists_contDiff_cartesianSOHomotopy
    {m : ℕ} (hm : 0 < m)
    (R : P → SOGroup m) (hR : Continuous R)
    (hRzero : ∀ z, R (0, z) = 1)
    {U : Set P} (hU : U ∈ nhdsSet cartesianSORelativeSet)
    (hRU : ContDiffOn ℝ ∞
      (fun p => matrixToEuclidean
        ((R p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ)) U) :
    ∃ Q : P → SOGroup m,
      (∀ i j, ContDiff ℝ ∞ fun p =>
        ((Q p : SOGroup m) : Matrix (Fin m) (Fin m) ℝ) i j) ∧
      (∀ z, Q (0, z) = 1) ∧
      (∀ z, z.1 ^ 2 + z.2 ^ 2 = 1 → Q (1, z) = R (1, z)) := by
  obtain ⟨Q, hQ, hEq⟩ := exists_contDiff_SO_approx_and_eqOn
    hm hR isClosed_cartesianSORelativeSet hU hRU
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro z
    rw [hEq (timeZero_mem_cartesianSORelativeSet z), hRzero]
  · intro z hz
    exact hEq (endpointCircle_mem_cartesianSORelativeSet hz)


-- @@ L81-99 verbatim
/-- Curried form matching the input expected by `SOLocalExtension`. -/
theorem exists_contDiff_curriedCartesianSOHomotopy
    {m : ℕ} (hm : 0 < m)
    (R : ℝ → ℝ × ℝ → SOGroup m)
    (hR : Continuous fun p : P => R p.1 p.2)
    (hRzero : ∀ z, R 0 z = 1)
    {U : Set P} (hU : U ∈ nhdsSet cartesianSORelativeSet)
    (hRU : ContDiffOn ℝ ∞
      (fun p : P => matrixToEuclidean
        ((R p.1 p.2 : SOGroup m) : Matrix (Fin m) (Fin m) ℝ)) U) :
    ∃ Q : ℝ → ℝ × ℝ → SOGroup m,
      (∀ i j, ContDiff ℝ ∞ fun p : P =>
        ((Q p.1 p.2 : SOGroup m) : Matrix (Fin m) (Fin m) ℝ) i j) ∧
      (∀ z, Q 0 z = 1) ∧
      (∀ z, z.1 ^ 2 + z.2 ^ 2 = 1 → Q 1 z = R 1 z) := by
  obtain ⟨Q, hQ, hQzero, hQone⟩ :=
    exists_contDiff_cartesianSOHomotopy hm
      (fun p => R p.1 p.2) hR hRzero hU hRU
  exact ⟨fun s z => Q (s, z), hQ, hQzero, hQone⟩


-- @@ L101-101 verbatim
end Submission
