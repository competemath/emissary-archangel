module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.Discrete


-- @@ L4-17 verbatim
/-!
# Finite shells in a discrete lattice

For a discrete subgroup of a proper metric space, the intersection with any bounded closed set is
finite. We record a few convenient corollaries specialized to `Submodule ℤ ℝ²⁴`.

These lemmas will be used when defining and studying the lattice theta series and root counts.

## Main statements
* `finite_closedBall_inter`
* `finite_shell_norm_le`
* `finite_subtype_norm_le`
* `finite_subtype_norm_lt`
-/


-- @@ L19-19 verbatim
namespace SpherePacking.Dim24.Uniqueness.RigidityClassify


-- @@ L21-21 verbatim
open scoped RealInnerProductSpace

-- @@ L22-22 verbatim
open Metric


-- @@ L24-24 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

-- @@ L25-31 verbatim
/-- Lattice points in a closed ball form a finite set. -/
public theorem finite_closedBall_inter (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] (R : ℝ) :
    (closedBall (0 : ℝ²⁴) R ∩ (L : Set ℝ²⁴)).Finite := by
  change (closedBall (0 : ℝ²⁴) R ∩ (L.toAddSubgroup : Set ℝ²⁴)).Finite
  haveI : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  exact finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall
    inferInstance


-- @@ L33-39 verbatim
/-- The set `{v ∈ L | ‖v‖ ≤ R}` is finite for a discrete lattice `L`. -/
public theorem finite_shell_norm_le (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] (R : ℝ) :
    {v : ℝ²⁴ | v ∈ L ∧ ‖v‖ ≤ R}.Finite := by
  -- `‖v‖ ≤ R` means `v ∈ closedBall 0 R`.
  have : {v : ℝ²⁴ | v ∈ L ∧ ‖v‖ ≤ R} = closedBall (0 : ℝ²⁴) R ∩ (L : Set ℝ²⁴) := by
    ext v; simp [Set.mem_inter_iff, and_comm]
  simpa [this] using finite_closedBall_inter (L := L) (R := R)


-- @@ L41-59 verbatim
/-- The subset `{z : L | ‖z‖ ≤ R}` is finite when `L` is discrete. -/
public theorem finite_subtype_norm_le (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] (R : ℝ) :
    {z : L | ‖(z : ℝ²⁴)‖ ≤ R}.Finite := by
  have hFinAmb : (Metric.closedBall (0 : ℝ²⁴) R ∩ (L : Set ℝ²⁴)).Finite :=
    finite_closedBall_inter (L := L) (R := R)
  let e : L ↪ ℝ²⁴ := ⟨fun z : L => (z : ℝ²⁴), Subtype.val_injective⟩
  have :
      e ⁻¹' (Metric.closedBall (0 : ℝ²⁴) R ∩ (L : Set ℝ²⁴)) =
        {z : L | ‖(z : ℝ²⁴)‖ ≤ R} := by
    ext z
    constructor
    · intro hz
      have hz' : (e z : ℝ²⁴) ∈ Metric.closedBall (0 : ℝ²⁴) R := hz.1
      simpa [e, mem_closedBall_zero_iff] using hz'
    · intro hz
      refine ⟨?_, ?_⟩
      · simpa [e, mem_closedBall_zero_iff] using hz
      · simp [e]
  simpa [this] using (Set.Finite.preimage_embedding (f := e) hFinAmb)


-- @@ L61-66 verbatim
/-- The subset `{z : L | ‖z‖ < R}` is finite when `L` is discrete. -/
public theorem finite_subtype_norm_lt (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] (R : ℝ) :
    {z : L | ‖(z : ℝ²⁴)‖ < R}.Finite := by
  refine (finite_subtype_norm_le (L := L) (R := R)).subset ?_
  intro z hz
  exact le_of_lt (by simpa using hz)


-- @@ L68-68 verbatim
end SpherePacking.Dim24.Uniqueness.RigidityClassify
