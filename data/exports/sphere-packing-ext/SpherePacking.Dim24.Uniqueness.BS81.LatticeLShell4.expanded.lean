module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL


-- @@ L4-10 verbatim
/-!
# Elementary facts about `latticeShell4`

This file records elementary facts about `twoCodeVectors C` and the norm-`4` shell
`latticeShell4 C`. These are the easy direction of BS81 Lemma 17:
`twoCodeVectors C ⊆ latticeShell4 C`.
-/


-- @@ L12-12 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open scoped RealInnerProductSpace Pointwise


-- @@ L18-18 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L20-23 verbatim
/-- If `C` is finite, then so is `twoCodeVectors C`. -/
public lemma twoCodeVectors_finite {C : Set ℝ²⁴} (hfin : C.Finite) :
    (twoCodeVectors C).Finite := by
  simpa [twoCodeVectors] using hfin.image (fun u : ℝ²⁴ => (2 : ℝ) • u)


-- @@ L25-31 verbatim
/-- For a spherical code `C`, the scaled code `twoCodeVectors C` lies in `latticeShell4 C`. -/
public lemma twoCodeVectors_subset_latticeShell4_of_code
    (C : Set ℝ²⁴) (hC : IsSphericalCode 24 C (1 / 2 : ℝ)) :
    twoCodeVectors C ⊆ latticeShell4 C := by
  intro x hx
  rcases hx with ⟨u, hu, rfl⟩
  exact smul_mem_latticeShell4_of_norm_one (C := C) hu (hC.norm_one hu)


-- @@ L33-43 verbatim
/-- Scaling by `2` preserves cardinality: `ncard (twoCodeVectors C) = ncard C`. -/
public lemma ncard_twoCodeVectors_eq (C : Set ℝ²⁴) :
    Set.ncard (twoCodeVectors C) = Set.ncard C := by
  have hinj : Function.Injective (fun u : ℝ²⁴ => (2 : ℝ) • u) := by
    intro u v huv
    have hu2 : IsUnit (2 : ℝ) := by
      have : (2 : ℝ) ≠ 0 := by simp
      exact isUnit_iff_ne_zero.2 this
    exact (IsUnit.smul_left_cancel (a := (2 : ℝ)) hu2).1 huv
  simpa [twoCodeVectors] using
    Set.ncard_image_of_injective (s := C) (f := fun u : ℝ²⁴ => (2 : ℝ) • u) hinj


-- @@ L45-45 verbatim
end

-- @@ L46-46 verbatim
end SpherePacking.Dim24.Uniqueness.BS81
