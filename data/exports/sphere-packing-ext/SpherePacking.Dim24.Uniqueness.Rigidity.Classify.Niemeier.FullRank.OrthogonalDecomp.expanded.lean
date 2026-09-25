module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.IsZLatticeOfUnimodular
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional


-- @@ L5-18 verbatim
/-!
# Orthogonal decomposition for `spanR L`

For a `ℤ`-submodule `L ⊆ ℝ²⁴`, let `W = spanR L` and `K = Wᗮ`. We record the basic orthogonal
decomposition `ℝ²⁴ ≃ₗ W × K`.

## Main definitions
* `IsZLatticeOfUnimodular.W`
* `IsZLatticeOfUnimodular.K`
* `IsZLatticeOfUnimodular.decomp`

## Main statements
* `IsZLatticeOfUnimodular.isCompl_W_K`
-/



-- @@ L21-21 verbatim
namespace SpherePacking.Dim24.Uniqueness.RigidityClassify


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open scoped RealInnerProductSpace


-- @@ L27-27 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L29-29 verbatim
namespace IsZLatticeOfUnimodular


-- @@ L31-31 verbatim
variable (L : Submodule ℤ ℝ²⁴)


-- @@ L33-34 verbatim
/-- The real span `W = spanR L`, as an `ℝ`-subspace of `ℝ²⁴`. -/
@[expose] public abbrev W : Submodule ℝ ℝ²⁴ := spanR (L := L)

-- @@ L35-36 verbatim
/-- The orthogonal complement `K = Wᗮ`. -/
@[expose] public abbrev K : Submodule ℝ ℝ²⁴ := (W (L := L))ᗮ


-- @@ L38-40 verbatim
/-- Any element of `L` lies in the real span `W = spanR L`. -/
public lemma mem_W_of_mem_L {x : ℝ²⁴} (hx : x ∈ L) : x ∈ W (L := L) :=
  Submodule.subset_span hx


-- @@ L42-42 verbatim
instance : (W (L := L)).HasOrthogonalProjection := by infer_instance


-- @@ L44-47 verbatim
/-- The span `W` and its orthogonal complement `K` are complementary subspaces. -/
public lemma isCompl_W_K : IsCompl (W (L := L)) (K (L := L)) := by
  simpa [IsZLatticeOfUnimodular.K] using
    (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection (K := (W (L := L))))


-- @@ L49-52 verbatim
/-- The (linear) orthogonal decomposition `ℝ²⁴ ≃ₗ W × K`. -/
@[expose]
public noncomputable def decomp : (W (L := L) × K (L := L)) ≃ₗ[ℝ] ℝ²⁴ :=
  Submodule.prodEquivOfIsCompl (W (L := L)) (K (L := L)) (isCompl_W_K (L := L))


-- @@ L54-56 verbatim
@[simp] lemma decomp_apply (x : W (L := L) × (W (L := L))ᗮ) :
    decomp (L := L) x = x.1 + x.2 := by
  rfl


-- @@ L58-58 verbatim
end IsZLatticeOfUnimodular


-- @@ L60-60 verbatim
end


-- @@ L62-62 verbatim
end SpherePacking.Dim24.Uniqueness.RigidityClassify
