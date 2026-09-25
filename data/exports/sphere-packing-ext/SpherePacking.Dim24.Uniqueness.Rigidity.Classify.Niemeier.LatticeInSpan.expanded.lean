module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.IsZLatticeOfUnimodular
public import Mathlib.Algebra.Module.ZLattice.Basic


-- @@ L5-16 verbatim
/-!
# A lattice inside its real span

Given a `ℤ`-submodule `L ⊆ ℝ²⁴`, we view `L` as a `ℤ`-submodule of its real span `spanR L`.
This is a convenient construction for the implication `Unimodular → IsZLattice`.

## Main definitions
* `IsZLatticeOfUnimodular.latticeInSpanR`

## Main statements
* `IsZLatticeOfUnimodular.instIsZLattice_latticeInSpanR`
-/


-- @@ L18-18 verbatim
namespace SpherePacking.Dim24.Uniqueness.RigidityClassify


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open scoped RealInnerProductSpace


-- @@ L24-24 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L26-26 verbatim
namespace IsZLatticeOfUnimodular


-- @@ L28-28 verbatim
variable (L : Submodule ℤ ℝ²⁴)


-- @@ L30-34 verbatim
/-- View `L` as a `ℤ`-submodule of its real span `spanR L`. -/
@[expose]
public def latticeInSpanR : Submodule ℤ (spanR (L := L)) :=
  Submodule.comap
    (((spanR (L := L)).subtype : spanR (L := L) →ₗ[ℝ] ℝ²⁴).restrictScalars ℤ) L


-- @@ L36-39 verbatim
/-- Membership in `latticeInSpanR L` is definitional membership in `L` after coercion to `ℝ²⁴`. -/
@[simp] public lemma mem_latticeInSpanR_iff (x : spanR (L := L)) :
    x ∈ latticeInSpanR (L := L) ↔ (x : ℝ²⁴) ∈ L := by
  rfl


-- @@ L41-59 verbatim
/-- If `L` is discrete, then `latticeInSpanR L` has the discrete topology. -/
public instance instDiscreteTopology_latticeInSpanR [DiscreteTopology L] :
    DiscreteTopology (latticeInSpanR (L := L)) := by
  -- Use a continuous injective map into the discrete space `L`.
  let f : latticeInSpanR (L := L) → L :=
    fun x => ⟨((x : spanR (L := L)) : ℝ²⁴), x.property⟩
  have hf : Continuous f := by
    -- `fun_prop` handles continuity between subtypes of `ℝ²⁴`.
    dsimp [f]
    fun_prop
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxy' :
        ((x : spanR (L := L)) : ℝ²⁴) = ((y : spanR (L := L)) : ℝ²⁴) :=
      congrArg (fun z : L => (z : ℝ²⁴)) hxy
    -- `spanR (L := L)` is a subtype of `ℝ²⁴`.
    exact Subtype.ext hxy'
  exact DiscreteTopology.of_continuous_injective (hc := hf) (hinj := hinj)


-- @@ L61-98 verbatim
/-- If `L` is discrete, then `latticeInSpanR L` is a `ℤ`-lattice in `spanR L`. -/
public instance instIsZLattice_latticeInSpanR [DiscreteTopology L] :
    IsZLattice ℝ (latticeInSpanR (L := L)) := by
  -- Show `span ℝ (latticeInSpanR : Set (spanR L)) = ⊤` by comparing its image in `ℝ²⁴`.
  refine ⟨?_⟩
  -- Let `W := spanR L` and `LW := latticeInSpanR L`.
  let W : Submodule ℝ ℝ²⁴ := spanR (L := L)
  let LW : Submodule ℤ W := latticeInSpanR (L := L)
  have hinj : Function.Injective (W.subtype : W →ₗ[ℝ] ℝ²⁴) := fun _ _ h => by
    apply Subtype.ext
    exact h
  have himg :
      (fun w : W => (w : ℝ²⁴)) '' (LW : Set W) = (L : Set ℝ²⁴) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [LW, W, latticeInSpanR] using hw
    · intro hx
      refine ⟨⟨x, ?_⟩, ?_, rfl⟩
      · -- `x ∈ spanR L`
        exact Submodule.subset_span hx
      · -- membership in `LW`
        simpa [LW, W, latticeInSpanR] using hx
  have hmap :
      Submodule.map (W.subtype : W →ₗ[ℝ] ℝ²⁴)
          (Submodule.span ℝ (LW : Set W))
        =
        W := by
    -- Use `map_span` and the definition of `W`.
    rw [Submodule.map_span]
    simp [W, IsZLatticeOfUnimodular.spanR, himg]
  -- Pull back along the injective map `W.subtype`.
  have :
      Submodule.span ℝ (LW : Set W) = ⊤ := by
    have := congrArg (Submodule.comap (W.subtype : W →ₗ[ℝ] ℝ²⁴)) hmap
    -- simplify `comap (subtype) W = ⊤` and `comap_map = _` for injective maps
    simpa [Submodule.comap_map_eq_of_injective hinj] using this
  simpa [LW] using this


-- @@ L100-100 verbatim
end IsZLatticeOfUnimodular


-- @@ L102-102 verbatim
end


-- @@ L104-104 verbatim
end SpherePacking.Dim24.Uniqueness.RigidityClassify
