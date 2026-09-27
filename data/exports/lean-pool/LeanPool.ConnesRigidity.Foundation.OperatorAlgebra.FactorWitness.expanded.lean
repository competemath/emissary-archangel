/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 35621-35749.
Modifications: renamed and generalized the spatial witness while preserving
the spatial-to-tracial argument. Paper: §3. See the upstream PORT_MAP.md.
-/
module

public import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.Projection.Supremum

public import LeanPool.ConnesRigidity.Core


-- @@ L19-21 verbatim
/-!
The factor witness component of the Connes rigidity formalization.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace Connes

-- @@ L26-26 verbatim
namespace FactorWitness


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-40 verbatim
/-- Spatial witness data for a factor equivalence. Paper: §3. -/
structure SpatialWitness (G H : CountableDiscreteGroup) where
  /--
  The `unitary` component of `SpatialWitness`.
  -/
  unitary : GroupL2 G ≃ₗᵢ[ℂ] GroupL2 H
  maps_group_factor :
    ∀ T : GroupL2 G →L[ℂ] GroupL2 G,
      T ∈ groupVonNeumannAlgebra G ↔
        unitary.conjStarAlgEquiv T ∈ groupVonNeumannAlgebra H
  maps_vacuum : unitary (delta G 1) = delta H 1


-- @@ L42-42 verbatim
namespace SpatialWitness


-- @@ L44-44 verbatim
universe u v


-- @@ L46-46 verbatim
variable {G : CountableDiscreteGroup.{u}}

-- @@ L47-47 verbatim
variable {H : CountableDiscreteGroup.{v}}


-- @@ L49-90 verbatim
/-- Turn a spatial witness into its conjugation star-algebra equivalence. Paper: §3. -/
def toStarAlgEquiv (w : SpatialWitness G H) :
    GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H where
  toFun x :=
    ⟨w.unitary.conjStarAlgEquiv x,
      (w.maps_group_factor x).mp x.property⟩
  invFun y :=
    ⟨w.unitary.conjStarAlgEquiv.symm y, by
      apply (w.maps_group_factor (w.unitary.conjStarAlgEquiv.symm y)).mpr
      have h := w.unitary.conjStarAlgEquiv.apply_symm_apply
        (y : GroupL2 H →L[ℂ] GroupL2 H)
      rw [h]
      exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact w.unitary.conjStarAlgEquiv.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact w.unitary.conjStarAlgEquiv.apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul w.unitary.conjStarAlgEquiv
      (x : GroupL2 G →L[ℂ] GroupL2 G)
      (y : GroupL2 G →L[ℂ] GroupL2 G)
  map_add' x y := by
    apply Subtype.ext
    exact map_add w.unitary.conjStarAlgEquiv
      (x : GroupL2 G →L[ℂ] GroupL2 G)
      (y : GroupL2 G →L[ℂ] GroupL2 G)
  map_star' x := by
    apply Subtype.ext
    exact map_star w.unitary.conjStarAlgEquiv
      (x : GroupL2 G →L[ℂ] GroupL2 G)
  map_smul' c x := by
    apply Subtype.ext
    change
      w.unitary.conjStarAlgEquiv
        (c • (x : GroupL2 G →L[ℂ] GroupL2 G)) =
        c • w.unitary.conjStarAlgEquiv
          (x : GroupL2 G →L[ℂ] GroupL2 G)
    exact map_smul w.unitary.conjStarAlgEquiv c
      (x : GroupL2 G →L[ℂ] GroupL2 G)


-- @@ L92-103 verbatim
/-- The spatial witness preserves the canonical vacuum trace. Paper: §3. -/
theorem trace_preserving (w : SpatialWitness G H)
    (x : GroupVonNeumannAlgebra G) :
    canonicalTrace H (w.toStarAlgEquiv x) = canonicalTrace G x := by
  change inner ℂ (delta H 1)
      (w.unitary ((x : GroupL2 G →L[ℂ] GroupL2 G)
        (w.unitary.symm (delta H 1)))) =
    inner ℂ (delta G 1)
      ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))
  rw [← w.maps_vacuum, w.unitary.symm_apply_apply]
  exact w.unitary.inner_map_map (delta G 1)
    ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))


-- @@ L105-110 verbatim
/-- Package the spatial witness as a trace-preserving factor equivalence. Paper: §3. -/
def toTracialGroupFactorEquiv
    (w : SpatialWitness G H) : TracialGroupFactorEquiv G H where
  toStarAlgEquiv := w.toStarAlgEquiv
  normal := StarAlgEquiv.isNormal w.toStarAlgEquiv
  trace_preserving := w.trace_preserving


-- @@ L112-112 verbatim
end SpatialWitness


-- @@ L114-117 verbatim
/-- Spatial-to-tracial transfer. Paper: §3. -/
theorem tracialEquiv_of_spatialWitness {G H : CountableDiscreteGroup}
    (w : SpatialWitness G H) : TracialGroupFactorsIsomorphic G H :=
  ⟨w.toTracialGroupFactorEquiv⟩


-- @@ L119-119 verbatim
end

-- @@ L120-120 verbatim
end FactorWitness

-- @@ L121-121 verbatim
end Connes
