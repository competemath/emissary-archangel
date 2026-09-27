/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 35621-35749.
Modifications: extracted projection-supremum transport from the spatial
witness, replaced the local multiplication relation by inherited operator
order, and separated the abstract specification from its concrete proof.
Paper: §3. See the upstream PORT_MAP.md.
-/
module

public import LeanPool.ConnesRigidity.Core
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder


-- @@ L21-28 verbatim
/-!
# Projection-supremum transport

This module relates the inherited operator order on projections in concrete
star subalgebras to multiplication, then transports projection suprema across
star-algebra equivalences. It supplies the normality witness consumed by the
spatial factor equivalence in Zhou §3.
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace Connes


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
universe u v


-- @@ L38-51 verbatim
/-- The inherited operator order agrees with the algebraic order on star-subalgebra projections. -/
theorem StarSubalgebra.le_iff_mul_eq_left_of_isStarProjection
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {A : StarSubalgebra ℂ (E →L[ℂ] E)} {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p * q = p := by
  have hp' : IsStarProjection (p : E →L[ℂ] E) := hp.map A.subtype
  have hq' : IsStarProjection (q : E →L[ℂ] E) := hq.map A.subtype
  constructor
  · intro h
    apply Subtype.ext
    exact (hq'.mul_right_and_mul_left_of_nonneg_of_le hp'.nonneg h).1
  · intro h
    exact hp'.le_of_mul_eq_left hq' (congrArg Subtype.val h)


-- @@ L53-66 verbatim
/-- A star-algebra equivalence preserves operator order between subalgebra projections. -/
@[simp]
theorem StarAlgEquiv.map_le_map_iff_of_isStarProjection
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : StarSubalgebra ℂ (E →L[ℂ] E)} {B : StarSubalgebra ℂ (F →L[ℂ] F)}
    (e : A ≃⋆ₐ[ℂ] B) {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    e p ≤ e q ↔ p ≤ q := by
  rw [StarSubalgebra.le_iff_mul_eq_left_of_isStarProjection (hp.map e) (hq.map e),
    StarSubalgebra.le_iff_mul_eq_left_of_isStarProjection hp hq]
  exact ⟨fun h ↦ by
      simpa only [map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm h,
    fun h ↦ by simpa only [map_mul] using congrArg e h⟩


-- @@ L68-68 verbatim
namespace IsProjectionSupremum


-- @@ L70-96 verbatim
/-- A star-algebra equivalence carries a projection supremum to its image. -/
theorem map_starAlgEquiv
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : StarSubalgebra ℂ (E →L[ℂ] E)} {B : StarSubalgebra ℂ (F →L[ℂ] F)}
    (e : A ≃⋆ₐ[ℂ] B) {S : Set A} {p : A}
    (hp : IsProjectionSupremum S p) :
    IsProjectionSupremum (e '' S) (e p) := by
  refine IsProjectionSupremum.intro (hp.isStarProjection.map e) ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨(hp.upper hq).1.map e,
      (StarAlgEquiv.map_le_map_iff_of_isStarProjection
        e (hp.upper hq).1 hp.isStarProjection).2
        (hp.upper hq).2⟩
  · intro r hr hupper
    have hr' : IsStarProjection (e.symm r) := hr.map e.symm
    have hbound : ∀ q ∈ S, q ≤ e.symm r := by
      intro q hq
      have h := hupper (e q) ⟨q, hq, rfl⟩
      simpa only [StarAlgEquiv.symm_apply_apply] using
        (StarAlgEquiv.map_le_map_iff_of_isStarProjection
          e.symm ((hp.upper hq).1.map e) hr).2 h
    have h := hp.least hr' hbound
    have h' : e.symm (e p) ≤ e.symm r := by
      simpa only [StarAlgEquiv.symm_apply_apply] using h
    exact (StarAlgEquiv.map_le_map_iff_of_isStarProjection
      e.symm (hp.isStarProjection.map e) hr).1 h'


-- @@ L98-98 verbatim
end IsProjectionSupremum


-- @@ L100-109 verbatim
/-- Every star-algebra equivalence between operator subalgebras preserves projection suprema. -/
theorem StarAlgEquiv.isNormal
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : StarSubalgebra ℂ (E →L[ℂ] E)} {B : StarSubalgebra ℂ (F →L[ℂ] F)}
    (e : A ≃⋆ₐ[ℂ] B) :
    IsNormalStarAlgEquiv e :=
  IsNormalStarAlgEquiv.intro
    (fun _ _ ↦ IsProjectionSupremum.map_starAlgEquiv e)
    (fun _ _ ↦ IsProjectionSupremum.map_starAlgEquiv e.symm)


-- @@ L111-111 verbatim
end

-- @@ L112-112 verbatim
end Connes
