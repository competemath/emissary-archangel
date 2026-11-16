/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.ProductNorm


-- @@ L8-14 verbatim
/-!
# Independence of the realization for the original integral PBW preimage

The restricted braid is determined on its original skew-generator algebra by formulas
in the Cartan datum alone. Its injectivity transports uniqueness of actual PBW preimages.
No comparison of abstract PBW span models is involved.
-/


-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
open LieLean LieLean.QuantumGroup LusztigF RestrictedBraidIsometry

-- @@ L18-18 verbatim
namespace PBWProductNorm

-- @@ L19-19 verbatim
local notation "𝕂" => RatFunc ℚ

-- @@ L20-20 verbatim
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

-- @@ L21-21 verbatim
attribute [local instance] neZero_ratFunc_X

-- @@ L22-23 verbatim
variable {I Y Z : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] [AddCommGroup Z]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (S : D.RootDatum Z)


-- @@ L25-37 verbatim
/-- The original restricted braid is independent of the ambient realization. -/
theorem projectedBraid_eq (i : I) {x : Quotient D 𝕧}
    (hx : x ∈ quotientSkewGenerators D i) :
    projectedBraid R i x = projectedBraid S i x := by
  have hs := mem_sourceWord_span i hx
  clear hx
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    rw [projectedBraid_word, projectedBraid_word]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | smul c a _ ha => simp only [map_smul, ha]


-- @@ L39-47 verbatim
/-- Injectivity of the projected braid restricted to its actual left kernel. -/
theorem projectedBraid_injective (i : I) {x y : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0) (hy : quotientLDeriv D i y = 0)
    (h : projectedBraid R i x = projectedBraid R i y) : x = y := by
  apply quotientPlus_injective R
  apply (braidEquivOfNotRoot R ratFunc_X_not_root i).injective
  have he := congrArg (quotientPlus R) h
  simpa only [projectedBraid_spec, quotientSkewProjection_of_ker D i hx,
    quotientSkewProjection_of_ker D i hy] using he


-- @@ L49-49 verbatim
open Modified

-- @@ L50-50 verbatim
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU

-- @@ L51-51 verbatim
variable {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}


-- @@ L53-61 verbatim
/-- Forward restricted braid sends the actual adapted inverse-braid preimage to its tail. -/
theorem projectedBraid_preimage {i : I} {w : List I} (hw : cs.IsReduced (i :: w))
    (c : Fin w.length → ℕ) :
    projectedBraid R i (integralPBWPreimage R hw (Fin.cons 0 c)) =
      integralPBWPreimage R (w := w) (by simpa using hw.drop 1) c := by
  apply quotientPlus_injective R
  rw [projectedBraid_spec, quotientSkewProjection_of_ker D i
    (quotientLDeriv_integralPBWPreimage_cons_zero R hw c)]
  exact braid_integralPBWPreimage_cons_zero R hw c


-- @@ L63-78 verbatim
/-- Actual equality of the original integral preimages for any two root data. -/
theorem preimage_realization_independent {w : List I} (hw : cs.IsReduced w)
    (c : Fin w.length → ℕ) :
    (integralPBWPreimage R hw c : Quotient D 𝕧) = integralPBWPreimage S hw c := by
  induction w with
  | nil => rw [preimage_nil R, preimage_nil S]
  | cons i w ih =>
    rw [integralPBWPreimage_cons R hw, integralPBWPreimage_cons S hw]
    congr 1
    apply projectedBraid_injective R i
      (quotientLDeriv_integralPBWPreimage_cons_zero R hw _)
      (quotientLDeriv_integralPBWPreimage_cons_zero S hw _)
    rw [projectedBraid_preimage R]
    rw [projectedBraid_eq R S i ((mem_quotientSkewGenerators_iff D i _).mpr
      (quotientLDeriv_integralPBWPreimage_cons_zero S hw _)), projectedBraid_preimage S]
    exact ih _ _


-- @@ L80-80 verbatim
end PBWProductNorm
