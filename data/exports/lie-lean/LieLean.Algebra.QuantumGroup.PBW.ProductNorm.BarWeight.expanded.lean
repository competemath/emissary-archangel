/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.LusztigF.BarQuotient
import LieLean.Algebra.QuantumGroup.PBW.ProductNorm.IntrinsicDegree


-- @@ L9-11 verbatim
/-! Bar preserves the actual free and quotient weight spaces. These elementary
reconstructed lemmas supply the degree constraint for the PBW bar comparison;
they do not assert preservation of the crystal lattice or balancedness. -/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
open LieLean LieLean.QuantumGroup

-- @@ L15-15 verbatim
local notation "𝕂" => RatFunc ℚ

-- @@ L16-16 verbatim
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

-- @@ L17-17 verbatim
namespace LusztigF

-- @@ L18-18 verbatim
variable {I : Type*}


-- @@ L20-20 verbatim
variable [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)


-- @@ L22-32 expanded
/-- On the original quotient, bar preserves the actual grand-loop weight space. -/
theorem quotientBar_mem_Uw {ν : I →₀ ℕ} {x : Quotient D (RatFunc.X : RatFunc ℚ)}
    (hx : (negativeQuotientEquiv D).symm x ∈ GrandLoop.Uw D (RatFunc.X : RatFunc ℚ) ν) :
    (negativeQuotientEquiv D).symm (quotientBar D x) ∈ GrandLoop.Uw D (RatFunc.X : RatFunc ℚ) ν :=
  by
  obtain ⟨a, ha, he⟩ := hx
  have hq : toQuotient D (RatFunc.X : RatFunc ℚ) a = x :=
    by
    apply (negativeQuotientEquiv D).symm.injective
    rw [negativeQuotientEquiv_symm_toQuotient]
    exact he
  rw [← hq, quotientBar_toQuotient, negativeQuotientEquiv_symm_toQuotient]
  exact ⟨bar a, bar_mem_weightSpace ha, rfl⟩


-- @@ L34-41 expanded
/-- Bar both preserves and reflects the root-lattice degree. -/
theorem quotientBar_mem_Uw_iff {ν : I →₀ ℕ} {x : Quotient D (RatFunc.X : RatFunc ℚ)} :
    (negativeQuotientEquiv D).symm (quotientBar D x) ∈ GrandLoop.Uw D (RatFunc.X : RatFunc ℚ) ν ↔
      (negativeQuotientEquiv D).symm x ∈ GrandLoop.Uw D (RatFunc.X : RatFunc ℚ) ν :=
  by
  constructor
  · intro hx
    simpa only [quotientBar_quotientBar D x] using quotientBar_mem_Uw D hx
  · exact quotientBar_mem_Uw D


-- @@ L42-42 verbatim
end LusztigF


-- @@ L44-44 verbatim
namespace PBWProductNorm

-- @@ L45-45 verbatim
open LusztigF Modified

-- @@ L46-46 verbatim
attribute [local instance] neZero_ratFunc_X

-- @@ L47-47 verbatim
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU

-- @@ L48-50 verbatim
variable {I Y : Type*} [DecidableEq I] [Finite I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}


-- @@ L52-56 expanded
/-- The bar of the original integral PBW preimage has the same computed degree. -/
theorem bar_homogeneous_Uw {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    (negativeQuotientEquiv D).symm (quotientBar D (integralPBWPreimage R hw c)) ∈
      GrandLoop.Uw D (RatFunc.X : RatFunc ℚ) (degree D w c) :=
  quotientBar_mem_Uw D (homogeneous_Uw R hw c)


-- @@ L57-57 verbatim
end PBWProductNorm
