/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalCoefficient
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse


-- @@ L22-23 verbatim
/-! Time identities derived from the source deformation data, including the actual inverse and
normal paths. -/


-- @@ L25-25 verbatim
section


-- @@ L27-27 verbatim
/-! The actual time coefficient of the vector potential, with uniform factorial bounds. -/


-- @@ L29-29 verbatim
section


-- @@ L31-31 verbatim
/-! The vector-potential multiplier is a fixed linear contraction of the normal functional. -/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
namespace EulerPacketCrossProduct


-- @@ L39-39 verbatim
open EulerSmoothLimit EulerTransverseGramInverse InnerProductSpace


-- @@ L41-44 verbatim
/-- Normal vector, given by `(ContinuousLinearMap.apply ℝ Space (1 : ℝ)).comp (realAdjoint (U :=
Space) (E := ℝ))`. -/
def normalVector : (Space →L[ℝ] ℝ) →L[ℝ] Space :=
  (ContinuousLinearMap.apply ℝ Space (1 : ℝ)).comp (realAdjoint (U := Space) (E := ℝ))


-- @@ L46-46 verbatim
@[simp] theorem normalVector_apply (N : Space →L[ℝ] ℝ) : normalVector N = N.adjoint 1 := rfl


-- @@ L48-50 verbatim
/-- Normal potential map, given by `-(crossOperator.comp normalVector)`. -/
def normalPotentialMap : (Space →L[ℝ] ℝ) →L[ℝ] (Space →L[ℝ] Space) :=
  -(crossOperator.comp normalVector)


-- @@ L52-53 verbatim
@[simp] theorem normalPotentialMap_apply (N : Space →L[ℝ] ℝ) :
    normalPotentialMap N = -crossLeft (N.adjoint 1) := rfl


-- @@ L55-60 verbatim
theorem normalPotentialMap_norm : ‖normalPotentialMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro N
  simp only [normalPotentialMap_apply, norm_neg, one_mul]
  apply (crossLeft_norm_le (N.adjoint 1)).trans
  simpa only [norm_one, mul_one, LinearIsometryEquiv.norm_map] using N.adjoint.le_opNorm 1


-- @@ L62-67 verbatim
theorem normalVector_eq (m : Space) (N : Space →L[ℝ] ℝ)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / (‖m‖ ^ 2)) : N.adjoint 1 = ((‖m‖^2)⁻¹) • m := by
  apply ext_inner_right ℝ
  intro v
  rw [N.adjoint_inner_left, real_inner_smul_left]
  rw [Real.inner_apply, one_mul, hN, div_eq_mul_inv, mul_comm]


-- @@ L69-78 verbatim
/-- No additional inverse or derivative estimate is needed after constructing the normal functional.
-/
theorem normalPotentialMap_eq (m : Space) (N : Space →L[ℝ] ℝ)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / (‖m‖ ^ 2)) : normalPotentialMap N = potentialMultiplier m := by
  change -(crossOperator (N.adjoint 1)) = potentialMultiplier m
  rw [normalVector_eq m N hN, map_smul, crossOperator_apply]
  apply ContinuousLinearMap.ext
  intro v
  change -(((‖m‖^2)⁻¹) • crossLeft m v) = (-((‖m‖^2)⁻¹)) • crossLeft m v
  exact (neg_smul _ _).symm


-- @@ L80-80 verbatim
end EulerPacketCrossProduct


-- @@ L82-82 verbatim
end

-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end


-- @@ L87-87 verbatim
section


-- @@ L89-89 verbatim
/-! The literal vector-potential multiplier inherits the source normal coefficient bounds. -/


-- @@ L91-91 verbatim
@[expose] public section


-- @@ L93-93 verbatim
noncomputable section


-- @@ L95-95 verbatim
namespace EulerSourcePotentialCoefficient


-- @@ L97-98 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketCrossProduct
  EulerSourceNormalCoefficient EulerSourceForwardCoefficient EulerTimeLpGramGevrey EulerGevrey

-- @@ L99-99 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L101-102 verbatim
/-- Normal field: an abbreviation for `Space →ᵇ (Space →L[ℝ] ℝ)`. -/
abbrev NormalField := Space →ᵇ (Space →L[ℝ] ℝ)

-- @@ L103-104 verbatim
/-- Potential field: an abbreviation for `Space →ᵇ (Space →L[ℝ] Space)`. -/
abbrev PotentialField := Space →ᵇ (Space →L[ℝ] Space)


-- @@ L106-106 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L108-109 verbatim
/-- Cache the standard `NormedAddCommGroup NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient1 : NormedAddCommGroup NormalField := inferInstance

-- @@ L110-111 verbatim
/-- Cache the standard `NormedSpace ℝ NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient2 : NormedSpace ℝ NormalField := inferInstance

-- @@ L112-114 verbatim
/-- Cache the standard `NormedAddCommGroup PotentialField` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient3 : NormedAddCommGroup PotentialField := inferInstance

-- @@ L115-116 verbatim
/-- Cache the standard `NormedSpace ℝ PotentialField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient4 : NormedSpace ℝ PotentialField := inferInstance

-- @@ L117-120 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,NormalField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient5 : NormedAddCommGroup C(K,NormalField) :=
    inferInstance

-- @@ L121-122 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,NormalField)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient6 : NormedSpace ℝ C(K,NormalField) := inferInstance

-- @@ L123-126 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient7 : NormedAddCommGroup C(K,PotentialField) :=
    inferInstance

-- @@ L127-129 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient8 : NormedSpace ℝ C(K,PotentialField) := inferInstance


-- @@ L131-134 verbatim
/-- Potential path map, given by `(normalPotentialMap.compLeftContinuousBounded
Space).compLeftContinuous ℝ K`. -/
def potentialPathMap : C(K,NormalField) →L[ℝ] C(K,PotentialField) :=
  (normalPotentialMap.compLeftContinuousBounded Space).compLeftContinuous ℝ K


-- @@ L136-138 verbatim
omit [CompactSpace K] in
@[simp] theorem potentialPathMap_apply (N : C(K, NormalField)) (t : K) (x : Space) :
    potentialPathMap N t x = normalPotentialMap (N t x) := rfl


-- @@ L140-150 verbatim
theorem potentialPathMap_norm : ‖potentialPathMap (K := K)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro N
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg N)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg N)).mpr
  intro x
  change ‖normalPotentialMap (N t x)‖ ≤ ‖N‖
  exact (normalPotentialMap.le_of_opNorm_le normalPotentialMap_norm (N t x)).trans
    (by simpa only [one_mul] using ((N t).norm_coe_le_norm x).trans (N.norm_coe_le_norm t))


-- @@ L152-153 verbatim
variable (m : SmoothCoefficientPath K Space) (c : ℝ) (hc : 0 < c)
  (hm : ∀ t x, c ≤ ‖m.field t x‖ ^ 2)


-- @@ L155-157 verbatim
/-- Potential coefficient, given by `potentialPathMap (normalFunctional m c hc hm)`. -/
def potentialCoefficient : C(K,PotentialField) :=
  potentialPathMap (normalFunctional m c hc hm)


-- @@ L159-162 verbatim
theorem potentialCoefficient_apply (t : K) (x : Space) :
    potentialCoefficient m c hc hm t x = potentialMultiplier (m.field t x) :=
  normalPotentialMap_eq (m.field t x) (normalFunctional m c hc hm t x)
    (normalFunctional_apply m c hc hm t x)


-- @@ L164-171 verbatim
theorem potentialCoefficient_translated (a : Space) :
    translateCoefficientPath (potentialCoefficient m c hc hm) a =
      potentialPathMap (translateCoefficientPath (normalFunctional m c hc hm) a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl


-- @@ L173-180 verbatim
theorem potentialCoefficient_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (potentialCoefficient m c hc hm)) := by
  have he : translateCoefficientPath (potentialCoefficient m c hc hm) =
      fun a => potentialPathMap (translateCoefficientPath (normalFunctional m c hc hm) a) :=
    funext (potentialCoefficient_translated m c hc hm)
  rw [he]
  exact (potentialPathMap (K := K)).contDiff.comp
    (normalFunctional_translation_contDiff m c hc hm)


-- @@ L182-198 verbatim
/-- The source coefficient passes through a linear contraction, with no radius or shift change. -/
theorem potentialCoefficient_translation_bound (Rc C Ri : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRi : 2 * gramCost c C 1 * (Rc + 1) ≤ Ri)
    (hbm : ∀ n t x, ‖iteratedFDeriv ℝ n (m.field t : Space → Space) x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (potentialCoefficient m c hc hm)) a‖ ≤
      (3*Ri*C)*majorant (4*Ri) 0 n := by
  have he : translateCoefficientPath (potentialCoefficient m c hc hm) =
      fun a => potentialPathMap (translateCoefficientPath (normalFunctional m c hc hm) a) :=
    funext (potentialCoefficient_translated m c hc hm)
  rw [he]
  have h := (potentialPathMap (K := K)).norm_iteratedFDeriv_comp_left
    ((normalFunctional_translation_contDiff m c hc hm).contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right (potentialPathMap_norm (K := K)) (norm_nonneg _)).trans
    (by
        simpa only [one_mul] using normalFunctional_translation_bound m c hc hm Rc C Ri hRc hC hRi
            hbm n a))


-- @@ L200-200 verbatim
end EulerSourcePotentialCoefficient


-- @@ L202-202 verbatim
end

-- @@ L203-203 verbatim
end


-- @@ L205-205 verbatim
end


-- @@ L207-207 verbatim
section


-- @@ L209-209 verbatim
/-! An inverse-free polynomial formula for the actual normal multiplier's time derivative. -/


-- @@ L211-211 verbatim
@[expose] public section


-- @@ L213-213 verbatim
noncomputable section


-- @@ L215-215 verbatim
namespace EulerPacketCrossProduct


-- @@ L217-217 verbatim
open ContinuousLinearMap InnerProductSpace EulerSmoothLimit


-- @@ L219-221 verbatim
/-- Differentiate the normal functional using only itself and the normal's derivative column. -/
def normalTimeMap (N : Space →L[ℝ] ℝ) (Q₁ : ℝ →L[ℝ] Space) : Space →L[ℝ] ℝ :=
  (N.comp N.adjoint).comp Q₁.adjoint - (2 : ℝ) • (N.comp Q₁).comp N


-- @@ L223-238 verbatim
theorem normalTimeMap_apply (m mt : Space) (N : Space →L[ℝ] ℝ) (hm : m ≠ 0)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / ‖m‖ ^ 2) (v : Space) :
    normalTimeMap N (toSpanSingleton ℝ mt) v =
      ⟪mt,v⟫_ℝ / ‖m‖^2 - (2*⟪m,mt⟫_ℝ/(‖m‖^2)^2)*⟪m,v⟫_ℝ := by
  have hd : ‖m‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hm)
  have hNm : N m = 1 := by rw [hN, real_inner_self_eq_norm_sq, div_self hd]
  have hAdj (s : ℝ) : N.adjoint s = s • (((‖m‖^2)⁻¹) • m) := by
    calc
      N.adjoint s = N.adjoint (s • (1 : ℝ)) := by simp
      _ = s • N.adjoint 1 := map_smul N.adjoint s 1
      _ = _ := by rw [normalVector_eq m N hN]
  simp only [normalTimeMap, sub_apply, smul_apply, comp_apply, adjoint_toSpanSingleton,
    innerSL_apply_apply, toSpanSingleton_apply]
  rw [hAdj, map_smul, map_smul, hNm, map_smul, hN mt, hN v]
  simp only [smul_eq_mul, mul_one]
  field_simp


-- @@ L240-248 verbatim
theorem normalTimeMap_vector (m mt : Space) (N : Space →L[ℝ] ℝ) (hm : m ≠ 0)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / ‖m‖ ^ 2) :
    (normalTimeMap N (toSpanSingleton ℝ mt)).adjoint 1 =
      ((‖m‖^2)⁻¹) • mt - (2*⟪m,mt⟫_ℝ/(‖m‖^2)^2) • m := by
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left, Real.inner_apply, one_mul, normalTimeMap_apply m mt N hm hN]
  simp only [inner_sub_left, real_inner_smul_left, div_eq_mul_inv]
  ring


-- @@ L250-257 verbatim
/-- This polynomial coefficient is exactly the derivative of −cross(m)/|m|². -/
theorem normalTimeMap_potential (m mt : Space) (N : Space →L[ℝ] ℝ) (hm : m ≠ 0)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / ‖m‖ ^ 2) :
    normalPotentialMap (normalTimeMap N (toSpanSingleton ℝ mt)) =
      potentialMultiplierDerivative m mt := by
  change -crossOperator ((normalTimeMap N (toSpanSingleton ℝ mt)).adjoint 1) = _
  rw [normalTimeMap_vector m mt N hm hN, map_sub, map_smul, map_smul, neg_sub]
  rfl


-- @@ L259-259 verbatim
end EulerPacketCrossProduct


-- @@ L261-261 verbatim
end

-- @@ L262-262 verbatim
end


-- @@ L264-264 verbatim
end


-- @@ L266-266 verbatim
@[expose] public section


-- @@ L268-268 verbatim
noncomputable section


-- @@ L270-270 verbatim
namespace EulerSourcePotentialCoefficient


-- @@ L272-274 verbatim
open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerPacketCrossProduct EulerSourceNormalCoefficient EulerBoundedFieldCalculus
  EulerOperatorGevreyCalculus EulerGevrey EulerTimeLpGramGevrey EulerVolterraConvolution

-- @@ L275-275 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L277-277 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L279-282 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient1 : NormedAddCommGroup (Space →L[ℝ] ℝ) :=
    inferInstance

-- @@ L283-284 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] ℝ)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient2 : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance

-- @@ L285-288 verbatim
/-- Cache the standard `NormedAddCommGroup (ℝ →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient3 : NormedAddCommGroup (ℝ →L[ℝ] Space) :=
    inferInstance

-- @@ L289-290 verbatim
/-- Cache the standard `NormedSpace ℝ (ℝ →L[ℝ] Space)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient4 : NormedSpace ℝ (ℝ →L[ℝ] Space) := inferInstance

-- @@ L291-292 verbatim
/-- Cache the standard `NormedAddCommGroup NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient5 : NormedAddCommGroup NormalField := inferInstance

-- @@ L293-294 verbatim
/-- Cache the standard `NormedSpace ℝ NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient6 : NormedSpace ℝ NormalField := inferInstance

-- @@ L295-298 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient7 : NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance

-- @@ L299-302 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient8 : NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance

-- @@ L303-304 verbatim
/-- Cache the standard `NormedAddCommGroup (ℝ →L[ℝ] ℝ)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient9 : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := inferInstance

-- @@ L305-306 verbatim
/-- Cache the standard `NormedSpace ℝ (ℝ →L[ℝ] ℝ)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient10 : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := inferInstance

-- @@ L307-310 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient11 : NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] ℝ) :=
    inferInstance

-- @@ L311-314 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient12 : NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] ℝ) :=
    inferInstance

-- @@ L315-318 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,NormalField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient13 : NormedAddCommGroup C(K,NormalField) :=
    inferInstance

-- @@ L319-321 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,NormalField)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient14 : NormedSpace ℝ C(K,NormalField) :=
    inferInstance

-- @@ L322-325 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient15 : NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ]
    Space) := inferInstance

-- @@ L326-329 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient16 : NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance

-- @@ L330-333 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] ℝ)` instance to shorten
typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient17 : NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] ℝ) :=
    inferInstance

-- @@ L334-337 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient18 : NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] ℝ) :=
    inferInstance

-- @@ L338-341 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient19 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L342-345 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient20 : NormedSpace ℝ (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L346-349 verbatim
/-- Cache the standard `NormedAddCommGroup PotentialField` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient21 : NormedAddCommGroup PotentialField :=
    inferInstance

-- @@ L350-351 verbatim
/-- Cache the standard `NormedSpace ℝ PotentialField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient22 : NormedSpace ℝ PotentialField := inferInstance

-- @@ L352-355 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient23 : NormedAddCommGroup C(K,PotentialField) :=
    inferInstance

-- @@ L356-359 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient24 : NormedSpace ℝ C(K,PotentialField) :=
    inferInstance


-- @@ L361-368 verbatim
/-- Time normal path, constructed using `pathCompositionMap`. -/
def timeNormalPath (N : C(K, NormalField)) (Q₁ : C(K, Space →ᵇ ℝ →L[ℝ] Space)) : C(K,NormalField) :=
  pathCompositionMap (E := ℝ) (F := ℝ) (U := Space)
    (pathCompositionMap (E := Space) (F := ℝ) (U := ℝ)
      N (pathAdjointMap (U := Space) (E := ℝ) N))
    (pathAdjointMap (U := ℝ) (E := Space) Q₁) -
      (2 : ℝ) • pathCompositionMap (E := ℝ) (F := ℝ) (U := Space)
        (pathCompositionMap (E := Space) (F := ℝ) (U := ℝ) N Q₁) N


-- @@ L370-371 verbatim
theorem timeNormalPath_apply (N : C(K, NormalField)) (Q₁ : C(K, Space →ᵇ ℝ →L[ℝ] Space))
    (t : K) (y : Space) : timeNormalPath N Q₁ t y = normalTimeMap (N t y) (Q₁ t y) := rfl


-- @@ L373-380 verbatim
theorem timeNormalPath_translation (N : C(K, NormalField)) (Q₁ : C(K, Space →ᵇ ℝ →L[ℝ] Space))
    (a : Space) : translateCoefficientPath (timeNormalPath N Q₁) a =
      timeNormalPath (translateCoefficientPath N a) (translateCoefficientPath Q₁ a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl


-- @@ L382-382 verbatim
section Families


-- @@ L384-386 verbatim
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (N : X → C(K, NormalField)) (Q₁ : X → C(K, Space →ᵇ ℝ →L[ℝ] Space))
  (hN : ContDiff ℝ ∞ N) (hQ₁ : ContDiff ℝ ∞ Q₁)


-- @@ L388-401 verbatim
include hN hQ₁ in
theorem timeNormalPath_contDiff : ContDiff ℝ ∞ (fun a => timeNormalPath (N a) (Q₁ a)) := by
  have hNa := (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ)).contDiff.comp hN
  have hQa := (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space)).contDiff.comp hQ₁
  have hNN := pathComposition_contDiff N
    (fun x => pathAdjointMap (U := Space) (E := ℝ) (N x)) hN hNa
  have hNQ := pathComposition_contDiff N Q₁ hN hQ₁
  have hA := pathComposition_contDiff (E := ℝ) (F := ℝ) (U := Space)
    (fun x => pathCompositionMap (E := Space) (F := ℝ) (U := ℝ)
      (N x) (pathAdjointMap (U := Space) (E := ℝ) (N x)))
    (fun x => pathAdjointMap (U := ℝ) (E := Space) (Q₁ x)) hNN hQa
  have hB := pathComposition_contDiff (E := ℝ) (F := ℝ) (U := Space)
    (fun x => pathCompositionMap (E := Space) (F := ℝ) (U := ℝ) (N x) (Q₁ x)) N hNQ hN
  exact hA.sub (hB.const_smul (2 : ℝ))


-- @@ L403-445 verbatim
include hN hQ₁ in
theorem timeNormalPath_bound (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n N a‖ ≤ C * majorant R 0 n)
    (hbQ₁ : ∀ n a, ‖iteratedFDeriv ℝ n Q₁ a‖ ≤ D * majorant R 0 n)
    (n : ℕ) (a : X) :
    ‖iteratedFDeriv ℝ n (fun x => timeNormalPath (N x) (Q₁ x)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  let A : X → C(K,NormalField) := fun x =>
    pathCompositionMap (E := ℝ) (F := ℝ) (U := Space)
      (pathCompositionMap (E := Space) (F := ℝ) (U := ℝ)
        (N x) (pathAdjointMap (U := Space) (E := ℝ) (N x)))
      (pathAdjointMap (U := ℝ) (E := Space) (Q₁ x))
  let B : X → C(K,NormalField) := fun x =>
    pathCompositionMap (E := ℝ) (F := ℝ) (U := Space)
      (pathCompositionMap (E := Space) (F := ℝ) (U := ℝ) (N x) (Q₁ x)) (N x)
  have hNa := (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ)).contDiff.comp hN
  have hQa := (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space)).contDiff.comp hQ₁
  have hNN := pathComposition_contDiff N
    (fun x => pathAdjointMap (U := Space) (E := ℝ) (N x)) hN hNa
  have hNQ := pathComposition_contDiff N Q₁ hN hQ₁
  have hA : ContDiff ℝ ∞ A := pathComposition_contDiff _ _ hNN hQa
  have hB : ContDiff ℝ ∞ B := pathComposition_contDiff _ _ hNQ hN
  have hbNa := contraction_bound (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ))
    pathAdjointMap_norm N hN R C hR hC 0 hbN
  have hbQa := contraction_bound (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space))
    pathAdjointMap_norm Q₁ hQ₁ R D hR hD 0 hbQ₁
  have hbNN := pathComposition_bound N (fun x => pathAdjointMap (U := Space) (E := ℝ) (N x)) hN hNa
    R C C hR hC hC 0 0 hbN hbNa
  have hbNQ := pathComposition_bound N Q₁ hN hQ₁ R C D hR hC hD 0 0 hbN hbQ₁
  have hbA : ∀ j x, ‖iteratedFDeriv ℝ j A x‖ ≤ (3*(3*C*C)*D)*majorant R 0 j :=
    pathComposition_bound _ _ hNN hQa R (3*C*C) D hR (by positivity) hD 0 0 hbNN hbQa
  have hbB : ∀ j x, ‖iteratedFDeriv ℝ j B x‖ ≤ (3*(3*C*D)*C)*majorant R 0 j :=
    pathComposition_bound _ _ hNQ hN R (3*C*D) C hR (by positivity) hC 0 0 hbNQ hbN
  have hb₂B (j : ℕ) (x : X) :
      ‖iteratedFDeriv ℝ j (fun y => (2 : ℝ) • B y) x‖ ≤
        (2*(3*(3*C*D)*C))*majorant R 0 j := by
    rw [iteratedFDeriv_const_smul_apply' (a := (2 : ℝ))
      (hB.contDiffAt.of_le (by simp)), norm_smul]
    norm_num only [Real.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (hbB j x) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have h := sub_bound A (fun y => (2 : ℝ) • B y) hA (hB.const_smul (2 : ℝ))
    R (3*(3*C*C)*D) (2*(3*(3*C*D)*C)) 0 hbA hb₂B n a
  exact h.trans_eq (by ring)


-- @@ L447-447 verbatim
end Families


-- @@ L449-450 verbatim
variable (m m₁ : SmoothCoefficientPath K Space) (c : ℝ) (hc : 0 < c)
  (hm : ∀ t y, c ≤ ‖m.field t y‖ ^ 2)


-- @@ L452-455 verbatim
/-- Potential time coefficient, given by `potentialPathMap (timeNormalPath (normalFunctional m c
hc hm) (normalColumn m₁).field)`. -/
def potentialTimeCoefficient : C(K,PotentialField) :=
  potentialPathMap (timeNormalPath (normalFunctional m c hc hm) (normalColumn m₁).field)


-- @@ L457-466 verbatim
theorem potentialTimeCoefficient_apply (t : K) (y : Space) :
    potentialTimeCoefficient m m₁ c hc hm t y =
      potentialMultiplierDerivative (m.field t y) (m₁.field t y) := by
  have hn : m.field t y ≠ 0 := by
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  exact normalTimeMap_potential (m.field t y) (m₁.field t y)
    (normalFunctional m c hc hm t y) hn (normalFunctional_apply m c hc hm t y)


-- @@ L468-478 verbatim
theorem potentialTimeCoefficient_translation :
    translateCoefficientPath (potentialTimeCoefficient m m₁ c hc hm) =
      fun a => potentialPathMap (timeNormalPath
        (translateCoefficientPath (normalFunctional m c hc hm) a)
        (translateCoefficientPath (normalColumn m₁).field a)) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl


-- @@ L480-485 verbatim
theorem potentialTimeCoefficient_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (potentialTimeCoefficient m m₁ c hc hm)) := by
  rw [potentialTimeCoefficient_translation]
  have h := timeNormalPath_contDiff _ _
    (normalFunctional_translation_contDiff m c hc hm) (normalColumn m₁).translation_contDiff
  exact (potentialPathMap (K := K)).contDiff.comp h


-- @@ L487-512 verbatim
/-- The derivative coefficient is polynomial in the already constructed normal functional. -/
theorem potentialTimeCoefficient_translation_bound (R C D : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath (normalFunctional m c hc hm)) a‖ ≤
      C * majorant R 0 n)
    (hbm₁ : ∀ n t y, ‖iteratedFDeriv ℝ n (m₁.field t : Space → Space) y‖ ≤ D * majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (potentialTimeCoefficient m m₁ c hc hm)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  have hQ (j : ℕ) (x : Space) :
      ‖iteratedFDeriv ℝ j (translateCoefficientPath (normalColumn m₁).field) x‖ ≤ D*majorant R 0 j
          := by
    apply (normalColumn m₁).norm_iteratedFDeriv_translation_le j (D*majorant R 0 j)
      (mul_nonneg hD (majorant_nonneg R hR 0 j))
    intro t y
    exact SmoothCoefficientPath.map_derivative_bound
      (ContinuousLinearMap.toSpanSingletonLIE ℝ Space).toLinearIsometry.toContinuousLinearMap
      (ContinuousLinearMap.toSpanSingletonLIE ℝ
          Space).toLinearIsometry.norm_toContinuousLinearMap_le
      m₁ j (D*majorant R 0 j) (hbm₁ j) t y
  rw [potentialTimeCoefficient_translation]
  exact contraction_bound (potentialPathMap (K := K)) potentialPathMap_norm _
    (timeNormalPath_contDiff _ _ (normalFunctional_translation_contDiff m c hc hm)
      (normalColumn m₁).translation_contDiff) R (27*C^2*D) hR (by positivity) 0
    (timeNormalPath_bound _ _ (normalFunctional_translation_contDiff m c hc hm)
      (normalColumn m₁).translation_contDiff R C D hR hC hD hbN hQ) n a


-- @@ L514-514 verbatim
end EulerSourcePotentialCoefficient


-- @@ L516-516 verbatim
end

-- @@ L517-517 verbatim
end


-- @@ L519-519 verbatim
end


-- @@ L521-521 verbatim
section


-- @@ L523-524 verbatim
/-! The potential time coefficient from an actual continuous, translation-smooth normal derivative
path. -/


-- @@ L526-526 verbatim
@[expose] public section


-- @@ L528-528 verbatim
noncomputable section


-- @@ L530-530 verbatim
namespace EulerSourcePotentialCoefficient


-- @@ L532-533 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerSourceNormalCoefficient
  EulerPacketCrossProduct EulerOperatorGevreyCalculus EulerGevrey EulerVolterraConvolution

-- @@ L534-534 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L536-536 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L538-542 verbatim
/-- Column path, given by `mapCoefficientPath (ContinuousLinearMap.toSpanSingletonLIE ℝ
Space).toLinearIsometry.toContinuousLinearMap`. -/
def columnPath : C(K,Space →ᵇ Space) →L[ℝ] C(K,Space →ᵇ ℝ →L[ℝ] Space) :=
  mapCoefficientPath (ContinuousLinearMap.toSpanSingletonLIE ℝ
      Space).toLinearIsometry.toContinuousLinearMap


-- @@ L544-554 verbatim
theorem columnPath_norm : ‖columnPath (K := K)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).mpr
  intro y
  change ‖(ContinuousLinearMap.toSpanSingletonLIE ℝ Space) (A t y)‖ ≤ ‖A‖
  rw [LinearIsometryEquiv.norm_map]
  exact ((A t).norm_coe_le_norm y).trans (A.norm_coe_le_norm t)


-- @@ L556-563 verbatim
omit [CompactSpace K] in
theorem columnPath_translation (A : C(K, Space →ᵇ Space)) (a : Space) :
    translateCoefficientPath (columnPath A) a = columnPath (translateCoefficientPath A a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl


-- @@ L565-565 verbatim
section Coefficient


-- @@ L567-568 verbatim
variable (m : SmoothCoefficientPath K Space) (m₁ : C(K, Space →ᵇ Space))
  (c : ℝ) (hc : 0 < c) (hm : ∀ t y, c ≤ ‖m.field t y‖ ^ 2)


-- @@ L570-573 verbatim
/-- Potential time path, given by `potentialPathMap (timeNormalPath (normalFunctional m c hc hm)
(columnPath m₁))`. -/
def potentialTimePath : C(K,PotentialField) :=
  potentialPathMap (timeNormalPath (normalFunctional m c hc hm) (columnPath m₁))


-- @@ L575-583 verbatim
theorem potentialTimePath_apply (t : K) (y : Space) :
    potentialTimePath m m₁ c hc hm t y = potentialMultiplierDerivative (m.field t y) (m₁ t y) := by
  have hn : m.field t y ≠ 0 := by
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  exact normalTimeMap_potential (m.field t y) (m₁ t y)
    (normalFunctional m c hc hm t y) hn (normalFunctional_apply m c hc hm t y)


-- @@ L585-594 verbatim
theorem potentialTimePath_translation :
    translateCoefficientPath (potentialTimePath m m₁ c hc hm) = fun a =>
      potentialPathMap (timeNormalPath (translateCoefficientPath (normalFunctional m c hc hm) a)
        (columnPath (translateCoefficientPath m₁ a))) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl


-- @@ L596-601 verbatim
theorem potentialTimePath_orbit (h₁ : ContDiff ℝ ∞ (translateCoefficientPath m₁)) :
    ContDiff ℝ ∞ (translateCoefficientPath (potentialTimePath m m₁ c hc hm)) := by
  rw [potentialTimePath_translation]
  have hcol := (columnPath (K := K)).contDiff.comp h₁
  have h := timeNormalPath_contDiff _ _ (normalFunctional_translation_contDiff m c hc hm) hcol
  exact (potentialPathMap (K := K)).contDiff.comp h


-- @@ L603-619 verbatim
theorem potentialTimePath_bound (h₁ : ContDiff ℝ ∞ (translateCoefficientPath m₁))
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath (normalFunctional m c hc hm)) a‖ ≤
      C * majorant R 0 n)
    (hb₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath m₁) a‖ ≤ D * majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (potentialTimePath m m₁ c hc hm)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  rw [potentialTimePath_translation]
  have hcol := (columnPath (K := K)).contDiff.comp h₁
  have hbcol := contraction_bound (columnPath (K := K)) columnPath_norm
    (translateCoefficientPath m₁) h₁ R D hR hD 0 hb₁
  have h := timeNormalPath_contDiff _ _ (normalFunctional_translation_contDiff m c hc hm) hcol
  exact contraction_bound (potentialPathMap (K := K)) potentialPathMap_norm _ h
    R (27*C^2*D) hR (by positivity) 0
    (timeNormalPath_bound _ _ (normalFunctional_translation_contDiff m c hc hm)
      hcol R C D hR hC hD hbN hbcol) n a


-- @@ L621-621 verbatim
end Coefficient


-- @@ L623-623 verbatim
section Time


-- @@ L625-630 verbatim
variable (T : ℝ) (hT : 0 ≤ T) (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (m₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space))
  (c : ℝ) (hc : 0 < c) (hm : ∀ t y, c ≤ ‖m.field t y‖ ^ 2)
  (hmt : ∀ t ∈ Icc (0 : ℝ) T, ∀ y : Space,
    HasDerivWithinAt (fun r => extendPath T hT m.field r y)
      (extendPath T hT m₁ t y) (Icc (0 : ℝ) T) t)


-- @@ L632-651 verbatim
include hmt in
theorem potentialTimePath_hasDerivWithinAt (t : Icc (0 : ℝ) T) (y : Space) :
    HasDerivWithinAt (fun r => extendPath T hT (potentialCoefficient m c hc hm) r y)
      (potentialTimePath m m₁ c hc hm t y) (Icc (0 : ℝ) T) t := by
  have hn : extendPath T hT m.field t y ≠ 0 := by
    change m.field (projIcc 0 T hT t) y ≠ 0
    rw [projIcc_of_mem hT t.property]
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  have h := potentialMultiplier_hasDerivWithinAt (Icc (0 : ℝ) T) t
    (fun r => extendPath T hT m.field r y) (extendPath T hT m₁ t y) (hmt t t.property y) hn
  convert h using 1 <;> try rfl
  · funext r
    exact potentialCoefficient_apply m c hc hm (projIcc 0 T hT r) y
  · rw [potentialTimePath_apply]
    change potentialMultiplierDerivative (m.field t y) (m₁ t y) =
      potentialMultiplierDerivative (m.field (projIcc 0 T hT t) y) (m₁ (projIcc 0 T hT t) y)
    rw [projIcc_of_mem hT t.property]


-- @@ L653-653 verbatim
end Time

-- @@ L654-654 verbatim
end EulerSourcePotentialCoefficient


-- @@ L656-656 verbatim
end

-- @@ L657-657 verbatim
end


-- @@ L659-659 verbatim
end


-- @@ L661-661 verbatim
section


-- @@ L663-663 verbatim
/-! Genuine time derivatives of the inverse deformation and its transported normal. -/


-- @@ L665-665 verbatim
@[expose] public section


-- @@ L667-667 verbatim
noncomputable section


-- @@ L669-669 verbatim
namespace EulerDeformationTime


-- @@ L671-671 verbatim
open Set ContinuousLinearMap EulerSmoothLimit


-- @@ L673-675 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instDeformationTimeInverse1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance

-- @@ L676-678 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instDeformationTimeInverse2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance


-- @@ L680-687 verbatim
/-- Inverse unit, bundling `val`, `inv`, `val_inv`, `inv_val`. -/
def inverseUnit (F G : Space →L[ℝ] Space)
    (hFG : F.comp G = ContinuousLinearMap.id ℝ Space)
    (hGF : G.comp F = ContinuousLinearMap.id ℝ Space) : (Space →L[ℝ] Space)ˣ where
  val := F
  inv := G
  val_inv := hFG
  inv_val := hGF


-- @@ L689-700 verbatim
theorem inverse_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (F G : ℝ → Space →L[ℝ] Space) (F₁ : Space →L[ℝ] Space)
    (hFG : ∀ r ∈ s, (F r).comp (G r) = ContinuousLinearMap.id ℝ Space)
    (hGF : ∀ r ∈ s, (G r).comp (F r) = ContinuousLinearMap.id ℝ Space)
    (hF : HasDerivWithinAt F F₁ s t) :
    HasDerivWithinAt G (-((G t).comp (F₁.comp (G t)))) s t := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ)
    (inverseUnit (F t) (G t) (hFG t ht) (hGF t ht))).comp_hasDerivWithinAt t hF
  change HasDerivWithinAt (fun r => Ring.inverse (F r)) (-((G t).comp (F₁.comp (G t)))) s t at h
  apply h.congr_of_mem _ ht
  intro r hr
  exact (Ring.inverse_unit (inverseUnit (F r) (G r) (hFG r hr) (hGF r hr))).symm


-- @@ L702-710 verbatim
/-- F_t=MF implies (F⁻¹)_t=−F⁻¹M on the same closed time set. -/
theorem inverse_strain_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (F G : ℝ → Space →L[ℝ] Space) (M : Space →L[ℝ] Space)
    (hFG : ∀ r ∈ s, (F r).comp (G r) = ContinuousLinearMap.id ℝ Space)
    (hGF : ∀ r ∈ s, (G r).comp (F r) = ContinuousLinearMap.id ℝ Space)
    (hF : HasDerivWithinAt F (M.comp (F t)) s t) :
    HasDerivWithinAt G (-((G t).comp M)) s t := by
  have h := inverse_hasDerivWithinAt s t ht F G (M.comp (F t)) hFG hGF hF
  rwa [ContinuousLinearMap.comp_assoc M (F t) (G t), hFG t ht, ContinuousLinearMap.comp_id] at h


-- @@ L712-716 verbatim
/-- Adjoint vector as an element of `(Space →L[ℝ] Space) →L[ℝ] Space`. -/
def adjointVector (m₀ : Space) : (Space →L[ℝ] Space) →L[ℝ] Space :=
  (ContinuousLinearMap.apply ℝ Space m₀).comp
    (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
      : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space))


-- @@ L718-729 verbatim
/-- The actual transported normal satisfies m_t=−M* m. -/
theorem normal_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (F G : ℝ → Space →L[ℝ] Space) (M : Space →L[ℝ] Space) (m₀ : Space)
    (hFG : ∀ r ∈ s, (F r).comp (G r) = ContinuousLinearMap.id ℝ Space)
    (hGF : ∀ r ∈ s, (G r).comp (F r) = ContinuousLinearMap.id ℝ Space)
    (hF : HasDerivWithinAt F (M.comp (F t)) s t) :
    HasDerivWithinAt (fun r => (G r).adjoint m₀) (-(M.adjoint ((G t).adjoint m₀))) s t := by
  have h := (adjointVector m₀).hasFDerivAt.comp_hasDerivWithinAt t
    (inverse_strain_hasDerivWithinAt s t ht F G M hFG hGF hF)
  convert h using 1 <;> try rfl
  change -(M.adjoint ((G t).adjoint m₀)) = (-((G t).comp M)).adjoint m₀
  simp only [map_neg, adjoint_comp, neg_apply, comp_apply]


-- @@ L731-731 verbatim
end EulerDeformationTime


-- @@ L733-733 verbatim
end

-- @@ L734-734 verbatim
end


-- @@ L736-736 verbatim
end


-- @@ L738-738 verbatim
@[expose] public section


-- @@ L740-740 verbatim
noncomputable section


-- @@ L742-742 verbatim
namespace EulerTransversePacketProvider.Data


-- @@ L744-746 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseBoundedFrame EulerBoundedFieldCalculus EulerOperatorGevreyCalculus
  EulerGevrey EulerSourcePotentialCoefficient EulerVolterraConvolution

-- @@ L747-747 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L749-749 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)


-- @@ L751-754 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketTimeData1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L755-757 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketTimeData2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

-- @@ L758-761 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketTimeData3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

-- @@ L762-765 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketTimeData4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

-- @@ L766-770 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ] Space)`
instance to shorten typeclass synthesis. -/
local instance instTransversePacketTimeData5 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space
    →L[ℝ] Space) :=
    inferInstance

-- @@ L771-775 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ] Space)` instance to
shorten typeclass synthesis. -/
local instance instTransversePacketTimeData6 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ]
    Space) :=
    inferInstance

-- @@ L776-778 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketTimeData7 : NormedAddCommGroup (Space →ᵇ Space) := inferInstance

-- @@ L779-780 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketTimeData8 : NormedSpace ℝ (Space →ᵇ Space) := inferInstance

-- @@ L781-784 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space)` instance to
shorten typeclass synthesis. -/
local instance instTransversePacketTimeData9 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space)
    := inferInstance

-- @@ L785-788 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketTimeData10 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space) :=
    inferInstance


-- @@ L790-793 verbatim
/-- The derivative of the inverse is constructed from the original fields. -/
def inverseDerivative : C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ] Space) :=
  -pathCompositionMap (α := Space) (K := Icc (0 : ℝ) D.T)
    (E := Space) (F := Space) (U := Space) D.FInv.field D.M.field


-- @@ L795-797 verbatim
/-- The derivative of the transported normal is the fixed adjoint-vector map of that path. -/
def normalDerivative : C(Icc (0 : ℝ) D.T,Space →ᵇ Space) :=
  mapCoefficientPath (normalMap D.m₀) D.inverseDerivative


-- @@ L799-800 verbatim
@[simp] theorem inverseDerivative_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.inverseDerivative t x = -((D.FInv.field t x).comp (D.M.field t x)) := rfl


-- @@ L802-806 verbatim
@[simp] theorem normalDerivative_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.normalDerivative t x = -((D.M.field t x).adjoint (D.normal.field t x)) := by
  change (-((D.FInv.field t x).comp (D.M.field t x))).adjoint D.m₀ =
    -((D.M.field t x).adjoint ((D.FInv.field t x).adjoint D.m₀))
  simp only [map_neg, adjoint_comp, neg_apply, comp_apply]


-- @@ L808-836 verbatim
/-- No differentiability of F⁻¹ is assumed: it follows from the actual inverse identities and
F_t=MF. -/
theorem inverse_hasDerivWithinAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le D.FInv.field r x)
      (extendPath D.T D.T_pos.le D.inverseDerivative t x) (Icc (0 : ℝ) D.T) t := by
  have hFG (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) D.T) :
      (extendPath D.T D.T_pos.le D.F.field r x).comp
        (extendPath D.T D.T_pos.le D.FInv.field r x) = ContinuousLinearMap.id ℝ Space := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.inverse_right (projIcc 0 D.T D.T_pos.le r) x v
  have hGF (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) D.T) :
      (extendPath D.T D.T_pos.le D.FInv.field r x).comp
        (extendPath D.T D.T_pos.le D.F.field r x) = ContinuousLinearMap.id ℝ Space := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.inverse_left (projIcc 0 D.T D.T_pos.le r) x v
  have hF₁ : extendPath D.T D.T_pos.le D.F₁.field t x =
      (extendPath D.T D.T_pos.le D.M.field t x).comp
        (extendPath D.T D.T_pos.le D.F.field t x) := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.strain_equation (projIcc 0 D.T D.T_pos.le t) x v
  have hF := D.frame_time t ht x
  rw [hF₁] at hF
  exact EulerDeformationTime.inverse_strain_hasDerivWithinAt (Icc (0 : ℝ) D.T) t ht
    (fun r => extendPath D.T D.T_pos.le D.F.field r x)
    (fun r => extendPath D.T D.T_pos.le D.FInv.field r x)
    (extendPath D.T D.T_pos.le D.M.field t x) hFG hGF hF


-- @@ L838-842 verbatim
theorem normal_hasDerivWithinAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le D.normal.field r x)
      (extendPath D.T D.T_pos.le D.normalDerivative t x) (Icc (0 : ℝ) D.T) t := by
  exact (normalMap D.m₀).hasFDerivAt.comp_hasDerivWithinAt t
    (D.inverse_hasDerivWithinAt t ht x)


-- @@ L844-854 verbatim
theorem inverseDerivative_translation :
    translateCoefficientPath D.inverseDerivative = fun a =>
      -pathCompositionMap (α := Space) (K := Icc (0 : ℝ) D.T)
        (E := Space) (F := Space) (U := Space) (translateCoefficientPath D.FInv.field a)
        (translateCoefficientPath D.M.field a) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl


-- @@ L856-864 verbatim
theorem normalDerivative_translation :
    translateCoefficientPath D.normalDerivative = fun a =>
      mapCoefficientPath (normalMap D.m₀) (translateCoefficientPath D.inverseDerivative a) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl


-- @@ L866-868 verbatim
theorem inverseDerivative_orbit : ContDiff ℝ ∞ (translateCoefficientPath D.inverseDerivative) := by
  rw [D.inverseDerivative_translation]
  exact (pathComposition_contDiff _ _ D.FInv.translation_contDiff D.M.translation_contDiff).neg


-- @@ L870-873 verbatim
theorem normalDerivative_orbit : ContDiff ℝ ∞ (translateCoefficientPath D.normalDerivative) := by
  rw [D.normalDerivative_translation]
  exact (mapCoefficientPath (K := Icc (0 : ℝ) D.T) (normalMap D.m₀)).contDiff.comp
    D.inverseDerivative_orbit


-- @@ L875-888 verbatim
theorem normalPathMap_norm :
    ‖mapCoefficientPath (K := Icc (0 : ℝ) D.T) (normalMap D.m₀)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).mpr
  intro x
  change ‖normalMap D.m₀ (A t x)‖ ≤ ‖A‖
  calc
    _ ≤ ‖normalMap D.m₀‖ * ‖A t x‖ := (normalMap D.m₀).le_opNorm _
    _ ≤ 1 * ‖A t x‖ := mul_le_mul_of_nonneg_right (normalMap_norm D.m₀ D.m₀_unit) (norm_nonneg _)
    _ ≤ ‖A‖ := by simpa only [one_mul] using ((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)


-- @@ L890-900 verbatim
theorem inverseDerivative_bound (R CI CM : ℝ) (hR : 0 ≤ R) (hCI : 0 ≤ CI) (hCM : 0 ≤ CM)
    (hI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ CI * majorant R 0
        n)
    (hM : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.M.field) a‖ ≤ CM * majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤ (3*CI*CM)*majorant R 0
        n := by
  rw [D.inverseDerivative_translation]
  exact neg_bound _ R (3*CI*CM) 0
    (pathComposition_bound _ _ D.FInv.translation_contDiff D.M.translation_contDiff
      R CI CM hR hCI hCM 0 0 hI hM) n a


-- @@ L902-912 verbatim
theorem normalDerivative_bound (R CI CM : ℝ) (hR : 0 ≤ R) (hCI : 0 ≤ CI) (hCM : 0 ≤ CM)
    (hI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ CI * majorant R 0
        n)
    (hM : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.M.field) a‖ ≤ CM * majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath D.normalDerivative) a‖ ≤ (3*CI*CM)*majorant R 0 n
        := by
  rw [D.normalDerivative_translation]
  exact contraction_bound (mapCoefficientPath (K := Icc (0 : ℝ) D.T) (normalMap D.m₀))
    D.normalPathMap_norm _ D.inverseDerivative_orbit R (3*CI*CM) hR (by positivity) 0
    (D.inverseDerivative_bound R CI CM hR hCI hCM hI hM) n a


-- @@ L914-916 verbatim
/-- The actual time coefficient for the periodic-potential multiplier. -/
def potentialDerivative : C(Icc (0 : ℝ) D.T,PotentialField) :=
  potentialTimePath D.normal D.normalDerivative D.normalLower D.normalLower_pos D.normal_lower


-- @@ L918-920 verbatim
theorem potentialDerivative_orbit : ContDiff ℝ ∞ (translateCoefficientPath D.potentialDerivative) :=
  potentialTimePath_orbit D.normal D.normalDerivative D.normalLower D.normalLower_pos D.normal_lower
    D.normalDerivative_orbit


-- @@ L922-928 verbatim
theorem potential_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le
      (potentialCoefficient D.normal D.normalLower D.normalLower_pos D.normal_lower) r x)
      (D.potentialDerivative t x) (Icc (0 : ℝ) D.T) t := by
  convert potentialTimePath_hasDerivWithinAt D.T D.T_pos.le D.normal D.normalDerivative
    D.normalLower D.normalLower_pos D.normal_lower D.normal_hasDerivWithinAt t x using 1
  dsimp only [potentialDerivative]


-- @@ L930-930 verbatim
end EulerTransversePacketProvider.Data
