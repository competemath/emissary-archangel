import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-10 verbatim
/-!
The final claim constructs the tracial quotients and states the original gamma assertion.
`Analysis.TracialSplitting.Challenge.main_iff_original` verifies statement preservation.
-/


-- @@ L12-12 verbatim
universe uA uD uE uI uR uX u v


-- @@ L14-14 verbatim
namespace Pureness


-- @@ L16-16 verbatim
open scoped ComplexOrder


-- @@ L18-20 verbatim
structure CStarAlgebraNorm (R : Type uR) [Ring R] [StarRing R] [Algebra ℂ R]
    extends AlgebraNorm ℂ R where
  cstar : ∀ x, toAlgebraNorm (star x * x) = toAlgebraNorm x * toAlgebraNorm x


-- @@ L22-25 verbatim
structure TracialState (A : Type uA) [CStarAlgebra A] [PartialOrder A] where
  functional : A →ₚ[ℂ] ℂ
  normalized : functional 1 = 1
  tracial : ∀ a b : A, functional (a * b) = functional (b * a)


-- @@ L27-30 verbatim
structure ClosedStarIdeal (D : Type uD) [CStarAlgebra D] where
  ideal : TwoSidedIdeal D
  star_mem : ∀ {u : D}, u ∈ ideal → star u ∈ ideal
  isClosed : IsClosed (ideal : Set D)


-- @@ L32-32 verbatim
end Pureness


-- @@ L34-34 verbatim
universe uNuclear


-- @@ L36-36 verbatim
namespace ComparatorModel


-- @@ L38-38 verbatim
section


-- @@ L40-40 verbatim
namespace Pureness


-- @@ L42-42 verbatim
open scoped TensorProduct ComplexOrder


-- @@ L44-44 verbatim
abbrev CStarAlgebraNorm := @_root_.OAI.Pureness.CStarAlgebraNorm


-- @@ L46-47 verbatim
def IsNuclear (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (B : Type v) [CStarAlgebra B], Subsingleton (CStarAlgebraNorm (A ⊗[ℂ] B))


-- @@ L49-49 verbatim
abbrev TracialState := @_root_.OAI.Pureness.TracialState


-- @@ L51-51 verbatim
end Pureness


-- @@ L53-53 verbatim
namespace CurrentMain


-- @@ L55-55 verbatim
open _root_.OAI.ComparatorModel.Pureness


-- @@ L57-57 verbatim
open scoped ComplexOrder


-- @@ L59-61 verbatim
def RealRankZero (D : Type) [CStarAlgebra D] : Prop :=
  ∀ a : D, IsSelfAdjoint a → ∀ ε : ℝ, 0 < ε →
    ∃ b : D, IsSelfAdjoint b ∧ (spectrum ℂ b).Finite ∧ ‖a - b‖ < ε


-- @@ L63-65 verbatim
def traceTwoNorm {D : Type} [CStarAlgebra D] [PartialOrder D]
    (τ : TracialState D) (a : D) : ℝ :=
  Real.sqrt (τ.functional (star a * a)).re


-- @@ L67-67 verbatim
end CurrentMain


-- @@ L69-69 verbatim
namespace Pureness


-- @@ L71-71 verbatim
open Filter


-- @@ L73-73 verbatim
open scoped Topology NNReal ENNReal


-- @@ L75-75 verbatim
abbrev ClosedStarIdeal := @_root_.OAI.Pureness.ClosedStarIdeal


-- @@ L77-77 verbatim
namespace ClosedStarIdeal


-- @@ L79-79 verbatim
variable {D : Type} [CStarAlgebra D] (J : ClosedStarIdeal D)


-- @@ L81-81 verbatim
abbrev Quotient := J.ideal.ringCon.Quotient


-- @@ L83-83 verbatim
def quotientMap : D →ₐ[ℂ] J.Quotient := J.ideal.ringCon.mkₐ ℂ


-- @@ L85-91 verbatim
instance quotientStar : Star (J.Quotient) where
  star := Quotient.map' star (by
    intro u v h
    change J.ideal.ringCon u v at h
    change J.ideal.ringCon (star u) (star v)
    rw [TwoSidedIdeal.rel_iff] at h ⊢
    simpa only [star_sub] using J.star_mem h)


-- @@ L93-96 verbatim
instance quotientStarRing : StarRing (J.Quotient) where
  star_involutive x := Quotient.inductionOn' x (fun u => congrArg J.quotientMap (star_star u))
  star_mul x y := Quotient.inductionOn₂' x y (fun u v => congrArg J.quotientMap (star_mul u v))
  star_add x y := Quotient.inductionOn₂' x y (fun u v => congrArg J.quotientMap (star_add u v))


-- @@ L98-99 verbatim
instance quotientStarModule : StarModule ℂ (J.Quotient) where
  star_smul c x := Quotient.inductionOn' x (fun u => congrArg J.quotientMap (star_smul c u))


-- @@ L101-102 verbatim
abbrev idealSubmodule : Submodule ℂ (D) :=
  (J.quotientMap).toLinearMap.ker


-- @@ L104-110 verbatim
instance idealSubmodule_closed : IsClosed (J.idealSubmodule : Set D) := by
  have he : (J.idealSubmodule : Set D) = (J.ideal : Set D) := by
    ext u
    change J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ u ∈ J.ideal
    exact Quotient.eq
  rw [he]
  exact J.isClosed


-- @@ L112-114 verbatim
def quotientLinearEquiv :
    (D ⧸ J.idealSubmodule) ≃ₗ[ℂ] J.Quotient :=
  (J.quotientMap).toLinearMap.quotKerEquivOfSurjective ((J.ideal.ringCon.mkₐ_surjective (α := ℂ)))


-- @@ L116-118 verbatim
instance quotientNormedAddCommGroup : NormedAddCommGroup (J.Quotient) :=
  NormedAddCommGroup.induced _ _ (J.quotientLinearEquiv).symm
    (J.quotientLinearEquiv).symm.injective


-- @@ L120-121 verbatim
instance quotientNormedSpace : NormedSpace ℂ (J.Quotient) :=
  NormedSpace.induced ℂ _ _ (J.quotientLinearEquiv).symm


-- @@ L123-126 verbatim
def quotientNormEquiv : J.Quotient ≃ₗᵢ[ℂ]
    (D ⧸ J.idealSubmodule) where
  __ := (J.quotientLinearEquiv).symm
  norm_map' _ := rfl


-- @@ L128-129 verbatim
instance quotientCompleteSpace : CompleteSpace (J.Quotient) :=
  (J.quotientNormEquiv).toIsometryEquiv.completeSpace_iff.mpr inferInstance


-- @@ L131-137 verbatim
class NormConstruction : Prop where
  mul_le : ∀ {D : Type} [CStarAlgebra D] (J : ClosedStarIdeal D) (x y : J.Quotient),
    ‖x*y‖ ≤ ‖x‖*‖y‖
  star_eq : ∀ {D : Type} [CStarAlgebra D] (J : ClosedStarIdeal D) (x : J.Quotient),
    ‖star x‖ = ‖x‖
  square_le : ∀ {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (J : ClosedStarIdeal D) (x : J.Quotient), ‖x‖ * ‖x‖ ≤ ‖star x * x‖


-- @@ L139-139 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction]


-- @@ L141-143 verbatim
instance quotientNormedRing : NormedRing (J.Quotient) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := NormConstruction.mul_le J


-- @@ L145-146 verbatim
instance quotientNormedAlgebra : NormedAlgebra ℂ (J.Quotient) where
  norm_smul_le := norm_smul_le


-- @@ L148-149 verbatim
instance quotientNormedStarGroup : NormedStarGroup (J.Quotient) where
  norm_star_le x := (NormConstruction.star_eq J x).le


-- @@ L151-151 verbatim
end ClosedStarIdeal


-- @@ L153-153 verbatim
end Pureness


-- @@ L155-155 verbatim
namespace Pureness.ClosedStarIdeal


-- @@ L157-157 verbatim
open Filter


-- @@ L159-159 verbatim
open scoped Topology NNReal ENNReal


-- @@ L161-161 verbatim
variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L163-163 verbatim
variable (J : ClosedStarIdeal D)


-- @@ L165-165 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction]


-- @@ L167-168 verbatim
instance quotientCStarAlgebra : CStarAlgebra (J.Quotient) where
  norm_mul_self_le := NormConstruction.square_le J


-- @@ L170-170 verbatim
end Pureness.ClosedStarIdeal


-- @@ L172-172 verbatim
namespace CurrentMain


-- @@ L174-174 verbatim
section


-- @@ L176-176 verbatim
open _root_.OAI.ComparatorModel.Pureness


-- @@ L178-178 verbatim
variable {D : Type} {I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L180-180 verbatim
variable (τ : I → TracialState D) [Nonempty I]


-- @@ L182-182 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction]


-- @@ L184-184 verbatim
def familyTwoNorm (a : D) : ℝ := ⨆ i, traceTwoNorm (τ i) a


-- @@ L186-186 verbatim
end


-- @@ L188-188 verbatim
open _root_.OAI.ComparatorModel.Pureness Filter


-- @@ L190-190 verbatim
open scoped Topology NNReal ENNReal


-- @@ L192-192 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction]


-- @@ L194-195 verbatim
instance boundedFamilyProductCStar {X : Type} {D : Type} [CStarAlgebra D] [Nontrivial D] :
    CStarAlgebra (lp (fun _ : X => D) ∞) where


-- @@ L197-197 verbatim
section UniformNull


-- @@ L199-199 verbatim
variable {D : Type} {I : Type} {X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L201-201 verbatim
variable (τ : I → TracialState D) [Nonempty I]


-- @@ L203-204 verbatim
def IsFamilyNull (F : Filter X) (u : X → D) : Prop :=
  Tendsto (fun n => familyTwoNorm τ (u n)) F (𝓝 0)


-- @@ L206-223 verbatim
class NullConstruction : Prop where
  zero : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    (F : Filter X), IsFamilyNull τ F (fun _ => 0)
  add : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u v : X → D}, IsFamilyNull τ F u → IsFamilyNull τ F v →
    IsFamilyNull τ F (fun n => u n + v n)
  neg : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u : X → D}, IsFamilyNull τ F u → IsFamilyNull τ F (fun n => -u n)
  star : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u : X → D}, IsFamilyNull τ F u → IsFamilyNull τ F (fun n => star (u n))
  mul_left : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u v : X → D}, IsFamilyNull τ F v → ∀ {M : ℝ},
    (∀ n, ‖u n‖ ≤ M) → IsFamilyNull τ F (fun n => u n * v n)
  mul_right : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u v : X → D}, IsFamilyNull τ F u → ∀ {M : ℝ},
    (∀ n, ‖v n‖ ≤ M) → IsFamilyNull τ F (fun n => u n * v n)
  closed : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I] (F : Filter X),
    IsClosed {u : lp (fun _ : X => D) ∞ | IsFamilyNull τ F (fun n => u n)}


-- @@ L225-225 verbatim
variable [Nontrivial D]


-- @@ L227-227 verbatim
variable [ComparatorModel.CurrentMain.NullConstruction]


-- @@ L229-237 verbatim
def familyNullTwoSided (F : Filter X) : TwoSidedIdeal (lp (fun _ : X => D) ∞) :=
  TwoSidedIdeal.mk' {u | IsFamilyNull τ F (fun n => u n)}
    (NullConstruction.zero τ F)
    (fun hu hv => NullConstruction.add τ hu hv)
    (fun hu => NullConstruction.neg τ hu)
    (fun {u _} hv => NullConstruction.mul_left τ hv
      (lp.norm_apply_le_norm ENNReal.top_ne_zero u))
    (fun {_ v} hu => NullConstruction.mul_right τ hu
      (lp.norm_apply_le_norm ENNReal.top_ne_zero v))


-- @@ L239-251 verbatim
def familyNullIdeal (F : Filter X) : ClosedStarIdeal (lp (fun _ : X => D) ∞) where
  ideal := familyNullTwoSided τ F
  star_mem := by
    intro u hu
    apply (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ (star u)).mpr
    exact NullConstruction.star τ ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u).mp hu)
  isClosed := by
    have he : (familyNullTwoSided τ F : Set (lp (fun _ : X => D) ∞)) =
        {u | IsFamilyNull τ F (fun n => u n)} := by
      ext u
      exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u
    rw [he]
    exact NullConstruction.closed τ F


-- @@ L253-253 verbatim
end UniformNull


-- @@ L255-255 verbatim
variable {D : Type} {I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L257-257 verbatim
variable (τ : I → TracialState D) [Nonempty I]


-- @@ L259-259 verbatim
variable [ComparatorModel.CurrentMain.NullConstruction]


-- @@ L261-262 verbatim
def IsFamilyCauchy (u : ℕ → D) : Prop :=
  IsFamilyNull τ (atTop : Filter (ℕ × ℕ)) (fun p => u p.1 - u p.2)


-- @@ L264-279 verbatim
class CauchyConstruction : Prop where
  const : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] (a : D), IsFamilyCauchy τ (fun _ => a)
  add : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] {u v : ℕ → D},
    IsFamilyCauchy τ u → IsFamilyCauchy τ v → IsFamilyCauchy τ (fun n => u n+v n)
  star : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] {u : ℕ → D},
    IsFamilyCauchy τ u → IsFamilyCauchy τ (fun n => star (u n))
  mul : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] {u v : ℕ → D},
    IsFamilyCauchy τ u → IsFamilyCauchy τ v → ∀ {M N : ℝ},
    (∀ n, ‖u n‖ ≤ M) → (∀ n, ‖v n‖ ≤ N) → IsFamilyCauchy τ (fun n => u n*v n)
  closed : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] [Nontrivial D],
    IsClosed {u : lp (fun _ : ℕ => D) ∞ | IsFamilyCauchy τ (fun n => u n)}


-- @@ L281-281 verbatim
variable [Nontrivial D]


-- @@ L283-283 verbatim
variable [ComparatorModel.CurrentMain.CauchyConstruction]


-- @@ L285-294 verbatim
def familyCauchyAlgebra : StarSubalgebra ℂ (lp (fun _ : ℕ => D) ∞) where
  carrier := {u | IsFamilyCauchy τ (fun n => u n)}
  zero_mem' := CauchyConstruction.const τ 0
  one_mem' := CauchyConstruction.const τ 1
  add_mem' hu hv := CauchyConstruction.add τ hu hv
  mul_mem' {u v} hu hv := CauchyConstruction.mul τ hu hv
    (lp.norm_apply_le_norm ENNReal.top_ne_zero u)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero v)
  algebraMap_mem' z := CauchyConstruction.const τ (algebraMap ℂ D z)
  star_mem' hu := CauchyConstruction.star τ hu


-- @@ L296-297 verbatim
instance familyCauchy_complete : CompleteSpace (familyCauchyAlgebra τ) :=
  (CauchyConstruction.closed τ).completeSpace_coe


-- @@ L299-299 verbatim
instance familyCauchy_cstar : CStarAlgebra (familyCauchyAlgebra τ) where


-- @@ L301-309 verbatim
def familyCauchyNullIdeal : ClosedStarIdeal (familyCauchyAlgebra τ) where
  ideal := TwoSidedIdeal.comap (familyCauchyAlgebra τ).val.toRingHom
    (familyNullIdeal τ atTop).ideal
  star_mem := by
    intro u hu
    apply (familyNullIdeal τ atTop).star_mem hu
  isClosed := by
    exact (familyNullIdeal τ atTop).isClosed.preimage
      (continuous_subtype_val : Continuous (fun u : familyCauchyAlgebra τ => u.1))


-- @@ L311-311 verbatim
abbrev UniformTracialCompletion := (familyCauchyNullIdeal τ).Quotient


-- @@ L313-313 verbatim
end CurrentMain


-- @@ L315-315 verbatim
namespace Pureness.ClosedStarIdeal


-- @@ L317-317 verbatim
open scoped ComplexOrder


-- @@ L319-319 verbatim
variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L321-321 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction]


-- @@ L323-324 verbatim
instance quotientOrder (J : ClosedStarIdeal D) : PartialOrder J.Quotient :=
  CStarAlgebra.spectralOrder _


-- @@ L326-327 verbatim
instance quotientStarOrdered (J : ClosedStarIdeal D) : StarOrderedRing J.Quotient :=
  CStarAlgebra.spectralOrderedRing _


-- @@ L329-329 verbatim
variable (J : ClosedStarIdeal D)


-- @@ L331-331 verbatim
variable (τ : TracialState D) (hτ : ∀ a ∈ J.ideal, τ.functional a = 0)


-- @@ L333-339 verbatim
def descendedValue : J.Quotient → ℂ := Quotient.lift τ.functional (by
  intro u v huv
  change J.ideal.ringCon u v at huv
  rw [TwoSidedIdeal.rel_iff] at huv
  have h := hτ (u-v) huv
  rw [map_sub, sub_eq_zero] at h
  exact h)


-- @@ L341-344 verbatim
def descendedLinear : J.Quotient →ₗ[ℂ] ℂ where
  toFun := J.descendedValue τ hτ
  map_add' x y := Quotient.inductionOn₂' x y (fun u v => τ.functional.map_add u v)
  map_smul' c x := Quotient.inductionOn' x (fun u => τ.functional.map_smul c u)


-- @@ L346-358 verbatim
def descendedTrace : TracialState J.Quotient where
  functional := { J.descendedLinear τ hτ with
    monotone' := by
      intro x y hxy
      apply sub_nonneg.mp
      change 0 ≤ J.descendedLinear τ hτ y - J.descendedLinear τ hτ x
      rw [← map_sub]
      obtain ⟨z,hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
      rw [hz]
      induction z using Quotient.inductionOn' with
      | h u => exact τ.functional.map_nonneg (star_mul_self_nonneg u) }
  normalized := τ.normalized
  tracial x y := Quotient.inductionOn₂' x y (fun u v => τ.tracial u v)


-- @@ L360-360 verbatim
end Pureness.ClosedStarIdeal


-- @@ L362-362 verbatim
namespace CurrentMain


-- @@ L364-364 verbatim
section


-- @@ L366-366 verbatim
open _root_.OAI.ComparatorModel.Pureness Filter


-- @@ L368-368 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L370-370 verbatim
section UltraTrace


-- @@ L372-372 verbatim
variable {D : Type} {X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]


-- @@ L374-374 verbatim
variable (θ : X → TracialState D) (U : Ultrafilter X)


-- @@ L376-376 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction]


-- @@ L378-379 verbatim
instance boundedFamilyProductOrder : PartialOrder (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrder _


-- @@ L381-382 verbatim
instance boundedFamilyProductStarOrdered : StarOrderedRing (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrderedRing _


-- @@ L384-385 verbatim
def ultraTraceValue (u : lp (fun _ : X => D) ∞) : ℂ :=
  limUnder (U : Filter X) (fun n => (θ n).functional (u n))


-- @@ L387-390 verbatim
class LimitConstruction : Prop where
  tendsto : ∀ {D X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (θ : X → Pureness.TracialState D) (U : Ultrafilter X) (u : lp (fun _ : X => D) ∞),
    Tendsto (fun n => (θ n).functional (u n)) (U : Filter X) (𝓝 (ultraTraceValue θ U u))


-- @@ L392-392 verbatim
variable [ComparatorModel.CurrentMain.LimitConstruction]


-- @@ L394-403 verbatim
def ultraTraceLinear : lp (fun _ : X => D) ∞ →ₗ[ℂ] ℂ where
  toFun := ultraTraceValue θ U
  map_add' u v := by
    apply tendsto_nhds_unique (LimitConstruction.tendsto θ U (u+v))
    simpa only [lp.coeFn_add, Pi.add_apply, map_add] using
      (LimitConstruction.tendsto θ U u).add (LimitConstruction.tendsto θ U v)
  map_smul' z u := by
    apply tendsto_nhds_unique (LimitConstruction.tendsto θ U (z • u))
    simpa only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul] using
      (LimitConstruction.tendsto θ U u).const_mul z


-- @@ L405-412 verbatim
def boundedFamilyEval (n : X) : lp (fun _ : X => D) ∞ →⋆ₐ[ℂ] D where
  toFun u := u n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl


-- @@ L414-432 verbatim
def ultraTrace : TracialState (lp (fun _ : X => D) ∞) where
  functional := { ultraTraceLinear θ U with
    monotone' := by
      intro u v huv
      exact le_of_tendsto_of_tendsto (LimitConstruction.tendsto θ U u)
        (LimitConstruction.tendsto θ U v) (Eventually.of_forall (fun n =>
          (θ n).functional.monotone (map_rel (boundedFamilyEval n) huv))) }
  normalized := by
    apply tendsto_nhds_unique (LimitConstruction.tendsto θ U 1)
    have he (n : X) : (θ n).functional ((1 : lp (fun _ : X => D) ∞) n) = 1 :=
      (θ n).normalized
    simp only [he]
    exact tendsto_const_nhds
  tracial u v := by
    change ultraTraceValue θ U (u*v) = ultraTraceValue θ U (v*u)
    apply tendsto_nhds_unique (LimitConstruction.tendsto θ U (u*v))
    have he (n : X) : (θ n).functional ((u*v) n) = (θ n).functional ((v*u) n) :=
      (θ n).tracial (u n) (v n)
    simpa only [he] using LimitConstruction.tendsto θ U (v*u)


-- @@ L434-434 verbatim
end UltraTrace


-- @@ L436-436 verbatim
variable {D : Type} {I : Type} {X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]


-- @@ L438-438 verbatim
variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)


-- @@ L440-440 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction]


-- @@ L442-442 verbatim
abbrev FamilyUltrapower := (familyNullIdeal τ (U : Filter X)).Quotient


-- @@ L444-448 verbatim
class TraceConstruction : Prop where
  null : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D] (τ : I → Pureness.TracialState D) [Nonempty I]
    (U : Ultrafilter X) (s : X → I) (u : lp (fun _ : X => D) ∞),
    IsFamilyNull τ (U : Filter X) (fun n => u n) →
      (ultraTrace (fun n => τ (s n)) U).functional u = 0


-- @@ L450-450 verbatim
variable [ComparatorModel.CurrentMain.TraceConstruction]


-- @@ L452-460 verbatim
def familyLimitTrace (s : X → I) : TracialState (FamilyUltrapower τ U) :=
  (familyNullIdeal τ (U : Filter X)).descendedTrace
    (ultraTrace (fun n => τ (s n)) U) (fun u hu => by
      apply TraceConstruction.null τ U s u
      have he : u ∈ familyNullTwoSided τ (U : Filter X) ↔
          IsFamilyNull τ (U : Filter X) (fun n => u n) := by
        unfold familyNullTwoSided
        exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u
      exact he.mp hu)


-- @@ L462-462 verbatim
end


-- @@ L464-464 verbatim
section


-- @@ L466-466 verbatim
open _root_.OAI.ComparatorModel.Pureness Filter


-- @@ L468-468 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L470-470 verbatim
section PullbackTrace


-- @@ L472-472 verbatim
variable {D : Type} {E : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L474-474 verbatim
variable [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]


-- @@ L476-476 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]


-- @@ L478-485 verbatim
def pullbackTrace (τ : TracialState E) (ι : D →⋆ₐ[ℂ] E) : TracialState D where
  functional := { τ.functional.toLinearMap.comp ι.toLinearMap with
    monotone' := fun _ _ h => τ.functional.monotone (map_rel ι h) }
  normalized := by change τ.functional (ι 1) = 1; rw [map_one, τ.normalized]
  tracial x y := by
    change τ.functional (ι (x*y)) = τ.functional (ι (y*x))
    rw [map_mul ι x y, map_mul ι y x]
    exact τ.tracial _ _


-- @@ L487-487 verbatim
end PullbackTrace


-- @@ L489-489 verbatim
variable {D : Type} {I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L491-491 verbatim
variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]


-- @@ L493-493 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]


-- @@ L495-496 verbatim
instance familyCauchyOrder : PartialOrder (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrder _


-- @@ L498-499 verbatim
instance familyCauchyStarOrdered : StarOrderedRing (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrderedRing _


-- @@ L501-503 verbatim
def cauchyTrace (i : I) : TracialState (familyCauchyAlgebra τ) :=
  pullbackTrace (ultraTrace (fun _ : ℕ => τ i) (Ultrafilter.of atTop))
    (familyCauchyAlgebra τ).subtype


-- @@ L505-513 verbatim
def completionTrace (i : I) : TracialState (UniformTracialCompletion τ) :=
  (familyCauchyNullIdeal τ).descendedTrace (cauchyTrace τ i) (fun u hu => by
    apply TraceConstruction.null τ (Ultrafilter.of atTop) (fun _ => i) u.1
    have he : u.1 ∈ familyNullTwoSided τ atTop ↔
        IsFamilyNull τ atTop (fun n => u.1 n) := by
      unfold familyNullTwoSided
      exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u.1
    have hn : IsFamilyNull τ atTop (fun n => u.1 n) := he.mp hu
    exact hn.mono_left (Ultrafilter.of_le atTop))


-- @@ L515-516 verbatim
def boundedFamilyConstant {X : Type} (a : D) : lp (fun _ : X => D) ∞ :=
  ⟨fun _ => a, memℓp_infty_iff.mpr ⟨‖a‖,by rintro _ ⟨n,rfl⟩; exact le_rfl⟩⟩


-- @@ L518-518 verbatim
end


-- @@ L520-520 verbatim
section


-- @@ L522-522 verbatim
open _root_.OAI.ComparatorModel.Pureness Filter


-- @@ L524-524 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L526-526 verbatim
variable {D : Type} {I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L528-528 verbatim
variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]


-- @@ L530-530 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]


-- @@ L532-538 verbatim
instance completionNontrivial : Nontrivial (UniformTracialCompletion τ) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  have he := congrArg (completionTrace τ i).functional h
  rw [(completionTrace τ i).normalized, map_zero] at he
  exact one_ne_zero he


-- @@ L540-540 verbatim
end


-- @@ L542-542 verbatim
open _root_.OAI.ComparatorModel.Pureness Filter


-- @@ L544-544 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L546-546 verbatim
variable {D : Type} {I : Type} {X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L548-548 verbatim
variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)


-- @@ L550-550 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]


-- @@ L552-561 verbatim
def familyUltrapowerMap : D →⋆ₐ[ℂ] FamilyUltrapower τ U where
  toFun a := (familyNullIdeal τ (U : Filter X)).quotientMap (boundedFamilyConstant a)
  map_zero' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_zero
  map_one' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_one
  map_add' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_add
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  map_mul' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_mul
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  commutes' z := (familyNullIdeal τ (U : Filter X)).quotientMap.commutes z
  map_star' _ := rfl


-- @@ L563-563 verbatim
end CurrentMain


-- @@ L565-565 verbatim
namespace Pureness


-- @@ L567-567 verbatim
open Filter Topology


-- @@ L569-569 verbatim
variable {A : Type uA} [NormedRing A]


-- @@ L571-571 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]


-- @@ L573-574 verbatim
def TopologicallySimple (A : Type uA) [NormedRing A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤


-- @@ L576-576 verbatim
end Pureness


-- @@ L578-578 verbatim
end


-- @@ L580-580 verbatim
namespace CurrentMain


-- @@ L582-582 verbatim
open _root_.OAI.ComparatorModel.Pureness Filter


-- @@ L584-584 verbatim
variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]


-- @@ L586-588 verbatim
def StablyFinite (A : Type uA) [CStarAlgebra A] : Prop :=
  ∀ n : ℕ, ∀ v : CStarMatrix (Fin n) (Fin n) A,
    star v*v = 1 → v*star v = 1


-- @@ L590-602 verbatim
def UniformPropertyGammaAt (A : Type) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ) : Prop :=
  ∃ p : FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U,
    IsStarProjection p ∧ ∀ x : UniformTracialCompletion (fun τ : TracialState A => τ),
      p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x =
        familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x * p ∧
      ∀ s : ℕ → TracialState A,
        (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
          (p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x) =
        (1/2 : ℂ) *
        (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
          (familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x)


-- @@ L604-612 verbatim
def Statement : Prop := ∀
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (_ : TopologicallySimple A) (_ : ¬FiniteDimensional ℂ A)
    (_ : IsNuclear.{0, uNuclear} A) (_hfinite : StablyFinite A)
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
    (_ : (U : Filter ℕ) ≤ atTop)
    (_ : RealRankZero (FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U)),
    UniformPropertyGammaAt A U


-- @@ L614-614 verbatim
end CurrentMain


-- @@ L616-616 verbatim
end ComparatorModel


-- @@ L618-618 verbatim
namespace ComparatorModel.CurrentMain


-- @@ L620-626 verbatim
def MainClaim : Prop :=
  ∃ h0 : ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction, letI := h0;
  ∃ h1 : ComparatorModel.CurrentMain.NullConstruction, letI := h1;
  ∃ h2 : ComparatorModel.CurrentMain.CauchyConstruction, letI := h2;
  ∃ h3 : ComparatorModel.CurrentMain.LimitConstruction, letI := h3;
  ∃ h4 : ComparatorModel.CurrentMain.TraceConstruction, letI := h4;
  Statement.{uNuclear}


-- @@ L628-628 verbatim
end ComparatorModel.CurrentMain


-- @@ L630-630 verbatim
end


-- @@ L632-632 verbatim
end OAI
