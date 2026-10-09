import OAI.Analysis.TracialSplitting.ChallengeDefinitions


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe uA uD uE uI uR uX


-- @@ L9-9 verbatim
section


-- @@ L11-11 verbatim
namespace Pureness


-- @@ L13-13 verbatim
open scoped TensorProduct ComplexOrder


-- @@ L15-15 verbatim
universe u v


-- @@ L17-18 verbatim
def IsNuclear (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (B : Type v) [CStarAlgebra B], Subsingleton (CStarAlgebraNorm (A ⊗[ℂ] B))


-- @@ L20-20 verbatim
end Pureness


-- @@ L22-22 verbatim
namespace CurrentMain


-- @@ L24-24 verbatim
section


-- @@ L26-26 verbatim
open Pureness


-- @@ L28-28 verbatim
open scoped ComplexOrder


-- @@ L30-32 verbatim
def RealRankZero (D : Type uD) [CStarAlgebra D] : Prop :=
  ∀ a : D, IsSelfAdjoint a → ∀ ε : ℝ, 0 < ε →
    ∃ b : D, IsSelfAdjoint b ∧ (spectrum ℂ b).Finite ∧ ‖a - b‖ < ε


-- @@ L34-36 verbatim
def traceTwoNorm {D : Type uD} [CStarAlgebra D] [PartialOrder D]
    (τ : TracialState D) (a : D) : ℝ :=
  Real.sqrt (τ.functional (star a * a)).re


-- @@ L38-38 verbatim
variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L40-41 verbatim
lemma traceTwoNorm_eq_gns (τ : TracialState D) (a : D) :
    traceTwoNorm τ a = ‖τ.functional.toPreGNS a‖ := rfl


-- @@ L43-46 verbatim
omit [StarOrderedRing D] in

lemma traceTwoNorm_nonneg (τ : TracialState D) (a : D) :
    0 ≤ traceTwoNorm τ a := Real.sqrt_nonneg _


-- @@ L48-51 verbatim
omit [StarOrderedRing D] in

@[simp] lemma traceTwoNorm_zero (τ : TracialState D) : traceTwoNorm τ 0 = 0 := by
  simp [traceTwoNorm]


-- @@ L53-56 verbatim
omit [StarOrderedRing D] in

@[simp] lemma traceTwoNorm_one (τ : TracialState D) : traceTwoNorm τ 1 = 1 := by
  simp [traceTwoNorm, τ.normalized]


-- @@ L58-61 verbatim
lemma traceTwoNorm_add_le (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (a + b) ≤ traceTwoNorm τ a + traceTwoNorm τ b := by
  simpa only [traceTwoNorm_eq_gns, map_add] using
    norm_add_le (τ.functional.toPreGNS a) (τ.functional.toPreGNS b)


-- @@ L63-67 verbatim
omit [StarOrderedRing D] in

@[simp] lemma traceTwoNorm_star (τ : TracialState D) (a : D) :
    traceTwoNorm τ (star a) = traceTwoNorm τ a := by
  simp only [traceTwoNorm, star_star, τ.tracial a (star a)]


-- @@ L69-78 verbatim
lemma traceTwoNorm_mul_left (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (a * b) ≤ ‖a‖ * traceTwoNorm τ b := by
  let f := τ.functional
  have hop : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  calc
    traceTwoNorm τ (a * b) = ‖f.leftMulMapPreGNS a (f.toPreGNS b)‖ := rfl
    _ ≤ ‖f.leftMulMapPreGNS a‖ * ‖f.toPreGNS b‖ := (f.leftMulMapPreGNS a).le_opNorm _
    _ ≤ ‖a‖ * traceTwoNorm τ b := mul_le_mul_of_nonneg_right hop (norm_nonneg _)


-- @@ L80-86 verbatim
lemma traceTwoNorm_mul_right (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (b * a) ≤ ‖a‖ * traceTwoNorm τ b := by
  calc
    traceTwoNorm τ (b * a) = traceTwoNorm τ (star a * star b) := by
      rw [← star_mul, traceTwoNorm_star]
    _ ≤ ‖star a‖ * traceTwoNorm τ (star b) := traceTwoNorm_mul_left τ _ _
    _ = ‖a‖ * traceTwoNorm τ b := by rw [norm_star, traceTwoNorm_star]


-- @@ L88-90 verbatim
lemma traceTwoNorm_le_norm (τ : TracialState D) (a : D) :
    traceTwoNorm τ a ≤ ‖a‖ := by
  simpa only [mul_one, traceTwoNorm_one] using traceTwoNorm_mul_left τ a 1


-- @@ L92-99 verbatim
lemma trace_norm_le_twoNorm (τ : TracialState D) (a : D) :
    ‖τ.functional a‖ ≤ traceTwoNorm τ a := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (τ.functional.toPreGNS 1)
    (τ.functional.toPreGNS a)
  have hone : ‖τ.functional.toPreGNS 1‖ = 1 := traceTwoNorm_one τ
  simpa only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, hone,
    ← traceTwoNorm_eq_gns] using h


-- @@ L101-103 verbatim
lemma trace_norm_le_norm (τ : TracialState D) (a : D) :
    ‖τ.functional a‖ ≤ ‖a‖ :=
  (trace_norm_le_twoNorm τ a).trans (traceTwoNorm_le_norm τ a)


-- @@ L105-105 verbatim
end


-- @@ L107-107 verbatim
open scoped ComplexOrder


-- @@ L109-109 verbatim
variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L111-113 verbatim
lemma traceTwoNorm_neg (τ : Pureness.TracialState D) (a : D) :
    traceTwoNorm τ (-a) = traceTwoNorm τ a := by
  simp only [traceTwoNorm_eq_gns, map_neg, norm_neg]


-- @@ L115-115 verbatim
end CurrentMain


-- @@ L117-117 verbatim
namespace Pureness


-- @@ L119-119 verbatim
open Filter


-- @@ L121-121 verbatim
open scoped Topology NNReal ENNReal


-- @@ L123-123 verbatim
namespace ClosedStarIdeal


-- @@ L125-125 verbatim
variable {D : Type uD} [CStarAlgebra D] (J : ClosedStarIdeal D)


-- @@ L127-127 verbatim
abbrev Quotient := J.ideal.ringCon.Quotient


-- @@ L129-129 verbatim
def quotientMap : D →ₐ[ℂ] J.Quotient := J.ideal.ringCon.mkₐ ℂ


-- @@ L131-132 verbatim
lemma quotientMap_surjective : Function.Surjective J.quotientMap :=
  J.ideal.ringCon.mkₐ_surjective (α := ℂ)


-- @@ L134-137 verbatim
lemma rel_star (u v : D) (h : J.ideal.ringCon u v) :
    J.ideal.ringCon (star u) (star v) := by
  rw [TwoSidedIdeal.rel_iff] at h ⊢
  simpa only [star_sub] using J.star_mem h


-- @@ L139-140 verbatim
instance quotientStar : Star (J.Quotient) where
  star := Quotient.map' star (J.rel_star)


-- @@ L142-143 verbatim
lemma quotientMap_star (u : D) :
    J.quotientMap (star u) = star (J.quotientMap u) := rfl


-- @@ L145-158 verbatim
instance quotientStarRing : StarRing (J.Quotient) where
  star_involutive x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← J.quotientMap_star,← J.quotientMap_star,star_star]
  star_mul x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_mul,← J.quotientMap_star,star_mul,map_mul,
      J.quotientMap_star,J.quotientMap_star]
  star_add x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_add,← J.quotientMap_star,star_add,map_add,
      J.quotientMap_star,J.quotientMap_star]


-- @@ L160-163 verbatim
instance quotientStarModule : StarModule ℂ (J.Quotient) where
  star_smul c x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← _root_.map_smul,← J.quotientMap_star,star_smul,_root_.map_smul,J.quotientMap_star]


-- @@ L165-166 verbatim
abbrev idealSubmodule : Submodule ℂ (D) :=
  (J.quotientMap).toLinearMap.ker


-- @@ L168-174 verbatim
lemma idealSubmodule_coe :
    (J.idealSubmodule : Set (D)) =
      (J.ideal : Set (D)) := by
  ext u
  change J.quotientMap u = 0 ↔ u ∈ J.ideal
  change (J.ideal).ringCon.mk' u = (J.ideal).ringCon.mk' 0 ↔ _
  exact Quotient.eq


-- @@ L176-178 verbatim
instance idealSubmodule_closed : IsClosed (J.idealSubmodule : Set (D)) := by
  rw [J.idealSubmodule_coe]
  exact J.isClosed


-- @@ L180-182 verbatim
def quotientLinearEquiv :
    (D ⧸ J.idealSubmodule) ≃ₗ[ℂ] J.Quotient :=
  (J.quotientMap).toLinearMap.quotKerEquivOfSurjective (J.quotientMap_surjective)


-- @@ L184-185 verbatim
lemma quotientLinearEquiv_mk (u : D) :
    J.quotientLinearEquiv (Submodule.Quotient.mk u) = J.quotientMap u := rfl


-- @@ L187-189 verbatim
instance quotientNormedAddCommGroup : NormedAddCommGroup (J.Quotient) :=
  NormedAddCommGroup.induced _ _ (J.quotientLinearEquiv).symm
    (J.quotientLinearEquiv).symm.injective


-- @@ L191-192 verbatim
instance quotientNormedSpace : NormedSpace ℂ (J.Quotient) :=
  NormedSpace.induced ℂ _ _ (J.quotientLinearEquiv).symm


-- @@ L194-197 verbatim
def quotientNormEquiv : J.Quotient ≃ₗᵢ[ℂ]
    (D ⧸ J.idealSubmodule) where
  __ := (J.quotientLinearEquiv).symm
  norm_map' _ := rfl


-- @@ L199-203 verbatim
lemma quotientMap_norm_le (u : D) :
    ‖J.quotientMap u‖ ≤ ‖u‖ := by
  change ‖(J.quotientLinearEquiv).symm (J.quotientMap u)‖ ≤ ‖u‖
  rw [← J.quotientLinearEquiv_mk, LinearEquiv.symm_apply_apply]
  exact Submodule.Quotient.norm_mk_le _ u


-- @@ L205-210 verbatim
lemma quotient_norm_lt_rep (x : J.Quotient) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : D, J.quotientMap u = x ∧ ‖u‖ < ‖x‖+ε := by
  obtain ⟨u,hu,hun⟩ := Submodule.Quotient.norm_mk_lt ((J.quotientLinearEquiv).symm x) hε
  refine ⟨u,?_,hun⟩
  apply (J.quotientLinearEquiv).symm.injective
  rw [← J.quotientLinearEquiv_mk,LinearEquiv.symm_apply_apply,hu]


-- @@ L212-213 verbatim
instance quotientCompleteSpace : CompleteSpace (J.Quotient) :=
  (J.quotientNormEquiv).toIsometryEquiv.completeSpace_iff.mpr inferInstance


-- @@ L215-231 verbatim
lemma quotient_norm_mul_le (x y : J.Quotient) : ‖x*y‖ ≤ ‖x‖*‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc := ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
    Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖,‖y‖)) ε hε
  simp only [Set.mem_prod,Metric.mem_ball,and_imp,Prod.forall,Prod.exists] at hc
  obtain ⟨δ,η,⟨hδ,hη⟩,h⟩ := hc
  obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep x hδ
  obtain ⟨v,rfl,hv⟩ := J.quotient_norm_lt_rep y hη
  simp only [Real.dist_eq,abs_sub_lt_iff] at h
  specialize h ‖u‖ ‖v‖ ⟨by linarith,by linarith [J.quotientMap_norm_le u]⟩
    ⟨by linarith,by linarith [J.quotientMap_norm_le v]⟩
  calc
    _ = ‖J.quotientMap (u*v)‖ := by rw [map_mul]
    _ ≤ ‖u*v‖ := J.quotientMap_norm_le _
    _ ≤ ‖u‖*‖v‖ := norm_mul_le _ _
    _ ≤ _ := by linarith [h.2]


-- @@ L233-235 verbatim
instance quotientNormedRing : NormedRing (J.Quotient) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := J.quotient_norm_mul_le


-- @@ L237-238 verbatim
instance quotientNormedAlgebra : NormedAlgebra ℂ (J.Quotient) where
  norm_smul_le := norm_smul_le


-- @@ L240-247 verbatim
lemma quotient_norm_star (x : J.Quotient) : ‖star x‖ = ‖x‖ := by
  have hle (y : J.Quotient) : ‖star y‖ ≤ ‖y‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep y hε
    rw [← J.quotientMap_star]
    exact (J.quotientMap_norm_le (star u)).trans (by simpa only [norm_star] using hu.le)
  exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))


-- @@ L249-250 verbatim
instance quotientNormedStarGroup : NormedStarGroup (J.Quotient) where
  norm_star_le x := (J.quotient_norm_star x).le


-- @@ L252-252 verbatim
end ClosedStarIdeal


-- @@ L254-254 verbatim
end Pureness


-- @@ L256-256 verbatim
namespace Pureness.ClosedStarIdeal


-- @@ L258-258 verbatim
open Filter


-- @@ L260-260 verbatim
open scoped Topology NNReal ENNReal


-- @@ L262-262 verbatim
variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L264-264 verbatim
variable (J : ClosedStarIdeal D)


-- @@ L266-275 verbatim
def idealStarAlgebra : NonUnitalStarSubalgebra ℂ (D) where
  carrier := J.ideal
  zero_mem' := (J.ideal).zero_mem
  add_mem' := (J.ideal).add_mem
  mul_mem' {u v} _ hv := (J.ideal).mul_mem_left u v hv
  smul_mem' c u hu := by
    change c • u ∈ J.ideal
    rw [Algebra.smul_def]
    exact (J.ideal).mul_mem_left (algebraMap ℂ _ c) u hu
  star_mem' := J.star_mem


-- @@ L277-278 verbatim
instance idealStarAlgebraCompleteSpace : CompleteSpace (J.idealStarAlgebra) :=
  (J.isClosed).completeSpace_coe


-- @@ L280-281 verbatim
instance idealStarAlgebraCStar : NonUnitalCStarAlgebra (J.idealStarAlgebra) where
  norm_mul_self_le u := CStarRing.norm_mul_self_le u.1


-- @@ L283-284 verbatim
instance idealPartialOrder : PartialOrder (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrder _


-- @@ L286-287 verbatim
instance idealStarOrderedRing : StarOrderedRing (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrderedRing _


-- @@ L289-289 verbatim
local instance : LE (J.idealStarAlgebra) := (J.idealPartialOrder).toLE


-- @@ L291-291 verbatim
local instance : Preorder (J.idealStarAlgebra) := (J.idealPartialOrder).toPreorder


-- @@ L293-299 verbatim
def idealInclusion : J.idealStarAlgebra →⋆ₙₐ[ℂ] D where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl


-- @@ L301-308 verbatim
lemma idealInclusion_nonneg {e : J.idealStarAlgebra} (he : 0 ≤ e) :
    0 ≤ (e : D) :=
  by
    have hs : star (CFC.sqrt e)*CFC.sqrt e = e := by
      rw [(CFC.sqrt_nonneg e).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self e he]
    have hs' := congrArg Subtype.val hs
    rw [← hs']
    exact star_mul_self_nonneg _


-- @@ L310-315 verbatim
lemma norm_one_sub {e : D} (he : 0 ≤ e) (hn : ‖e‖ ≤ 1) :
    ‖1-e‖ ≤ 1 := by
  have he1 : e ≤ 1 := by
    simpa using (CStarAlgebra.norm_le_iff_le_algebraMap e (by norm_num : (0:ℝ) ≤ 1) he).mp hn
  rw [CStarAlgebra.norm_le_iff_le_algebraMap (1-e) (by norm_num : (0:ℝ) ≤ 1) (sub_nonneg.mpr he1)]
  simpa using sub_le_self (1 : D) he


-- @@ L317-331 verbatim
lemma exists_ideal_contraction {w : D} (hw : w ∈ J.ideal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, e ∈ J.ideal ∧ IsSelfAdjoint e ∧
      ‖1-e‖ ≤ 1 ∧ ‖w*(1-e)‖ < ε := by
  let W : J.idealStarAlgebra := ⟨w,hw⟩
  have hl := CStarAlgebra.increasingApproximateUnit (J.idealStarAlgebra)
  have ht := hl.tendsto_mul_left W
  have heps := (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨e,hp,hn,hm⟩ := (hl.eventually_nonneg.and (hl.eventually_norm.and heps)).exists
  refine ⟨e.1,e.2,?_,norm_one_sub (J.idealInclusion_nonneg hp) hn,?_⟩
  · exact congrArg Subtype.val hp.isSelfAdjoint
  · change dist (W*e) W < ε at hm
    rw [dist_eq_norm] at hm
    change ‖w*e.1-w‖ < ε at hm
    simpa only [mul_sub,mul_one,← neg_sub (w*e.1) w,norm_neg] using hm


-- @@ L333-372 verbatim
lemma quotient_norm_square_le (x : J.Quotient) :
    ‖x‖*‖x‖ ≤ ‖star x*x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
  obtain ⟨v,hv,hvn⟩ := J.quotient_norm_lt_rep
    (star (J.quotientMap u)*J.quotientMap u) (half_pos hε)
  let w := star u*u-v
  have hw : w ∈ J.ideal := by
    change (J.ideal).ringCon w 0
    apply Quotient.exact
    change J.quotientMap w = J.quotientMap 0
    simp only [w,map_sub,map_mul,J.quotientMap_star,hv,sub_self]
    exact (_root_.map_zero (J.quotientMap)).symm
  obtain ⟨e,he,hestar,hen,hwe⟩ := J.exists_ideal_contraction hw (half_pos hε)
  have heq : J.quotientMap e = 0 := Quotient.sound he
  have hmap : J.quotientMap (u*(1-e)) = J.quotientMap u := by
    simp [map_mul,map_sub,heq]
  have hun := J.quotientMap_norm_le (u*(1-e))
  rw [hmap] at hun
  have hidentity : star (u*(1-e))*(u*(1-e)) =
      (1-e)*v*(1-e)+(1-e)*(w*(1-e)) := by
    simp only [star_mul,star_sub,star_one,hestar.star_eq,w]
    noncomm_ring
  have hterm1 : ‖(1-e)*v*(1-e)‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖1-e‖*‖v‖*‖1-e‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖v‖*1 := by gcongr
      _ = ‖v‖ := by ring
  have hterm2 : ‖(1-e)*(w*(1-e))‖ < ε/2 := by
    calc
      _ ≤ ‖1-e‖*‖w*(1-e)‖ := norm_mul_le _ _
      _ ≤ 1*‖w*(1-e)‖ := by gcongr
      _ < ε/2 := by simpa using hwe
  calc
    _ ≤ ‖u*(1-e)‖*‖u*(1-e)‖ := mul_self_le_mul_self (norm_nonneg _) hun
    _ = ‖star (u*(1-e))*(u*(1-e))‖ := (CStarRing.norm_star_mul_self (x := u*(1-e))).symm
    _ ≤ ‖(1-e)*v*(1-e)‖+‖(1-e)*(w*(1-e))‖ := by rw [hidentity]; exact norm_add_le _ _
    _ ≤ ‖star (J.quotientMap u)*J.quotientMap u‖+ε := by linarith


-- @@ L374-375 verbatim
instance quotientCStarAlgebra : CStarAlgebra (J.Quotient) where
  norm_mul_self_le := J.quotient_norm_square_le


-- @@ L377-377 verbatim
end Pureness.ClosedStarIdeal


-- @@ L379-379 verbatim
namespace CurrentMain


-- @@ L381-381 verbatim
section


-- @@ L383-383 verbatim
open Pureness


-- @@ L385-385 verbatim
variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L387-387 verbatim
variable (τ : I → TracialState D) [Nonempty I]


-- @@ L389-389 verbatim
def familyTwoNorm (a : D) : ℝ := ⨆ i, traceTwoNorm (τ i) a


-- @@ L391-394 verbatim
omit [Nonempty I] in

lemma familyTwoNorm_bdd (a : D) : BddAbove (Set.range (fun i => traceTwoNorm (τ i) a)) :=
  ⟨‖a‖, by rintro _ ⟨i, rfl⟩; exact traceTwoNorm_le_norm (τ i) a⟩


-- @@ L396-400 verbatim
omit [Nonempty I] in

lemma traceTwoNorm_le_family (i : I) (a : D) :
    traceTwoNorm (τ i) a ≤ familyTwoNorm τ a :=
  le_ciSup (familyTwoNorm_bdd τ a) i


-- @@ L402-404 verbatim
lemma familyTwoNorm_nonneg (a : D) : 0 ≤ familyTwoNorm τ a := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact (traceTwoNorm_nonneg (τ i) a).trans (traceTwoNorm_le_family τ i a)


-- @@ L406-407 verbatim
lemma familyTwoNorm_le_norm (a : D) : familyTwoNorm τ a ≤ ‖a‖ :=
  ciSup_le (fun i => traceTwoNorm_le_norm (τ i) a)


-- @@ L409-411 verbatim
@[simp] lemma familyTwoNorm_zero : familyTwoNorm τ 0 = 0 := by
  apply le_antisymm _ (familyTwoNorm_nonneg τ 0)
  simpa only [norm_zero] using familyTwoNorm_le_norm τ 0


-- @@ L413-418 verbatim
lemma familyTwoNorm_add_le (a b : D) :
    familyTwoNorm τ (a + b) ≤ familyTwoNorm τ a + familyTwoNorm τ b := by
  apply ciSup_le
  intro i
  exact (traceTwoNorm_add_le (τ i) a b).trans
    (add_le_add (traceTwoNorm_le_family τ i a) (traceTwoNorm_le_family τ i b))


-- @@ L420-423 verbatim
omit [Nonempty I] in

@[simp] lemma familyTwoNorm_neg (a : D) : familyTwoNorm τ (-a) = familyTwoNorm τ a := by
  simp only [familyTwoNorm, traceTwoNorm_neg]


-- @@ L425-428 verbatim
omit [Nonempty I] in

lemma familyTwoNorm_sub_swap (a b : D) : familyTwoNorm τ (a - b) = familyTwoNorm τ (b - a) := by
  rw [← neg_sub b a, familyTwoNorm_neg]


-- @@ L430-433 verbatim
lemma familyTwoNorm_sub_triangle (a b c : D) :
    familyTwoNorm τ (a - c) ≤ familyTwoNorm τ (a - b) + familyTwoNorm τ (b - c) := by
  convert familyTwoNorm_add_le τ (a - b) (b - c) using 1
  abel_nf


-- @@ L435-438 verbatim
omit [StarOrderedRing D] [Nonempty I] in

@[simp] lemma familyTwoNorm_star (a : D) : familyTwoNorm τ (star a) = familyTwoNorm τ a := by
  simp only [familyTwoNorm, traceTwoNorm_star]


-- @@ L440-445 verbatim
lemma familyTwoNorm_mul_left (a b : D) :
    familyTwoNorm τ (a * b) ≤ ‖a‖ * familyTwoNorm τ b := by
  apply ciSup_le
  intro i
  exact (traceTwoNorm_mul_left (τ i) a b).trans
    (mul_le_mul_of_nonneg_left (traceTwoNorm_le_family τ i b) (norm_nonneg _))


-- @@ L447-452 verbatim
lemma familyTwoNorm_mul_right (a b : D) :
    familyTwoNorm τ (a * b) ≤ familyTwoNorm τ a * ‖b‖ := by
  apply ciSup_le
  intro i
  simpa only [mul_comm] using (traceTwoNorm_mul_right (τ i) b a).trans
    (mul_le_mul_of_nonneg_left (traceTwoNorm_le_family τ i a) (norm_nonneg _))


-- @@ L454-454 verbatim
end


-- @@ L456-456 verbatim
open Pureness Filter


-- @@ L458-458 verbatim
open scoped Topology NNReal ENNReal


-- @@ L460-461 verbatim
instance boundedFamilyProductCStar {X : Type uX} {D : Type uD} [CStarAlgebra D] [Nontrivial D] :
    CStarAlgebra (lp (fun _ : X => D) ∞) where


-- @@ L463-463 verbatim
section UniformNull


-- @@ L465-465 verbatim
variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L467-467 verbatim
variable (τ : I → TracialState D) [Nonempty I]


-- @@ L469-470 verbatim
def IsFamilyNull (F : Filter X) (u : X → D) : Prop :=
  Tendsto (fun n => familyTwoNorm τ (u n)) F (𝓝 0)


-- @@ L472-475 verbatim
lemma isFamilyNull_iff (F : Filter X) (u : X → D) :
    IsFamilyNull τ F u ↔ ∀ ε > 0, ∀ᶠ n in F, familyTwoNorm τ (u n) < ε := by
  simp only [IsFamilyNull, Metric.tendsto_nhds, Real.dist_eq, sub_zero,
    abs_of_nonneg (familyTwoNorm_nonneg τ _)]


-- @@ L477-479 verbatim
lemma isFamilyNull_zero (F : Filter X) : IsFamilyNull τ F (fun _ => 0) := by
  simp only [IsFamilyNull, familyTwoNorm_zero]
  exact tendsto_const_nhds


-- @@ L481-486 verbatim
lemma isFamilyNull_add {F : Filter X} {u v : X → D}
    (hu : IsFamilyNull τ F u) (hv : IsFamilyNull τ F v) :
    IsFamilyNull τ F (fun n => u n + v n) := by
  apply squeeze_zero (fun n => familyTwoNorm_nonneg τ _)
    (fun n => familyTwoNorm_add_le τ _ _)
  simpa only [add_zero] using hu.add hv


-- @@ L488-492 verbatim
omit [Nonempty I] in

lemma isFamilyNull_neg {F : Filter X} {u : X → D}
    (hu : IsFamilyNull τ F u) : IsFamilyNull τ F (fun n => -u n) := by
  simpa only [IsFamilyNull, familyTwoNorm_neg] using hu


-- @@ L494-498 verbatim
omit [StarOrderedRing D] [Nonempty I] in

lemma isFamilyNull_star {F : Filter X} {u : X → D}
    (hu : IsFamilyNull τ F u) : IsFamilyNull τ F (fun n => star (u n)) := by
  simpa only [IsFamilyNull, familyTwoNorm_star] using hu


-- @@ L500-506 verbatim
lemma isFamilyNull_mul_left {F : Filter X} {u v : X → D}
    (hv : IsFamilyNull τ F v) {M : ℝ} (hu : ∀ n, ‖u n‖ ≤ M) :
    IsFamilyNull τ F (fun n => u n * v n) := by
  apply squeeze_zero (fun n => familyTwoNorm_nonneg τ _) (fun n =>
    (familyTwoNorm_mul_left τ _ _).trans
      (mul_le_mul_of_nonneg_right (hu n) (familyTwoNorm_nonneg τ _)))
  simpa only [mul_zero] using hv.const_mul M


-- @@ L508-514 verbatim
lemma isFamilyNull_mul_right {F : Filter X} {u v : X → D}
    (hu : IsFamilyNull τ F u) {M : ℝ} (hv : ∀ n, ‖v n‖ ≤ M) :
    IsFamilyNull τ F (fun n => u n * v n) := by
  apply squeeze_zero (fun n => familyTwoNorm_nonneg τ _) (fun n =>
    (familyTwoNorm_mul_right τ _ _).trans
      (mul_le_mul_of_nonneg_left (hv n) (familyTwoNorm_nonneg τ _)))
  simpa only [zero_mul] using hu.mul_const M


-- @@ L516-532 verbatim
lemma familyNull_isClosed (F : Filter X) :
    IsClosed {u : lp (fun _ : X => D) ∞ | IsFamilyNull τ F (fun n => u n)} := by
  apply isClosed_of_closure_subset
  intro u hu
  change IsFamilyNull τ F (fun n => u n)
  rw [isFamilyNull_iff]
  intro ε hε
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp hu (ε/2) (by linarith)
  have hnear (n : X) : familyTwoNorm τ (u n-v n) < ε/2 :=
    (familyTwoNorm_le_norm τ _).trans_lt
      ((lp.norm_apply_le_norm ENNReal.top_ne_zero (u-v) n).trans_lt
        (by simpa only [dist_eq_norm] using huv))
  have he := (isFamilyNull_iff τ F _).mp hv (ε/2) (by linarith)
  filter_upwards [he] with n hn
  have ht := familyTwoNorm_add_le τ (u n-v n) (v n)
  rw [sub_add_cancel] at ht
  linarith [hnear n]


-- @@ L534-534 verbatim
variable [Nontrivial D]


-- @@ L536-544 verbatim
def familyNullTwoSided (F : Filter X) : TwoSidedIdeal (lp (fun _ : X => D) ∞) :=
  TwoSidedIdeal.mk' {u | IsFamilyNull τ F (fun n => u n)}
    (isFamilyNull_zero τ F)
    (fun hu hv => isFamilyNull_add τ hu hv)
    (fun hu => isFamilyNull_neg τ hu)
    (fun {u _} hv => isFamilyNull_mul_left τ hv
      (lp.norm_apply_le_norm ENNReal.top_ne_zero u))
    (fun {_ v} hu => isFamilyNull_mul_right τ hu
      (lp.norm_apply_le_norm ENNReal.top_ne_zero v))


-- @@ L546-549 verbatim
lemma familyNull_mem (F : Filter X) (u : lp (fun _ : X => D) ∞) :
    u ∈ familyNullTwoSided τ F ↔ IsFamilyNull τ F (fun n => u n) := by
  unfold familyNullTwoSided
  exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u


-- @@ L551-554 verbatim
lemma familyNull_star (F : Filter X) {u : lp (fun _ : X => D) ∞}
    (hu : u ∈ familyNullTwoSided τ F) : star u ∈ familyNullTwoSided τ F := by
  apply (familyNull_mem τ F (star u)).mpr
  exact isFamilyNull_star τ ((familyNull_mem τ F u).mp hu)


-- @@ L556-563 verbatim
def familyNullIdeal (F : Filter X) : ClosedStarIdeal (lp (fun _ : X => D) ∞) where
  ideal := familyNullTwoSided τ F
  star_mem := familyNull_star τ F
  isClosed := by
    have he : (familyNullTwoSided τ F : Set (lp (fun _ : X => D) ∞)) = {u | IsFamilyNull τ F (fun n => u n)} :=
      Set.ext (familyNull_mem τ F)
    rw [he]
    exact familyNull_isClosed τ F


-- @@ L565-565 verbatim
end UniformNull


-- @@ L567-567 verbatim
variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L569-569 verbatim
variable (τ : I → TracialState D) [Nonempty I]


-- @@ L571-572 verbatim
def IsFamilyCauchy (u : ℕ → D) : Prop :=
  IsFamilyNull τ (atTop : Filter (ℕ × ℕ)) (fun p => u p.1 - u p.2)


-- @@ L574-576 verbatim
lemma isFamilyCauchy_const (a : D) : IsFamilyCauchy τ (fun _ => a) := by
  simpa only [IsFamilyCauchy, sub_self] using
    isFamilyNull_zero τ (atTop : Filter (ℕ × ℕ))


-- @@ L578-580 verbatim
lemma isFamilyCauchy_add {u v : ℕ → D} (hu : IsFamilyCauchy τ u)
    (hv : IsFamilyCauchy τ v) : IsFamilyCauchy τ (fun n => u n+v n) := by
  simpa only [IsFamilyCauchy, add_sub_add_comm] using isFamilyNull_add τ hu hv


-- @@ L582-586 verbatim
omit [StarOrderedRing D] [Nonempty I] in

lemma isFamilyCauchy_star {u : ℕ → D} (hu : IsFamilyCauchy τ u) :
    IsFamilyCauchy τ (fun n => star (u n)) := by
  simpa only [IsFamilyCauchy, star_sub] using isFamilyNull_star τ hu


-- @@ L588-595 verbatim
lemma isFamilyCauchy_mul {u v : ℕ → D} (hu : IsFamilyCauchy τ u)
    (hv : IsFamilyCauchy τ v) {M N : ℝ} (hM : ∀ n, ‖u n‖ ≤ M)
    (hN : ∀ n, ‖v n‖ ≤ N) : IsFamilyCauchy τ (fun n => u n*v n) := by
  have h₁ := isFamilyNull_mul_left τ hv (fun p : ℕ × ℕ => hM p.1)
  have h₂ := isFamilyNull_mul_right τ hu (fun p : ℕ × ℕ => hN p.2)
  have he (p : ℕ × ℕ) : u p.1 * (v p.1-v p.2) + (u p.1-u p.2)*v p.2 =
      u p.1*v p.1-u p.2*v p.2 := by noncomm_ring
  simpa only [IsFamilyCauchy, he] using isFamilyNull_add τ h₁ h₂


-- @@ L597-597 verbatim
variable [Nontrivial D]


-- @@ L599-608 verbatim
def familyCauchyAlgebra : StarSubalgebra ℂ (lp (fun _ : ℕ => D) ∞) where
  carrier := {u | IsFamilyCauchy τ (fun n => u n)}
  zero_mem' := isFamilyCauchy_const τ 0
  one_mem' := isFamilyCauchy_const τ 1
  add_mem' hu hv := isFamilyCauchy_add τ hu hv
  mul_mem' {u v} hu hv := isFamilyCauchy_mul τ hu hv
    (lp.norm_apply_le_norm ENNReal.top_ne_zero u)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero v)
  algebraMap_mem' z := isFamilyCauchy_const τ (algebraMap ℂ D z)
  star_mem' hu := isFamilyCauchy_star τ hu


-- @@ L610-627 verbatim
lemma familyCauchyAlgebra_isClosed : IsClosed
    (familyCauchyAlgebra τ : Set (lp (fun _ : ℕ => D) ∞)) := by
  apply isClosed_of_closure_subset
  intro u hu
  change IsFamilyCauchy τ (fun n => u n)
  rw [IsFamilyCauchy, isFamilyNull_iff]
  intro ε hε
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp hu (ε/3) (by linarith)
  have hnear (n : ℕ) : familyTwoNorm τ (u n-v n) < ε/3 :=
    (familyTwoNorm_le_norm τ _).trans_lt
      ((lp.norm_apply_le_norm ENNReal.top_ne_zero (u-v) n).trans_lt
        (by simpa only [dist_eq_norm] using huv))
  have he := (isFamilyNull_iff τ _ _).mp hv (ε/3) (by linarith)
  filter_upwards [he] with p hp
  have h₁ := familyTwoNorm_sub_triangle τ (u p.1) (v p.1) (u p.2)
  have h₂ := familyTwoNorm_sub_triangle τ (v p.1) (v p.2) (u p.2)
  rw [familyTwoNorm_sub_swap τ (v p.2) (u p.2)] at h₂
  linarith [hnear p.1, hnear p.2]


-- @@ L629-630 verbatim
instance familyCauchy_complete : CompleteSpace (familyCauchyAlgebra τ) :=
  (familyCauchyAlgebra_isClosed τ).completeSpace_coe


-- @@ L632-632 verbatim
instance familyCauchy_cstar : CStarAlgebra (familyCauchyAlgebra τ) where


-- @@ L634-642 verbatim
def familyCauchyNullIdeal : ClosedStarIdeal (familyCauchyAlgebra τ) where
  ideal := TwoSidedIdeal.comap (familyCauchyAlgebra τ).val.toRingHom
    (familyNullIdeal τ atTop).ideal
  star_mem := by
    intro u hu
    apply (familyNullIdeal τ atTop).star_mem hu
  isClosed := by
    exact (familyNullIdeal τ atTop).isClosed.preimage
      (continuous_subtype_val : Continuous (fun u : familyCauchyAlgebra τ => u.1))


-- @@ L644-644 verbatim
abbrev UniformTracialCompletion := (familyCauchyNullIdeal τ).Quotient


-- @@ L646-646 verbatim
end CurrentMain


-- @@ L648-648 verbatim
namespace Pureness.ClosedStarIdeal


-- @@ L650-650 verbatim
open scoped ComplexOrder


-- @@ L652-652 verbatim
variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L654-655 verbatim
instance quotientOrder (J : ClosedStarIdeal D) : PartialOrder J.Quotient :=
  CStarAlgebra.spectralOrder _


-- @@ L657-658 verbatim
instance quotientStarOrdered (J : ClosedStarIdeal D) : StarOrderedRing J.Quotient :=
  CStarAlgebra.spectralOrderedRing _


-- @@ L660-660 verbatim
variable (J : ClosedStarIdeal D)


-- @@ L662-662 verbatim
variable (τ : TracialState D) (hτ : ∀ a ∈ J.ideal, τ.functional a = 0)


-- @@ L664-673 verbatim
omit [StarOrderedRing D] in

include hτ in

lemma trace_congr (u v : D) (huv : J.ideal.ringCon u v) :
    τ.functional u = τ.functional v := by
  rw [TwoSidedIdeal.rel_iff] at huv
  have h := hτ (u-v) huv
  rw [map_sub, sub_eq_zero] at h
  exact h


-- @@ L675-675 verbatim
def descendedValue : J.Quotient → ℂ := Quotient.lift τ.functional (J.trace_congr τ hτ)


-- @@ L677-679 verbatim
omit [StarOrderedRing D] in

lemma descendedValue_map (u : D) : J.descendedValue τ hτ (J.quotientMap u) = τ.functional u := rfl


-- @@ L681-690 verbatim
def descendedLinear : J.Quotient →ₗ[ℂ] ℂ where
  toFun := J.descendedValue τ hτ
  map_add' x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_add, J.descendedValue_map, J.descendedValue_map, J.descendedValue_map, map_add]
  map_smul' c x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← map_smul, J.descendedValue_map, J.descendedValue_map, map_smul]
    rfl


-- @@ L692-697 verbatim
lemma descendedLinear_square_nonneg (x : J.Quotient) :
    0 ≤ J.descendedLinear τ hτ (star x*x) := by
  obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
  change 0 ≤ J.descendedValue τ hτ (star (J.quotientMap u) * J.quotientMap u)
  rw [← J.quotientMap_star, ← map_mul, J.descendedValue_map]
  exact τ.functional.map_nonneg (star_mul_self_nonneg u)


-- @@ L699-719 verbatim
def descendedTrace : TracialState J.Quotient where
  functional := { J.descendedLinear τ hτ with
    monotone' := by
      intro x y hxy
      apply sub_nonneg.mp
      change 0 ≤ J.descendedLinear τ hτ y - J.descendedLinear τ hτ x
      rw [← map_sub]
      obtain ⟨z,hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
      rw [hz]
      exact J.descendedLinear_square_nonneg τ hτ z }
  normalized := by
    change J.descendedValue τ hτ 1 = 1
    rw [← map_one J.quotientMap, J.descendedValue_map]
    exact τ.normalized
  tracial x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    change J.descendedValue τ hτ (J.quotientMap u * J.quotientMap v) =
      J.descendedValue τ hτ (J.quotientMap v * J.quotientMap u)
    rw [← map_mul, ← map_mul, J.descendedValue_map, J.descendedValue_map]
    exact τ.tracial u v


-- @@ L721-721 verbatim
end Pureness.ClosedStarIdeal


-- @@ L723-723 verbatim
namespace CurrentMain


-- @@ L725-725 verbatim
section


-- @@ L727-727 verbatim
open Pureness Filter


-- @@ L729-729 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L731-739 verbatim
lemma bounded_ultrafilter_tendsto {X : Type uX} {E : Type uE} [NormedAddCommGroup E] [ProperSpace E]
    (U : Ultrafilter X) (f : X → E) (M : ℝ) (hM : ∀ n, ‖f n‖ ≤ M) :
    Tendsto f (U : Filter X) (𝓝 (limUnder (U : Filter X) f)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨r,_,hr⟩ := (isCompact_closedBall (0 : E) M).ultrafilter_le_nhds' (U.map f)
    (show Metric.closedBall (0 : E) M ∈ U.map f from by
      change {n | f n ∈ Metric.closedBall (0 : E) M} ∈ U
      exact Filter.Eventually.of_forall (fun n => by simpa using hM n))
  exact ⟨r,hr⟩


-- @@ L741-741 verbatim
section UltraTrace


-- @@ L743-743 verbatim
variable {D : Type uD} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]


-- @@ L745-745 verbatim
variable (θ : X → TracialState D) (U : Ultrafilter X)


-- @@ L747-748 verbatim
instance boundedFamilyProductOrder : PartialOrder (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrder _


-- @@ L750-751 verbatim
instance boundedFamilyProductStarOrdered : StarOrderedRing (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrderedRing _


-- @@ L753-754 verbatim
def ultraTraceValue (u : lp (fun _ : X => D) ∞) : ℂ :=
  limUnder (U : Filter X) (fun n => (θ n).functional (u n))


-- @@ L756-761 verbatim
omit [Nontrivial D] in

lemma ultraTraceValue_tendsto (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => (θ n).functional (u n)) (U : Filter X) (𝓝 (ultraTraceValue θ U u)) :=
  bounded_ultrafilter_tendsto U _ ‖u‖ (fun n =>
    (trace_norm_le_norm (θ n) _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))


-- @@ L763-769 verbatim
omit [Nontrivial D] in

lemma ultraTraceValue_add (u v : lp (fun _ : X => D) ∞) :
    ultraTraceValue θ U (u+v) = ultraTraceValue θ U u+ultraTraceValue θ U v := by
  apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U (u+v))
  simpa only [lp.coeFn_add, Pi.add_apply, map_add] using
    (ultraTraceValue_tendsto θ U u).add (ultraTraceValue_tendsto θ U v)


-- @@ L771-775 verbatim
lemma ultraTraceValue_smul (z : ℂ) (u : lp (fun _ : X => D) ∞) :
    ultraTraceValue θ U (z • u) = z • ultraTraceValue θ U u := by
  apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U (z • u))
  simpa only [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_eq_mul] using
    (ultraTraceValue_tendsto θ U u).const_mul z


-- @@ L777-780 verbatim
def ultraTraceLinear : lp (fun _ : X => D) ∞ →ₗ[ℂ] ℂ where
  toFun := ultraTraceValue θ U
  map_add' := ultraTraceValue_add θ U
  map_smul' := ultraTraceValue_smul θ U


-- @@ L782-789 verbatim
def boundedFamilyEval (n : X) : lp (fun _ : X => D) ∞ →⋆ₐ[ℂ] D where
  toFun u := u n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl


-- @@ L791-809 verbatim
def ultraTrace : TracialState (lp (fun _ : X => D) ∞) where
  functional := { ultraTraceLinear θ U with
    monotone' := by
      intro u v huv
      exact le_of_tendsto_of_tendsto (ultraTraceValue_tendsto θ U u)
        (ultraTraceValue_tendsto θ U v) (Eventually.of_forall (fun n =>
          (θ n).functional.monotone (map_rel (boundedFamilyEval n) huv))) }
  normalized := by
    apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U 1)
    have he (n : X) : (θ n).functional ((1 : lp (fun _ : X => D) ∞) n) = 1 :=
      (θ n).normalized
    simp only [he]
    exact tendsto_const_nhds
  tracial u v := by
    change ultraTraceValue θ U (u*v) = ultraTraceValue θ U (v*u)
    apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U (u*v))
    have he (n : X) : (θ n).functional ((u*v) n) = (θ n).functional ((v*u) n) :=
      (θ n).tracial (u n) (v n)
    simpa only [he] using ultraTraceValue_tendsto θ U (v*u)


-- @@ L811-811 verbatim
end UltraTrace


-- @@ L813-813 verbatim
variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]


-- @@ L815-815 verbatim
variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)


-- @@ L817-817 verbatim
abbrev FamilyUltrapower := (familyNullIdeal τ (U : Filter X)).Quotient


-- @@ L819-828 verbatim
lemma ultraTrace_null (s : X → I) (u : lp (fun _ : X => D) ∞)
    (hu : u ∈ (familyNullIdeal τ (U : Filter X)).ideal) :
    (ultraTrace (fun n => τ (s n)) U).functional u = 0 := by
  have hn : IsFamilyNull τ (U : Filter X) (fun n => u n) :=
    (familyNull_mem τ _ u).mp hu
  have ht : Tendsto (fun n => (τ (s n)).functional (u n)) (U : Filter X) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      (trace_norm_le_twoNorm (τ (s n)) _).trans (traceTwoNorm_le_family τ (s n) _)) hn
  exact tendsto_nhds_unique (ultraTraceValue_tendsto (fun n => τ (s n)) U u) ht


-- @@ L830-832 verbatim
def familyLimitTrace (s : X → I) : TracialState (FamilyUltrapower τ U) :=
  (familyNullIdeal τ (U : Filter X)).descendedTrace
    (ultraTrace (fun n => τ (s n)) U) (ultraTrace_null τ U s)


-- @@ L834-834 verbatim
end


-- @@ L836-836 verbatim
section


-- @@ L838-838 verbatim
open Pureness Filter


-- @@ L840-840 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L842-842 verbatim
section PullbackTrace


-- @@ L844-844 verbatim
variable {D : Type uD} {E : Type uE} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L846-846 verbatim
variable [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]


-- @@ L848-855 verbatim
def pullbackTrace (τ : TracialState E) (ι : D →⋆ₐ[ℂ] E) : TracialState D where
  functional := { τ.functional.toLinearMap.comp ι.toLinearMap with
    monotone' := fun _ _ h => τ.functional.monotone (map_rel ι h) }
  normalized := by change τ.functional (ι 1) = 1; rw [map_one, τ.normalized]
  tracial x y := by
    change τ.functional (ι (x*y)) = τ.functional (ι (y*x))
    rw [map_mul ι x y, map_mul ι y x]
    exact τ.tracial _ _


-- @@ L857-857 verbatim
end PullbackTrace


-- @@ L859-859 verbatim
variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L861-861 verbatim
variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]


-- @@ L863-872 verbatim
omit [Nontrivial D] in

lemma isFamilyCauchy_iff (u : ℕ → D) : IsFamilyCauchy τ u ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, familyTwoNorm τ (u m-u n) < ε := by
  simp only [IsFamilyCauchy, isFamilyNull_iff, eventually_atTop_prod_self]
  constructor <;> intro h ε hε
  · obtain ⟨N,hN⟩ := h ε hε
    exact ⟨N,fun m hm n hn => hN m n hm hn⟩
  · obtain ⟨N,hN⟩ := h ε hε
    exact ⟨N,fun m n hm hn => hN m hm n hn⟩


-- @@ L874-882 verbatim
lemma cauchy_trace_values (i : I) (u : familyCauchyAlgebra τ) :
    CauchySeq (fun n : ℕ => (τ i).functional (u.1 n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := (isFamilyCauchy_iff τ _).mp u.2 ε hε
  refine ⟨N,fun m hm n hn => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  exact (trace_norm_le_twoNorm (τ i) _).trans_lt
    ((traceTwoNorm_le_family τ i _).trans_lt (hN m hm n hn))


-- @@ L884-885 verbatim
instance familyCauchyOrder : PartialOrder (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrder _


-- @@ L887-888 verbatim
instance familyCauchyStarOrdered : StarOrderedRing (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrderedRing _


-- @@ L890-892 verbatim
def cauchyTrace (i : I) : TracialState (familyCauchyAlgebra τ) :=
  pullbackTrace (ultraTrace (fun _ : ℕ => τ i) (Ultrafilter.of atTop))
    (familyCauchyAlgebra τ).subtype


-- @@ L894-901 verbatim
lemma cauchyTrace_tendsto (i : I) (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => (τ i).functional (u.1 n)) atTop
      (𝓝 ((cauchyTrace τ i).functional u)) := by
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete (cauchy_trace_values τ i u)
  have he : z = (cauchyTrace τ i).functional u := tendsto_nhds_unique
    (hz.mono_left (Ultrafilter.of_le atTop))
    (ultraTraceValue_tendsto (fun _ : ℕ => τ i) (Ultrafilter.of atTop) u.1)
  exact he ▸ hz


-- @@ L903-912 verbatim
lemma cauchyTrace_null (i : I) (u : familyCauchyAlgebra τ)
    (hu : u ∈ (familyCauchyNullIdeal τ).ideal) :
    (cauchyTrace τ i).functional u = 0 := by
  have hmem : u.1 ∈ (familyNullIdeal τ atTop).ideal := hu
  have hn := (familyNull_mem τ atTop u.1).mp hmem
  have ht : Tendsto (fun n : ℕ => (τ i).functional (u.1 n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      (trace_norm_le_twoNorm (τ i) _).trans (traceTwoNorm_le_family τ i _)) hn
  exact tendsto_nhds_unique (cauchyTrace_tendsto τ i u) ht


-- @@ L914-915 verbatim
def completionTrace (i : I) : TracialState (UniformTracialCompletion τ) :=
  (familyCauchyNullIdeal τ).descendedTrace (cauchyTrace τ i) (cauchyTrace_null τ i)


-- @@ L917-918 verbatim
def boundedFamilyConstant {X : Type uX} (a : D) : lp (fun _ : X => D) ∞ :=
  ⟨fun _ => a, memℓp_infty_iff.mpr ⟨‖a‖,by rintro _ ⟨n,rfl⟩; exact le_rfl⟩⟩


-- @@ L920-921 verbatim
def cauchyConstant (a : D) : familyCauchyAlgebra τ :=
  ⟨boundedFamilyConstant a, isFamilyCauchy_const τ a⟩


-- @@ L923-930 verbatim
def completionMap : D →⋆ₐ[ℂ] UniformTracialCompletion τ where
  toFun a := (familyCauchyNullIdeal τ).quotientMap (cauchyConstant τ a)
  map_zero' := (familyCauchyNullIdeal τ).quotientMap.map_zero
  map_one' := (familyCauchyNullIdeal τ).quotientMap.map_one
  map_add' a b := (familyCauchyNullIdeal τ).quotientMap.map_add (cauchyConstant τ a) (cauchyConstant τ b)
  map_mul' a b := (familyCauchyNullIdeal τ).quotientMap.map_mul (cauchyConstant τ a) (cauchyConstant τ b)
  commutes' z := (familyCauchyNullIdeal τ).quotientMap.commutes z
  map_star' a := (familyCauchyNullIdeal τ).quotientMap_star (cauchyConstant τ a)


-- @@ L932-932 verbatim
end


-- @@ L934-934 verbatim
section


-- @@ L936-936 verbatim
open Pureness Filter


-- @@ L938-938 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L940-940 verbatim
variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L942-942 verbatim
variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]


-- @@ L944-950 verbatim
instance completionNontrivial : Nontrivial (UniformTracialCompletion τ) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  have he := congrArg (completionTrace τ i).functional h
  rw [(completionTrace τ i).normalized, map_zero] at he
  exact one_ne_zero he


-- @@ L952-952 verbatim
end


-- @@ L954-954 verbatim
open Pureness Filter


-- @@ L956-956 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L958-958 verbatim
variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L960-960 verbatim
variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)


-- @@ L962-971 verbatim
def familyUltrapowerMap : D →⋆ₐ[ℂ] FamilyUltrapower τ U where
  toFun a := (familyNullIdeal τ (U : Filter X)).quotientMap (boundedFamilyConstant a)
  map_zero' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_zero
  map_one' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_one
  map_add' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_add
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  map_mul' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_mul
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  commutes' z := (familyNullIdeal τ (U : Filter X)).quotientMap.commutes z
  map_star' a := (familyNullIdeal τ (U : Filter X)).quotientMap_star (boundedFamilyConstant a)


-- @@ L973-973 verbatim
end CurrentMain


-- @@ L975-975 verbatim
namespace Pureness


-- @@ L977-977 verbatim
open Filter Topology


-- @@ L979-979 verbatim
variable {A : Type uA} [NormedRing A]


-- @@ L981-982 verbatim
def TopologicallySimple (A : Type uA) [NormedRing A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤


-- @@ L984-984 verbatim
end Pureness


-- @@ L986-986 verbatim
end


-- @@ L988-988 verbatim
namespace CurrentMain


-- @@ L990-990 verbatim
open Pureness Filter


-- @@ L992-994 verbatim
def StablyFinite (A : Type uA) [CStarAlgebra A] : Prop :=
  ∀ n : ℕ, ∀ v : CStarMatrix (Fin n) (Fin n) A,
    star v*v = 1 → v*star v = 1


-- @@ L996-1008 verbatim
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


-- @@ L1010-1010 verbatim
end CurrentMain


-- @@ L1012-1012 verbatim
end


-- @@ L1014-1014 verbatim
end OAI
