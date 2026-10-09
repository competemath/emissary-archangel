import OAI.Analysis.TracialSplitting.CoefficientApproximation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe uA


-- @@ L9-9 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L11-11 verbatim
open UniformSpace.Completion


-- @@ L13-13 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L15-15 verbatim
open scoped TensorProduct InnerProductSpace


-- @@ L17-17 verbatim
open UniformSpace.Completion


-- @@ L19-19 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L21-21 verbatim
open UniformSpace.Completion


-- @@ L23-23 verbatim
open scoped ComplexOrder TensorProduct InnerProductSpace


-- @@ L25-25 verbatim
open UniformSpace.Completion UnitalTomsWinter


-- @@ L27-27 verbatim
open scoped ComplexOrder TensorProduct InnerProductSpace


-- @@ L29-29 verbatim
open Pureness UnitalTomsWinter


-- @@ L31-31 verbatim
open scoped Pointwise


-- @@ L33-33 verbatim
open scoped ComplexOrder


-- @@ L35-35 verbatim
open scoped ComplexOrder


-- @@ L37-37 verbatim
namespace Pureness


-- @@ L39-39 verbatim
section


-- @@ L41-41 verbatim
open scoped ComplexOrder


-- @@ L43-43 verbatim
open Topology


-- @@ L45-45 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L47-61 verbatim
lemma TracialState.norm_apply_le_four (τ : TracialState A) (a : A) :
    ‖τ.functional a‖ ≤ 4 * ‖a‖ := by
  obtain ⟨y, hypos, hynorm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg a
  nth_rw 1 [hy]
  simp only [map_sum, map_smul]
  apply (norm_sum_le _ _).trans
  simp only [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
  calc
    _ ≤ ∑ i : Fin 4, ‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hb := τ.functional.norm_apply_le_of_nonneg (y i) (hypos i)
      rw [τ.normalized, norm_one, one_mul] at hb
      exact hb.trans (hynorm i)
    _ = _ := by simp


-- @@ L63-65 verbatim
noncomputable def TracialState.toWeakDual (τ : TracialState A) : WeakDual ℂ A :=
  StrongDual.toWeakDual
    { toLinearMap := τ.functional.toLinearMap, cont := map_continuous τ.functional }


-- @@ L67-68 verbatim
@[simp] lemma TracialState.toWeakDual_apply (τ : TracialState A) (a : A) :
    τ.toWeakDual a = τ.functional a := rfl


-- @@ L70-76 verbatim
lemma TracialState.toWeakDual_injective : Function.Injective (TracialState.toWeakDual (A := A)) := by
  intro τ ρ h
  have heq : τ.functional = ρ.functional := PositiveLinearMap.ext
    (fun a => congrArg (fun f : WeakDual ℂ A => f a) h)
  cases τ
  cases ρ
  congr


-- @@ L78-79 verbatim
noncomputable instance : TopologicalSpace (TracialState A) :=
  TopologicalSpace.induced TracialState.toWeakDual inferInstance


-- @@ L81-83 verbatim
lemma TracialState.isEmbedding_toWeakDual :
    Topology.IsEmbedding (TracialState.toWeakDual (A := A)) :=
  TracialState.toWeakDual_injective.isEmbedding_induced


-- @@ L85-86 verbatim
noncomputable def tracialStateCarrier : Set (WeakDual ℂ A) :=
  {f | f 1 = 1 ∧ (∀ a, 0 ≤ a → 0 ≤ f a) ∧ ∀ a b, f (a * b) = f (b * a)}


-- @@ L88-99 verbatim
noncomputable def tracialStateFromWeakDual (f : WeakDual ℂ A) (hf : f ∈ tracialStateCarrier) :
    TracialState A where
  functional :=
    { f.toStrongDual.toLinearMap with
      monotone' := by
        intro a b hab
        change f a ≤ f b
        apply sub_nonneg.mp
        rw [← map_sub]
        exact hf.2.1 (b - a) (sub_nonneg.mpr hab) }
  normalized := hf.1
  tracial := hf.2.2


-- @@ L101-109 verbatim
lemma range_tracialState_toWeakDual :
    Set.range (TracialState.toWeakDual (A := A)) = tracialStateCarrier := by
  ext f
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ.normalized, fun a ha => τ.functional.map_nonneg ha, τ.tracial⟩
  · intro hf
    refine ⟨tracialStateFromWeakDual f hf, ?_⟩
    exact DFunLike.ext _ _ (fun a => rfl)


-- @@ L111-131 verbatim
omit [StarOrderedRing A] in
lemma isClosed_tracialStateCarrier : IsClosed (tracialStateCarrier (A := A)) := by
  have hnorm : IsClosed {f : WeakDual ℂ A | f 1 = 1} :=
    isClosed_eq (WeakDual.eval_continuous 1) continuous_const
  have hpos : IsClosed {f : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ f a} := by
    have heq : {f : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ f a} =
        ⋂ a : A, ⋂ (_ : 0 ≤ a), {f : WeakDual ℂ A | 0 ≤ f a} := by
      ext f
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact isClosed_iInter fun a => isClosed_iInter fun _ =>
      isClosed_le continuous_const (WeakDual.eval_continuous a)
  have htrace : IsClosed {f : WeakDual ℂ A | ∀ a b, f (a * b) = f (b * a)} := by
    have heq : {f : WeakDual ℂ A | ∀ a b, f (a * b) = f (b * a)} =
        ⋂ a : A, ⋂ b : A, {f : WeakDual ℂ A | f (a * b) = f (b * a)} := by
      ext f
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (WeakDual.eval_continuous (a * b)) (WeakDual.eval_continuous (b * a))
  exact hnorm.inter (hpos.inter htrace)


-- @@ L133-141 verbatim
lemma isCompact_tracialStateCarrier : IsCompact (tracialStateCarrier (A := A)) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 4).of_isClosed_subset
    isClosed_tracialStateCarrier
  intro f hf
  change f.toStrongDual ∈ Metric.closedBall 0 4
  rw [Metric.mem_closedBall, dist_zero_right]
  apply ContinuousLinearMap.opNorm_le_bound f.toStrongDual (by norm_num)
  intro a
  exact (tracialStateFromWeakDual f hf).norm_apply_le_four a


-- @@ L143-146 verbatim
noncomputable instance : CompactSpace (TracialState A) := by
  constructor
  apply TracialState.isEmbedding_toWeakDual.isCompact_iff.mpr
  simpa only [Set.image_univ, range_tracialState_toWeakDual] using isCompact_tracialStateCarrier (A := A)


-- @@ L148-150 verbatim
lemma TracialState.continuous_eval (a : A) :
    Continuous (fun τ : TracialState A => τ.functional a) :=
  (WeakDual.eval_continuous a).comp TracialState.isEmbedding_toWeakDual.continuous


-- @@ L152-152 verbatim
theorem isCompact_tracialState_univ : IsCompact (Set.univ : Set (TracialState A)) := isCompact_univ


-- @@ L154-154 verbatim
end


-- @@ L156-156 verbatim
open scoped ComplexOrder


-- @@ L158-158 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L160-171 verbatim
omit [StarOrderedRing A] in
lemma convex_tracialStateCarrier : Convex ℝ (tracialStateCarrier (A := A)) := by
  intro f hf g hg r s hr hs hrs
  refine ⟨?_,?_,?_⟩
  · change r • f 1 + s • g 1 = 1
    rw [hf.1,hg.1,← add_smul,hrs,one_smul]
  · intro a ha
    change 0 ≤ r • f a + s • g a
    exact add_nonneg (smul_nonneg hr (hf.2.1 a ha)) (smul_nonneg hs (hg.2.1 a ha))
  · intro a b
    change r • f (a*b) + s • g (a*b) = r • f (b*a) + s • g (b*a)
    rw [hf.2.2,hg.2.2]


-- @@ L173-173 verbatim
end Pureness


-- @@ L175-175 verbatim
namespace NuclearTrace


-- @@ L177-177 verbatim
open scoped ComplexOrder


-- @@ L179-179 verbatim
variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L181-181 verbatim
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]


-- @@ L183-183 verbatim
variable [Fintype I]


-- @@ L185-193 verbatim
def traceTupleCost (x z : I → selfAdjoint A) : WeakDual ℂ A →ₗ[ℝ] ℝ where
  toFun τ := ∑ i, (τ (CFC.abs ((x i : A) - z i))).re
  map_add' τ ρ := by
    change (∑ i, (τ (CFC.abs ((x i : A) - z i)) + ρ (CFC.abs ((x i : A) - z i))).re) = _
    simp only [Complex.add_re,Finset.sum_add_distrib]
  map_smul' r τ := by
    change (∑ i, (r • τ (CFC.abs ((x i : A) - z i))).re) =
      r • ∑ i, (τ (CFC.abs ((x i : A) - z i))).re
    simp only [Complex.smul_re, Finset.smul_sum]


-- @@ L195-199 verbatim
lemma traceTupleCost_continuous (x z : I → selfAdjoint A) :
    Continuous (traceTupleCost x z) := by
  apply continuous_finsetSum
  intro i _
  exact Complex.continuous_re.comp (WeakDual.eval_continuous _)


-- @@ L201-204 verbatim
lemma traceTupleCost_eq (x z : I → selfAdjoint A) (τ : Pureness.TracialState A) :
    traceTupleCost x z τ.toWeakDual = tracialTupleSeminorm τ (x-z) := by
  rw [tracialTupleSeminorm_apply]
  rfl


-- @@ L206-210 verbatim
lemma traceTupleCost_continuous_right (x : I → selfAdjoint A)
    (τ : Pureness.TracialState A) :
    Continuous (fun z => traceTupleCost x z τ.toWeakDual) := by
  simp only [traceTupleCost_eq]
  exact (tracialTupleSeminorm_continuous τ).comp (continuous_const.sub continuous_id)


-- @@ L212-224 verbatim
lemma traceTupleCost_convex_right (x : I → selfAdjoint A)
    (τ : Pureness.TracialState A) {Y : Set (I → selfAdjoint A)} (hY : Convex ℝ Y) :
    ConvexOn ℝ Y (fun z => traceTupleCost x z τ.toWeakDual) := by
  refine ⟨hY,?_⟩
  intro y hy z hz r s hr hs hrs
  simp only [traceTupleCost_eq]
  have he : x - (r • y + s • z) = r • (x-y) + s • (x-z) := by
    rw [smul_sub,smul_sub]
    calc
      x - (r • y + s • z) = (r+s) • x - (r • y + s • z) := by rw [hrs,one_smul]
      _ = r • x - r • y + (s • x - s • z) := by rw [add_smul]; abel
  rw [he]
  exact (tracialTupleSeminorm τ).convexOn.2 (Set.mem_univ _) (Set.mem_univ _) hr hs hrs


-- @@ L226-264 verbatim
theorem nuclear_uniform_tracial_coefficient_approximation
    (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (hT : Nonempty (Pureness.TracialState A)) (x : I → selfAdjoint A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L ∈ coefficientCone α, ∀ τ : Pureness.TracialState A,
      ∑ i, CurrentMain.traceOneNorm τ ((x i : A) - L (x i)) < ε := by
  classical
  let Y := (coefficientCone α).map (evalTuple x)
  let X := Pureness.tracialStateCarrier (A := A)
  have hXne : X.Nonempty := by
    obtain ⟨τ⟩ := hT
    exact ⟨τ.toWeakDual,τ.normalized,fun a ha => τ.functional.map_nonneg ha,τ.tracial⟩
  have hcost (τ : WeakDual ℂ A) (hτ : τ ∈ X) :
      (Pureness.tracialStateFromWeakDual τ hτ).toWeakDual = τ := by
    exact DFunLike.ext _ _ (fun _ => rfl)
  obtain ⟨z,hz,hall⟩ := @compact_convex_uniform_cost
    (WeakDual ℂ A) (I → selfAdjoint A) inferInstance inferInstance inferInstance
    inferInstance (WeakDual.instContinuousSMul ℝ) inferInstance inferInstance inferInstance
    inferInstance inferInstance X Y hXne
    Pureness.isCompact_tracialStateCarrier Pureness.convex_tracialStateCarrier
    Y.convex (fun τ z => traceTupleCost x z τ)
    (fun z _ => traceTupleCost_continuous x z)
    (fun z _ => (traceTupleCost x z).concaveOn Pureness.convex_tracialStateCarrier)
    (fun τ hτ => by
      rw [← hcost τ hτ]
      exact (traceTupleCost_continuous_right x _).continuousOn)
    (fun τ hτ => by
      rw [← hcost τ hτ]
      exact traceTupleCost_convex_right x _ Y.convex)
    (ε := ε) (by
      intro τ hτ
      obtain ⟨L,hL,hclose⟩ := nuclear_tracial_coefficient_approximation hA α hα
        (Pureness.tracialStateFromWeakDual τ hτ) x hε
      refine ⟨evalTuple x L,⟨L,hL,rfl⟩,?_⟩
      exact hclose)
  obtain ⟨L,hL,rfl⟩ := hz
  refine ⟨L,hL,fun τ => ?_⟩
  exact hall τ.toWeakDual ⟨τ.normalized,fun a ha => τ.functional.map_nonneg ha,τ.tracial⟩


-- @@ L266-266 verbatim
end NuclearTrace


-- @@ L268-268 verbatim
end


-- @@ L270-270 verbatim
end OAI
