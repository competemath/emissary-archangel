import OAI.Analysis.RecursivePotentials.VariableCompletion


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uIndex uSpace uOther uDomain uTarget uFiber


-- @@ L7-7 verbatim
open scoped BigOperators


-- @@ L9-9 verbatim
namespace RecursivePotentials


-- @@ L11-11 verbatim
open Filter Topology


-- @@ L13-13 verbatim
open Filter Topology


-- @@ L15-15 verbatim
open scoped ENNReal


-- @@ L17-17 verbatim
open UniformSpace


-- @@ L19-19 verbatim
open Filter


-- @@ L21-21 verbatim
open scoped Topology


-- @@ L23-23 verbatim
open Filter Topology TopologicalSpace


-- @@ L25-25 verbatim
open scoped ENNReal


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace LpSupport


-- @@ L31-33 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
  [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]


-- @@ L35-52 verbatim
lemma separable [Countable ι] [∀ i, SeparableSpace (E i)] (hp : p ≠ ⊤) :
    SeparableSpace (↥(lp E p)) := by
  let S : Set (↥(lp E p)) := ⋃ i, Set.range (lp.single p i : E i → lp E p)
  have hS : TopologicalSpace.IsSeparable S := TopologicalSpace.IsSeparable.iUnion
    (fun i => TopologicalSpace.isSeparable_range (lp.singleContinuousLinearMap ℝ E p i).continuous)
  let V : Submodule ℝ (↥(lp E p)) := Submodule.span ℝ S
  have hsingle (i : ι) (x : E i) : lp.single p i x ∈ V :=
    Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, ⟨x,rfl⟩⟩)
  have htop : V.topologicalClosure = ⊤ := by
    apply top_unique
    intro x hx
    exact V.isClosed_topologicalClosure.mem_of_tendsto (lp.hasSum_single hp x)
      (Filter.Eventually.of_forall fun J => V.topologicalClosure.sum_mem
        fun i hi => V.le_topologicalClosure (hsingle i (x i)))
  have hh := (hS.span (R := ℝ)).closure
  change TopologicalSpace.IsSeparable (V.topologicalClosure : Set (↥(lp E p))) at hh
  rw [htop] at hh
  exact TopologicalSpace.isSeparable_univ_iff.mp (by simpa using hh)


-- @@ L54-54 verbatim
end LpSupport


-- @@ L56-67 verbatim
lemma dual_separable_of_equiv {E : Type uSpace} {F : Type uOther} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [SeparableSpace (E →L[ℝ] ℝ)]
    (e : E ≃L[ℝ] F) : SeparableSpace (F →L[ℝ] ℝ) := by
  let D : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ F E ℝ).flip e.symm.toContinuousLinearMap
  have hD : Function.Surjective D := by
    intro f
    refine ⟨f.comp e.toContinuousLinearMap, ?_⟩
    ext y
    change f (e (e.symm y)) = f y
    rw [e.apply_symm_apply]
  exact hD.denseRange.separableSpace D.continuous


-- @@ L69-71 verbatim
structure PowerExponent where
  val : ℝ
  one_lt : 1 < val


-- @@ L73-73 verbatim
namespace PowerExponent


-- @@ L75-75 verbatim
lemma pos (p : PowerExponent) : 0 < p.val := zero_lt_one.trans p.one_lt


-- @@ L77-77 verbatim
lemma ne_zero (p : PowerExponent) : p.val ≠ 0 := p.pos.ne'


-- @@ L79-80 verbatim
instance (p : PowerExponent) : Fact (1 ≤ ENNReal.ofReal p.val) :=
  ⟨by simpa using ENNReal.ofReal_le_ofReal p.one_lt.le⟩


-- @@ L82-83 verbatim
def conjugate (p : PowerExponent) : PowerExponent :=
  ⟨Real.conjExponent p.val, (Real.HolderConjugate.conjExponent p.one_lt).symm.lt⟩


-- @@ L85-86 verbatim
lemma holder (p : PowerExponent) : p.val.HolderConjugate p.conjugate.val :=
  Real.HolderConjugate.conjExponent p.one_lt


-- @@ L88-88 verbatim
end PowerExponent


-- @@ L90-90 verbatim
namespace ScalarLp


-- @@ L92-92 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι]


-- @@ L94-94 verbatim
abbrev Space (ι : Type uIndex) (p : PowerExponent) := ↥(lp (fun _ : ι => ℝ) (ENNReal.ofReal p.val))


-- @@ L96-96 verbatim
variable (p q : PowerExponent) (hpq : p.val.HolderConjugate q.val)


-- @@ L98-102 verbatim
def pairing : Space ι q →L[ℝ] (Space ι p →L[ℝ] ℝ) := by
  let := hpq.symm.ennrealOfReal
  exact lp.dualPairing (ENNReal.ofReal q.val) (ENNReal.ofReal p.val)
    (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)


-- @@ L104-106 verbatim
lemma pairing_apply {ι : Type uIndex} [DecidableEq ι] (p q : PowerExponent)
    (hpq : p.val.HolderConjugate q.val) (y : Space ι q) (x : Space ι p) :
    pairing p q hpq y x = ∑' i, y i * x i := rfl


-- @@ L108-112 verbatim
@[simp] lemma pairing_single_right (y : Space ι q) (i : ι) (a : ℝ) :
    pairing p q hpq y (lp.single (ENNReal.ofReal p.val) i a) = y i * a := by
  rw [pairing_apply, tsum_eq_single i, lp.single_apply_self]
  intro j hj
  rw [lp.single_apply_ne _ _ _ hj, mul_zero]


-- @@ L114-118 verbatim
@[simp] lemma pairing_single_left (i : ι) (a : ℝ) (x : Space ι p) :
    pairing p q hpq (lp.single (ENNReal.ofReal q.val) i a) x = a * x i := by
  rw [pairing_apply, tsum_eq_single i, lp.single_apply_self]
  intro j hj
  rw [lp.single_apply_ne _ _ _ hj, zero_mul]


-- @@ L120-121 verbatim
def coefficient (f : Space ι p →L[ℝ] ℝ) (i : ι) : ℝ :=
  f (lp.single (ENNReal.ofReal p.val) i 1)


-- @@ L123-128 verbatim
lemma apply_single (f : Space ι p →L[ℝ] ℝ) (i : ι) (a : ℝ) :
    f (lp.single (ENNReal.ofReal p.val) i a) = a * coefficient p f i := by
  have hh := lp.single_smul (E := fun _ : ι => ℝ) (ENNReal.ofReal p.val) i a (1:ℝ)
  simp only [smul_eq_mul, mul_one] at hh
  rw [hh, map_smul, smul_eq_mul]
  rfl


-- @@ L130-130 verbatim
def norming (a r : ℝ) : ℝ := (if 0 ≤ a then 1 else -1) * |a| ^ (r-1)


-- @@ L132-134 verbatim
lemma abs_norming (a r : ℝ) : |norming a r| = |a| ^ (r-1) := by
  unfold norming
  split <;> simp [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg a) _)]


-- @@ L136-150 verbatim
lemma norming_mul (a : ℝ) : norming a q.val * a = |a| ^ q.val := by
  by_cases ha : a = 0
  · simp [ha, norming, Real.zero_rpow q.ne_zero]
  have hab : 0 < |a| := abs_pos.mpr ha
  have he : |a| ^ q.val = |a| ^ (q.val-1) * |a| := by
    calc |a| ^ q.val = |a| ^ ((q.val-1)+1) := by congr 1; ring
         _ = _ := by rw [Real.rpow_add hab, Real.rpow_one]
  rw [he]
  unfold norming
  split
  · rename_i ha
    simp only [one_mul, abs_of_nonneg ha]
  · rename_i ha
    rw [abs_of_neg (lt_of_not_ge ha)]
    ring


-- @@ L152-152 verbatim
include hpq


-- @@ L154-155 verbatim
lemma norming_rpow (a : ℝ) : |norming a q.val| ^ p.val = |a| ^ q.val := by
  rw [abs_norming, ← Real.rpow_mul (abs_nonneg a), hpq.symm.sub_one_mul_conj]


-- @@ L157-192 verbatim
lemma restriction_bound (f : Space ι p →L[ℝ] ℝ) (S : Finset ι) :
    ∑ i ∈ S, |coefficient p f i| ^ q.val ≤ ‖f‖ ^ q.val := by
  let A := ∑ i ∈ S, |coefficient p f i| ^ q.val
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  let v : Space ι p := ∑ i ∈ S, lp.single (ENNReal.ofReal p.val) i (norming (coefficient p f i) q.val)
  have hv : ‖v‖ ^ p.val = A := by
    have hh := lp.norm_sum_single (E := fun _ : ι => ℝ) (p := ENNReal.ofReal p.val)
      (by simpa only [ENNReal.toReal_ofReal p.pos.le] using p.pos)
      (fun i => norming (coefficient p f i) q.val) S
    simp only [ENNReal.toReal_ofReal p.pos.le, Real.norm_eq_abs, norming_rpow p q hpq] at hh
    exact hh
  have hfv : f v = A := by
    dsimp [v,A]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [apply_single, norming_mul]
  have hv' : ‖v‖ = A ^ (1/p.val) := by
    rw [← hv, ← Real.rpow_mul (norm_nonneg _)]
    simp [p.ne_zero]
  have hf : A ≤ ‖f‖ * A ^ (1/p.val) := by
    calc A = f v := hfv.symm
         _ ≤ ‖f‖ * ‖v‖ := (le_abs_self _).trans (f.le_opNorm v)
         _ = _ := by rw [hv']
  change A ≤ ‖f‖ ^ q.val
  by_cases hz : A = 0
  · rw [hz]; positivity
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
  have hsplit : A = A ^ (1/q.val) * A ^ (1/p.val) := by
    rw [← Real.rpow_add hAp]
    have he : 1/q.val + 1/p.val = 1 := by simpa only [one_div] using hpq.symm.inv_add_inv_eq_one
    rw [he, Real.rpow_one]
  have hb : A ^ (1/q.val) ≤ ‖f‖ :=
    (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hAp (1/p.val))).mp (hsplit.symm.trans_le hf)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hA _) hb q.pos.le
  simpa only [← Real.rpow_mul hA, one_div_mul_cancel q.ne_zero, Real.rpow_one] using hh


-- @@ L194-198 verbatim
lemma restriction_mem (f : Space ι p →L[ℝ] ℝ) :
    Memℓp (coefficient p f) (ENNReal.ofReal q.val) := by
  apply memℓp_gen' (C := ‖f‖ ^ q.val)
  intro S
  simpa only [ENNReal.toReal_ofReal q.pos.le, Real.norm_eq_abs] using restriction_bound p q hpq f S


-- @@ L200-201 verbatim
def restrict (f : Space ι p →L[ℝ] ℝ) : Space ι q :=
  ⟨coefficient p f, restriction_mem p q hpq f⟩


-- @@ L203-204 verbatim
@[simp] lemma restrict_apply (f : Space ι p →L[ℝ] ℝ) (i : ι) :
    restrict p q hpq f i = coefficient p f i := rfl


-- @@ L206-212 verbatim
lemma pairing_restrict (f : Space ι p →L[ℝ] ℝ) : pairing p q hpq (restrict p q hpq f) = f := by
  apply lp.ext_continuousLinearMap ENNReal.ofReal_ne_top
  intro i
  apply ContinuousLinearMap.ext
  intro a
  change pairing p q hpq (restrict p q hpq f) (lp.single _ i a) = f (lp.single _ i a)
  rw [pairing_single_right, restrict_apply, apply_single, mul_comm]


-- @@ L214-233 verbatim
theorem isReflexive : IsReflexive (Space ι p) := by
  rw [isReflexive_iff]
  intro F
  let G : Space ι q →L[ℝ] ℝ := F.comp (pairing p q hpq)
  let x := restrict q p hpq.symm G
  have hG : G = (pairing p q hpq).flip x := by
    apply lp.ext_continuousLinearMap ENNReal.ofReal_ne_top
    intro i
    apply ContinuousLinearMap.ext
    intro a
    change G (lp.single _ i a) = pairing p q hpq (lp.single _ i a) x
    rw [apply_single]

    rw [pairing_single_left]
    rfl
  refine ⟨x, ?_⟩
  intro f
  have hh := congrArg (fun H : Space ι q →L[ℝ] ℝ => H (restrict p q hpq f)) hG
  change F (pairing p q hpq (restrict p q hpq f)) = pairing p q hpq (restrict p q hpq f) x at hh
  simpa only [pairing_restrict] using hh


-- @@ L235-238 verbatim
omit hpq in
lemma separable {ι : Type uIndex} [DecidableEq ι] (p q : PowerExponent)
    (_hpq : p.val.HolderConjugate q.val) [Countable ι] : SeparableSpace (Space ι p) :=
  LpSupport.separable (fun _ : ι => ℝ) (ENNReal.ofReal p.val) ENNReal.ofReal_ne_top


-- @@ L240-244 verbatim
lemma dual_separable [Countable ι] : SeparableSpace (Space ι p →L[ℝ] ℝ) := by
  let : SeparableSpace (Space ι q) := separable q p hpq.symm
  have hh : Function.Surjective (pairing p q hpq (ι := ι)) :=
    fun f => ⟨restrict p q hpq f, pairing_restrict p q hpq f⟩
  exact hh.denseRange.separableSpace (pairing p q hpq).continuous


-- @@ L246-246 verbatim
end ScalarLp


-- @@ L248-248 verbatim
end


-- @@ L250-250 verbatim
namespace AggregationVector


-- @@ L252-252 verbatim
noncomputable section


-- @@ L254-254 verbatim
open scoped ENNReal


-- @@ L256-257 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)


-- @@ L259-264 verbatim
lemma toLpLinear_apply (v : AggregationVector T e) (s : ι) : toLpLinear T e v s = v s := by
  change (∑ i ∈ (show ι →₀ ℝ from v).support, lp.single _ i (v i)) s = v s
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  split_ifs with hs
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hs).symm


-- @@ L266-266 verbatim
end


-- @@ L268-268 verbatim
end AggregationVector


-- @@ L270-270 verbatim
namespace AggregationSpace


-- @@ L272-272 verbatim
noncomputable section


-- @@ L274-274 verbatim
open AggregationVector


-- @@ L276-277 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)


-- @@ L279-283 verbatim
lemma lpEquiv_coe (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (v : AggregationVector T e) :
    lpEquiv T e hp hstep h hh (v : AggregationSpace T e) = toLpLinear T e v :=
  ContinuousLinearMap.fromCompletion_apply_coe _ v


-- @@ L285-291 verbatim
lemma lpEquiv_apply (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (x : AggregationSpace T e) (s : ι) :
    lpEquiv T e hp hstep h hh x s = coordinate T e s x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq; exact ((lp.evalCLM ℝ (fun _ : ι => ℝ) (ENNReal.ofReal e.val) s).comp (lpEquiv T e hp hstep h hh).toContinuousLinearMap).continuous; exact (coordinate T e s).continuous
  | ih v => rw [lpEquiv_coe,toLpLinear_apply,coordinate_coe]


-- @@ L293-312 verbatim
theorem lp_comparisons (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (x : AggregationSpace T e) :
    (h+1:ℝ)^(-1/e.val)*‖lpEquiv T e hp hstep h hh x‖ ≤ ‖x‖ ∧
      ‖x‖ ≤ 2*(h+1:ℝ)^(1-1/e.val)*‖lpEquiv T e hp hstep h hh x‖ := by
  have hboth : ‖x‖ ≤ 2*(h+1:ℝ)^(1-1/e.val)*‖lpEquiv T e hp hstep h hh x‖ ∧
      ‖lpEquiv T e hp hstep h hh x‖ ≤ (h+1:ℝ)^(1/e.val)*‖x‖ := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact (isClosed_le continuous_norm
        (continuous_const.mul (lpEquiv T e hp hstep h hh).continuous.norm)).inter
        (isClosed_le (lpEquiv T e hp hstep h hh).continuous.norm
          (continuous_const.mul continuous_norm))
    | ih v => simpa only [lpEquiv_coe,UniformSpace.Completion.norm_coe] using
        AggregationVector.lp_comparisons T e hp hstep h hh v
  refine ⟨?_,hboth.1⟩
  have hl := mul_le_mul_of_nonneg_left hboth.2 (Real.rpow_nonneg (by positivity : (0:ℝ)≤h+1) (-1/e.val))
  have he : (h+1:ℝ)^(-1/e.val) * (h+1:ℝ)^(1/e.val) = 1 := by
    rw [← Real.rpow_add (by positivity : (0:ℝ)<h+1),show -1/e.val+1/e.val=0 by ring,Real.rpow_zero]
  rwa [← mul_assoc,he,one_mul] at hl


-- @@ L314-318 verbatim
theorem finite_height_reflexive (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : IsReflexive (AggregationSpace T e) := by
  let p : PowerExponent := ⟨e.val,hp⟩
  exact (ScalarLp.isReflexive p p.conjugate p.holder (ι := ι)).of_equiv (lpEquiv T e hp hstep h hh).symm


-- @@ L320-325 verbatim
theorem finite_height_dual_separable [Countable ι] (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : SeparableSpace (AggregationSpace T e →L[ℝ] ℝ) := by
  let p : PowerExponent := ⟨e.val,hp⟩
  let : SeparableSpace (ScalarLp.Space ι p →L[ℝ] ℝ) := ScalarLp.dual_separable p p.conjugate p.holder
  exact dual_separable_of_equiv (lpEquiv T e hp hstep h hh).symm


-- @@ L327-327 verbatim
end


-- @@ L329-329 verbatim
end AggregationSpace


-- @@ L331-331 verbatim
end RecursivePotentials


-- @@ L333-333 verbatim
end OAI
