import Mathlib
import OAI.Probability.Subsphere.Models
import OAI.Probability.Subsphere.Estimates.Numerics


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L9-9 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
namespace SubsphereCurrent


-- @@ L13-13 verbatim
section FiniteVersion

-- @@ L14-14 verbatim
variable {X A : Type*} [MeasurableSpace X] [Fintype A] [Nonempty A]

-- @@ L15-15 verbatim
variable {μ : Measure X} (p : X → PMF A)


-- @@ L17-20 verbatim
def borelPMF (hp : ∀ a, AEMeasurable (fun x => p x a) μ) (x : X) : PMF A :=
  if h : ∑ a, (hp a).mk (fun x => p x a) x = 1
  then PMF.ofFintype (fun a => (hp a).mk (fun x => p x a) x) h
  else PMF.pure (Classical.arbitrary A)


-- @@ L22-35 verbatim
lemma measurable_borelPMF (hp : ∀ a, AEMeasurable (fun x => p x a) μ) (a : A) :
    Measurable (fun x => borelPMF p hp x a) := by
  classical
  have hm (b : A) := (hp b).measurable_mk
  have hs : MeasurableSet {x | ∑ b, (hp b).mk (fun x => p x b) x = 1} :=
    measurableSet_eq_fun (Finset.measurable_sum _ (fun b _ => hm b)) measurable_const
  have he : (fun x => borelPMF p hp x a) = fun x =>
      if ∑ b, (hp b).mk (fun x => p x b) x = 1
      then (hp a).mk (fun x => p x a) x else PMF.pure (Classical.arbitrary A) a := by
    funext x
    unfold borelPMF
    split_ifs <;> rfl
  rw [he]
  exact Measurable.ite hs (hm a) measurable_const


-- @@ L37-49 verbatim
lemma borelPMF_ae_eq (hp : ∀ a, AEMeasurable (fun x => p x a) μ) :
    p =ᵐ[μ] borelPMF p hp := by
  classical
  have hc : ∀ᵐ x ∂μ, ∀ a, p x a = (hp a).mk (fun x => p x a) x :=
    ae_all_iff.mpr (fun a => (hp a).ae_eq_mk)
  filter_upwards [hc] with x hx
  have hs : ∑ a, (hp a).mk (fun x => p x a) x = 1 := by
    simp_rw [← hx]
    simpa only [tsum_fintype] using (p x).tsum_coe
  apply PMF.ext
  intro a
  simp only [borelPMF, dite_eq_left hs, PMF.ofFintype_apply]
  exact hx a

-- @@ L50-50 verbatim
end FiniteVersion


-- @@ L52-52 verbatim
namespace KernelLearner


-- @@ L54-59 verbatim
def borelVersion {d M T : ℕ} (L : KernelLearner d M T) (hL : L.CompletedRules) :
    KernelLearner d M T where
  initial := L.initial
  transition t q := borelPMF (L.transition t q) (hL t q)
  output := L.output
  output_probability := L.output_probability


-- @@ L61-64 verbatim
lemma borelVersion_rules {d M T : ℕ} (L : KernelLearner d M T) (hL : L.CompletedRules) :
    (L.borelVersion hL).BorelRules := by
  intro t q a
  exact measurable_borelPMF _ _ a


-- @@ L66-83 verbatim
lemma run_congr {d M T : ℕ} (L K : KernelLearner d M T)
    (hi : L.initial = K.initial) (s : UnitSphere d) (x : Samples d T)
    (ht : ∀ t q (i : Fin T), L.transition t q (x i, ⟪x i,s.val⟫) =
      K.transition t q (x i, ⟪x i,s.val⟫)) (n : ℕ) :
    L.run s x n = K.run s x n := by
  induction n with
  | zero => simp only [run, hi]
  | succ n ih =>
    simp only [run, ih]
    congr 1
    funext a
    cases a with
    | inr a => rfl
    | inl q =>
      dsimp only
      split_ifs
      · rw [ht]
      · rfl


-- @@ L85-102 verbatim
lemma borelVersion_success_ae {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.CompletedRules) (hd : 3 ≤ d) (ε : ℝ) :
    (fun z : UnitSphere d × Samples d T => L.conditionalSuccess ε z.1 z.2) =ᵐ[
      (uniformSphere d).prod (sampleLaw d T)]
    (fun z => (L.borelVersion hL).conditionalSuccess ε z.1 z.2) := by
  let : NeZero d := ⟨by omega⟩
  have hgood : ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)),
      ∀ t q (i : Fin T), L.transition t q (z.2 i, ⟪z.2 i,z.1.val⟫) =
      (L.borelVersion hL).transition t q (z.2 i, ⟪z.2 i,z.1.val⟫) := by
    simp only [ae_all_iff]
    intro t q i
    have he := (SubsphereRegression.sphere_sample_observation_quasi
      (E := Vector d) (by simpa using hd) i).ae (borelPMF_ae_eq (L.transition t q) (hL t q))
    simpa only [borelVersion, real_inner_comm, SubsphereRegression.sphereLaw,
      uniformSphere, sampleLaw, observationReference, SubsphereRegression.Vector] using he
  filter_upwards [hgood] with z hz
  have hr := run_congr L (L.borelVersion hL) rfl z.1 z.2 hz T
  simp only [conditionalSuccess, estimateLaw, terminal, hr, borelVersion]


-- @@ L104-104 verbatim
end KernelLearner

-- @@ L105-105 verbatim
end SubsphereCurrent

-- @@ L106-106 verbatim
end

-- @@ L107-107 verbatim
end

-- @@ L108-108 verbatim
section

-- @@ L109-109 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L110-110 verbatim
open scoped ENNReal NNReal

-- @@ L111-111 verbatim
noncomputable section

-- @@ L112-112 verbatim
namespace SubsphereCurrent


-- @@ L114-115 verbatim
def finiteCDF {n : ℕ} (p : PMF (Fin n)) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if h : j < n then (p ⟨j,h⟩).toReal else 0


-- @@ L117-118 verbatim
lemma finiteCDF_zero {n : ℕ} (p : PMF (Fin n)) : finiteCDF p 0 = 0 := by
  simp [finiteCDF]


-- @@ L120-122 verbatim
lemma finiteCDF_succ {n : ℕ} (p : PMF (Fin n)) (i : Fin n) :
    finiteCDF p (i.val + 1) = finiteCDF p i.val + (p i).toReal := by
  simp [finiteCDF, Finset.sum_range_succ, i.isLt]


-- @@ L124-128 verbatim
lemma finiteCDF_mono {n : ℕ} (p : PMF (Fin n)) : Monotone (finiteCDF p) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
  intro k _ _
  split_ifs <;> positivity


-- @@ L130-136 verbatim
lemma finiteCDF_total {n : ℕ} (p : PMF (Fin n)) : finiteCDF p n = 1 := by
  have hs : ∑ i : Fin n, p i = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  have ht : ∑ i : Fin n, (p i).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i), hs, ENNReal.toReal_one]
  rw [← ht]
  simpa [finiteCDF] using (Fin.sum_univ_eq_sum_range
    (fun j => if h : j < n then (p ⟨j,h⟩).toReal else 0) n).symm


-- @@ L138-147 verbatim
lemma finiteCDF_interval_unique {n : ℕ} (p : PMF (Fin n)) {i j : Fin n} {r : ℝ}
    (hi : finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1))
    (hj : finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1)) : i = j := by
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with h | h | h
  · have := finiteCDF_mono p (show i.val+1 ≤ j.val by omega)
    linarith
  · exact h
  · have := finiteCDF_mono p (show j.val+1 ≤ i.val by omega)
    linarith


-- @@ L149-163 verbatim
lemma finiteCDF_interval_exists {n : ℕ} (p : PMF (Fin n)) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ i : Fin n, finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1) := by
  have hex : ∃ k : ℕ, r < finiteCDF p k := ⟨n, by rwa [finiteCDF_total]⟩
  have hpos : 0 < Nat.find hex := by
    by_contra! h
    have hz : Nat.find hex = 0 := by omega
    have hh := Nat.find_spec hex
    rw [hz, finiteCDF_zero] at hh
    linarith
  have hle : Nat.find hex ≤ n := Nat.find_min' hex (by rwa [finiteCDF_total])
  refine ⟨⟨Nat.find hex - 1, by omega⟩, ?_, ?_⟩
  · change finiteCDF p (Nat.find hex - 1) ≤ r
    exact le_of_not_gt (Nat.find_min hex (by omega))
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] using Nat.find_spec hex


-- @@ L165-167 verbatim
def finiteSample {n : ℕ} [NeZero n] (p : PMF (Fin n)) (r : ℝ) : Fin n :=
  if h : ∃ i : Fin n, finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1)
  then h.choose else 0


-- @@ L169-174 verbatim
lemma finiteSample_eq_on_interval {n : ℕ} [NeZero n] (p : PMF (Fin n))
    (i : Fin n) {r : ℝ} (hi : finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1)) :
    finiteSample p r = i := by
  have hex : ∃ j : Fin n, finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1) := ⟨i, hi⟩
  rw [finiteSample, dite_eq_left hex]
  exact finiteCDF_interval_unique p hex.choose_spec hi


-- @@ L176-195 verbatim
lemma finiteSample_eq_iff {n : ℕ} [NeZero n] (p : PMF (Fin n)) (i : Fin n) (r : ℝ) :
    finiteSample p r = i ↔
      (finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1)) ∨
      (i = 0 ∧ ¬ ∃ j : Fin n, finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1)) := by
  by_cases hex : ∃ j : Fin n, finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1)
  · constructor
    · intro h
      left
      have hc : hex.choose = i := by simpa only [finiteSample, dite_eq_left hex] using h
      simpa only [hc] using hex.choose_spec
    · rintro (h | ⟨_, h⟩)
      · exact finiteSample_eq_on_interval p i h
      · exact (h hex).elim
  · constructor
    · intro hi
      right
      exact ⟨(by simpa [finiteSample, hex] using hi.symm), hex⟩
    · rintro (hi | ⟨hi, _⟩)
      · exact (hex ⟨i, hi⟩).elim
      · simp [finiteSample, hex, hi]


-- @@ L197-205 verbatim
lemma measurable_finiteCDF {X : Type*} [MeasurableSpace X] {n : ℕ}
    {p : X → PMF (Fin n)} (hp : ∀ i, Measurable (fun x => p x i)) (k : ℕ) :
    Measurable (fun x => finiteCDF (p x) k) := by
  unfold finiteCDF
  apply Finset.measurable_sum
  intro j _
  split_ifs
  · exact (hp _).ennreal_toReal
  · exact measurable_const


-- @@ L207-221 verbatim
lemma measurable_finiteSample {X : Type*} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {p : X → PMF (Fin n)} {r : X → ℝ}
    (hp : ∀ i, Measurable (fun x => p x i)) (hr : Measurable r) :
    Measurable (fun x => finiteSample (p x) (r x)) := by
  apply measurable_to_countable'
  intro i
  simp only [Set.preimage, Set.mem_singleton_iff, finiteSample_eq_iff]
  have hm (j : Fin n) : MeasurableSet
      {x | finiteCDF (p x) j.val ≤ r x ∧ r x < finiteCDF (p x) (j.val+1)} :=
    (measurableSet_le (measurable_finiteCDF hp _) hr).inter
      (measurableSet_lt hr (measurable_finiteCDF hp _))
  have he : MeasurableSet {x | ∃ j : Fin n, finiteCDF (p x) j.val ≤ r x ∧
      r x < finiteCDF (p x) (j.val+1)} := by
    simpa only [Set.ofPred_exists] using MeasurableSet.iUnion hm
  exact (hm i).union ((MeasurableSet.const _).inter he.compl)


-- @@ L223-223 verbatim
def coinLaw : Measure ℝ := volume.restrict (Ico 0 1)


-- @@ L225-227 verbatim
instance coinLaw_probability : IsProbabilityMeasure coinLaw := by
  constructor
  simp [coinLaw, Real.volume_Ico]


-- @@ L229-258 verbatim
lemma finiteSample_map {n : ℕ} [NeZero n] (p : PMF (Fin n)) :
    coinLaw.map (finiteSample p) = p.toMeasure := by
  have hm : Measurable (finiteSample p) :=
    measurable_finiteSample (fun _ => measurable_const) measurable_id
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply hm (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  change volume.restrict (Ico 0 1) ((finiteSample p) ⁻¹' {i}) = p i
  rw [Measure.restrict_apply (hm (measurableSet_singleton i))]
  have he : ((finiteSample p) ⁻¹' {i}) ∩ Ico 0 1 =
      Ico (finiteCDF p i.val) (finiteCDF p (i.val+1)) := by
    ext r
    constructor
    · rintro ⟨he,hr0,hr1⟩
      have hex := finiteCDF_interval_exists p hr0 hr1
      have hs : finiteSample p r = i := he
      rcases (finiteSample_eq_iff p i r).1 hs with hi | hi
      · exact hi
      · exact (hi.2 hex).elim
    · intro hi
      refine ⟨finiteSample_eq_on_interval p i hi, ?_, ?_⟩
      · have hlo : 0 ≤ finiteCDF p i.val := by
          simpa only [finiteCDF_zero] using finiteCDF_mono p (Nat.zero_le i.val)
        exact hlo.trans hi.1
      · have hhi : finiteCDF p (i.val+1) ≤ 1 := by
          simpa only [finiteCDF_total] using finiteCDF_mono p (show i.val+1 ≤ n by omega)
        exact hi.2.trans_le hhi
  rw [he, Real.volume_Ico, finiteCDF_succ]
  simp only [add_sub_cancel_left, ENNReal.ofReal_toReal (p.apply_ne_top i)]


-- @@ L260-267 verbatim
lemma lintegral_finiteSample {n : ℕ} [NeZero n] (p : PMF (Fin n))
    (f : Fin n → ℝ≥0∞) :
    (∫⁻ r, f (finiteSample p r) ∂coinLaw) = ∑ i, p i * f i := by
  have hm : Measurable (finiteSample p) :=
    measurable_finiteSample (fun _ => measurable_const) measurable_id
  rw [← lintegral_map (measurable_of_finite f) hm, finiteSample_map, lintegral_countable']
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    tsum_fintype, mul_comm]


-- @@ L269-269 verbatim
section EquivSampling

-- @@ L270-270 verbatim
variable {A B : Type*}

-- @@ L271-279 verbatim
lemma pmf_map_equiv_apply (e : A ≃ B) (p : PMF A) (b : B) :
    p.map e b = p (e.symm b) := by
  classical
  have he (a : A) : b = e a ↔ e.symm b = a := by
    constructor
    · intro h; simp [h]
    · intro h; rw [← h, e.apply_symm_apply]
  simp only [PMF.map_apply, he]
  simp


-- @@ L281-281 verbatim
variable [Fintype A] [Nonempty A]


-- @@ L283-285 verbatim
def samplePMF (p : PMF A) (r : ℝ) : A :=
  letI : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  (Fintype.equivFin A).symm (finiteSample (p.map (Fintype.equivFin A)) r)


-- @@ L287-293 verbatim
lemma measurable_samplePMF {X : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {p : X → PMF A} {r : X → ℝ}
    (hp : ∀ a, Measurable (fun x => p x a)) (hr : Measurable r) :
    Measurable (fun x => samplePMF (p x) (r x)) := by
  let : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  apply (measurable_of_finite (Fintype.equivFin A).symm).comp
  exact measurable_finiteSample (fun i => by simpa only [pmf_map_equiv_apply] using hp _) hr


-- @@ L295-303 verbatim
lemma lintegral_samplePMF (p : PMF A) (f : A → ℝ≥0∞) :
    (∫⁻ r, f (samplePMF p r) ∂coinLaw) = ∑ a, p a * f a := by
  let : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  change (∫⁻ r, (fun i => f ((Fintype.equivFin A).symm i))
    (finiteSample (p.map (Fintype.equivFin A)) r) ∂coinLaw) = _
  rw [lintegral_finiteSample (p.map (Fintype.equivFin A))
    (fun i => f ((Fintype.equivFin A).symm i))]
  simp_rw [pmf_map_equiv_apply]
  exact Equiv.sum_comp (Fintype.equivFin A).symm (fun a => p a * f a)


-- @@ L305-315 verbatim
lemma samplePMF_map [MeasurableSpace A] [MeasurableSingletonClass A] (p : PMF A) :
    coinLaw.map (samplePMF p) = p.toMeasure := by
  let : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  let e := Fintype.equivFin A
  have hm : Measurable (finiteSample (p.map e)) :=
    measurable_finiteSample (fun _ => measurable_const) measurable_id
  change coinLaw.map (e.symm ∘ finiteSample (p.map e)) = _
  rw [← Measure.map_map (measurable_of_finite e.symm) hm, finiteSample_map,
    PMF.toMeasure_map _ _ (measurable_of_finite e.symm), PMF.map_comp]
  have he : e.symm ∘ e = id := by funext a; simp
  rw [he, PMF.map_id]

-- @@ L316-316 verbatim
end EquivSampling


-- @@ L318-318 verbatim
end SubsphereCurrent

-- @@ L319-319 verbatim
end

-- @@ L320-320 verbatim
end

-- @@ L321-321 verbatim
section

-- @@ L322-322 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L323-323 verbatim
open scoped ENNReal NNReal

-- @@ L324-324 verbatim
noncomputable section

-- @@ L325-325 verbatim
namespace SubsphereCurrent


-- @@ L327-327 verbatim
section CountableBind

-- @@ L328-329 verbatim
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]


-- @@ L331-338 verbatim
lemma pmf_toMeasure_bind (p : PMF A) (k : A → PMF B) :
    (p.bind k).toMeasure = p.toMeasure.bind (fun a => (k a).toMeasure) := by
  apply Measure.ext_of_singleton
  intro b
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.bind_apply, Measure.bind_apply (measurableSet_singleton b)
      (measurable_of_countable _).aemeasurable, lintegral_countable']
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]


-- @@ L340-344 verbatim
lemma pmf_lintegral_bind (p : PMF A) (k : A → PMF B) (f : B → ℝ≥0∞) :
    (∫⁻ b, f b ∂(p.bind k).toMeasure) =
      ∫⁻ a, ∫⁻ b, f b ∂(k a).toMeasure ∂p.toMeasure := by
  rw [pmf_toMeasure_bind, Measure.lintegral_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]

-- @@ L345-345 verbatim
end CountableBind


-- @@ L347-347 verbatim
section Chain

-- @@ L348-348 verbatim
variable {A : Type*} [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]


-- @@ L350-352 verbatim
def detChain (F : ℕ → A → ℝ → A) (a : A) : (n : ℕ) → (Fin n → ℝ) → A
  | 0, _ => a
  | n+1, r => F n (detChain F a n (Fin.init r)) (r (Fin.last n))


-- @@ L354-356 verbatim
def lawChain (K : ℕ → A → PMF A) (a : A) : ℕ → PMF A
  | 0 => PMF.pure a
  | n+1 => (lawChain K a n).bind (K n)


-- @@ L358-362 verbatim
omit [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A] in
lemma detChain_snoc (F : ℕ → A → ℝ → A) (a : A) (n : ℕ)
    (r : Fin n → ℝ) (u : ℝ) :
    detChain F a (n+1) (Fin.snoc r u) = F n (detChain F a n r) u := by
  simp [detChain]


-- @@ L364-372 verbatim
lemma measurable_detChain {F : ℕ → A → ℝ → A}
    (hF : ∀ n a, Measurable (F n a)) (a : A) (n : ℕ) :
    Measurable (detChain F a n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hj : Measurable (Function.uncurry (F n)) :=
      measurable_from_prod_countable_right (hF n)
    exact hj.comp ((ih.comp (by fun_prop)).prodMk (measurable_pi_apply (Fin.last n)))


-- @@ L374-395 verbatim
lemma detChain_lintegral {F : ℕ → A → ℝ → A} {K : ℕ → A → PMF A}
    (hF : ∀ n a, Measurable (F n a))
    (hFK : ∀ n a, coinLaw.map (F n a) = (K n a).toMeasure)
    (a : A) (n : ℕ) (f : A → ℝ≥0∞) :
    (∫⁻ r : Fin n → ℝ, f (detChain F a n r) ∂Measure.pi (fun _ => coinLaw)) =
      ∫⁻ b, f b ∂(lawChain K a n).toMeasure := by
  induction n generalizing f with
  | zero => simp [detChain, lawChain, PMF.toMeasure_pure]
  | succ n ih =>
    rw [SubsphereRegression.lintegral_pi_snoc coinLaw
      (fun r => f (detChain F a (n+1) r))
      ((measurable_of_countable f).comp (measurable_detChain hF a (n+1)))]
    simp_rw [detChain_snoc]
    calc
      _ = ∫⁻ r : Fin n → ℝ, ∫⁻ b, f b ∂(K n (detChain F a n r)).toMeasure
          ∂Measure.pi (fun _ => coinLaw) := by
        apply lintegral_congr
        intro r
        rw [← hFK, lintegral_map (measurable_of_countable f) (hF _ _)]
      _ = ∫⁻ b, ∫⁻ c, f c ∂(K n b).toMeasure ∂(lawChain K a n).toMeasure := by
        exact ih (fun b => ∫⁻ c, f c ∂(K n b).toMeasure)
      _ = _ := by rw [lawChain, pmf_lintegral_bind]


-- @@ L397-408 verbatim
omit [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A] in
lemma lawChain_bind_initial (K : ℕ → A → PMF A) (p : PMF A) (n : ℕ) :
    p.bind (fun a => lawChain K a n) =
      Nat.rec p (fun n q => q.bind (K n)) n := by
  induction n with
  | zero =>
    change p.bind PMF.pure = p
    exact PMF.bind_pure p
  | succ n ih =>
    change p.bind (fun a => (lawChain K a n).bind (K n)) =
      (Nat.rec (motive := fun _ => PMF A) p (fun n q => q.bind (K n)) n).bind (K n)
    rw [← PMF.bind_bind, ih]


-- @@ L410-410 verbatim
end Chain

-- @@ L411-411 verbatim
end SubsphereCurrent

-- @@ L412-412 verbatim
end

-- @@ L413-413 verbatim
end

-- @@ L414-414 verbatim
section

-- @@ L415-415 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L416-416 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L417-417 verbatim
noncomputable section


-- @@ L419-419 verbatim
namespace SubsphereCurrent

-- @@ L420-426 verbatim
instance sumMeasurableSingletonClass {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton a := by
    cases a with
    | inl a => simpa only [← Set.image_singleton] using MeasurableSet.inl_image (measurableSet_singleton a)
    | inr b => simpa only [← Set.image_singleton] using MeasurableSet.inr_image (measurableSet_singleton b)


-- @@ L428-433 verbatim
lemma measurable_countable_select {X Y J : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp
    (hφ.prodMk measurable_id)

-- @@ L434-434 verbatim
end SubsphereCurrent


-- @@ L436-436 verbatim
namespace SubsphereRegression.Learner

-- @@ L437-437 verbatim
open SubsphereCurrent (measurable_countable_select)


-- @@ L439-480 verbatim
lemma measurable_run_of_rules {d M T : ℕ} {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (L : Learner d M T Ω)
    (hi : Measurable L.initialChoice)
    (ht : ∀ t q, Measurable (fun z : Ω × (Vector d × ℝ) => L.transition t z.1 q z.2))
    {s : X → UnitSphere d} {ω : X → Ω} {x : X → Samples d T}
    (hs : Measurable s) (hω : Measurable ω) (hx : Measurable x) (n : ℕ) :
    Measurable (fun z => L.run (s z) (ω z) (x z) n) := by
  induction n with
  | zero =>
    exact (measurable_of_countable (fun a : Bool × State M =>
      if a.1 then Sum.inr (0,a.2) else Sum.inl a.2)).comp (hi.comp hω)
  | succ n ih =>
    change Measurable (fun z => (match L.run (s z) (ω z) (x z) n with
      | Sum.inr done => Sum.inr done
      | Sum.inl q => if hn : n < T then
          let row := x z ⟨n,hn⟩
          let a := L.transition (n+1) (ω z) q (row, ⟪row,(s z).val⟫)
          if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2
        else Sum.inl q))
    let F : RunStatus M → X → RunStatus M := fun status z => match status with
      | Sum.inr done => Sum.inr done
      | Sum.inl q => if hn : n < T then
          let row := x z ⟨n,hn⟩
          let a := L.transition (n+1) (ω z) q (row, ⟪row,(s z).val⟫)
          if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2
        else Sum.inl q
    have hF : ∀ status, Measurable (F status) := by
      intro status
      cases status with
      | inr done => exact measurable_const
      | inl q =>
        by_cases hn : n < T
        · dsimp [F]
          simp only [dite_eq_left hn]
          have hr : Measurable (fun z => x z ⟨n,hn⟩) := (measurable_pi_apply _).comp hx
          exact (measurable_of_countable (fun a : Bool × State M =>
            (if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2 : RunStatus M))).comp
            ((ht (n+1) q).comp (hω.prodMk (hr.prodMk (hr.inner (measurable_subtype_coe.comp hs)))))
        · dsimp [F]
          simp only [dite_eq_right hn]
          exact measurable_const
    exact measurable_countable_select hF ih


-- @@ L482-497 verbatim
lemma measurable_estimate_of_rules {d M T : ℕ} {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (L : Learner d M T Ω)
    (hi : Measurable L.initialChoice)
    (ht : ∀ t q, Measurable (fun z : Ω × (Vector d × ℝ) => L.transition t z.1 q z.2))
    (ho : ∀ t q, Measurable (fun ω => L.output t ω q))
    {s : X → UnitSphere d} {ω : X → Ω} {x : X → Samples d T}
    (hs : Measurable s) (hω : Measurable ω) (hx : Measurable x) :
    Measurable (fun z => L.estimate (s z) (ω z) (x z)) := by
  have hr := L.measurable_run_of_rules hi ht hs hω hx T
  have hterm : Measurable (fun z => L.terminal (s z) (ω z) (x z)) := by
    unfold terminal
    exact (measurable_of_countable (fun status : RunStatus M =>
      match status with | Sum.inl q => (T,q) | Sum.inr done => done) :
      Measurable (fun status : RunStatus M =>
        match status with | Sum.inl q => (T,q) | Sum.inr done => done)).comp hr
  exact measurable_countable_select (fun a : ℕ × State M => (ho a.1 a.2).comp hω) hterm

-- @@ L498-498 verbatim
end SubsphereRegression.Learner


-- @@ L500-500 verbatim
namespace SubsphereCurrent

-- @@ L501-501 verbatim
namespace KernelLearner

-- @@ L502-502 verbatim
abbrev OutputTape (d M : ℕ) := (ℕ × State M) → UnitSphere d

-- @@ L503-503 verbatim
abbrev Tape (d M T : ℕ) := (Bool × State M) × ((Fin T → ℝ) × OutputTape d M)


-- @@ L505-506 verbatim
def outputTapeLaw {d M T : ℕ} (L : KernelLearner d M T) : Measure (OutputTape d M) :=
  Measure.infinitePi (fun a : ℕ × State M => L.output a.1 a.2)


-- @@ L508-513 verbatim
instance outputTapeLaw_probability {d M T : ℕ} (L : KernelLearner d M T) :
    IsProbabilityMeasure L.outputTapeLaw := by
  let : ∀ a : ℕ × State M, IsProbabilityMeasure (L.output a.1 a.2) :=
    fun a => L.output_probability a.1 a.2
  unfold outputTapeLaw
  infer_instance


-- @@ L515-516 verbatim
def tapeLaw {d M T : ℕ} (L : KernelLearner d M T) : Measure (Tape d M T) :=
  L.initial.toMeasure.prod ((Measure.pi (fun _ : Fin T => coinLaw)).prod L.outputTapeLaw)


-- @@ L518-519 verbatim
instance tapeLaw_probability {d M T : ℕ} (L : KernelLearner d M T) :
    IsProbabilityMeasure L.tapeLaw := by unfold tapeLaw; infer_instance


-- @@ L521-522 verbatim
def tapeCoin {d M T : ℕ} (t : ℕ) (ω : Tape d M T) : ℝ :=
  if h : t-1 < T then ω.2.1 ⟨t-1,h⟩ else 0


-- @@ L524-527 verbatim
lemma measurable_tapeCoin {d M T : ℕ} (t : ℕ) :
    Measurable (tapeCoin (d := d) (M := M) (T := T) t) := by
  unfold tapeCoin
  split_ifs <;> fun_prop


-- @@ L529-533 verbatim
def asTape {d M T : ℕ} (L : KernelLearner d M T) :
    SubsphereRegression.Learner d M T (Tape d M T) where
  initialChoice := Prod.fst
  transition t ω q obs := samplePMF (L.transition t q obs) (tapeCoin t ω)
  output t ω q := ω.2.2 (t,q)


-- @@ L535-539 verbatim
lemma asTape_measurable_transition {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (t : ℕ) (q : State M) :
    Measurable (fun z : Tape d M T × (Vector d × ℝ) => L.asTape.transition t z.1 q z.2) :=
  measurable_samplePMF (fun a => (hL t q a).comp measurable_snd)
    ((measurable_tapeCoin t).comp measurable_fst)


-- @@ L541-554 verbatim
lemma asTape_admissible {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) : L.asTape.Admissible L.tapeLaw := by
  have hi : Measurable L.asTape.initialChoice := measurable_fst
  have ht := L.asTape_measurable_transition hL
  have ho (t : ℕ) (q : State M) : Measurable (fun ω => L.asTape.output t ω q) := by
    change Measurable (fun ω : Tape d M T => ω.2.2 (t,q))
    fun_prop
  refine ⟨hi.aemeasurable, fun t q => (ht t q).aemeasurable,
    fun t q => (ho t q).aemeasurable, ?_, ?_⟩
  · intro s
    exact (L.asTape.measurable_estimate_of_rules hi ht ho measurable_const
      measurable_fst measurable_snd).aemeasurable
  · exact (L.asTape.measurable_estimate_of_rules hi ht ho measurable_fst
      (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)).aemeasurable


-- @@ L556-562 verbatim
def stepPMF {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) (n : ℕ) (a : RunStatus M) : PMF (RunStatus M) :=
  match a with
  | .inr done => PMF.pure (.inr done)
  | .inl q => if hn : n < T then
      (L.transition (n+1) q (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)).map (tagged M (n+1))
    else PMF.pure (.inl q)


-- @@ L564-571 verbatim
def stepDet {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) (n : ℕ) (a : RunStatus M) (u : ℝ) : RunStatus M :=
  match a with
  | .inr done => .inr done
  | .inl q => if hn : n < T then
      tagged M (n+1) (samplePMF (L.transition (n+1) q
        (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)) u)
    else .inl q


-- @@ L573-583 verbatim
lemma stepDet_measurable {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) (a : RunStatus M) :
    Measurable (L.stepDet s x n a) := by
  cases a with
  | inr done => exact measurable_const
  | inl q =>
    unfold stepDet
    split_ifs
    · exact (measurable_of_countable (tagged M (n+1))).comp
        (measurable_samplePMF (fun _ => measurable_const) measurable_id)
    · exact measurable_const


-- @@ L585-598 verbatim
lemma stepDet_map {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) (a : RunStatus M) :
    coinLaw.map (L.stepDet s x n a) = (L.stepPMF s x n a).toMeasure := by
  cases a with
  | inr done =>
    change coinLaw.map (fun _ => Sum.inr done) = (PMF.pure (Sum.inr done) : PMF (RunStatus M)).toMeasure
    simp [PMF.toMeasure_pure]
  | inl q =>
    unfold stepDet stepPMF
    split_ifs
    · rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), ← samplePMF_map]
      exact (Measure.map_map (measurable_of_countable (tagged M (n+1)))
        (measurable_samplePMF (fun _ => measurable_const) measurable_id)).symm
    · simp [PMF.toMeasure_pure]


-- @@ L600-609 verbatim
lemma run_eq_bind_chain {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) :
    L.run s x n = (L.initial.map (tagged M 0)).bind
      (fun a => lawChain (L.stepPMF s x) a n) := by
  induction n with
  | zero => simp [run, lawChain]
  | succ n ih =>
    change (L.run s x n).bind (L.stepPMF s x n) = _
    rw [ih, PMF.bind_bind]
    rfl


-- @@ L611-623 verbatim
lemma asTape_run_eq_detChain {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (ω : Tape d M T) {n : ℕ} (hn : n ≤ T) :
    L.asTape.run s ω x n = detChain (L.stepDet s x) (tagged M 0 ω.1) n
      (fun i => ω.2.1 (Fin.castLE hn i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [SubsphereRegression.fin_prefix_snoc hn, detChain_snoc]
    simp only [SubsphereRegression.Learner.run, ih (by omega)]
    cases he : detChain (L.stepDet s x) (tagged M 0 ω.1) n
      (fun i => ω.2.1 (Fin.castLE (by omega) i)) with
    | inr done => rfl
    | inl q => simp [stepDet, asTape, tapeCoin, tagged, show n < T by omega]


-- @@ L625-626 verbatim
def finish (M T : ℕ) (status : RunStatus M) : ℕ × State M :=
  match status with | .inl q => (T,q) | .inr done => done


-- @@ L628-634 verbatim
lemma asTape_estimate_eq {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) (ω : Tape d M T) :
    L.asTape.estimate s ω x =
      ω.2.2 (finish M T (detChain (L.stepDet s x) (tagged M 0 ω.1) T ω.2.1)) := by
  unfold SubsphereRegression.Learner.estimate SubsphereRegression.Learner.terminal
  rw [L.asTape_run_eq_detChain s x ω le_rfl]
  rfl


-- @@ L636-641 verbatim
lemma lintegral_outputTape_eval {d M T : ℕ} (L : KernelLearner d M T)
    (a : ℕ × State M) (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ o, f (o a) ∂L.outputTapeLaw) = ∫⁻ u, f u ∂L.output a.1 a.2 := by
  let : ∀ a : ℕ × State M, IsProbabilityMeasure (L.output a.1 a.2) :=
    fun a => L.output_probability a.1 a.2
  exact (measurePreserving_eval_infinitePi (fun a : ℕ × State M => L.output a.1 a.2) a).lintegral_comp hf


-- @@ L643-684 verbatim
lemma lintegral_asTape_estimate {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (s : UnitSphere d) (x : Samples d T)
    (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (L.asTape.estimate s ω x) ∂L.tapeLaw) = ∫⁻ u, f u ∂L.estimateLaw s x := by
  have hE : Measurable (fun ω => f (L.asTape.estimate s ω x)) :=
    hf.comp (L.asTape.measurable_estimate_of_rules measurable_fst
      (L.asTape_measurable_transition hL) (fun t q => by
        change Measurable (fun ω : Tape d M T => ω.2.2 (t,q)); fun_prop)
      measurable_const measurable_id measurable_const)
  rw [tapeLaw, lintegral_prod _ hE.aemeasurable]
  calc
    _ = ∫⁻ a, ∫⁻ r : Fin T → ℝ,
        ∫⁻ u, f u ∂L.output
          (finish M T (detChain (L.stepDet s x) (tagged M 0 a) T r)).1
          (finish M T (detChain (L.stepDet s x) (tagged M 0 a) T r)).2
        ∂Measure.pi (fun _ => coinLaw) ∂L.initial.toMeasure := by
      apply lintegral_congr
      intro a
      rw [lintegral_prod (fun y : (Fin T → ℝ) × OutputTape d M =>
        f (L.asTape.estimate s (a,y) x))
        (hE.comp (measurable_const.prodMk measurable_id)).aemeasurable]
      apply lintegral_congr
      intro r
      simp_rw [asTape_estimate_eq]
      exact L.lintegral_outputTape_eval _ f hf
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ u, f u ∂L.output (finish M T b).1 (finish M T b).2
        ∂(lawChain (L.stepPMF s x) (tagged M 0 a) T).toMeasure ∂L.initial.toMeasure := by
      apply lintegral_congr
      intro a
      exact detChain_lintegral (L.stepDet_measurable s x) (L.stepDet_map s x) (tagged M 0 a) T
        (fun b => ∫⁻ u, f u ∂L.output (finish M T b).1 (finish M T b).2)
    _ = ∫⁻ b, ∫⁻ u, f u ∂L.output (finish M T b).1 (finish M T b).2
        ∂(L.run s x T).toMeasure := by
      rw [run_eq_bind_chain, pmf_lintegral_bind, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
        lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    _ = ∫⁻ a, ∫⁻ u, f u ∂L.output a.1 a.2 ∂(L.terminal s x).toMeasure := by
      unfold terminal
      rw [← PMF.toMeasure_map _ _ (measurable_of_countable _),
        lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = _ := by
      rw [estimateLaw, Measure.lintegral_bind (measurable_of_countable _).aemeasurable hf.aemeasurable]


-- @@ L686-686 verbatim
end KernelLearner

-- @@ L687-687 verbatim
end SubsphereCurrent

-- @@ L688-688 verbatim
end

-- @@ L689-689 verbatim
end

-- @@ L690-690 verbatim
section

-- @@ L691-691 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L692-692 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L693-693 verbatim
noncomputable section

-- @@ L694-694 verbatim
universe u v w

-- @@ L695-695 verbatim
namespace SubsphereCurrent


-- @@ L697-698 verbatim
instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) :=
  SubsphereRegression.sampleLaw_probability d T

-- @@ L699-700 verbatim
instance uniformSphere_probability (d : ℕ) [NeZero d] : IsProbabilityMeasure (uniformSphere d) :=
  SubsphereRegression.uniformSphere_probability d


-- @@ L702-707 verbatim
def swapFirstTwo (A : Type u) (B : Type v) (C : Type w)
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] :
    A × (B × C) ≃ᵐ B × (A × C) :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl C)).trans
      MeasurableEquiv.prodAssoc)


-- @@ L709-716 verbatim
lemma measurePreserving_swapFirstTwo {A : Type u} {B : Type v} {C : Type w}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (swapFirstTwo A B C) (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  exact (measurePreserving_prodAssoc ν μ ρ).comp
    (((MeasureTheory.Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ρ)).comp
      (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ ν ρ)))


-- @@ L718-718 verbatim
namespace KernelLearner

-- @@ L719-722 verbatim
instance estimateLaw_probability {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) : IsProbabilityMeasure (L.estimateLaw s x) := by
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  exact ae_of_all _ (fun a => L.output_probability a.1 a.2)


-- @@ L724-726 verbatim
lemma conditionalSuccess_le_one {d M T : ℕ} (L : KernelLearner d M T)
    (ε : ℝ) (s : UnitSphere d) (x : Samples d T) : L.conditionalSuccess ε s x ≤ 1 :=
  prob_le_one


-- @@ L728-729 verbatim
def successTest {d : ℕ} (s : UnitSphere d) (ε : ℝ) (u : UnitSphere d) : ℝ≥0∞ :=
  {u | angularError s u ≤ ε}.indicator (fun _ => 1) u


-- @@ L731-739 verbatim
lemma measurable_successTest {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s u : X → UnitSphere d} (hs : Measurable s) (hu : Measurable u) (ε : ℝ) :
    Measurable (fun x => successTest (s x) ε (u x)) := by
  have he : Measurable (fun x => angularError (s x) (u x)) :=
    Real.continuous_arccos.measurable.comp
      ((measurable_subtype_coe.comp hu).inner (measurable_subtype_coe.comp hs))
  simpa only [successTest, Set.indicator_apply, Set.mem_ofPred_eq] using
    (Measurable.ite (measurableSet_le he measurable_const) measurable_const measurable_const :
      Measurable (fun x => if angularError (s x) (u x) ≤ ε then (1 : ℝ≥0∞) else 0))


-- @@ L741-748 verbatim
lemma conditionalSuccess_eq_integral_tape {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (ε : ℝ) (s : UnitSphere d) (x : Samples d T) :
    L.conditionalSuccess ε s x = ∫⁻ ω, successTest s ε (L.asTape.estimate s ω x) ∂L.tapeLaw := by
  rw [L.lintegral_asTape_estimate hL s x (successTest s ε)
    (measurable_successTest measurable_const measurable_id ε)]
  have hS : MeasurableSet {u : UnitSphere d | angularError s u ≤ ε} :=
    measurableSet_le (by unfold angularError; fun_prop) measurable_const
  simp only [successTest, conditionalSuccess, lintegral_indicator_const hS, one_mul]


-- @@ L750-757 verbatim
lemma measurable_tape_test {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (ε : ℝ) {X : Type*} [MeasurableSpace X]
    {s : X → UnitSphere d} {ω : X → Tape d M T} {x : X → Samples d T}
    (hs : Measurable s) (hω : Measurable ω) (hx : Measurable x) :
    Measurable (fun z => successTest (s z) ε (L.asTape.estimate (s z) (ω z) (x z))) :=
  measurable_successTest hs (L.asTape.measurable_estimate_of_rules measurable_fst
    (L.asTape_measurable_transition hL) (fun t q => by
      change Measurable (fun ω : Tape d M T => ω.2.2 (t,q)); fun_prop) hs hω hx) ε


-- @@ L759-764 verbatim
lemma measurable_conditionalSuccess {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (ε : ℝ) :
    Measurable (fun z : UnitSphere d × Samples d T => L.conditionalSuccess ε z.1 z.2) := by
  simp_rw [L.conditionalSuccess_eq_integral_tape hL ε]
  exact (L.measurable_tape_test hL ε (measurable_fst.comp measurable_fst)
    measurable_snd (measurable_snd.comp measurable_fst)).lintegral_prod_right


-- @@ L766-796 verbatim
lemma uniformSuccess_asTape {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.BorelRules) (ε : ℝ) [NeZero d] :
    L.asTape.uniformSuccess L.tapeLaw ε =
      ∫⁻ z : UnitSphere d × Samples d T, L.conditionalSuccess ε z.1 z.2
        ∂(uniformSphere d).prod (sampleLaw d T) := by
  have hm := L.measurable_tape_test hL ε measurable_fst
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  have hset : MeasurableSet {z : UnitSphere d × (Tape d M T × Samples d T) |
      angularError z.1 (L.asTape.estimate z.1 z.2.1 z.2.2) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact Real.continuous_arccos.measurable.comp
      ((measurable_subtype_coe.comp (L.asTape.measurable_estimate_of_rules measurable_fst
        (L.asTape_measurable_transition hL) (fun t q => by
          change Measurable (fun ω : Tape d M T => ω.2.2 (t,q)); fun_prop)
        measurable_fst (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd))).inner
        (measurable_subtype_coe.comp measurable_fst))
  change ((uniformSphere d).prod (L.tapeLaw.prod (sampleLaw d T)))
    {z | angularError z.1 (L.asTape.estimate z.1 z.2.1 z.2.2) ≤ ε} = _
  rw [← one_mul (((uniformSphere d).prod (L.tapeLaw.prod (sampleLaw d T))) _),
    ← lintegral_indicator_const hset 1]
  change (∫⁻ z : UnitSphere d × (Tape d M T × Samples d T),
    successTest z.1 ε (L.asTape.estimate z.1 z.2.1 z.2.2)
      ∂(uniformSphere d).prod (L.tapeLaw.prod (sampleLaw d T))) = _
  rw [lintegral_prod (μ := uniformSphere d) (ν := L.tapeLaw.prod (sampleLaw d T))
      (fun z => successTest z.1 ε (L.asTape.estimate z.1 z.2.1 z.2.2)) hm.aemeasurable,
    lintegral_prod _ (L.measurable_conditionalSuccess hL ε).aemeasurable]
  apply lintegral_congr
  intro s
  rw [lintegral_prod_symm _ (L.measurable_tape_test hL ε measurable_const
    measurable_fst measurable_snd).aemeasurable]
  exact lintegral_congr fun x => (L.conditionalSuccess_eq_integral_tape hL ε s x).symm


-- @@ L798-798 verbatim
end KernelLearner


-- @@ L800-800 verbatim
namespace SeededLearner

-- @@ L801-819 verbatim
lemma uniformSuccess_average_seed {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (ε : ℝ) [NeZero d] :
    L.uniformSuccess ρ ε = ∫⁻ ω, ∫⁻ z : UnitSphere d × Samples d T,
      (L.rules ω).conditionalSuccess ε z.1 z.2
        ∂(uniformSphere d).prod (sampleLaw d T) ∂ρ := by
  let e := swapFirstTwo Ω (UnitSphere d) (Samples d T)
  have hp := measurePreserving_swapFirstTwo ρ (uniformSphere d) (sampleLaw d T)
  have hm := (hL.uniform_experiment ε).comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  change AEMeasurable (fun z : Ω × (UnitSphere d × Samples d T) =>
    (L.rules z.1).conditionalSuccess ε z.2.1 z.2.2)
      (ρ.prod ((uniformSphere d).prod (sampleLaw d T))) at hm
  have he := hp.lintegral_comp_emb e.measurableEmbedding
    (fun z : UnitSphere d × (Ω × Samples d T) =>
      (L.rules z.2.1).conditionalSuccess ε z.1 z.2.2)
  change (∫⁻ z : Ω × (UnitSphere d × Samples d T),
    (L.rules z.1).conditionalSuccess ε z.2.1 z.2.2
      ∂ρ.prod ((uniformSphere d).prod (sampleLaw d T))) = L.uniformSuccess ρ ε at he
  rw [← he, lintegral_prod _ hm]


-- @@ L821-828 verbatim
lemma uniformSuccess_of_pointwise {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (ε : ℝ) [NeZero d] (c : ℝ≥0∞)
    (hc : ∀ s, c ≤ L.success ρ ε s) : c ≤ L.uniformSuccess ρ ε := by
  rw [uniformSuccess, lintegral_prod _ (hL.uniform_experiment ε)]
  calc
    c = ∫⁻ _ : UnitSphere d, c ∂uniformSphere d := by simp
    _ ≤ _ := lintegral_mono hc


-- @@ L830-854 verbatim
lemma exists_good_seed {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (ε : ℝ) [NeZero d] :
    ∃ ω, (L.rules ω).CompletedRules ∧ L.uniformSuccess ρ ε ≤
      ∫⁻ z : UnitSphere d × Samples d T, (L.rules ω).conditionalSuccess ε z.1 z.2
        ∂(uniformSphere d).prod (sampleLaw d T) := by
  let f := fun ω => ∫⁻ z : UnitSphere d × Samples d T,
    (L.rules ω).conditionalSuccess ε z.1 z.2 ∂(uniformSphere d).prod (sampleLaw d T)
  have hf : ∫⁻ ω, f ω ∂ρ ≠ ∞ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞)
    calc
      _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂ρ := by
        apply lintegral_mono
        intro ω
        calc
          _ ≤ ∫⁻ _ : UnitSphere d × Samples d T, (1 : ℝ≥0∞)
              ∂(uniformSphere d).prod (sampleLaw d T) :=
            lintegral_mono fun z => (L.rules ω).conditionalSuccess_le_one ε z.1 z.2
          _ = 1 := by simp
      _ = 1 := by simp
  obtain ⟨ω,hω,hbound⟩ := exists_notMem_null_lintegral_le (f := f) hf
    (N := {ω | ¬(L.rules ω).CompletedRules}) hL.completed_rules
  refine ⟨ω, by simpa using hω, ?_⟩
  rw [L.uniformSuccess_average_seed ρ hL ε]
  exact hbound

-- @@ L855-855 verbatim
end SeededLearner

-- @@ L856-856 verbatim
end SubsphereCurrent

-- @@ L857-857 verbatim
end

-- @@ L858-858 verbatim
end

-- @@ L859-859 verbatim
section

-- @@ L860-860 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L861-861 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L862-862 verbatim
noncomputable section

-- @@ L863-863 verbatim
universe u

-- @@ L864-864 verbatim
namespace SubsphereCurrent


-- @@ L866-890 verbatim
theorem explicit_precision : ExplicitPrecision.{u} := by
  intro M hM
  obtain ⟨d₁, hd₁⟩ := SubsphereRegression.explicit_precision_old_model.{0} M hM
  refine ⟨max 3 d₁, ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ L hL hs
  let : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  have hs' : (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε := by
    rcases hs with hs | hs
    · exact hs
    · exact L.uniformSuccess_of_pointwise ρ hL ε _ hs
  obtain ⟨ω, hω, hgood⟩ := L.exists_good_seed ρ hL ε
  let K := (L.rules ω).borelVersion hω
  have hK : K.BorelRules := (L.rules ω).borelVersion_rules hω
  have hsuccess : (2/3 : ℝ≥0∞) ≤ K.asTape.uniformSuccess K.tapeLaw ε := by
    rw [K.uniformSuccess_asTape hK ε]
    calc
      (2/3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε := hs'
      _ ≤ ∫⁻ z : UnitSphere d × Samples d T, (L.rules ω).conditionalSuccess ε z.1 z.2
          ∂(uniformSphere d).prod (sampleLaw d T) := hgood
      _ = ∫⁻ z : UnitSphere d × Samples d T, K.conditionalSuccess ε z.1 z.2
          ∂(uniformSphere d).prod (sampleLaw d T) :=
        lintegral_congr_ae ((L.rules ω).borelVersion_success_ae hω (by omega) ε)
  exact hd₁ d (by omega) T ε hε hε10 (KernelLearner.Tape d (M d) T)
    K.tapeLaw inferInstance K.asTape (K.asTape_admissible hK) (Or.inl hsuccess)


-- @@ L892-892 verbatim
end SubsphereCurrent

-- @@ L893-893 verbatim
end

-- @@ L894-894 verbatim
end


-- @@ L896-896 verbatim
end OAI
