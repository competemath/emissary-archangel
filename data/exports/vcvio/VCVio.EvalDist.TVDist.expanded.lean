/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.Probability.ProbabilityMassFunction.TotalVariation
public import VCVio.EvalDist.Defs.Basic
public import VCVio.EvalDist.Monad.Basic
public import VCVio.EvalDist.Defs.NeverFails


-- @@ L13-21 verbatim
/-!
# Total Variation Distance for SPMFs and Monadic Computations

This file extends the TV distance from `PMF` (defined in
`ToMathlib.Probability.ProbabilityMassFunction.TotalVariation`) to:

1. `SPMF.tvDist` — on sub-probability mass functions (via `toPMF`)
2. `tvDist` — on any monad with `MonadLiftT m SPMF` (via `evalSPMF`)
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open ENNReal


-- @@ L29-29 verbatim
universe u v


-- @@ L31-31 verbatim
/-! ### SPMF.tvDist -/


-- @@ L33-33 verbatim
namespace SPMF


-- @@ L35-35 verbatim
variable {α : Type*}


-- @@ L37-38 verbatim
/-- Total variation distance on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def tvDist (p q : SPMF α) : ℝ := p.toPMF.tvDist q.toPMF


-- @@ L40-40 verbatim
@[simp] lemma tvDist_self (p : SPMF α) : p.tvDist p = 0 := PMF.tvDist_self _

-- @@ L41-41 verbatim
lemma tvDist_comm (p q : SPMF α) : p.tvDist q = q.tvDist p := PMF.tvDist_comm _ _

-- @@ L42-42 verbatim
lemma tvDist_nonneg (p q : SPMF α) : 0 ≤ p.tvDist q := PMF.tvDist_nonneg _ _


-- @@ L44-45 verbatim
lemma tvDist_triangle (p q r : SPMF α) :
    p.tvDist r ≤ p.tvDist q + q.tvDist r := PMF.tvDist_triangle _ _ _


-- @@ L47-47 verbatim
lemma tvDist_le_one (p q : SPMF α) : p.tvDist q ≤ 1 := PMF.tvDist_le_one _ _


-- @@ L49-50 verbatim
@[simp] lemma tvDist_eq_zero_iff {p q : SPMF α} : p.tvDist q = 0 ↔ p.toPMF = q.toPMF :=
  PMF.tvDist_eq_zero_iff


-- @@ L52-55 verbatim
universe w in
lemma tvDist_map_le {α' : Type w} {β : Type w} (f : α' → β)
    (p q : SPMF α') : SPMF.tvDist (f <$> p) (f <$> q) ≤ SPMF.tvDist p q := by
  simpa only [SPMF.tvDist, SPMF.toPMF_map] using PMF.tvDist_map_le (Option.map f) p.toPMF q.toPMF


-- @@ L57-61 verbatim
universe w in
lemma tvDist_bind_right_le {α' : Type w} {β : Type w} (f : α' → SPMF β)
    (p q : SPMF α') : SPMF.tvDist (p >>= f) (q >>= f) ≤ SPMF.tvDist p q := by
  simpa only [SPMF.tvDist, SPMF.toPMF_bind, Option.elimM, PMF.monad_bind_eq_bind] using
    PMF.tvDist_bind_right_le _ p.toPMF q.toPMF


-- @@ L63-63 verbatim
end SPMF


-- @@ L65-65 verbatim
/-! ### Monadic tvDist -/


-- @@ L67-67 verbatim
section monadic


-- @@ L69-69 verbatim
variable {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] {α : Type u}


-- @@ L71-74 expanded
/-- Total variation distance between two monadic computations,
defined via their evaluation distributions. -/
noncomputable def tvDist (mx my : m α) : ℝ :=
  SPMF.tvDist (evalSPMF mx) (evalSPMF my)


-- @@ L76-77 verbatim
omit [Monad m] [LawfulMonadLiftT m SPMF] in
@[simp] lemma tvDist_self (mx : m α) : tvDist mx mx = 0 := SPMF.tvDist_self _


-- @@ L79-82 expanded
omit [Monad m] [LawfulMonadLiftT m SPMF] in
@[simp]
lemma tvDist_eq_zero_iff (mx my : m α) : tvDist mx my = 0 ↔ evalSPMF mx = evalSPMF my := by
  simp only [tvDist, SPMF.tvDist_eq_zero_iff, SPMF.toPMF_inj]


-- @@ L84-86 verbatim
omit [Monad m] [LawfulMonadLiftT m SPMF] in
lemma tvDist_comm (mx my : m α) : tvDist mx my = tvDist my mx :=
  SPMF.tvDist_comm _ _


-- @@ L88-89 verbatim
omit [Monad m] [LawfulMonadLiftT m SPMF] in
lemma tvDist_nonneg (mx my : m α) : 0 ≤ tvDist mx my := SPMF.tvDist_nonneg _ _


-- @@ L91-94 verbatim
omit [Monad m] [LawfulMonadLiftT m SPMF] in
lemma tvDist_triangle (mx my mz : m α) :
    tvDist mx mz ≤ tvDist mx my + tvDist my mz :=
  SPMF.tvDist_triangle _ _ _


-- @@ L96-97 verbatim
omit [Monad m] [LawfulMonadLiftT m SPMF] in
lemma tvDist_le_one (mx my : m α) : tvDist mx my ≤ 1 := SPMF.tvDist_le_one _ _


-- @@ L99-101 expanded
lemma tvDist_map_le [LawfulMonad m] {β : Type u} (f : α → β) (mx my : m α) :
    tvDist (f <$> mx) (f <$> my) ≤ tvDist mx my := by
  simpa only [tvDist, evalSPMF_map] using SPMF.tvDist_map_le f (evalSPMF mx) (evalSPMF my)


-- @@ L103-105 verbatim
lemma tvDist_bind_right_le [LawfulMonad m] {β : Type u} (f : α → m β) (mx my : m α) :
    tvDist (mx >>= f) (my >>= f) ≤ tvDist mx my := by
  simpa only [tvDist, evalSPMF_bind] using SPMF.tvDist_bind_right_le _ _ _


-- @@ L107-107 verbatim
/-! ### TV distance bounds -/


-- @@ L109-143 expanded
omit [LawfulMonadLiftT m SPMF] in
/-- Total variation distance is bounded by the probability of an event `p` whenever the two
computations have equal output distribution off `p` (and equal probability of `p`). -/
lemma tvDist_le_probEvent_of_probOutput_eq_of_not {mx my : m α} [NeverFail mx] [NeverFail my]
    (p : α → Prop) (h_eq : ∀ x, ¬p x → probOutput mx x = probOutput my x)
    (h_event_eq : probEvent mx p = probEvent my p) : tvDist mx my ≤ (probEvent mx p).toReal := by
  classical
  rw [tvDist, SPMF.tvDist, PMF.tvDist]
  refine ENNReal.toReal_mono probEvent_ne_top ?_
  rw [PMF.etvDist, tsum_option _ ENNReal.summable]
  have hfailx : (evalSPMF mx).toPMF none = 0 := by
    simpa only [← SPMF.run_eq_toPMF, probFailure_def] using probFailure_eq_zero (mx := mx)
  have hfaily : (evalSPMF my).toPMF none = 0 := by
    simpa only [← SPMF.run_eq_toPMF, probFailure_def] using probFailure_eq_zero (mx := my)
  have hsum :
    (∑' x, ENNReal.absDiff ((evalSPMF mx).toPMF (some x)) ((evalSPMF my).toPMF (some x))) =
      ∑' x, ENNReal.absDiff (probOutput mx x) (probOutput my x) :=
    by
    refine tsum_congr fun x => ?_
    simp [probOutput_def, SPMF.apply_eq_toPMF_some]
  rw [hfailx, hfaily, ENNReal.absDiff_self, zero_add, hsum]
  calc
    (∑' x, ENNReal.absDiff (probOutput mx x) (probOutput my x)) / 2 ≤
        (∑' x, if p x then (probOutput mx x + probOutput my x) else 0) / 2 :=
      by
      gcongr with x
      by_cases hx : p x
      · simpa [hx] using ENNReal.absDiff_le_add (probOutput mx x) (probOutput my x)
      · simp [hx, h_eq x hx, ENNReal.absDiff_self]
    _ = (probEvent mx p + probEvent my p) / 2 :=
      by
      rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
      exact congrArg (· / 2) (tsum_congr fun x => by by_cases hx : p x <;> simp [hx])
    _ = probEvent mx p := by
      rw [← h_event_eq, ← two_mul, mul_div_assoc]
      simp [ENNReal.mul_div_cancel two_ne_zero ofNat_ne_top]


-- @@ L145-145 verbatim
end monadic


-- @@ L147-147 verbatim
/-! ### TV distance for bind (left) -/


-- @@ L149-167 verbatim
private lemma pmf_etvDist_bind_left_le {α : Type u} {β : Type u}
    (p : PMF α) (f g : α → PMF β) :
    (p.bind f).etvDist (p.bind g) ≤ ∑' a, (f a).etvDist (g a) * p a := by
  have hrhs :
      (∑' a, (f a).etvDist (g a) * p a) =
        (∑' a, (∑' b, ENNReal.absDiff ((f a) b) ((g a) b)) * p a) / 2 := by
    simp only [PMF.etvDist, div_eq_mul_inv, ← ENNReal.tsum_mul_right, mul_right_comm]
  rw [PMF.etvDist, hrhs]
  refine ENNReal.div_le_div_right ?_ 2
  calc ∑' y, ENNReal.absDiff (∑' x, p x * (f x) y) (∑' x, p x * (g x) y)
      ≤ ∑' y, ∑' x, ENNReal.absDiff (p x * (f x) y) (p x * (g x) y) :=
        ENNReal.tsum_le_tsum fun y => ENNReal.absDiff_tsum_le _ _
    _ ≤ ∑' y, ∑' x, ENNReal.absDiff ((f x) y) ((g x) y) * p x :=
        ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun x => by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            ENNReal.absDiff_mul_right_le ((f x) y) ((g x) y) (p x)
    _ = ∑' x, ∑' y, ENNReal.absDiff ((f x) y) ((g x) y) * p x := ENNReal.tsum_comm
    _ = ∑' x, (∑' y, ENNReal.absDiff ((f x) y) ((g x) y)) * p x := by
        simp_rw [ENNReal.tsum_mul_right]


-- @@ L169-187 verbatim
private lemma pmf_tvDist_bind_left_le
    {α : Type u} {β : Type u}
    (p : PMF α) (f g : α → PMF β) :
    PMF.tvDist (p.bind f) (p.bind g) ≤ ∑' a, (p a).toReal * PMF.tvDist (f a) (g a) := by
  simp only [PMF.tvDist]
  refine le_trans (ENNReal.toReal_mono ?_ (pmf_etvDist_bind_left_le p f g)) ?_
  · exact ne_top_of_le_ne_top one_ne_top (le_trans
      (ENNReal.tsum_le_tsum fun a => mul_le_mul' (PMF.etvDist_le_one _ _) le_rfl)
      (by simp [p.tsum_coe]))
  · refine le_of_eq ?_
    calc
      ((∑' a, (f a).etvDist (g a) * p a)).toReal
          = ∑' a, ((f a).etvDist (g a) * p a).toReal :=
            ENNReal.tsum_toReal_eq fun a =>
              ENNReal.mul_ne_top (PMF.etvDist_ne_top _ _) (PMF.apply_ne_top _ _)
      _ = ∑' a, (p a).toReal * PMF.tvDist (f a) (g a) := by
              refine tsum_congr fun a => ?_
              rw [ENNReal.toReal_mul, PMF.tvDist]
              ac_rfl


-- @@ L189-200 verbatim
private lemma spmf_tvDist_bind_left_le_liftM
    {α : Type u} {β : Type u}
    (p : PMF α) (f g : α → PMF β) :
    SPMF.tvDist
        ((liftM p : SPMF α) >>= fun a => liftM (f a))
        ((liftM p : SPMF α) >>= fun a => liftM (g a)) ≤
      ∑' a, (p a).toReal * SPMF.tvDist (liftM (f a)) (liftM (g a)) := by
  have h := pmf_tvDist_bind_left_le p (fun a => PMF.map Option.some (f a))
    (fun a => PMF.map Option.some (g a))
  simp_rw [← PMF.bind_pure_comp] at h
  simpa [SPMF.tvDist, SPMF.toPMF_bind, SPMF.toPMF_liftM, Option.elimM,
    PMF.monad_bind_eq_bind, Function.comp_def] using h


-- @@ L202-227 expanded
lemma tvDist_bind_left_le {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] {α : Type u} {β : Type u} (mx : m α) (f g : α → m β) :
    tvDist (mx >>= f) (mx >>= g) ≤ ∑' a, (probOutput mx a).toReal * tvDist (f a) (g a) :=
  by
  rw [tvDist, evalSPMF_bind, evalSPMF_bind]
  simp_rw [evalSPMF_def]
  calc
    SPMF.tvDist ((liftM (liftM mx : PMF α) : SPMF α) >>= fun a => liftM (liftM (f a) : PMF β))
          ((liftM (liftM mx : PMF α) : SPMF α) >>= fun a => liftM (liftM (g a) : PMF β)) ≤
        ∑' a,
          ((liftM mx : PMF α) a).toReal *
            SPMF.tvDist (liftM (liftM (f a) : PMF β)) (liftM (liftM (g a) : PMF β)) :=
      spmf_tvDist_bind_left_le_liftM (liftM mx : PMF α) (fun a => (liftM (f a) : PMF β))
        (fun a => (liftM (g a) : PMF β))
    _ = ∑' a, (probOutput mx a).toReal * tvDist (f a) (g a) :=
      by
      refine tsum_congr fun a => ?_
      have h1 : ((liftM mx : PMF α) a).toReal = (probOutput mx a).toReal :=
        by
        congr 1
        rw [probOutput_def, evalSPMF_def]
        exact (SPMF.liftM_apply (liftM mx : PMF α) a).symm
      have h2 :
        (liftM (liftM (f a) : PMF β) : SPMF β).tvDist (liftM (liftM (g a) : PMF β) : SPMF β) =
          tvDist (f a) (g a) :=
        by
        rw [tvDist, evalSPMF_def, evalSPMF_def]
        rfl
      rw [h1, h2]


-- @@ L229-229 verbatim
/-! ### TV distance for bind with a constant bound -/


-- @@ L231-270 expanded
/-- Total-variation distance is convex over a shared `bind`: if `tvDist (f a) (g a) ≤ c` for every
`a ∈ support mx`, then `tvDist (mx >>= f) (mx >>= g) ≤ c`. The real-valued root of the `const`
bound, with `ℝ≥0∞` companion `ofReal_tvDist_bind_left_le_const`. -/
theorem tvDist_bind_left_le_const {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [EvalDistCompatible m] {α β : Type u} (mx : m α)
    (f g : α → m β) (c : ℝ) (hfg : ∀ a, a ∈ support mx → tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c := by
  classical
  have hprob_ne_top : ∀ a : α, probOutput mx a ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top one_ne_top (probOutput_le_one (mx := mx) (x := a))
  have hp_sum_ne_top : (∑' a : α, probOutput mx a) ≠ ⊤ := by rw [tsum_probOutput_of_liftM_PMF];
    exact one_ne_top
  have hp_summable : Summable (fun a : α => (probOutput mx a).toReal) :=
    ENNReal.summable_toReal hp_sum_ne_top
  have hp_sum_toReal : (∑' a : α, (probOutput mx a).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq hprob_ne_top, tsum_probOutput_of_liftM_PMF, ENNReal.toReal_one]
  have hlhs_nonneg : ∀ a : α, 0 ≤ (probOutput mx a).toReal * tvDist (f a) (g a) := fun _ =>
    mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)
  have hlhs_le_p :
    ∀ a : α, (probOutput mx a).toReal * tvDist (f a) (g a) ≤ (probOutput mx a).toReal := fun _ =>
    mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)
  have hlhs_summable : Summable (fun a : α => (probOutput mx a).toReal * tvDist (f a) (g a)) :=
    Summable.of_nonneg_of_le hlhs_nonneg hlhs_le_p hp_summable
  have hrhs_summable : Summable (fun a : α => (probOutput mx a).toReal * c) :=
    Summable.mul_right _ hp_summable
  refine (tvDist_bind_left_le mx f g).trans ?_
  calc
    (∑' a : α, (probOutput mx a).toReal * tvDist (f a) (g a)) ≤
        ∑' a : α, (probOutput mx a).toReal * c :=
      Summable.tsum_le_tsum
        (fun a => by
          by_cases ha : a ∈ support mx
          · exact mul_le_mul_of_nonneg_left (hfg a ha) ENNReal.toReal_nonneg
          · rw [probOutput_eq_zero_of_not_mem_support ha]; simp)
        hlhs_summable hrhs_summable
    _ = (∑' a : α, (probOutput mx a).toReal) * c := (Summable.tsum_mul_right _ hp_summable)
    _ = c := by rw [hp_sum_toReal, one_mul]


-- @@ L272-280 verbatim
/-- Unrestricted companion of `tvDist_bind_left_le_const`: a uniform per-`a` bound
`tvDist (f a) (g a) ≤ c` lifts through the shared `mx` bind. -/
theorem tvDist_bind_left_le_const'
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {α β : Type u} (mx : m α) (f g : α → m β) (c : ℝ)
    (hfg : ∀ a, tvDist (f a) (g a) ≤ c) :
    tvDist (mx >>= f) (mx >>= g) ≤ c :=
  tvDist_bind_left_le_const mx f g c fun a _ => hfg a


-- @@ L282-298 verbatim
/-- `ℝ≥0∞` form of `tvDist_bind_left_le_const`, matching the quantitative APIs: a per-`a` bound
`ENNReal.ofReal (tvDist (f a) (g a)) ≤ ε` on the support of `mx` lifts through the shared bind. -/
theorem ofReal_tvDist_bind_left_le_const
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {α β : Type u}
    (mx : m α) (f g : α → m β) (ε : ℝ≥0∞)
    (hfg : ∀ a, a ∈ support mx → ENNReal.ofReal (tvDist (f a) (g a)) ≤ ε) :
    ENNReal.ofReal (tvDist (mx >>= f) (mx >>= g)) ≤ ε := by
  classical
  by_cases htop : ε = (⊤ : ℝ≥0∞)
  · simp [htop]
  · have hreal : tvDist (mx >>= f) (mx >>= g) ≤ ε.toReal :=
      tvDist_bind_left_le_const mx f g ε.toReal
        (fun a ha => (ENNReal.ofReal_le_iff_le_toReal htop).mp (hfg a ha))
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hreal


-- @@ L300-308 verbatim
/-- Unrestricted companion of `ofReal_tvDist_bind_left_le_const`. -/
theorem ofReal_tvDist_bind_left_le_const'
    {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [EvalDistCompatible m]
    {α β : Type u}
    (mx : m α) (f g : α → m β) (ε : ℝ≥0∞)
    (hfg : ∀ a, ENNReal.ofReal (tvDist (f a) (g a)) ≤ ε) :
    ENNReal.ofReal (tvDist (mx >>= f) (mx >>= g)) ≤ ε :=
  ofReal_tvDist_bind_left_le_const mx f g ε fun a _ => hfg a


-- @@ L310-310 verbatim
/-! ### TV distance for bind with a bad event -/


-- @@ L312-342 expanded
/-- Bound the weighted TV sum from `tvDist_bind_left_le` by the probability of a bad event
when the two continuations are distributionally equal off that event. -/
lemma tsum_probOutput_toReal_mul_tvDist_le_probEvent {m : Type u → Type v} [Monad m]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] {α : Type u} {β : Type u} (mx : m α) (f g : α → m β)
    (bad : α → Prop) (h_eq : ∀ a, ¬bad a → evalSPMF (f a) = evalSPMF (g a)) :
    (∑' a, (probOutput mx a).toReal * tvDist (f a) (g a)) ≤ (probEvent mx bad).toReal := by
  classical
  have h_p_summable : Summable (fun a : α => (probOutput mx a).toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
  calc
    (∑' a, (probOutput mx a).toReal * tvDist (f a) (g a)) ≤
        ∑' a, if bad a then (probOutput mx a).toReal else 0 :=
      by
      refine
        Summable.tsum_le_tsum (fun a => ?_)
          (h_p_summable.of_nonneg_of_le
            (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
            (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _)))
          (h_p_summable.of_nonneg_of_le
            (fun a => by by_cases ha : bad a <;> simp [ha, ENNReal.toReal_nonneg])
            (fun a => by by_cases ha : bad a <;> simp [ha, ENNReal.toReal_nonneg]))
      by_cases ha : bad a
      · simpa [ha] using mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one (f a) (g a))
      · simp [ha, (tvDist_eq_zero_iff (f a) (g a)).2 (h_eq a ha)]
    _ = (probEvent mx bad).toReal :=
      by
      rw [probEvent_eq_tsum_ite,
        ENNReal.tsum_toReal_eq fun a => by
          by_cases ha : bad a
          · simp [ha, ne_top_of_le_ne_top one_ne_top (probOutput_le_one (mx := mx) (x := a))]
          · simp [ha]]
      exact tsum_congr fun a => by by_cases ha : bad a <;> simp [ha]


-- @@ L344-353 expanded
/-- If two continuations are equal off a bad event, binding them over the same base
computation changes TV distance by at most the probability of that bad event. -/
lemma tvDist_bind_left_event_le {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] {α : Type u} {β : Type u} (mx : m α) (f g : α → m β) (bad : α → Prop)
    (h_eq : ∀ a, ¬bad a → evalSPMF (f a) = evalSPMF (g a)) :
    tvDist (mx >>= f) (mx >>= g) ≤ (probEvent mx bad).toReal :=
  le_trans (tvDist_bind_left_le mx f g)
    (tsum_probOutput_toReal_mul_tvDist_le_probEvent mx f g bad h_eq)


-- @@ L355-365 expanded
/-- `ENNReal` form of `tvDist_bind_left_event_le`, matching the quantitative
identical-until-bad APIs. -/
lemma ofReal_tvDist_bind_left_event_le {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] {α : Type u} {β : Type u} (mx : m α) (f g : α → m β)
    (bad : α → Prop) (h_eq : ∀ a, ¬bad a → evalSPMF (f a) = evalSPMF (g a)) :
    ENNReal.ofReal (tvDist (mx >>= f) (mx >>= g)) ≤ probEvent mx bad :=
  by
  refine le_trans (ENNReal.ofReal_le_ofReal (tvDist_bind_left_event_le mx f g bad h_eq)) ?_
  rw [ENNReal.ofReal_toReal probEvent_ne_top]


-- @@ L367-381 expanded
/-- Bind/event TV bound with different base computations: the base TV distance plus the
bad-event probability controls the whole bind. -/
lemma tvDist_bind_event_le {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] {α : Type u} {β : Type u} (mx my : m α) (f g : α → m β)
    (bad : α → Prop) (h_eq : ∀ a, ¬bad a → evalSPMF (f a) = evalSPMF (g a)) :
    tvDist (mx >>= f) (my >>= g) ≤ (probEvent mx bad).toReal + tvDist mx my := by
  calc
    tvDist (mx >>= f) (my >>= g) ≤ tvDist (mx >>= f) (mx >>= g) + tvDist (mx >>= g) (my >>= g) :=
      tvDist_triangle _ _ _
    _ ≤ (probEvent mx bad).toReal + tvDist mx my :=
      add_le_add (tvDist_bind_left_event_le mx f g bad h_eq) (tvDist_bind_right_le g mx my)


-- @@ L383-394 expanded
/-- `ENNReal` form of `tvDist_bind_event_le`. -/
lemma ofReal_tvDist_bind_event_le {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] {α : Type u} {β : Type u} (mx my : m α) (f g : α → m β)
    (bad : α → Prop) (h_eq : ∀ a, ¬bad a → evalSPMF (f a) = evalSPMF (g a)) :
    ENNReal.ofReal (tvDist (mx >>= f) (my >>= g)) ≤
      probEvent mx bad + ENNReal.ofReal (tvDist mx my) :=
  by
  refine le_trans (ENNReal.ofReal_le_ofReal (tvDist_bind_event_le mx my f g bad h_eq)) ?_
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (tvDist_nonneg mx my),
    ENNReal.ofReal_toReal probEvent_ne_top]


-- @@ L396-411 expanded
/-- Bind/event TV bound with different base computations, charging the bad-event
probability under the right base computation. This is the symmetric orientation of
`tvDist_bind_event_le`, useful when the bad event is introduced by the simulated side. -/
lemma tvDist_bind_event_right_le {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadLiftT m PMF]
    [LawfulMonadLiftT m PMF] {α : Type u} {β : Type u} (mx my : m α) (f g : α → m β)
    (bad : α → Prop) (h_eq : ∀ a, ¬bad a → evalSPMF (f a) = evalSPMF (g a)) :
    tvDist (mx >>= f) (my >>= g) ≤ tvDist mx my + (probEvent my bad).toReal := by
  calc
    tvDist (mx >>= f) (my >>= g) ≤ tvDist (mx >>= f) (my >>= f) + tvDist (my >>= f) (my >>= g) :=
      tvDist_triangle _ _ _
    _ ≤ tvDist mx my + (probEvent my bad).toReal :=
      add_le_add (tvDist_bind_right_le f mx my) (tvDist_bind_left_event_le my f g bad h_eq)


-- @@ L413-424 expanded
/-- `ENNReal` form of `tvDist_bind_event_right_le`. -/
lemma ofReal_tvDist_bind_event_right_le {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] {α : Type u} {β : Type u} (mx my : m α)
    (f g : α → m β) (bad : α → Prop) (h_eq : ∀ a, ¬bad a → evalSPMF (f a) = evalSPMF (g a)) :
    ENNReal.ofReal (tvDist (mx >>= f) (my >>= g)) ≤
      ENNReal.ofReal (tvDist mx my) + probEvent my bad :=
  by
  refine le_trans (ENNReal.ofReal_le_ofReal (tvDist_bind_event_right_le mx my f g bad h_eq)) ?_
  rw [ENNReal.ofReal_add (tvDist_nonneg mx my) ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal probEvent_ne_top]


-- @@ L426-426 verbatim
section bool_tvdist


-- @@ L428-428 verbatim
variable {m : Type → Type v} [MonadLiftT m SPMF]


-- @@ L430-445 expanded
/-- For any `Bool` computation, the difference of `Pr[= true]` values is bounded by
TV distance. -/
lemma abs_probOutput_toReal_sub_le_tvDist (game₁ game₂ : m Bool) :
    |(probOutput game₁ true).toReal - (probOutput game₂ true).toReal| ≤ tvDist game₁ game₂ :=
  by
  simp only [probOutput_def, SPMF.apply_eq_toPMF_some, tvDist, SPMF.tvDist, PMF.tvDist]
  have happ :
    ∀ (p : PMF (Option Bool)),
      ((fun x : Option Bool => if x = some true then some () else none) <$> p) (some ()) =
        p (some true) :=
    fun p => by simp [PMF.map_apply_eq, tsum_fintype]
  rw [← ENNReal.absDiff_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  apply ENNReal.toReal_mono (PMF.etvDist_ne_top _ _)
  rw [← happ (evalSPMF game₁).toPMF, ← happ (evalSPMF game₂).toPMF, ← PMF.etvDist_option_punit]
  exact
    PMF.etvDist_map_le (fun x : Option Bool => if x = some true then some () else none)
      (evalSPMF game₁).toPMF (evalSPMF game₂).toPMF


-- @@ L447-447 verbatim
end bool_tvdist


-- @@ L449-449 verbatim
end
