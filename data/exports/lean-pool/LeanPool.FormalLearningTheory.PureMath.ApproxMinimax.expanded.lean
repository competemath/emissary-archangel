/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
module

public import LeanPool.FormalLearningTheory.PureMath.KLDivergence
import Mathlib.Algebra.BigOperators.Field


-- @@ L11-36 verbatim
/-!
# Approximate Minimax for Finite Boolean Games

Infrastructure for the minimax theorem in finite Boolean games: PMF construction
utilities, payoff analysis, covering arguments, and MWU potential bounds.

## Main definitions

- `normalizeToPMF` : normalize a positive weight vector to FinitePMF
- `pointMassPMF` : point mass distribution on a single element
- `uniformPMF` : uniform distribution over a Fintype
- `empiricalPMF` : empirical distribution of a finite sequence
- `boolGamePayoff` : expected payoff of a distribution in a Boolean game
- `MWUConfig` : multiplicative weights update state

## Main results

- `exists_covering_row` : if minimax value > 0, every column has a covering row
- `covering_minimax` : ∃ p, ∀ c, 1/|C| ≤ boolGamePayoff(p, c)
- `finite_approx_minimax` : approximate minimax for finite Boolean games
- `mwu_potential_T_bound` : after T MWU rounds, Φ_T ≤ |C| · (1 - ηv)^T

## References

- Arora, Hazan, Kale, "The Multiplicative Weights Update Method", ToC 8(1), 2012
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
open Finset


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
/-! ## PMF Construction Utilities -/


-- @@ L46-55 verbatim
/-- Normalize a strictly positive weight vector to a FinitePMF. -/
def normalizeToPMF {C : Type*} [Fintype C] [Nonempty C]
    (w : C → ℝ) (hw : ∀ c, 0 < w c) : FinitePMF C where
  prob c := w c / ∑ c' : C, w c'
  prob_nonneg c :=
    div_nonneg (le_of_lt (hw c))
      (Finset.sum_nonneg fun c' _ => le_of_lt (hw c'))
  prob_sum_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (Finset.sum_pos (fun c _ => hw c) univ_nonempty))


-- @@ L57-59 verbatim
lemma normalizeToPMF_prob {C : Type*} [Fintype C] [Nonempty C]
    (w : C → ℝ) (hw : ∀ c, 0 < w c) (c : C) :
    (normalizeToPMF w hw).prob c = w c / ∑ c' : C, w c' := rfl


-- @@ L61-66 verbatim
/-- Point mass PMF at a single element. -/
def pointMassPMF {C : Type*} [Fintype C] [DecidableEq C] (c₀ : C) :
    FinitePMF C where
  prob c := if c = c₀ then 1 else 0
  prob_nonneg c := by split_ifs <;> norm_num
  prob_sum_one := by simp [sum_ite_eq']


-- @@ L68-70 verbatim
/-- Uniform PMF over a nonempty Fintype. -/
def uniformPMF (C : Type*) [Fintype C] [Nonempty C] : FinitePMF C :=
  normalizeToPMF (fun _ => (1 : ℝ)) fun _ => one_pos


-- @@ L72-85 verbatim
/-- Build FinitePMF from empirical frequencies of a finite sequence. -/
def empiricalPMF {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℕ} (hT : 0 < T) (rs : Fin T → α) : FinitePMF α where
  prob a := (univ.filter (fun t => rs t = a)).card / (T : ℝ)
  prob_nonneg a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  prob_sum_one := by
    rw [← Finset.sum_div]
    suffices h : (∑ a : α, ((univ.filter (fun t : Fin T => rs t = a)).card : ℝ)) = T by
      rw [h]; exact div_self (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT))
    -- Use card_eq_sum_card_fiberwise: #s = Σ_{b ∈ t} #{a ∈ s | f a = b}
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := rs) (s := univ) (t := univ)
      (fun t _ => mem_univ (rs t))
    simp_all


-- @@ L87-87 verbatim
/-! ## Boolean Game Payoff -/


-- @@ L89-92 verbatim
/-- Expected payoff of distribution p against column c in a Boolean game. -/
def boolGamePayoff {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FinitePMF R) (c : C) : ℝ :=
  ∑ r : R, p.prob r * (if M r c then (1 : ℝ) else 0)


-- @@ L94-98 verbatim
lemma boolGamePayoff_nonneg {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FinitePMF R) (c : C) :
    0 ≤ boolGamePayoff M p c :=
  Finset.sum_nonneg fun r _ =>
    mul_nonneg (p.prob_nonneg r) (by split_ifs <;> norm_num)


-- @@ L100-106 verbatim
lemma boolGamePayoff_le_one {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FinitePMF R) (c : C) :
    boolGamePayoff M p c ≤ 1 := by
  calc boolGamePayoff M p c
      ≤ ∑ r : R, p.prob r := Finset.sum_le_sum fun r _ =>
        mul_le_of_le_one_right (p.prob_nonneg r) (by split_ifs <;> norm_num)
    _ = 1 := p.prob_sum_one


-- @@ L108-118 verbatim
/-- Point mass payoff equals the game value at that row-column pair. -/
lemma boolGamePayoff_pointMass {R C : Type*} [Fintype R] [DecidableEq R]
    (M : R → C → Bool) (r₀ : R) (c : C) :
    boolGamePayoff M (pointMassPMF r₀) c = if M r₀ c then 1 else 0 := by
  simp only [boolGamePayoff, pointMassPMF]
  conv_lhs =>
    arg 2; ext r
    rw [show (if r = r₀ then (1 : ℝ) else 0) * (if M r c then (1 : ℝ) else 0) =
      if r = r₀ then (if M r c then 1 else 0) else 0 from by
        split_ifs <;> simp]
  simp


-- @@ L120-132 verbatim
/-- The minimax value of a Boolean game is at most 1. -/
lemma minimax_value_le_one {R C : Type*} [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    v ≤ 1 := by
  obtain ⟨r, hr⟩ := hrow (uniformPMF C)
  calc v ≤ ∑ c : C, (uniformPMF C).prob c *
      (if M r c then (1 : ℝ) else 0) := hr
    _ ≤ ∑ c : C, (uniformPMF C).prob c := Finset.sum_le_sum fun c _ =>
        mul_le_of_le_one_right ((uniformPMF C).prob_nonneg c)
          (by split_ifs <;> norm_num)
    _ = 1 := (uniformPMF C).prob_sum_one


-- @@ L134-134 verbatim
/-! ## Covering Row Lemma -/


-- @@ L136-156 verbatim
/-- If minimax value > 0, every column has a row with M(r,c) = true. -/
lemma exists_covering_row {R C : Type*} [Fintype C]
    (M : R → C → Bool) (v : ℝ) (hv : 0 < v)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ c₀ : C, ∃ r : R, M r c₀ = true := by
  classical
  intro c₀
  obtain ⟨r, hr⟩ := hrow (pointMassPMF c₀)
  refine ⟨r, ?_⟩
  by_contra h
  have hf : M r c₀ = false := Bool.eq_false_iff.mpr h
  have : (∑ c : C, (pointMassPMF c₀).prob c *
      (if M r c then (1 : ℝ) else 0)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro c _
    simp only [pointMassPMF]
    split_ifs with h1 h2
    · subst h1; rw [hf] at h2; exact absurd h2 Bool.false_ne_true
    all_goals simp
  linarith


-- @@ L158-158 verbatim
/-! ## Covering Minimax Theorem -/


-- @@ L160-201 verbatim
/-- **Covering-based minimax**: if the minimax value > 0, there exists
    a row distribution with payoff ≥ 1/|C| against every column.

    Proof: for each column c, pick a row r_c with M(r_c, c) = true
    (guaranteed by `exists_covering_row`). The empirical distribution of
    these rows gives payoff ≥ 1/|C| against every column, since each
    column c₀ is covered by at least one row (namely r_c₀). -/
theorem covering_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ) (hv : 0 < v)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FinitePMF R, ∀ c : C,
      (1 : ℝ) / Fintype.card C ≤ boolGamePayoff M p c := by
  classical
  have hcover := exists_covering_row M v hv hrow
  choose r_c hr_c using hcover
  let n := Fintype.card C
  have hn : 0 < n := Fintype.card_pos
  let eC := (Fintype.equivFin C).symm
  let rs : Fin n → R := fun i => r_c (eC i)
  refine ⟨empiricalPMF hn rs, fun c₀ => ?_⟩
  simp only [boolGamePayoff]
  let i₀ : Fin n := (Fintype.equivFin C) c₀
  have hrs_i₀ : rs i₀ = r_c c₀ := by
    simp only [rs, eC, i₀, Equiv.symm_apply_apply]
  calc (1 : ℝ) / n
      = (1 : ℝ) / n * 1 := (mul_one _).symm
    _ ≤ (empiricalPMF hn rs).prob (r_c c₀) * (if M (r_c c₀) c₀ then 1 else 0) := by
        simp only [hr_c c₀]
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        simp only [empiricalPMF]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        rw [Nat.one_le_cast]
        apply Finset.card_pos.mpr
        exact ⟨i₀, by simp [hrs_i₀]⟩
    _ ≤ ∑ r : R, (empiricalPMF hn rs).prob r * (if M r c₀ then 1 else 0) := by
        apply Finset.single_le_sum (f := fun r =>
          (empiricalPMF hn rs).prob r * (if M r c₀ then (1 : ℝ) else 0))
        · intro r _
          exact mul_nonneg ((empiricalPMF hn rs).prob_nonneg r) (by split_ifs <;> norm_num)
        · exact mem_univ _


-- @@ L203-203 verbatim
/-! ## Approximate Minimax Theorem -/


-- @@ L205-226 verbatim
/-- **Approximate minimax for finite Boolean games**.

If for every column mixture q, the row player has a pure best response
with expected payoff ≥ v, then there exists a row mixture p such that
every pure column gets payoff ≥ v - ε.

This version uses the covering argument (payoff ≥ 1/|C| for all columns)
combined with the feasibility condition v - ε ≤ 1/|C|. -/
theorem finite_approx_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C] [Nonempty R]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (hε_feasible : v - ε ≤ 1 / Fintype.card C) :
    ∃ p : FinitePMF R, ∀ c : C,
      v - ε ≤ boolGamePayoff M p c := by
  classical
  by_cases hv : v ≤ 0
  · exact ⟨uniformPMF R, fun c => le_trans (by linarith) (boolGamePayoff_nonneg M _ c)⟩
  · push Not at hv
    obtain ⟨p, hp⟩ := covering_minimax M v hv hrow
    exact ⟨p, fun c => le_trans hε_feasible (hp c)⟩


-- @@ L228-232 verbatim
/-! ## MWU Infrastructure

Multiplicative Weights Update state and potential analysis. The potential bound
is the core analytic result: after T rounds, Φ_T ≤ |C| · (1 - ηv)^T.
-/


-- @@ L234-238 verbatim
/-- MWU config: weight vector with positivity proof. -/
structure MWUConfig (C : Type*) [Fintype C] where
  /-- Current nonnegative weight for each expert/concept. -/
  weights : C → ℝ
  weights_pos : ∀ c, 0 < weights c


-- @@ L240-242 verbatim
/-- Potential = sum of weights. -/
def MWUConfig.potential {C : Type*} [Fintype C] (cfg : MWUConfig C) : ℝ :=
  ∑ c : C, cfg.weights c


-- @@ L244-246 verbatim
lemma MWUConfig.potential_pos {C : Type*} [Fintype C] [Nonempty C]
    (cfg : MWUConfig C) : 0 < cfg.potential :=
  Finset.sum_pos (fun c _ => cfg.weights_pos c) univ_nonempty


-- @@ L248-251 verbatim
/-- Initial config: all weights = 1. -/
def mwuInit (C : Type*) [Fintype C] : MWUConfig C where
  weights := fun _ => 1
  weights_pos := fun _ => one_pos


-- @@ L253-255 verbatim
lemma mwuInit_potential (C : Type*) [Fintype C] :
    (mwuInit C).potential = Fintype.card C := by
  simp [MWUConfig.potential, mwuInit, sum_const, nsmul_eq_mul, mul_one]


-- @@ L257-260 verbatim
/-- Normalize config to PMF. -/
def MWUConfig.toPMF {C : Type*} [Fintype C] [Nonempty C]
    (cfg : MWUConfig C) : FinitePMF C :=
  normalizeToPMF cfg.weights cfg.weights_pos


-- @@ L262-267 verbatim
/-- One MWU update step on weights. -/
def mwuUpdateWeights {C : Type*} [Fintype C] {R : Type*}
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1)
    (cfg : MWUConfig C) (r : R) : MWUConfig C where
  weights c := cfg.weights c * (if M r c then (1 - η) else 1)
  weights_pos c := mul_pos (cfg.weights_pos c) (by split_ifs <;> linarith)


-- @@ L269-289 verbatim
/-- Best response payoff ≥ v · Φ in terms of weights. -/
lemma best_response_payoff_weights {R C : Type*} [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (cfg : MWUConfig C) :
    v * cfg.potential ≤
    ∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) := by
  have hr := (hrow cfg.toPMF).choose_spec
  have hΦ_pos := cfg.potential_pos
  -- hr says: v ≤ Σ_c (w(c)/Φ) · M(r,c) = (Σ_c w(c)·M(r,c)) / Φ
  -- So v · Φ ≤ Σ_c w(c) · M(r,c)
  have key : (∑ c : C, cfg.toPMF.prob c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0)) =
    (∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0)) / cfg.potential := by
    simp only [MWUConfig.toPMF, normalizeToPMF, MWUConfig.potential]
    rw [Finset.sum_div]; congr 1; ext c; field_simp
  rw [key] at hr
  rwa [le_div_iff₀ hΦ_pos] at hr


-- @@ L291-325 verbatim
/-- Potential bound after one step: Φ' ≤ Φ · (1 - η·v). -/
lemma potential_one_step_bound {R C : Type*} [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη : 0 ≤ η) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (cfg : MWUConfig C) :
    (mwuUpdateWeights M η hη1 cfg (hrow cfg.toPMF).choose).potential ≤
    cfg.potential * (1 - η * v) := by
  simp only [MWUConfig.potential, mwuUpdateWeights]
  -- LHS = Σ_c w(c) * (if M r c then 1-η else 1)
  -- We show this equals Φ - η * Σ_c w(c) * M(r,c)
  have hsum_eq : (∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then 1 - η else 1)) =
    (∑ c : C, cfg.weights c) -
    η * ∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) := by
    have : ∀ c : C, cfg.weights c *
        (if M (hrow cfg.toPMF).choose c then 1 - η else 1) =
      cfg.weights c - η * (cfg.weights c *
        (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0)) := by
      intro c; split_ifs <;> ring
    simp_rw [this, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum_eq]
  -- RHS = Φ * (1 - ηv) = Φ - ηvΦ
  -- Need: Φ - η * S ≤ Φ - η * v * Φ, i.e., η * v * Φ ≤ η * S
  have hbr := best_response_payoff_weights M v hrow cfg
  -- hbr : v * Φ ≤ S where S = Σ_c w(c) · M(r,c)
  set S := ∑ c : C, cfg.weights c *
    (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) with hS_def
  -- From hbr: v * Φ ≤ S, so η * v * Φ ≤ η * S
  have h1 : η * (v * cfg.potential) ≤ η * S := mul_le_mul_of_nonneg_left hbr hη
  -- So Φ - η * S ≤ Φ - η * v * Φ = Φ * (1 - η * v)
  -- Unfold potential to make linarith see the connection
  unfold MWUConfig.potential at h1 hbr
  linarith


-- @@ L327-337 verbatim
/-- MWU run: iterate T steps, returning final config and row sequence. -/
def mwuRun {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    (T : ℕ) → MWUConfig C × (Fin T → R)
  | 0 => (mwuInit C, Fin.elim0)
  | T + 1 =>
    let ⟨cfg, rows⟩ := mwuRun M η hη1 v hrow T
    let r := (hrow cfg.toPMF).choose
    (mwuUpdateWeights M η hη1 cfg r, Fin.snoc rows r)


-- @@ L339-345 verbatim
/-- The MWU config after T steps. -/
abbrev mwuConfig {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) : MWUConfig C :=
  (mwuRun M η hη1 v hrow T).1


-- @@ L347-353 verbatim
/-- The MWU row sequence after T steps. -/
abbrev mwuRows {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) : Fin T → R :=
  (mwuRun M η hη1 v hrow T).2


-- @@ L355-383 verbatim
/-- **Potential bound after T steps**: Φ_T ≤ |C| · (1 - ηv)^T.

This is the core MWU guarantee. Combined with individual weight lower
bounds (w_T(c) = (1-η)^{losses(c)}), it yields the regret bound. -/
theorem mwu_potential_T_bound {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη : 0 ≤ η) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) :
    (mwuConfig M η hη1 v hrow T).potential ≤
    Fintype.card C * (1 - η * v) ^ T := by
  induction T with
  | zero =>
    simp only [mwuConfig, mwuRun, mwuInit_potential, pow_zero, mul_one, le_refl]
  | succ T ih =>
    simp only [mwuConfig, mwuRun] at ih ⊢
    set run_T := mwuRun M η hη1 v hrow T
    set cfg_T := run_T.1
    set r := (hrow cfg_T.toPMF).choose
    have hstep := potential_one_step_bound M η hη hη1 v hrow cfg_T
    simp only [cfg_T] at hstep
    have hv1 : v ≤ 1 := minimax_value_le_one M v hrow
    have h1ηv : 0 ≤ 1 - η * v := by nlinarith [mul_le_of_le_one_left hη hv1]
    calc (mwuUpdateWeights M η hη1 cfg_T
            ((hrow cfg_T.toPMF).choose)).potential
        ≤ cfg_T.potential * (1 - η * v) := hstep
      _ ≤ (↑(Fintype.card C) * (1 - η * v) ^ T) * (1 - η * v) :=
          mul_le_mul_of_nonneg_right ih h1ηv
      _ = ↑(Fintype.card C) * (1 - η * v) ^ (T + 1) := by ring


-- @@ L385-385 verbatim
/-! ## MWU Individual Weight Tracking + Regret Extraction -/


-- @@ L387-398 verbatim
/-- Count how many rounds hit a fixed column, aligned to the recursion of `mwuRun`. -/
private def mwuHitCount
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    (T : ℕ) → C → ℕ
  | 0, _ => 0
  | T + 1, c =>
      let cfg := mwuConfig M η hη1 v hrow T
      let r := (hrow cfg.toPMF).choose
      mwuHitCount M η hη1 v hrow T c + if M r c then 1 else 0


-- @@ L400-407 verbatim
/-- A single weight is bounded by the potential. -/
private lemma weight_le_potential
    {C : Type*} [Fintype C] (cfg : MWUConfig C) (c : C) :
    cfg.weights c ≤ cfg.potential := by
  unfold MWUConfig.potential
  exact Finset.single_le_sum
    (fun c _ => le_of_lt (cfg.weights_pos c))
    (by simp)


-- @@ L409-425 verbatim
/-- Exact individual-weight tracking: the weight of column `c` after `T` rounds is
    `(1-η)` to the number of rounds in which `c` was hit. -/
private lemma mwu_weight_eq_pow_hitCount
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ (T : ℕ) (c : C),
      (mwuConfig M η hη1 v hrow T).weights c =
        (1 - η) ^ (mwuHitCount M η hη1 v hrow T c)
  | 0, c => by
      simp [mwuConfig, mwuRun, mwuHitCount, mwuInit]
  | T + 1, c => by
      simp [mwuConfig, mwuRun, mwuHitCount, mwuUpdateWeights,
        mwu_weight_eq_pow_hitCount M η hη1 v hrow T c,
        mul_comm]
      split_ifs <;> ring


-- @@ L427-444 verbatim
/-- The recursive hit counter agrees with the sum of Boolean indicators over the
    emitted row sequence. -/
private lemma mwuHitCount_eq_sum_indicator
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ (T : ℕ) (c : C),
      (mwuHitCount M η hη1 v hrow T c : ℝ) =
        ∑ t : Fin T, if M (mwuRows M η hη1 v hrow T t) c then (1 : ℝ) else 0
  | 0, c => by
      simp [mwuHitCount, mwuRows, mwuRun]
  | T + 1, c => by
      simp only [mwuHitCount, mwuRows, mwuRun]
      push_cast
      rw [mwuHitCount_eq_sum_indicator M η hη1 v hrow T c]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc]


-- @@ L446-472 verbatim
/-- Specialized empirical-payoff identity for ApproxMinimax
    (avoids cyclic import with FiniteVCApprox). -/
private lemma boolGamePayoff_empirical_eq_avg
    {R C : Type*} [Fintype R] [DecidableEq R]
    {T : ℕ} (hT : 0 < T) (rs : Fin T → R) (M : R → C → Bool) (c : C) :
    boolGamePayoff M (empiricalPMF hT rs) c =
      (∑ t : Fin T, if M (rs t) c then (1 : ℝ) else 0) / T := by
  simp only [boolGamePayoff, empiricalPMF]
  conv_lhs => arg 2; ext r; rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  symm
  conv_lhs =>
    rw [show (∑ t : Fin T, if M (rs t) c then (1 : ℝ) else 0) =
      ∑ r : R, ∑ t ∈ univ.filter (fun t => rs t = r),
        (if M (rs t) c then (1 : ℝ) else 0) from by
      rw [← Finset.sum_biUnion (s := univ)]
      · congr 1; ext t; simp
      · intro r₁ _ r₂ _ hne
        simp only [Function.onFun, Finset.disjoint_filter]
        simp_all]
  congr 1
  ext r
  rw [Finset.sum_congr rfl (fun t ht => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht])]
  rw [Finset.sum_const, nsmul_eq_mul]


-- @@ L474-485 verbatim
/-- Empirical payoff of the MWU row sequence equals the normalized hit count. -/
private lemma boolGamePayoff_empirical_eq_hitCount
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    [DecidableEq R]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    {T : ℕ} (hT : 0 < T) (c : C) :
    boolGamePayoff M (empiricalPMF hT (mwuRows M η hη1 v hrow T)) c =
      (mwuHitCount M η hη1 v hrow T c : ℝ) / T := by
  rw [boolGamePayoff_empirical_eq_avg]
  rw [← mwuHitCount_eq_sum_indicator M η hη1 v hrow T c]


-- @@ L487-580 verbatim
/-- Arithmetic core: from the potential bound and sufficiently small η /
    large T, deduce a per-column hit-rate lower bound.
    Uses Real.log — exactly 4 Mathlib lemmas. -/
private lemma hitRate_from_potential
    {N H T : ℕ} {η v ε : ℝ}
    (hNpos : 0 < (N : ℝ))
    (hη : 0 < η) (hη1 : η < 1)
    (hv1 : v ≤ 1)
    (hTpos : 0 < T)
    (hpot :
      (1 - η) ^ H ≤ (N : ℝ) * (1 - η * v) ^ T)
    (hηsmall : η ≤ ε / 4)
    (hlargeT : Real.log (N : ℝ) / (η * T) ≤ ε / 4) :
    v - ε ≤ (H : ℝ) / T := by
  have hbase : 0 < 1 - η := by linarith
  have hbasev : 0 < 1 - η * v := by
    have hηv_le : η * v ≤ η := mul_le_of_le_one_right (le_of_lt hη) hv1
    linarith
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hHnonneg : 0 ≤ (H : ℝ) := by positivity
  have hlog :
      (H : ℝ) * Real.log (1 - η) ≤
        Real.log (N : ℝ) + (T : ℝ) * Real.log (1 - η * v) := by
    have h0 :
        Real.log ((1 - η) ^ H) ≤
          Real.log ((N : ℝ) * (1 - η * v) ^ T) := by
      exact Real.log_le_log (pow_pos hbase H) hpot
    rw [Real.log_pow,
      Real.log_mul hNne (pow_ne_zero T (ne_of_gt hbasev)),
      Real.log_pow] at h0
    simpa [mul_comm, mul_left_comm, mul_assoc] using h0
  have hlog_up : Real.log (1 - η * v) ≤ -η * v :=
    by linarith [Real.log_le_sub_one_of_pos hbasev]
  have hlog_down : -η / (1 - η) ≤ Real.log (1 - η) := by
    have h := Real.one_sub_inv_le_log_of_pos hbase
    have hne : 1 - η ≠ 0 := by linarith
    have hrew : 1 - (1 - η)⁻¹ = -η / (1 - η) := by field_simp [hne]; ring
    simpa [hrew] using h
  have hTreal_nonneg : (0 : ℝ) ≤ T := by positivity
  have hanti :
      (T : ℝ) * η * v - Real.log (N : ℝ) ≤
        (H : ℝ) * (-Real.log (1 - η)) := by
    -- From hlog: H * log(1-η) ≤ log N + T * log(1-η*v)
    -- From hlog_up: log(1-η*v) ≤ -η*v, so T * log(1-η*v) ≤ T*(-η*v)
    -- Hence H * log(1-η) ≤ log N - T*η*v
    -- Since log(1-η) < 0 (as 0 < η < 1), -log(1-η) > 0
    -- So H * (-log(1-η)) ≥ -log N + T*η*v = T*η*v - log N
    by_cases hv_sign : 0 ≤ v
    · nlinarith [mul_nonneg hTreal_nonneg (mul_nonneg (le_of_lt hη) hv_sign)]
    · push Not at hv_sign
      -- v < 0 means T*η*v - log N < 0 ≤ H*(-log(1-η))
      have hlog_neg : Real.log (1 - η) < 0 := Real.log_neg (by linarith) (by linarith)
      have h_rhs_nn : 0 ≤ (H : ℝ) * (-Real.log (1 - η)) := mul_nonneg hHnonneg (by linarith)
      have hTreal_pos : (0 : ℝ) < T := by exact_mod_cast hTpos
      have h_Tηv_neg : (T : ℝ) * η * v < 0 := by
        have := mul_neg_of_pos_of_neg hη hv_sign
        nlinarith
      linarith [Real.log_natCast_nonneg N]
  have hcoef : -Real.log (1 - η) ≤ η / (1 - η) := by
    have : -η / (1 - η) = -(η / (1 - η)) := by ring
    linarith
  have hanti' :
      (T : ℝ) * η * v - Real.log (N : ℝ) ≤
        (H : ℝ) * (η / (1 - η)) :=
    le_trans hanti (mul_le_mul_of_nonneg_left hcoef hHnonneg)
  have hnum :
      (1 - η) * ((T : ℝ) * η * v - Real.log (N : ℝ)) ≤ (H : ℝ) * η := by
    have h1η_nonneg : 0 ≤ 1 - η := by linarith
    calc (1 - η) * ((T : ℝ) * η * v - Real.log (N : ℝ))
        ≤ (1 - η) * ((H : ℝ) * (η / (1 - η))) :=
          mul_le_mul_of_nonneg_left hanti' h1η_nonneg
      _ = (H : ℝ) * η := by field_simp [show (1 : ℝ) - η ≠ 0 by linarith]; try ring
  have hηTpos : 0 < η * (T : ℝ) := by positivity
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hTpos)
  have hrate0 :
      (1 - η) * v - ((1 - η) * Real.log (N : ℝ)) / (η * T) ≤ (H : ℝ) / T := by
    have hdiv :=
      div_le_div_of_nonneg_right hnum (show 0 ≤ η * (T : ℝ) by positivity)
    have hsimpL :
        ((1 - η) * ((T : ℝ) * η * v - Real.log (N : ℝ))) / (η * T) =
          (1 - η) * v - ((1 - η) * Real.log (N : ℝ)) / (η * T) := by
      field_simp [show η ≠ 0 from ne_of_gt hη, hTne]; try ring
    have hsimpR :
        ((H : ℝ) * η) / (η * T) = (H : ℝ) / T := by
      field_simp [show η ≠ 0 from ne_of_gt hη, hTne]; try ring
    simpa [hsimpL, hsimpR] using hdiv
  have hterm1 : v - ε / 4 ≤ (1 - η) * v := by nlinarith [hηsmall, hv1]
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have haux : Real.log (N : ℝ) ≤ (ε / 4) * (η * T) := (div_le_iff₀ hηTpos).mp hlargeT
  have hterm2 :
      ((1 - η) * Real.log (N : ℝ)) / (η * T) ≤ ε / 4 := by
    apply (div_le_iff₀ hηTpos).2
    nlinarith [haux, hlog_nonneg]
  linarith


-- @@ L582-626 verbatim
/-- **Genuine approximate minimax via MWU regret extraction.**
    If every column mixture admits a pure row with expected payoff ≥ v,
    then there is a row mixture with payoff ≥ v - ε against every column. -/
theorem mwu_approx_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty R] [Nonempty C]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
    v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FinitePMF R, ∀ c : C, v - ε ≤ boolGamePayoff M p c := by
  classical
  by_cases htriv : v ≤ ε
  · exact ⟨uniformPMF R, fun c =>
      le_trans (sub_nonpos.mpr htriv) (boolGamePayoff_nonneg M _ c)⟩
  have hεv : ε < v := lt_of_not_ge htriv
  have hv : 0 < v := lt_trans hε hεv
  have hv1 : v ≤ 1 := minimax_value_le_one M v hrow
  let η : ℝ := ε / 4
  have hη : 0 < η := by positivity
  have hη1 : η < 1 := by dsimp [η]; linarith
  let N : ℕ := Fintype.card C
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast @Fintype.card_pos C _ _
  let T : ℕ := max 1 (Nat.ceil (16 * Real.log (N : ℝ) / ε ^ 2))
  have hTpos : 0 < T := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hTlarge0 : 16 * Real.log (N : ℝ) / ε ^ 2 ≤ (T : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast Nat.le_max_right 1 _
  have hlargeT : Real.log (N : ℝ) / (η * T) ≤ ε / 4 := by
    have hηTpos : 0 < η * (T : ℝ) := by positivity
    apply (div_le_iff₀ hηTpos).2
    have hε2pos : 0 < ε ^ 2 := by positivity
    have htmp : 16 * Real.log (N : ℝ) ≤ (T : ℝ) * ε ^ 2 := (div_le_iff₀ hε2pos).mp hTlarge0
    dsimp [η]; nlinarith
  let rows := mwuRows M η hη1 v hrow T
  let p := empiricalPMF hTpos rows
  refine ⟨p, fun c => ?_⟩
  have hpot :
      (1 - η) ^ (mwuHitCount M η hη1 v hrow T c) ≤
        (N : ℝ) * (1 - η * v) ^ T := by
    calc (1 - η) ^ (mwuHitCount M η hη1 v hrow T c)
        = (mwuConfig M η hη1 v hrow T).weights c :=
            (mwu_weight_eq_pow_hitCount M η hη1 v hrow T c).symm
      _ ≤ (mwuConfig M η hη1 v hrow T).potential := weight_le_potential _ c
      _ ≤ (N : ℝ) * (1 - η * v) ^ T := mwu_potential_T_bound M η (le_of_lt hη) hη1 v hrow T
  rw [boolGamePayoff_empirical_eq_hitCount M η hη1 v hrow hTpos c]
  exact hitRate_from_potential hNpos hη hη1 hv1 hTpos hpot (by dsimp [η]; linarith) hlargeT


-- @@ L628-628 verbatim
end -- noncomputable section
