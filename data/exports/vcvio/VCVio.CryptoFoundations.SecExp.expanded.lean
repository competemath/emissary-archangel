/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Instances
public import VCVio.EvalDist.Defs.Semantics
public import VCVio.EvalDist.TVDist
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.QueryTracking.QueryBound


-- @@ L15-24 verbatim
/-!
# Security Experiments

This file defines simple security experiments that succeed unless they terminate with failure.
Each experiment carries bundled subprobabilistic semantics, so the experiment can be interpreted
through an internal semantic monad instead of requiring a global `MonadLiftT _ SPMF` instance
on the ambient monad.

We also define `BoundedAdversary α β` as an oracle computation bundled with a query bound.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
universe u v w


-- @@ L30-30 verbatim
open OracleComp OracleSpec ENNReal Polynomial Prod


-- @@ L32-36 expanded
/-- Bias advantage of a Boolean-valued game: the gap between the probabilities of the two outputs.

This is the canonical single-game formulation for hidden-bit guessing experiments. -/
noncomputable def ProbComp.boolBiasAdvantage (p : ProbComp Bool) : ℝ :=
  |(probOutput p true).toReal - (probOutput p false).toReal|


-- @@ L38-43 expanded
/-- Distinguishing advantage between two Boolean-valued games, measured on the `true` branch.

For Boolean outputs this is equivalent to measuring the gap on `false`; choosing `true` is just a
conventional presentation. -/
noncomputable def ProbComp.boolDistAdvantage (p q : ProbComp Bool) : ℝ :=
  |(probOutput p true).toReal - (probOutput q true).toReal|


-- @@ L45-52 expanded
/-- Bias advantage of a Boolean-valued subdistribution: the gap between the probabilities of
returning `true` and `false`.

This is the `SPMF` analogue of `ProbComp.boolBiasAdvantage`, used for games that have already
been observed under bundled subprobabilistic semantics. Any remaining mass corresponds to failure
and therefore contributes to neither Boolean branch. -/
noncomputable def SPMF.boolBiasAdvantage (p : SPMF Bool) : ℝ :=
  |(probOutput p true).toReal - (probOutput p false).toReal|


-- @@ L54-57 expanded
/-- Distinguishing advantage between two Boolean-valued subdistributions, measured on the
`true` branch. SPMF analogue of `ProbComp.boolDistAdvantage`. -/
noncomputable def SPMF.boolDistAdvantage (p q : SPMF Bool) : ℝ :=
  |(probOutput p true).toReal - (probOutput q true).toReal|


-- @@ L59-70 expanded
/-- Re-express SPMF Boolean bias as twice the absolute deviation of `Pr[true]` from `1/2`,
assuming the SPMF is a full distribution (no failure mass). -/
lemma SPMF.boolBiasAdvantage_eq_two_mul_abs_sub_half (p : SPMF Bool)
    (htotal : probOutput p true + probOutput p false = 1) :
    p.boolBiasAdvantage = 2 * |(probOutput p true).toReal - 1 / 2| :=
  by
  have hfalse : probOutput p false = 1 - probOutput p true := by
    rw [← htotal, ENNReal.add_sub_cancel_left probOutput_ne_top]
  unfold SPMF.boolBiasAdvantage
  rw [hfalse, ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top, ENNReal.toReal_one,
    show
      (probOutput p true).toReal - (1 - (probOutput p true).toReal) =
        2 * ((probOutput p true).toReal - 1 / 2)
      by ring,
    abs_mul, abs_two]


-- @@ L72-122 expanded
/-- Hidden-bit decomposition at the SPMF level: the bias of a coin-flip guessing game equals the
distinguishing advantage between the two branches, assuming the coin is fair and both branches
have full mass (no failure).

This is the SPMF analogue of `ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch`.
The ProbComp version holds unconditionally because `ProbComp` distributions always have total mass
1. For `SPMF` distributions, the totality hypotheses are required because failure mass breaks the
`Pr[false] = 1 - Pr[true]` identity that the decomposition depends on. -/
lemma SPMF.boolBiasAdvantage_eq_boolDistAdvantage_coin_branch (coin p q : SPMF Bool)
    (hcoin_true : probOutput coin true = 1 / 2) (hcoin_false : probOutput coin false = 1 / 2)
    (hp : probOutput p true + probOutput p false = 1)
    (hq : probOutput q true + probOutput q false = 1) :
    (coin >>= fun b => (if b then p else q) >>= fun z => pure (b == z)).boolBiasAdvantage =
      p.boolDistAdvantage q :=
  by
  have hbt :
    ∀ x : Bool,
      probOutput ((if (true : Bool) then p else q) >>= fun z => (pure (true == z) : SPMF Bool)) x =
        probOutput p x :=
    by intro x; cases x <;> simp
  have hbf :
    ∀ x : Bool,
      probOutput ((if (false : Bool) then p else q) >>= fun z => (pure (false == z) : SPMF Bool))
          x =
        probOutput q (!x) :=
    by intro x; cases x <;> simp
  have hgame :
    ∀ x : Bool,
      probOutput (coin >>= fun b => (if b then p else q) >>= fun z => pure (b == z)) x =
        (probOutput p x + probOutput q (!x)) / 2 :=
    fun x => by
    rw [probOutput_bind_eq_tsum, tsum_fintype (L := .unconditional _), Fintype.sum_bool, hcoin_true,
      hcoin_false, hbt x, hbf x, ← left_distrib, one_div, mul_comm, div_eq_mul_inv]
  have htotal :
    probOutput (coin >>= fun b => (if b then p else q) >>= fun z => pure (b == z)) true +
        probOutput (coin >>= fun b => (if b then p else q) >>= fun z => pure (b == z)) false =
      1 :=
    by
    rw [hgame true, hgame false]
    simp only [Bool.not_true, Bool.not_false, ENNReal.div_add_div_same]
    rw [show
        probOutput p true + probOutput q false + (probOutput p false + probOutput q true) =
          (probOutput p true + probOutput p false) + (probOutput q true + probOutput q false)
        from by ring,
      hp, hq, show (1 : ℝ≥0∞) + 1 = 2 from by norm_num]
    exact ENNReal.div_self (by positivity) ENNReal.ofNat_ne_top
  rw [SPMF.boolBiasAdvantage_eq_two_mul_abs_sub_half _ htotal, hgame true, Bool.not_true]
  rw [show probOutput q false = 1 - probOutput q true from by
      rw [← hq, ENNReal.add_sub_cancel_left probOutput_ne_top],
    ENNReal.toReal_div,
    ENNReal.toReal_add probOutput_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top),
    ENNReal.toReal_sub_of_le (by rw [← hq]; exact le_add_right (le_refl _)) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]
  unfold SPMF.boolDistAdvantage
  rw [show
      ((probOutput p true).toReal + (1 - (probOutput q true).toReal)) / 2 - 1 / 2 =
        ((probOutput p true).toReal - (probOutput q true).toReal) / 2
      from by ring,
    abs_div, abs_two, mul_div_cancel₀ _ two_ne_zero]


-- @@ L124-127 verbatim
/-- Triangle inequality for SPMF Boolean distinguishing advantage. -/
lemma SPMF.boolDistAdvantage_triangle (p q r : SPMF Bool) :
    p.boolDistAdvantage r ≤ p.boolDistAdvantage q + q.boolDistAdvantage r :=
  abs_sub_le _ _ _


-- @@ L129-132 verbatim
/-- Triangle inequality for Boolean distinguishing advantage. -/
lemma ProbComp.boolDistAdvantage_triangle (p q r : ProbComp Bool) :
    p.boolDistAdvantage r ≤ p.boolDistAdvantage q + q.boolDistAdvantage r :=
  abs_sub_le _ _ _


-- @@ L134-149 expanded
/-- The `true`-branch probability of one Boolean-valued game is bounded above by the
`true`-branch probability of another game plus their distinguishing advantage.

This is the `ENNReal`-level interpretation of the real-valued identity `a ≤ b + |a - b|`,
packaged for SSP game-hopping: converting an `advantage p q ≤ ε` assumption into a direct
probability inequality `Pr[true|p] ≤ Pr[true|q] + ENNReal.ofReal ε` that plugs into chained
`calc`-style bounds. -/
lemma ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage (p q : ProbComp Bool) :
    probOutput p true ≤ probOutput q true + ENNReal.ofReal (p.boolDistAdvantage q) :=
  by
  unfold ProbComp.boolDistAdvantage
  set a : ℝ := (probOutput p true).toReal
  set b : ℝ := (probOutput q true).toReal
  rw [show probOutput p true = ENNReal.ofReal a from (ENNReal.ofReal_toReal probOutput_ne_top).symm,
    show probOutput q true = ENNReal.ofReal b from (ENNReal.ofReal_toReal probOutput_ne_top).symm, ←
    ENNReal.ofReal_add ENNReal.toReal_nonneg (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (a - b)])


-- @@ L151-159 expanded
/-- Re-express Boolean bias as twice the absolute deviation of `Pr[true]` from `1/2`. -/
lemma ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half (p : ProbComp Bool) :
    p.boolBiasAdvantage = 2 * |(probOutput p true).toReal - 1 / 2| :=
  by
  have hfalse : probOutput p false = 1 - probOutput p true := by simp [probOutput_false_eq_sub]
  unfold ProbComp.boolBiasAdvantage
  rw [hfalse, ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top, ENNReal.toReal_one,
    show
      (probOutput p true).toReal - (1 - (probOutput p true).toReal) =
        2 * ((probOutput p true).toReal - 1 / 2)
      by ring,
    abs_mul, abs_two]


-- @@ L161-172 expanded
/-- A hidden-bit guessing game over two Boolean branches has bias exactly equal to the
distinguishing advantage between those two branches. -/
lemma ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch
    (real rand : ProbComp Bool) :
    (do
          let b ← (uniformSample Bool)
          let z ←
            if b then 
              real
            else
              rand
          pure (b == z)).boolBiasAdvantage =
      real.boolDistAdvantage rand :=
  by
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half,
    probOutput_uniformBool_branch_toReal_sub_half, ProbComp.boolDistAdvantage, abs_div, abs_two,
    mul_div_cancel₀ _ two_ne_zero]


-- @@ L174-228 expanded
/-- Version of `boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch` with a shared sampled
prefix before the real/random branch is chosen. -/
lemma ProbComp.boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage {α : Type}
    (pref : ProbComp α) (real rand : α → ProbComp Bool) :
    (do
          let a ← pref
          let b ← (uniformSample Bool)
          let z ←
            if b then 
              real a
            else
              rand a
          pure (b == z)).boolBiasAdvantage =
      (do
            let a ← pref
            real a).boolDistAdvantage
        (do
          let a ← pref
          rand a) :=
  by
  let game : ProbComp Bool := do
    let a ← pref
    let b ← (uniformSample Bool)
    let z ←
      if b then 
        real a
      else
        rand a
    pure (b == z)
  let left : ProbComp Bool := do
    let a ← pref
    real a
  let right : ProbComp Bool := do
    let a ← pref
    rand a
  let branchGame : ProbComp Bool := do
    let b ← (uniformSample Bool)
    let z ←
      if b then 
        left
      else
        right
    pure (b == z)
  have hbranch : evalSPMF game = evalSPMF branchGame :=
    by
    apply evalSPMF_ext
    intro x
    calc
      probOutput game x =
          probOutput
            (do
              let b ← (uniformSample Bool)
              let a ← pref
              let z ←
                if b then 
                  real a
                else
                  rand a
              pure (b == z))
            x :=
        by
        simpa [game, monad_norm] using
          (probOutput_bind_bind_swap pref (uniformSample Bool)
            (fun a b => do
              let z ←
                if b then 
                  real a
                else
                  rand a
              pure (b == z))
            x)
      _ = probOutput branchGame x :=
        by
        refine probOutput_bind_congr' (uniformSample Bool) x ?_
        intro b
        cases b <;> simp [left, right]
  rw [show game.boolBiasAdvantage = branchGame.boolBiasAdvantage
      by
      unfold ProbComp.boolBiasAdvantage
      rw [evalSPMF_ext_iff.mp hbranch true, evalSPMF_ext_iff.mp hbranch false]]
  simpa [branchGame, left, right] using
    ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch left right


-- @@ L230-232 expanded
/-- The **advantage** of a game `p`, assumed to be a probabilistic computation ending with a `guard`
  statement, is the absolute difference between the probability of success and 1/2. -/
noncomputable def ProbComp.guessAdvantage (p : ProbComp Unit) : ℝ :=
  |1 / 2 - (probOutput p ()).toReal|


-- @@ L234-242 expanded
/-- The guess advantage of `p` equals the absolute difference between `1/2` and `p`'s
  probability of failure. -/
lemma ProbComp.guessAdvantage_eq_half_sub_probFailure (p : ProbComp Unit) :
    p.guessAdvantage = |1 / 2 - (probFailure p).toReal| :=
  by
  have h : probOutput p () = 1 - probFailure p := probOutput_eq_sub_probFailure_of_unit
  simp only [guessAdvantage, h, ENNReal.toReal_sub_of_le probFailure_le_one one_ne_top,
    ENNReal.toReal_one]
  rw [show (1 : ℝ) / 2 - (1 - (probFailure p).toReal) = -(1 / 2 - (probFailure p).toReal) from by
      ring,
    abs_neg]


-- @@ L244-251 expanded
/-- The guess advantage of `p` equals half the absolute difference between `p`'s
  probabilities of failure and success. -/
lemma ProbComp.guessAdvantage_eq_half_of_sub (p : ProbComp Unit) :
    p.guessAdvantage = 2⁻¹ * |(probFailure p).toReal - (probOutput p ()).toReal| :=
  by
  have h : probOutput p () = 1 - probFailure p := probOutput_eq_sub_probFailure_of_unit
  simp only [guessAdvantage, h, ENNReal.toReal_sub_of_le probFailure_le_one one_ne_top,
    ENNReal.toReal_one]
  grind


-- @@ L253-256 expanded
/-- The **advantage** between two games `p` and `q`, modeled as probabilistic computations returning
  `Unit`, is the absolute difference between their probabilities of success. -/
noncomputable def ProbComp.distAdvantage (p q : ProbComp Unit) : ℝ :=
  |(probOutput p ()).toReal - (probOutput q ()).toReal|


-- @@ L258-261 verbatim
/-- A game has zero distinguishing advantage against itself. -/
@[simp]
lemma ProbComp.distAdvantage_self (p : ProbComp Unit) : p.distAdvantage p = 0 := by
  simp [ProbComp.distAdvantage]


-- @@ L263-266 verbatim
/-- Distinguishing advantage is symmetric in its two games. -/
lemma ProbComp.distAdvantage_comm (p q : ProbComp Unit) :
    p.distAdvantage q = q.distAdvantage p :=
  abs_sub_comm _ _


-- @@ L268-276 expanded
/-- Distinguishing advantage equals the gap between the two games' failure probabilities. -/
lemma ProbComp.distAdvantage_eq_abs_sub_probFailure (p q : ProbComp Unit) :
    p.distAdvantage q = |(probFailure p).toReal - (probFailure q).toReal| :=
  by
  have hp : probOutput p () = 1 - probFailure p := probOutput_eq_sub_probFailure_of_unit
  have hq : probOutput q () = 1 - probFailure q := probOutput_eq_sub_probFailure_of_unit
  simp only [distAdvantage, hp, hq, ENNReal.toReal_sub_of_le probFailure_le_one one_ne_top,
    ENNReal.toReal_one]
  rw [show
      (1 - (probFailure p).toReal) - (1 - (probFailure q).toReal) =
        -((probFailure p).toReal - (probFailure q).toReal)
      by ring,
    abs_neg]


-- @@ L278-280 verbatim
/-- Distinguishing advantage is nonnegative. -/
lemma ProbComp.distAdvantage_nonneg (p q : ProbComp Unit) : 0 ≤ p.distAdvantage q :=
  abs_nonneg _


-- @@ L282-285 verbatim
/-- Triangle inequality for distinguishing advantage. -/
lemma ProbComp.distAdvantage_triangle (p q r : ProbComp Unit) :
    p.distAdvantage r ≤ p.distAdvantage q + q.distAdvantage r :=
  abs_sub_le _ _ _


-- @@ L287-296 verbatim
/-- The distinguishing advantage between the endpoints of a chain of games is bounded by the
sum of the consecutive advantages along the chain. -/
lemma ProbComp.distAdvantage_le_sum_range {n : ℕ} (games : ℕ → ProbComp Unit) :
    (games 0).distAdvantage (games n) ≤
      ∑ i ∈ Finset.range n, (games i).distAdvantage (games (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (distAdvantage_triangle _ _ _).trans (by gcongr)


-- @@ L298-302 verbatim
/-- Distinguishing advantage coincides with the total-variation distance of the two games. -/
lemma ProbComp.distAdvantage_eq_tvDist (p q : ProbComp Unit) :
    p.distAdvantage q = tvDist p q := by
  simp only [distAdvantage, tvDist, SPMF.tvDist, PMF.tvDist_option_punit]
  simp only [probOutput_def, SPMF.apply_eq_toPMF_some]


-- @@ L304-314 verbatim
/-- A security adversary bundling a computation with a bound on the number of queries it makes,
where the bound must be shown to satisfy `IsQueryBound`.
We also require an explicit list of all oracles used in the computation,
which is necessary in order to make certain reductions computable. -/
structure BoundedAdversary {ι : Type u} [DecidableEq ι]
    (spec : OracleSpec ι) (α β : Type u) where
  run : α → OracleComp spec β
  qb : ι → ℕ
  qb_isQueryBound (x : α) : IsPerIndexQueryBound (run x) (qb)
  activeOracles : List ι
  mem_activeOracles_iff (i : ι) : i ∈ activeOracles ↔ qb i ≠ 0


-- @@ L316-316 verbatim
namespace BoundedAdversary


-- @@ L318-318 verbatim
variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}


-- @@ L320-320 verbatim
end BoundedAdversary


-- @@ L322-332 verbatim
/-- Structure to represent a security experiment.
The experiment is considered successful unless it terminates with failure.

A `SecExp` carries bundled `SPMFSemantics` directly. This keeps the semantic assumptions attached
to the experiment itself: the surface monad can be interpreted through some internal semantic
monad, and only then observed as a subdistribution for measuring success and failure
probabilities. -/
structure SecExp (m : Type → Type w) [Monad m]
    extends SPMFSemantics m where
  /-- Main experiment body. Success is interpreted as terminating without failure. -/
  main : m Unit


-- @@ L334-334 verbatim
namespace SecExp


-- @@ L336-336 verbatim
variable {m : Type → Type w} [Monad m]


-- @@ L338-338 verbatim
section advantage


-- @@ L340-342 expanded
/-- Advantage of a failure-based security experiment: one minus its failure probability. -/
noncomputable def advantage (exp : SecExp m) : ℝ≥0∞ :=
  1 - probFailure (exp.toSPMFSemantics.evalSPMF exp.main)


-- @@ L344-350 expanded
/-- A failure-based experiment has zero advantage exactly when it fails with probability `1`. -/
@[simp]
lemma advantage_eq_zero_iff (exp : SecExp m) :
    exp.advantage = 0 ↔ probFailure (exp.toSPMFSemantics.evalSPMF exp.main) = 1 :=
  by
  rw [advantage, tsub_eq_zero_iff_le]
  simpa only [SPMFSemantics.probFailure, probFailure_def, evalSPMF_def, monadLift_self] using
    (exp.toSPMFSemantics.probFailure_le_one exp.main).ge_iff_eq


-- @@ L352-367 expanded
/-- A failure-based experiment has advantage `1` exactly when it never fails. -/
@[simp]
lemma advantage_eq_one_iff (exp : SecExp m) :
    exp.advantage = 1 ↔ probFailure (exp.toSPMFSemantics.evalSPMF exp.main) = 0 :=
  by
  rw [advantage]
  let p := probFailure (exp.toSPMFSemantics.evalSPMF exp.main)
  change 1 - p = 1 ↔ p = 0
  constructor
  · intro h
    by_contra hp
    have hp' : 0 < p := bot_lt_iff_ne_bot.mpr hp
    have hlt : 1 - p < (1 : ℝ≥0∞) := (ENNReal.sub_lt_self_iff one_ne_top).2 ⟨zero_lt_one, hp'⟩
    exact hlt.ne h
  · intro h
    simp only [h, tsub_zero]


-- @@ L369-369 verbatim
end advantage


-- @@ L371-371 verbatim
end SecExp
