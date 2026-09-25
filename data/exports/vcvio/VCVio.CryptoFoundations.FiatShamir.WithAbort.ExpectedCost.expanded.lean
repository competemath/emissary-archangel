/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Cost
public import Mathlib.Analysis.SpecificLimits.Basic


-- @@ L12-19 verbatim
/-!
# Expected-cost PMF theorems for Fiat-Shamir with aborts

Expected random-oracle query costs of `fsAbortSignLoop` and
`FiatShamirWithAbort.sign`/`verify`, stated as `tsum` identities over the
induced output distributions. These drive the aggregate runtime bounds used
in the security proof.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
open OracleComp OracleSpec


-- @@ L27-27 verbatim
variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}


-- @@ L29-29 verbatim
namespace FiatShamirWithAbort


-- @@ L31-31 verbatim
section expectedCostPMF


-- @@ L33-33 verbatim
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) (M : Type)


-- @@ L35-35 verbatim
variable {m : Type → Type u} [Monad m] [MonadLiftT ProbComp m]


-- @@ L37-56 expanded
private lemma signLoop_inRuntime_succ
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (n : ℕ) :
    HasQuery.Program.eval
        (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
          fsAbortSignLoop (m := m) ids M pk sk msg (n + 1))
        runtime =
      (do
        let attempt ←
          HasQuery.Program.eval
              (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
                fsAbortSignAttempt (m := m) ids M pk sk msg)
              runtime
        match attempt.2 with
        | some z =>
          pure (some (attempt.1, z))
        | none =>
          HasQuery.Program.eval
              (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
                fsAbortSignLoop (m := m) ids M pk sk msg n)
              runtime) :=
  rfl


-- @@ L58-58 verbatim
section


-- @@ L60-60 verbatim
variable [LawfulMonad m]


-- @@ L62-106 expanded
private lemma signLoop_queryCountDist_succ
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (n : ℕ) :
    HasQuery.queryCountDist
        (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
          fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
        runtime =
      (do
        let attempt ←
          HasQuery.Program.eval
              (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
                fsAbortSignAttempt (m := m) ids M pk sk msg)
              runtime
        match attempt.2 with
        | some _ =>
          pure 1
        | none =>
          let recCosts :=
            HasQuery.queryCountDist
              (fun
                  [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
                fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
              runtime
          Nat.succ <$> recCosts) :=
  by
  change
    AddWriterT.costs
        (do
          let attempt ←
            HasQuery.Program.withUnitCost
                (fun
                    [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))
                        (AddWriterT ℕ m)] =>
                  fsAbortSignAttempt (m := AddWriterT ℕ m) ids M pk sk msg)
                runtime
          match attempt.2 with
          | some z =>
            pure (some (attempt.1, z))
          | none =>
            HasQuery.Program.withUnitCost
                (fun
                    [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))
                        (AddWriterT ℕ m)] =>
                  fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
                runtime) =
      _
  rw [AddWriterT.costs_def, WriterT.run_bind, signAttempt_run_withUnitCost_eq]
  simp only [bind_map_left, map_bind, Functor.map_map, toAdd_mul, toAdd_ofAdd]
  refine bind_congr ?_
  intro attempt
  cases attempt.2 with
  | some z => simp
  |
    none =>
    simp [HasQuery.queryCountDist, HasQuery.queryCostDist, HasQuery.Program.withUnitCost,
      HasQuery.Program.withAddCost, AddWriterT.costs, add_comm]
    rfl


-- @@ L108-108 verbatim
end


-- @@ L110-111 verbatim
variable [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L113-120 expanded
/-- The probability that a single Fiat-Shamir-with-aborts signing attempt aborts. -/
noncomputable abbrev signAttemptAbortProbability
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) : ENNReal :=
  probEvent
    (HasQuery.Program.eval
      (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime)
    fun attempt ↦ attempt.2 = none


-- @@ L122-158 expanded
private lemma signLoop_probNone_succ
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (n : ℕ) :
    probOutput
        (HasQuery.Program.eval
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg (n + 1))
          runtime)
        none =
      (probEvent
          (HasQuery.Program.eval
            (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
              fsAbortSignAttempt (m := m) ids M pk sk msg)
            runtime)
          fun attempt ↦ attempt.2 = none) *
        probOutput
          (HasQuery.Program.eval
            (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg n)
            runtime)
          none :=
  by
  set attemptComp : m (Commit × Option Resp) :=
    HasQuery.Program.eval
      (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime
  set recLoop : m (Option (Commit × Resp)) :=
    HasQuery.Program.eval
      (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
        fsAbortSignLoop (m := m) ids M pk sk msg n)
      runtime
  rw [signLoop_inRuntime_succ]
  change
    probOutput
        (attemptComp >>= fun attempt =>
          match attempt.2 with
          | some z => pure (some (attempt.1, z))
          | none => recLoop)
        none =
      (probEvent attemptComp fun attempt ↦ attempt.2 = none) * probOutput recLoop none
  rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun attempt => ?_
  cases hAttempt : attempt.2 <;> simp [hAttempt]


-- @@ L160-160 verbatim
section


-- @@ L162-162 verbatim
variable [LawfulMonad m]


-- @@ L164-191 expanded
omit [LawfulMonadLiftT m SetM] in
private lemma signLoop_queryTailProbability_zero
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (n : ℕ) :
    (probEvent
        (HasQuery.queryCountDist
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
            fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
          runtime)
        fun q ↦ 0 < q) =
      1 :=
  by
  set attemptComp : m (Commit × Option Resp) :=
    HasQuery.Program.eval
      (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime
  set recCosts : m ℕ :=
    HasQuery.queryCountDist (m := m)
      (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
      runtime
  rw [signLoop_queryCountDist_succ]
  change
    (probEvent
        (attemptComp >>= fun attempt ↦
          match attempt.2 with
          | some _ => pure 1
          | none => Nat.succ <$> recCosts)
        fun q ↦ 0 < q) =
      1
  rw [probEvent_bind_of_const (r := 1)]
  · simp
  · intro attempt _
    cases attempt.2 <;> simp [probEvent_map]


-- @@ L193-232 expanded
omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
private lemma signLoop_queryTailProbability_succ
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (i n : ℕ) :
    (probEvent
        (HasQuery.queryCountDist
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
            fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (n + 1))
          runtime)
        fun q ↦ i + 1 < q) =
      (probEvent
          (HasQuery.Program.eval
            (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
              fsAbortSignAttempt (m := m) ids M pk sk msg)
            runtime)
          fun attempt ↦ attempt.2 = none) *
        probEvent
          (HasQuery.queryCountDist
            (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
              fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
            runtime)
          fun q ↦ i < q :=
  by
  set attemptComp : m (Commit × Option Resp) :=
    HasQuery.Program.eval
      (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
        fsAbortSignAttempt (m := m) ids M pk sk msg)
      runtime
  set recCosts : m ℕ :=
    HasQuery.queryCountDist (m := m)
      (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
        fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg n)
      runtime
  let cont : Commit × Option Resp → m ℕ := fun attempt =>
    match attempt.2 with
    | some _ => pure 1
    | none => Nat.succ <$> recCosts
  rw [signLoop_queryCountDist_succ]
  change
    (probEvent (attemptComp >>= cont) fun q ↦ i + 1 < q) =
      (probEvent attemptComp fun attempt ↦ attempt.2 = none) * probEvent recCosts fun q ↦ i < q
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_indicator, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun attempt => ?_
  cases hAttempt : attempt.2 <;> simp [cont, hAttempt, probEvent_map, Function.comp_def]


-- @@ L234-254 expanded
private theorem signLoop_queryTailProbability_eq_probNonePrefix
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) :
    ∀ i extra,
      (probEvent
          (HasQuery.queryCountDist
            (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
              fsAbortSignLoop (m := AddWriterT ℕ m) ids M pk sk msg (i + extra + 1))
            runtime)
          fun q ↦ i < q) =
        probOutput
          (HasQuery.Program.eval
            (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg i)
            runtime)
          none
  | 0, extra => by
    rw [Nat.zero_add, signLoop_queryTailProbability_zero (n := extra)]
    simp [HasQuery.Program.eval, fsAbortSignLoop]
  | i + 1, extra => by
    rw [Nat.add_right_comm i 1 extra,
      signLoop_queryTailProbability_succ (i := i) (n := i + extra + 1),
      signLoop_queryTailProbability_eq_probNonePrefix (i := i) (extra := extra), ←
      signLoop_probNone_succ (n := i)]


-- @@ L256-256 verbatim
end


-- @@ L258-274 expanded
private theorem signLoop_probNone_eq_signAttemptAbortProbability_pow
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) :
    ∀ i,
      probOutput
          (HasQuery.Program.eval
            (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg i)
            runtime)
          none =
        (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i
  | 0 => by simp [signAttemptAbortProbability, HasQuery.Program.eval, fsAbortSignLoop]
  | i + 1 => by
    rw [signLoop_probNone_succ (ids := ids) (M := M) (runtime := runtime) (pk := pk) (sk := sk)
        (msg := msg) (n := i),
      signLoop_probNone_eq_signAttemptAbortProbability_pow (runtime := runtime) (pk := pk) (sk :=
        sk) (msg := msg) i,
      pow_succ']


-- @@ L276-276 verbatim
section


-- @@ L278-289 expanded
/-- The probability that the first `i` signing attempts all abort is the `i`-th power of the
single-attempt abort probability. -/
theorem sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (i : ℕ) :
    probOutput
        (HasQuery.Program.eval
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime)
        none =
      (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i :=
  signLoop_probNone_eq_signAttemptAbortProbability_pow (ids := ids) (M := M) (runtime := runtime)
    (pk := pk) (sk := sk) (msg := msg) i


-- @@ L291-291 verbatim
end


-- @@ L293-293 verbatim
variable [LawfulMonad m]


-- @@ L295-295 verbatim
section schemeCost


-- @@ L297-297 verbatim
variable (hr : GenerableRelation Stmt Wit rel)


-- @@ L299-320 expanded
/-- The probability that signing makes more than `i` random-oracle queries is exactly the
probability that the first `i` signing attempts all abort.

Equivalently, the event `i < q` for the signer query count is the event that the retry loop of
length `i` returns `none`, meaning that the `(i + 1)`-st attempt is reached. -/
theorem sign_queryTailProbability_eq_probAllFirstAttemptsAbort
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) {i maxAttempts : ℕ} (hi : i < maxAttempts) :
    (probEvent
        (HasQuery.queryCountDist
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
            (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
          runtime)
        fun q ↦ i < q) =
      probOutput
        (HasQuery.Program.eval
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
            fsAbortSignLoop (m := m) ids M pk sk msg i)
          runtime)
        none :=
  by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_lt hi
  exact
    signLoop_queryTailProbability_eq_probNonePrefix (ids := ids) (M := M) (runtime := runtime)
      (pk := pk) (sk := sk) (msg := msg) (i := i) (extra := extra)


-- @@ L322-335 expanded
/-- The probability that signing makes more than `i` oracle queries is the `i`-th power of the
single-attempt abort probability, as long as `i < maxAttempts`. -/
theorem sign_queryTailProbability_eq_signAttemptAbortProbability_pow
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) {i maxAttempts : ℕ} (hi : i < maxAttempts) :
    (probEvent
        (HasQuery.queryCountDist
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
            (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
          runtime)
        fun q ↦ i < q) =
      (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i :=
  by
  rw [sign_queryTailProbability_eq_probAllFirstAttemptsAbort (hr := hr) (hi := hi)]
  exact
    sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow (ids := ids) (M := M) runtime pk
      sk msg i


-- @@ L337-357 expanded
/-- The expected number of signing queries is the sum, over prefixes of the retry loop, of the
probability that every attempt in the prefix aborts. -/
theorem sign_expectedQueries_eq_sum_abortPrefixProbabilities
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (maxAttempts : ℕ) :
    HasQuery.expectedQueries
        (((fun [HasQuery _ _] => (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg) :
          [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
        runtime =
      ∑ i ∈ Finset.range maxAttempts,
        probOutput
          (HasQuery.Program.eval
            (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m] =>
              fsAbortSignLoop (m := m) ids M pk sk msg i)
            runtime)
          none :=
  by
  rw [sign_expectedQueries_eq_sum_reachedAttemptProbabilities (ids := ids) (hr := hr) (M := M)
      (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) (maxAttempts := maxAttempts)]
  exact
    Finset.sum_congr rfl fun i hi =>
      sign_queryTailProbability_eq_probAllFirstAttemptsAbort (ids := ids) (hr := hr) (M := M)
        (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) (hi := Finset.mem_range.mp hi)


-- @@ L359-372 expanded
/-- The expected number of signing queries is the finite geometric sum of the one-step abort
probability. -/
theorem sign_expectedQueries_eq_sum_signAttemptAbortProbability_powers
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (maxAttempts : ℕ) :
    HasQuery.expectedQueries
        (((fun [HasQuery _ _] => (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg) :
          [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
        runtime =
      ∑ i ∈ Finset.range maxAttempts,
        (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i :=
  by
  rw [sign_expectedQueries_eq_sum_abortPrefixProbabilities (ids := ids) (hr := hr) (M := M)
      (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) (maxAttempts := maxAttempts)]
  exact
    Finset.sum_congr rfl fun i _ =>
      sign_abortPrefixProbability_eq_signAttemptAbortProbability_pow ids M runtime pk sk msg i


-- @@ L374-398 expanded
omit [LawfulMonadLiftT m PMF] in
/-- Once `i` reaches `maxAttempts`, the signer never makes more than `i` queries, so the tail
event has probability zero. -/
private theorem sign_queryTailProbability_eq_zero_of_le
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) {i maxAttempts : ℕ} (hi : maxAttempts ≤ i) :
    (probEvent
        (HasQuery.queryCountDist
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
            (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
          runtime)
        fun q ↦ i < q) =
      0 :=
  by
  refine probEvent_eq_zero fun c hc => ?_
  have hc' :
    c ∈
      support
        (AddWriterT.costs
          (HasQuery.Program.withUnitCost
            (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
              (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
            runtime)) :=
    by
    rw [HasQuery.Program.withUnitCost_eq_withAddCost]
    exact hc
  rw [AddWriterT.costs_def, support_map] at hc'
  rcases hc' with ⟨z, hz, rfl⟩
  exact
    not_lt.2 <|
      le_trans
        (sign_usesAtMostMaxAttemptsQueries (ids := ids) (hr := hr) (M := M) (runtime := runtime)
          (pk := pk) (sk := sk) (msg := msg) (maxAttempts := maxAttempts) z hz)
        hi


-- @@ L400-416 expanded
/-- Tail probabilities for the signer query count are bounded by the corresponding power of the
single-attempt abort probability. -/
theorem sign_queryTailProbability_le_signAttemptAbortProbability_pow
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (i maxAttempts : ℕ) :
    (probEvent
        (HasQuery.queryCountDist
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ℕ m)] =>
            (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg)
          runtime)
        fun q ↦ i < q) ≤
      (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i :=
  by
  by_cases hi : i < maxAttempts
  ·
    rw [sign_queryTailProbability_eq_signAttemptAbortProbability_pow (ids := ids) (hr := hr) (M :=
        M) (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) (hi := hi)]
  ·
    exact
      (sign_queryTailProbability_eq_zero_of_le ids M (hr := hr) runtime pk sk msg
            (Nat.le_of_not_lt hi)).trans_le
        zero_le


-- @@ L418-430 expanded
/-- The expected number of signing queries is bounded by the infinite geometric series generated by
the single-attempt abort probability. -/
theorem sign_expectedQueries_le_tsum_signAttemptAbortProbability_powers
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (maxAttempts : ℕ) :
    HasQuery.expectedQueries
        (((fun [HasQuery _ _] => (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg) :
          [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
        runtime ≤
      ∑' i : ℕ, (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i :=
  HasQuery.expectedQueries_le_tsum_of_tail_probs_le _ runtime fun i ↦
    sign_queryTailProbability_le_signAttemptAbortProbability_pow (ids := ids) (hr := hr) (M := M)
      (runtime := runtime) (pk := pk) (sk := sk) (msg := msg) (i := i) (maxAttempts := maxAttempts)


-- @@ L432-450 expanded
/-- If the single-attempt abort probability is bounded by `q`, then the expected number of signing
queries is bounded by the corresponding geometric series. -/
theorem sign_expectedQueries_le_geometric_of_signAttemptAbortProbability_le
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (maxAttempts : ℕ) {q : ENNReal}
    (hq : signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg ≤ q) :
    HasQuery.expectedQueries
        (((fun [HasQuery _ _] => (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg) :
          [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
        runtime ≤
      (1 - q)⁻¹ :=
  by
  calc
    HasQuery.expectedQueries
          (((fun [HasQuery _ _] => (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg) :
            [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
          runtime ≤
        ∑' i : ℕ, (signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg) ^ i :=
      sign_expectedQueries_le_tsum_signAttemptAbortProbability_powers ids M hr runtime pk sk msg
        maxAttempts
    _ ≤ ∑' i : ℕ, q ^ i := by gcongr
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q


-- @@ L452-462 expanded
/-- Specializing the geometric upper bound to the actual one-step abort probability yields the
canonical infinite geometric upper bound on expected query count. -/
theorem sign_expectedQueries_le_geometric
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (sk : Wit) (msg : M) (maxAttempts : ℕ) :
    HasQuery.expectedQueries
        (((fun [HasQuery _ _] => (FiatShamirWithAbort ids hr M maxAttempts).sign pk sk msg) :
          [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
        runtime ≤
      (1 - signAttemptAbortProbability (ids := ids) (M := M) runtime pk sk msg)⁻¹ :=
  sign_expectedQueries_le_geometric_of_signAttemptAbortProbability_le ids M hr runtime pk sk msg
    maxAttempts le_rfl


-- @@ L464-491 expanded
/-- Verification has expected weighted query cost equal to the cost of the single verification
query when a signature is present, and `0` when the signature is `none`. -/
theorem verify_expectedQueryCost_eq {ω : Type} [AddMonoid ω] [Preorder ω]
    (runtime : QueryImpl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) m) (pk : Stmt)
    (msg : M) (sig : Option (Commit × Resp)) (costFn : M × Commit → ω) (val : ω → ENNReal)
    (hval : Monotone val) (maxAttempts : ℕ) :
    HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => (FiatShamirWithAbort ids hr M maxAttempts).verify pk msg sig) :
          [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _))
        runtime costFn val =
      match sig with
      | none => val 0
      | some (w', _) => val (costFn (msg, w')) :=
  by
  rcases sig with _ | ⟨w', z⟩
  · let : DecidableEq ω := Classical.decEq ω
    simp [FiatShamirWithAbort, HasQuery.expectedQueryCost, AddWriterT.expectedCost,
      HasQuery.Program.withAddCost]
  · refine HasQuery.expectedQueryCost_eq_of_usesCostExactly ?_ hval
    change
      AddWriterT.HasCost
        (HasQuery.Program.withAddCost
          (fun [HasQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) (AddWriterT ω m)] =>
            (FiatShamirWithAbort (m := AddWriterT ω m) ids hr M maxAttempts).verify pk msg
              (some (w', z)))
          runtime costFn)
        (costFn (msg, w'))
    rw [AddWriterT.hasCost_iff]
    simp [FiatShamirWithAbort, HasQuery.Program.withAddCost, QueryImpl.withAddCost_apply,
      AddWriterT.outputs, AddWriterT.costs, AddWriterT.addTell]


-- @@ L493-493 verbatim
end schemeCost


-- @@ L495-495 verbatim
end expectedCostPMF


-- @@ L497-497 verbatim
end FiatShamirWithAbort
