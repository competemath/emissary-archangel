/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.EvalDist
public import VCVio.EvalDist.List
public import VCVio.OracleComp.Constructions.SampleableType
public import Init.Data.Vector.Lemmas


-- @@ L14-21 verbatim
/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
open OracleSpec


-- @@ L27-27 verbatim
universe u v w


-- @@ L29-29 verbatim
namespace OracleComp


-- @@ L31-39 verbatim
/-- Run the computation `oa` repeatedly `n` times to get a list of `n` results. -/
def replicate {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
      let x ← oa
      let xs ← replicate n oa
      pure (x :: xs)


-- @@ L41-45 verbatim
/-- Tail-recursive variant of `replicate`, running `oa` for each entry of a length-`n` list
built by `List.replicateTR`. Agrees with `replicate` via `replicateTR_eq_replicate`. -/
def replicateTR {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicateTR n ()).mapM fun () => oa


-- @@ L47-48 verbatim
variable {ι} {spec : OracleSpec ι} {α β : Type v}
  (oa : OracleComp spec α) (n : ℕ)


-- @@ L50-51 verbatim
@[simp, grind =]
lemma replicate_zero : replicate 0 oa = return [] := rfl


-- @@ L53-54 verbatim
@[simp, grind =]
lemma replicateTR_zero : replicateTR 0 oa = return [] := rfl


-- @@ L56-62 verbatim
/-- Bind-style unfolding of `replicate`, convenient for program-logic proofs. -/
@[simp, grind =]
lemma replicate_succ_bind :
    replicate (n + 1) oa = (do
      let x ← oa
      let xs ← replicate n oa
      pure (x :: xs)) := rfl


-- @@ L64-72 verbatim
/-- The tail-recursive `replicateTR` agrees with the recursive `replicate`. The
`@[simp]` annotation lets every later proof about `replicateTR` reduce to the
recursive form automatically. -/
@[simp, grind =]
lemma replicateTR_eq_replicate : replicateTR n oa = replicate n oa := by
  simp only [replicateTR, ← List.replicate_eq_replicateTR]
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, List.mapM_cons, ih]


-- @@ L74-75 verbatim
lemma replicate_succ : replicate (n + 1) oa = List.cons <$> oa <*> replicate n oa := by
  simp [replicate_succ_bind, monad_norm, Function.comp]


-- @@ L77-82 verbatim
@[simp, grind =]
lemma replicate_pure (x : α) :
    (pure x : OracleComp spec α).replicate n = pure (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp [hn, List.replicate]


-- @@ L84-84 verbatim
variable [IsUniformSpec spec]


-- @@ L86-90 expanded
lemma probFailure_replicate : probFailure (oa.replicate n) = 1 - (1 - probFailure oa) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp


-- @@ L92-105 expanded
/-- The probability of getting a list from `replicate` is the product of the chances of
getting each of the individual elements. -/
@[simp]
lemma probOutput_replicate (xs : List α) :
    probOutput (oa.replicate n) xs = if xs.length = n then (xs.map (probOutput oa ·)).prod else 0 :=
  by
  have : DecidableEq α := Classical.decEq α
  induction n generalizing xs with
  | zero => cases xs <;> simp [probOutput_eq_zero_of_not_mem_support]
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons y
      ys =>
      rw [replicate_succ, probOutput_cons_seq_map_cons_eq_mul oa (replicate n oa) y ys, ih]
      simp


-- @@ L107-116 expanded
lemma probEvent_replicate_of_probEvent_cons (p : List α → Prop) (hp : p []) (q : α → Prop)
    (hq : ∀ x xs, p (x :: xs) ↔ q x ∧ p xs) : probEvent (oa.replicate n) p = probEvent oa q ^ n :=
  by
  induction n with
  | zero => simp [hp]
  | succ n ih =>
    rw [replicate_succ,
      probEvent_seq_map_eq_mul oa (replicate n oa) List.cons p q p (fun x _ xs _ => hq x xs), ih,
      pow_succ, mul_comm]


-- @@ L118-131 verbatim
omit [IsUniformSpec spec] in
/-- Possible outputs of `replicate n oa` are lists of length `n` where
each element in the list is a possible output of `oa`. -/
@[simp]
lemma support_replicate :
    support (oa.replicate n) = {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} := by
  induction n with
  | zero => ext xs; aesop
  | succ n ih =>
    rw [replicate_succ]
    ext xs
    cases xs with
    | nil => simp
    | cons x xs => rw [cons_mem_support_seq_map_cons_iff, ih]; aesop


-- @@ L133-137 verbatim
@[simp]
lemma mem_finSupport_replicate [spec.DecidableEq] [DecidableEq α]
    (xs : List α) : xs ∈ finSupport (oa.replicate n) ↔
      xs.length = n ∧ ∀ x ∈ xs, x ∈ finSupport oa := by
  simp [mem_finSupport_iff_mem_support]


-- @@ L139-145 expanded
lemma probOutput_replicate_uniformSample {α : Type} [Fintype α] [SampleableType α] {n : ℕ}
    {xs : List α} (hlen : xs.length = n) :
    probOutput (replicate n (uniformSample α)) xs = (↑(Fintype.card α ^ n) : ENNReal)⁻¹ :=
  by
  simp only [probOutput_replicate, hlen, ite_true, probOutput_uniformSample]
  rw [List.prod_map_const, hlen]
  simpa [Nat.cast_pow] using (ENNReal.inv_pow (a := (Fintype.card α : ENNReal)) (n := n)).symm


-- @@ L147-147 verbatim
/-! ## SimulateQ distributivity -/


-- @@ L149-149 verbatim
section SimulateQ


-- @@ L151-152 verbatim
variable {ι'} {spec' : OracleSpec ι'} {r : Type v → Type*}
  [Monad r] [LawfulMonad r] (impl : QueryImpl spec r)


-- @@ L154-164 verbatim
omit [IsUniformSpec spec] in
/-- `simulateQ` distributes over `replicate`: simulating a replicated computation
equals running the simulated body `n` times via monadic recursion. -/
lemma simulateQ_replicate :
    simulateQ impl (replicate n oa) =
      (List.replicate n ()).mapM (fun _ => simulateQ impl oa) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replicate_succ_bind, simulateQ_bind, simulateQ_pure,
      List.replicate, List.mapM_cons, ih]


-- @@ L166-166 verbatim
end SimulateQ


-- @@ L168-168 verbatim
section VectorMapM


-- @@ L170-180 verbatim
/-- Index-extraction for `(Vector.ofFn id).mapM` over an `OracleComp`: any element in the
support of the monadic `mapM` has each component lying in the support of the corresponding
inner computation. -/
lemma support_ofFn_mapM_index
    {ι α : Type} {spec : OracleSpec ι} {L : ℕ}
    (f : Fin L → OracleComp spec α)
    {v : Vector α L}
    (hv : v ∈ support ((Vector.ofFn (id : Fin L → Fin L)).mapM f))
    (i : Fin L) : v[i] ∈ support (f i) := by
  simpa using
    Vector.support_mapM_index (Vector.ofFn (id : Fin L → Fin L)) f hv i


-- @@ L182-182 verbatim
end VectorMapM


-- @@ L184-184 verbatim
end OracleComp
