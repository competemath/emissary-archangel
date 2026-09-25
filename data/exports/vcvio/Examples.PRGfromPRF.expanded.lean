/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.PRG
public import VCVio.EvalDist.TVDist
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable


-- @@ L14-27 verbatim
/-!
# PRG from PRF

This file constructs a simple stream-style PRG from a PRF
`f : K → S → S × O`. Starting from a random state `s₀`, each round applies
the PRF to the current state, producing the next state and one output block.

The proof outline follows the standard switching argument:

1. Replace the real PRF with a random function.
2. Show that, except when the state chain repeats, the random-function world is
   identical to the ideal PRG world of independent uniform outputs.
3. Bound the remaining gap by the probability of a state collision.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
open OracleComp OracleSpec ENNReal PRFScheme PRGScheme

-- @@ L32-32 verbatim
open List (Vector)


-- @@ L34-34 verbatim
namespace PRGfromPRF


-- @@ L36-36 verbatim
variable {K S O : Type}

-- @@ L37-37 verbatim
variable [Inhabited K] [Fintype K] [SampleableType K]

-- @@ L38-38 verbatim
variable [Inhabited S] [Fintype S] [DecidableEq S] [SampleableType S]

-- @@ L39-39 verbatim
variable [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O]


-- @@ L41-46 verbatim
/-- Deterministically unroll `n` rounds of a state transition/output function. -/
def streamOutputs (step : S → S × O) : (n : ℕ) → S → List.Vector O n
  | 0, _ => .nil
  | n + 1, s =>
      let (s', out) := step s
      out ::ᵥ streamOutputs step n s'


-- @@ L48-55 verbatim
/-- Query the PRF oracle `n` times, threading the returned state and collecting outputs. -/
def oracleOutputs :
    (n : ℕ) → S → OracleComp (PRFScheme.PRFOracleSpec S (S × O)) (List.Vector O n)
  | 0, _ => pure .nil
  | n + 1, s => do
      let (s', out) ← PRFScheme.functionQuery s
      let rest ← oracleOutputs n s'
      pure (out ::ᵥ rest)


-- @@ L57-65 verbatim
/-- Query the PRF oracle `n` times, recording the states fed to the oracle. Repeated
states are exactly the bad event for the random-function to ideal-PRG hop. -/
def oracleVisitedStates :
    (n : ℕ) → S → OracleComp (PRFScheme.PRFOracleSpec S (S × O)) (List.Vector S n)
  | 0, _ => pure .nil
  | n + 1, s => do
      let (s', _) ← PRFScheme.functionQuery s
      let rest ← oracleVisitedStates n s'
      pure (s ::ᵥ rest)


-- @@ L67-71 verbatim
/-- Stream-style PRG obtained by iterating a PRF `n` times. The seed contains both the
PRF key and the initial state; later theorems assume the PRF key distribution is uniform. -/
@[simps!] def streamPRG (prf : PRFScheme K S (S × O)) (n : ℕ) :
    PRGScheme (K × S) (List.Vector O n) where
  gen ks := streamOutputs (prf.eval ks.1) n ks.2


-- @@ L73-73 verbatim
namespace streamPRG


-- @@ L75-75 verbatim
variable {prf : PRFScheme K S (S × O)} {n : ℕ}


-- @@ L77-88 expanded
/-- Reduction from a distinguisher on the stream PRG output to a PRF distinguisher. It
samples an initial state, queries the candidate oracle `n` times, and feeds the resulting
output vector to the PRG adversary. -/
def prfReduction (n : ℕ) (adv : PRGAdversary (List.Vector O n)) : PRFAdversary S (S × O) :=
  show OracleComp (unifSpec + (OracleSpec.ofFn (ι := S) (fun _ => S × O))) Bool from do
    let seed ←
      OracleComp.liftComp (spec := unifSpec) (superSpec :=
          unifSpec + (OracleSpec.ofFn (ι := S) (fun _ => S × O))) (uniformSample S)
    let outputs ← oracleOutputs n seed
    OracleComp.liftComp (spec := unifSpec) (superSpec :=
        unifSpec + (OracleSpec.ofFn (ι := S) (fun _ => S × O))) (adv outputs)


-- @@ L90-97 expanded
/-- Collision experiment for the ideal random-function world: sample an initial state,
iterate a lazy random oracle for `n` rounds, and test whether any queried state repeats. -/
def idealCollisionExp (n : ℕ) : ProbComp Bool := do
  let seed ← uniformSample S
  let states ←
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := S) (R := S × O))
            (oracleVisitedStates n seed)).run'
        ∅
  return decide (¬states.toList.Nodup)


-- @@ L99-101 expanded
/-- Probability of the bad event in the ideal random-function world. -/
noncomputable def collisionProb (n : ℕ) : ℝ :=
  (probOutput (idealCollisionExp (S := S) (O := O) n) true).toReal


-- @@ L103-119 verbatim
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S]
  [DecidableEq S] [SampleableType S] [Inhabited O] [Fintype O]
  [DecidableEq O] [SampleableType O] in
/-- Under the real PRF query implementation, querying the oracle `n` times produces the
same outputs as the deterministic `streamOutputs`. -/
private lemma simulateQ_prfReal_oracleOutputs (k : K) (n : ℕ) (s : S) :
    simulateQ (prfRealQueryImpl prf k) (oracleOutputs n s) =
      (pure (streamOutputs (prf.eval k) n s) : ProbComp _) := by
  induction n generalizing s with
  | zero => simp [oracleOutputs, streamOutputs]
  | succ n ih =>
    cases h : prf.eval k s with
    | mk s' out =>
        simp only [oracleOutputs, streamOutputs, simulateQ_bind,
          simulateQ_prfRealQueryImpl_functionQuery, h, pure_bind]
        rw [ih]
        simp


-- @@ L121-145 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [DecidableEq S]
    [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O] in
/-- Applying the real PRF query implementation to the full reduction body simplifies to
sampling a seed and running the adversary on deterministic output. -/
private lemma simulateQ_prfReal_reduction (k : K) (n : ℕ) (adv : PRGAdversary (List.Vector O n)) :
    simulateQ (prf.prfRealQueryImpl k)
        (show OracleComp (unifSpec + (OracleSpec.ofFn (ι := S) (fun _ => S × O))) Bool from do
          let seed ← liftComp (uniformSample S) (unifSpec + ofFn fun _ => S × O)
          let outputs ← oracleOutputs n seed
          liftComp (adv outputs) (unifSpec + ofFn fun _ => S × O)) =
      (do
        let s ← uniformSample S;
        adv (streamOutputs (prf.eval k) n s)) :=
  by
  change
    simulateQ (prf.prfRealQueryImpl k)
        (do
          let seed ← liftComp (uniformSample S) (unifSpec + ofFn fun _ => S × O)
          let outputs ← oracleOutputs n seed
          liftComp (adv outputs) (unifSpec + ofFn fun _ => S × O)) =
      (do
        let s ← uniformSample S
        adv (streamOutputs (prf.eval k) n s))
  rw [simulateQ_bind, simulateQ_prfRealQueryImpl_liftComp]
  refine bind_congr ?_
  intro s
  rw [simulateQ_bind, simulateQ_prfReal_oracleOutputs, pure_bind,
    simulateQ_prfRealQueryImpl_liftComp]


-- @@ L147-162 expanded
omit [Inhabited K] [Fintype K] [Inhabited S] [Fintype S] [DecidableEq S] [Inhabited O] [Fintype O]
    [DecidableEq O] [SampleableType O] in
/-- In the real world, the stream PRG experiment has the same output distribution as
the real PRF experiment for the reduction adversary, provided the PRF key
distribution is uniform. -/
theorem prgRealExp_eq_prfRealExp (hkey : evalSPMF prf.keygen = evalSPMF (uniformSample K))
    (adv : PRGAdversary (List.Vector O n)) :
    evalSPMF (PRGScheme.prgRealExp (streamPRG prf n) adv) =
      evalSPMF (PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)) :=
  by
  simp only [PRGScheme.prgRealExp, PRFScheme.prfRealExp, prfReduction, streamPRG]
  simp_rw [simulateQ_prfReal_reduction]
  change
    evalSPMF
        ((·, ·) <$> (uniformSample K) <*> (uniformSample S) >>= fun ks =>
          adv (streamOutputs (prf.eval ks.1) n ks.2)) =
      _
  simp only [monad_norm, Function.comp_def]
  rw [evalSPMF_bind, evalSPMF_bind, hkey]


-- @@ L164-168 expanded
/-- The output distribution that the ideal PRF reduction feeds to the PRG adversary:
sample an initial seed, then read `n` output blocks off the lazy random oracle chain. -/
def idealOutputs (n : ℕ) : ProbComp (List.Vector O n) := do
  let seed ← uniformSample S
  (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs n seed)).run' ∅


-- @@ L170-176 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [DecidableEq S] [Inhabited O] [Fintype O]
    [DecidableEq O] in
/-- The ideal PRG experiment for the stream adversary is exactly: sample a uniform output
vector and run the adversary on it. -/
lemma prgIdealExp_eq_bind (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgIdealExp adv = ((uniformSample (List.Vector O n)) >>= adv) :=
  rfl


-- @@ L178-197 expanded
omit [Inhabited S] [Fintype S] [Inhabited O] [Fintype O] [DecidableEq O] in
/-- The ideal PRF experiment, applied to the stream reduction, factors as sampling the
adversary's input via the lazy-random-oracle chain (`idealOutputs`) and then running the
adversary. -/
lemma prfIdealExp_prfReduction_eq (adv : PRGAdversary (List.Vector O n)) :
    PRFScheme.prfIdealExp (prfReduction (S := S) (O := O) n adv) =
      (idealOutputs (S := S) (O := O) n >>= adv) :=
  by
  unfold PRFScheme.prfIdealExp prfReduction idealOutputs
  rw [simulateQ_bind, simulateQ_prfIdealQueryImpl_liftComp, StateT.run'_liftM_bind]
  calc
    _ =
        ((uniformSample S) >>= fun seed =>
          (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs n seed)).run' ∅ >>=
            adv) :=
      by
      refine bind_congr fun seed => ?_
      rw [simulateQ_bind]
      simp only [simulateQ_prfIdealQueryImpl_liftComp]
      rw [StateT.run'_bind_liftM]
    _ = _ :=
      (bind_assoc (uniformSample S)
          (fun seed =>
            (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs n seed)).run' ∅)
          adv).symm


-- @@ L199-203 verbatim
/-- The per-seed output distribution: run the lazy random oracle chain for `n` rounds from a
fixed initial state `seed`, collecting the output blocks. Averaging over `seed ← $ᵗ S` gives
`idealOutputs`. -/
def seedOutputs (n : ℕ) (seed : S) : ProbComp (List.Vector O n) :=
  (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs n seed)).run' ∅


-- @@ L205-212 verbatim
/-- The per-seed collision experiment: run the lazy random oracle chain for `n` rounds from a
fixed initial state `seed`, and test whether any queried state repeats. Averaging over
`seed ← $ᵗ S` gives `idealCollisionExp`. -/
def seedCollisionExp (n : ℕ) (seed : S) : ProbComp Bool := do
  let states ←
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O))
      (oracleVisitedStates n seed)).run' ∅
  return decide (¬ states.toList.Nodup)


-- @@ L214-218 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [Inhabited O]
    [Fintype O] [DecidableEq O] in
/-- `idealOutputs` averages the per-seed chain outputs over a uniform initial state. -/
lemma idealOutputs_eq_bind :
    idealOutputs (S := S) (O := O) n = ((uniformSample S) >>= seedOutputs (S := S) (O := O) n) :=
  rfl


-- @@ L220-225 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [Inhabited O]
    [Fintype O] [DecidableEq O] in
/-- `idealCollisionExp` averages the per-seed collision test over a uniform initial state. -/
lemma idealCollisionExp_eq_bind :
    idealCollisionExp (S := S) (O := O) n =
      ((uniformSample S) >>= seedCollisionExp (S := S) (O := O) n) :=
  rfl


-- @@ L227-236 expanded
/-- Generalized collision experiment for an arbitrary starting cache `c`. Running the lazy
random oracle chain for `N` rounds from state `s`, the bad event is that the chain repeats a
state (`¬ Nodup`) or revisits a state already present in `c`. For `c = ∅` this reduces to
`seedCollisionExp`. The generalized cache is the induction vehicle: each fresh step extends
`c` by the just-visited state. -/
def genCollisionExp (N : ℕ) (s : S) (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) :
    ProbComp Bool := do
  let states ←
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleVisitedStates N s)).run' c
  return decide (¬states.toList.Nodup ∨ ∃ x ∈ states.toList, c.isCached x = true)


-- @@ L238-254 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [Inhabited O]
    [Fintype O] [DecidableEq O] in
/-- One lazy-random-oracle step of the output chain: sample/recall the answer at `s`, then
recurse on the returned next-state with the updated cache, prepending the output block. -/
private lemma simulateQ_oracleOutputs_succ_run' (N : ℕ) (s : S)
    (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) :
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs (N + 1) s)).run' c =
      (do
        let p ← ((OracleSpec.ofFn (ι := S) (fun _ => S × O)).randomOracle s).run c
        let rest ←
          (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs N p.1.1)).run' p.2
        pure (p.1.2 ::ᵥ rest)) :=
  by
  rw [oracleOutputs]
  simp only [simulateQ_bind, simulateQ_prfIdealQueryImpl_functionQuery, StateT.run'_bind']
  refine bind_congr fun a : (S × O) × (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache => ?_
  obtain ⟨⟨s', out⟩, c'⟩ := a
  simp [StateT.run'_eq]


-- @@ L256-273 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [Inhabited O]
    [Fintype O] [DecidableEq O] in
/-- One lazy-random-oracle step of the visited-state chain: sample/recall the answer at `s`, then
recurse on the returned next-state with the updated cache, prepending the just-visited state `s`. -/
private lemma simulateQ_oracleVisitedStates_succ_run' (N : ℕ) (s : S)
    (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) :
    (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleVisitedStates (N + 1) s)).run' c =
      (do
        let p ← ((OracleSpec.ofFn (ι := S) (fun _ => S × O)).randomOracle s).run c
        let rest ←
          (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleVisitedStates N p.1.1)).run'
              p.2
        pure (s ::ᵥ rest)) :=
  by
  rw [oracleVisitedStates]
  simp only [simulateQ_bind, simulateQ_prfIdealQueryImpl_functionQuery, StateT.run'_bind']
  refine bind_congr fun a : (S × O) × (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache => ?_
  obtain ⟨⟨s', out⟩, c'⟩ := a
  simp [StateT.run'_eq]


-- @@ L275-282 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [Inhabited O]
    [Fintype O] [DecidableEq O] in
/-- Cache-miss form of the lazy random oracle on input `s`: a fresh uniform draw `u : S × O`,
returned together with the cache extended by `s ↦ u`. -/
private lemma randomOracle_run_of_none (s : S)
    (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) (hc : c s = none) :
    ((OracleSpec.ofFn (ι := S) (fun _ => S × O)).randomOracle s).run c =
      (fun u => (u, c.cacheQuery s u)) <$> (uniformSample (S × O)) :=
  by rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc]; rfl


-- @@ L284-291 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [DecidableEq S]
    [Inhabited O] [Fintype O] [DecidableEq O] in
/-- Sampling a pair uniformly is the same as sampling each coordinate independently. -/
private lemma uniformSample_prod_eq_bind :
    (uniformSample (S × O)) =
      (do
        let a ← uniformSample S;
        let b ← uniformSample O;
        pure (a, b)) :=
  by
  rw [uniformSample]
  change ((·, ·) <$> (uniformSample S) <*> (uniformSample O)) = _
  simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]


-- @@ L293-326 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [DecidableEq S]
    [SampleableType S] [Inhabited O] [Fintype O] [DecidableEq O] in
/-- A uniform output vector of length `N + 1` decomposes as a uniform head block prepended to a
uniform vector of length `N`. -/
private lemma evalSPMF_uniformSample_vector_succ (N : ℕ) :
    evalSPMF (uniformSample (List.Vector O (N + 1))) =
      evalSPMF
        (do
          let out ← uniformSample O;
          let rest ← uniformSample (List.Vector O N);
          pure (out ::ᵥ rest)) :=
  by
  classical
  have : Fintype O := Fintype.ofFinite O
  refine evalSPMF_ext fun v => ?_
  obtain ⟨out, rest, rfl⟩ : ∃ out rest, v = out ::ᵥ rest :=
    ⟨v.head, v.tail, (List.Vector.cons_head_tail v).symm⟩
  have hR :
    probOutput
        (do
          let o ← uniformSample O;
          let r ← uniformSample (List.Vector O N);
          pure (o ::ᵥ r))
        (out ::ᵥ rest) =
      probOutput (uniformSample O) out * probOutput (uniformSample (List.Vector O N)) rest :=
    by
    rw [probOutput_bind_eq_tsum, tsum_eq_single out]
    · rw [probOutput_bind_eq_tsum, tsum_eq_single rest]
      · simp
      · intro b hb
        rw [probOutput_pure, if_neg (by simp [List.Vector.eq_cons_iff, Ne.symm hb]), mul_zero]
    · intro b hb
      rw [probOutput_bind_eq_tsum,
        ENNReal.tsum_eq_zero.2
          (fun r => by
            rw [probOutput_pure, if_neg (by simp [List.Vector.eq_cons_iff, Ne.symm hb]), mul_zero]),
        mul_zero]
  have hL :
    probOutput (uniformSample (List.Vector O (N + 1))) (out ::ᵥ rest) =
      probOutput (uniformSample O) out * probOutput (uniformSample (List.Vector O N)) rest :=
    by
    rw [probOutput_uniformSample, probOutput_uniformSample, probOutput_uniformSample, ←
      ENNReal.mul_inv (by simp) (by simp)]
    congr 1
    rw [← Nat.cast_mul]
    congr 1
    simp [card_vector, pow_succ, Nat.mul_comm]
  rw [hL, hR]


-- @@ L328-339 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [DecidableEq S]
    [Inhabited O] [Fintype O] [DecidableEq O] in
/-- The reference uniform output vector of length `N + 1`, written as a bind over a uniformly
sampled pair `p : S × O` whose first coordinate is discarded and whose second coordinate is the
prepended head block. This is the shared-base form used for the identical-until-bad coupling. -/
private lemma evalSPMF_uniformSample_vector_succ_pair (N : ℕ) :
    evalSPMF (uniformSample (List.Vector O (N + 1))) =
      evalSPMF
        (do
          let p ← uniformSample (S × O);
          let rest ← uniformSample (List.Vector O N);
          pure (p.2 ::ᵥ rest)) :=
  by
  rw [evalSPMF_uniformSample_vector_succ, uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  refine (evalSPMF_ext fun v => ?_).symm
  rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]


-- @@ L341-388 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [Inhabited O]
    [Fintype O] [DecidableEq O] in
/-- Cache-miss recursion for the generalized collision experiment. When `s` is uncached, the bad
event on the length-`N + 1` visited chain splits into the fresh draw at `s` (extending the cache by
`s`) followed by the bad event on the length-`N` sub-chain run against the extended cache. The
just-visited state `s` is folded into the cache, so the two bad events match pointwise. -/
private lemma genCollisionExp_succ_of_none (N : ℕ) (s : S)
    (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) (hc : c s = none) :
    genCollisionExp (N + 1) s c =
      (do
        let p ← uniformSample (S × O);
        genCollisionExp N p.1 (c.cacheQuery s p)) :=
  by
  rw [genCollisionExp, simulateQ_oracleVisitedStates_succ_run', randomOracle_run_of_none s c hc]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  rw [uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun a => bind_congr fun b => ?_
  rw [genCollisionExp]
  refine bind_congr fun rest => ?_
  congr 1
  rw [decide_eq_decide, List.Vector.toList_cons]
    -- pointwise equivalence of the two bad events, using `c s = none`.
    
  have hkey : ∀ x : S, (c.cacheQuery s (a, b)).isCached x = true ↔ (x = s ∨ c.isCached x = true) :=
    by
    intro x
    by_cases hx : x = s
    · subst hx; simp
    · rw [QueryCache.isCached_cacheQuery_of_ne c (a, b) hx]; simp [hx]
  have hcs : c.isCached s = false := by simp [QueryCache.isCached, hc]
  have hrest :
    (∃ x ∈ rest.toList, (c.cacheQuery s (a, b)).isCached x = true) ↔
      (s ∈ rest.toList ∨ ∃ x ∈ rest.toList, c.isCached x = true) :=
    by
    constructor
    · rintro ⟨x, hx, hxc⟩
      rcases (hkey x).1 hxc with rfl | hc'
      · exact Or.inl hx
      · exact Or.inr ⟨x, hx, hc'⟩
    · rintro (hs | ⟨x, hx, hxc⟩)
      · exact ⟨s, hs, (hkey s).2 (Or.inl rfl)⟩
      · exact ⟨x, hx, (hkey x).2 (Or.inr hxc)⟩
  have hhead :
    (∃ x ∈ (s :: rest.toList), c.isCached x = true) ↔ (∃ x ∈ rest.toList, c.isCached x = true) :=
    by
    constructor
    · rintro ⟨x, hx, hxc⟩
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [hcs] at hxc; exact absurd hxc (by simp)
      · exact ⟨x, hx, hxc⟩
    · rintro ⟨x, hx, hxc⟩; exact ⟨x, List.mem_cons_of_mem _ hx, hxc⟩
  rw [hrest, List.nodup_cons, hhead]
  tauto


-- @@ L390-406 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [Inhabited O]
    [Fintype O] [DecidableEq O] in
/-- Cache-hit determinism for the generalized collision experiment. When `s` is already cached, the
visited chain of length `N + 1` starts at `s`, which lies in the chain and is cached, so the bad
event always fires and the experiment returns `true` with probability one. -/
private lemma probOutput_genCollisionExp_succ_of_isCached (N : ℕ) (s : S)
    (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) (hc : c.isCached s = true) :
    probOutput (genCollisionExp (N + 1) s c) true = 1 :=
  by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · simp [genCollisionExp]
  · intro x hx
    rw [genCollisionExp, simulateQ_oracleVisitedStates_succ_run'] at hx
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hx
    obtain ⟨p, ⟨_, -, rest, -, hpeq⟩, rfl⟩ := hx
    subst hpeq
    rw [List.Vector.toList_cons, decide_eq_true (Or.inr ⟨s, List.mem_cons_self, hc⟩)]


-- @@ L408-482 expanded
omit [Inhabited S] [Fintype S] [Inhabited O] [Fintype O] [DecidableEq O] in
/-- **Generalized per-seed core coupling.** For an arbitrary starting cache `c`, the total
variation distance between the lazy-random-oracle output chain (run from cache `c`) and a
uniformly random output vector is bounded by the generalized collision probability. Proved by
induction on the number of rounds: a fresh query produces an independent uniform block and the
cache grows by exactly the just-visited state, so the collision recursion closes; a repeated
query has already triggered the bad event, where the bound is trivially `1`. -/
lemma tvDist_seedOutputs_le_collision_gen (N : ℕ) (s : S)
    (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) :
    tvDist ((simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs N s)).run' c)
        (uniformSample (List.Vector O N)) ≤
      (probOutput (genCollisionExp N s c) true).toReal :=
  by
  have : Fintype O := Fintype.ofFinite O
  induction N generalizing s c with
  | zero =>
    refine le_trans (le_of_eq ?_) ENNReal.toReal_nonneg
    rw [tvDist_eq_zero_iff]
    simp only [oracleOutputs, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine evalSPMF_ext fun y => ?_
    simp [List.Vector.eq_nil y]
  | succ N ih =>
    cases hc : c.isCached s with
    | false =>
      -- Cache miss: identical-until-bad coupling.
      
      have hcnone : c s = none := by simpa [QueryCache.isCached] using hc
      have hLHS :
        (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs (N + 1) s)).run' c =
          (do
            let p ← uniformSample (S × O);
            (fun v => p.2 ::ᵥ v) <$>
                (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs N p.1)).run'
                  (c.cacheQuery s p)) :=
        by
        rw [simulateQ_oracleOutputs_succ_run', randomOracle_run_of_none s c hcnone, bind_map_left]
        simp only [map_eq_bind_pure_comp, bind_pure_comp]
      have hRHS :
        evalSPMF (uniformSample (List.Vector O (N + 1))) =
          evalSPMF
            (do
              let p ← uniformSample (S × O);
              (fun v => p.2 ::ᵥ v) <$> (uniformSample (List.Vector O N))) :=
        by
        rw [evalSPMF_uniformSample_vector_succ_pair (S := S) N]
        congr 1
        refine bind_congr fun p => ?_
        rw [map_eq_bind_pure_comp]
        rfl
          -- Rewrite the goal as a TV distance between two binds over the shared pair `p : S × O`.
          
      rw [hLHS]
      rw [show
          tvDist
              ((uniformSample (S × O)) >>= fun p =>
                (fun v => p.2 ::ᵥ v) <$>
                  (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs N p.1)).run'
                    (c.cacheQuery s p))
              (uniformSample (List.Vector O (N + 1))) =
            tvDist
              ((uniformSample (S × O)) >>= fun p =>
                (fun v => p.2 ::ᵥ v) <$>
                  (simulateQ (prfIdealQueryImpl (D := S) (R := S × O)) (oracleOutputs N p.1)).run'
                    (c.cacheQuery s p))
              ((uniformSample (S × O)) >>= fun p =>
                (fun v => p.2 ::ᵥ v) <$> (uniformSample (List.Vector O N)))
          from by unfold tvDist; rw [hRHS]]
      refine
        le_trans (tvDist_bind_left_le _ _ _)
          ?_
            -- Bound each per-pair TV distance by the per-pair generalized collision probability.
            
      rw [genCollisionExp_succ_of_none N s c hcnone, probOutput_bind_eq_tsum,
        ENNReal.tsum_toReal_eq (fun p => ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)]
      refine Summable.tsum_le_tsum (fun p => ?_) ?_ ?_
      · rw [ENNReal.toReal_mul]
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        exact le_trans (tvDist_map_le (fun v => p.2 ::ᵥ v) _ _) (ih p.1 (c.cacheQuery s p))
      ·
        refine
          Summable.of_nonneg_of_le (fun p => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
            (fun p => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _))
            (ENNReal.summable_toReal tsum_probOutput_ne_top)
      · exact ENNReal.summable_toReal (by rw [← probOutput_bind_eq_tsum]; exact probOutput_ne_top)
    | true =>
      -- Cache hit: the bad event already fired, so the bound is trivially `1`.
      
      rw [probOutput_genCollisionExp_succ_of_isCached N s c hc, ENNReal.toReal_one]
      exact tvDist_le_one _ _


-- @@ L484-500 expanded
omit [Inhabited S] [Fintype S] [Inhabited O] [Fintype O] [DecidableEq O] in
/-- **Per-seed core coupling.** For a fixed initial state, the total variation distance between
the lazy-random-oracle output chain and a uniformly random output vector is bounded by the
probability that the state chain revisits a state. This is the fundamental "identical until
bad" step: until the chain repeats, the lazy random oracle returns independent uniform blocks.

The empty-cache specialization of `tvDist_seedOutputs_le_collision_gen`. -/
lemma tvDist_seedOutputs_le_collision (seed : S) :
    tvDist (seedOutputs n seed) (uniformSample (List.Vector O n)) ≤
      (probOutput (seedCollisionExp (O := O) n seed) true).toReal :=
  by
  have heq : genCollisionExp (O := O) n seed ∅ = seedCollisionExp (O := O) n seed :=
    by
    unfold genCollisionExp seedCollisionExp
    refine bind_congr fun states => ?_
    simp [QueryCache.isCached_empty]
  have h := tvDist_seedOutputs_le_collision_gen (O := O) n seed ∅
  rw [heq] at h
  exact h


-- @@ L502-534 expanded
omit [Inhabited S] [Fintype S] [Inhabited O] [Fintype O] [DecidableEq O] in
/-- **Core coupling.** The total variation distance between the lazy-random-oracle output
chain and a uniformly random output vector is bounded by the state-collision probability.
This is the fundamental "identical until bad" step: until the state chain repeats, the lazy
random oracle returns independent uniform blocks, matching the ideal PRG distribution.

Obtained by averaging the per-seed bound `tvDist_seedOutputs_le_collision` over the uniform
initial state. -/
lemma tvDist_idealOutputs_le_collisionProb :
    tvDist (idealOutputs (S := S) (O := O) n) (uniformSample (List.Vector O n)) ≤
      collisionProb (S := S) (O := O) n :=
  by
  rw [collisionProb, idealCollisionExp_eq_bind, idealOutputs_eq_bind]
    -- Replace the constant right-hand side by a (lossless) bind over the same seed.
    
  have h_const :
    tvDist ((uniformSample S) >>= seedOutputs n) (uniformSample (List.Vector O n)) =
      tvDist ((uniformSample S) >>= seedOutputs n)
        ((uniformSample S) >>= fun _ => uniformSample (List.Vector O n)) :=
    by
    simp only [tvDist]
    congr 1
    refine evalSPMF_ext fun y => ?_
    rw [probOutput_bind_const]
    simp
  rw [h_const]
  refine
    le_trans (tvDist_bind_left_le _ _ _)
      ?_
        -- Bound each per-seed TV distance by the per-seed collision probability, then reassemble.
        
  rw [probOutput_bind_eq_tsum]
  rw [ENNReal.tsum_toReal_eq (fun seed => ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)]
  refine Summable.tsum_le_tsum (fun seed => ?_) ?_ ?_
  · rw [ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_left (tvDist_seedOutputs_le_collision seed) ENNReal.toReal_nonneg
  ·
    exact
      Summable.of_nonneg_of_le (fun seed => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
        (fun seed => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _))
        (ENNReal.summable_toReal tsum_probOutput_ne_top)
  · exact ENNReal.summable_toReal (by rw [← probOutput_bind_eq_tsum]; exact probOutput_ne_top)


-- @@ L536-566 expanded
omit [Inhabited S] [Fintype S] [Inhabited O] [Fintype O] [DecidableEq O] in
/-- The gap between the ideal PRF and ideal PRG experiments is bounded by the
collision probability. This follows from the fundamental lemma of game playing:
when a lazy random function never receives the same input twice, its outputs are
independent uniform — matching the ideal PRG distribution exactly. The bound
comes from the probability that the state chain revisits some state.

*Proof outline (switching argument):*
1. Factor both experiments as: sample inputs to `adv`, then run `adv`.
2. In the ideal PRF world, the inputs come from a random-oracle chain.
3. In the ideal PRG world, the inputs are i.i.d. uniform.
4. Conditioned on no state collision, the random-oracle chain produces
   independent uniform outputs, so the two input distributions coincide.
5. By the "identical until bad" lemma (`tvDist_simulateQ_le_probEvent_bad`),
   the TV distance between the two input distributions is at most `Pr[collision]`.
6. By the data-processing inequality, running `adv` cannot increase the gap.

Full formalization requires coupling the random-oracle chain with independent
uniform outputs and instantiating the switching-lemma infrastructure for this
specific oracle. -/
theorem prfIdealGap_le_collisionProb (adv : PRGAdversary (List.Vector O n)) :
    |(probOutput (PRFScheme.prfIdealExp (prfReduction (S := S) (O := O) n adv)) true).toReal -
          (probOutput (PRGScheme.prgIdealExp adv) true).toReal| ≤
      collisionProb (S := S) (O := O) n :=
  by
  rw [prfIdealExp_prfReduction_eq adv, prgIdealExp_eq_bind adv]
  calc
    |(probOutput (idealOutputs n >>= adv) true).toReal -
            (probOutput ((uniformSample (List.Vector O n)) >>= adv) true).toReal| ≤
        tvDist (idealOutputs n >>= adv) ((uniformSample (List.Vector O n)) >>= adv) :=
      abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist (idealOutputs n) (uniformSample (List.Vector O n)) := (tvDist_bind_right_le _ _ _)
    _ ≤ collisionProb (S := S) (O := O) n := tvDist_idealOutputs_le_collisionProb


-- @@ L568-591 expanded
omit [Inhabited K] [Fintype K] [Inhabited S] [Fintype S] [Inhabited O] [Fintype O]
    [DecidableEq O] in
/-- Security of the stream PRG obtained from a PRF: PRG distinguishing advantage is
bounded by the PRF advantage of the reduction plus the collision probability in the
ideal random-function world. -/
theorem security (hkey : evalSPMF prf.keygen = evalSPMF (uniformSample K))
    (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgAdvantage (streamPRG prf n) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction (S := S) (O := O) n adv) +
        collisionProb (S := S) (O := O) n :=
  by
  unfold PRGScheme.prgAdvantage PRFScheme.prfAdvantage
  have hreal :
    (probOutput (PRGScheme.prgRealExp (streamPRG prf n) adv) true).toReal =
      (probOutput (PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)) true).toReal :=
    congrArg ENNReal.toReal (probOutput_congr rfl (prgRealExp_eq_prfRealExp hkey adv))
  rw [hreal]
  set a :=
    (probOutput (PRFScheme.prfRealExp prf (prfReduction (S := S) (O := O) n adv)) true).toReal
  set b := (probOutput (PRFScheme.prfIdealExp (prfReduction (S := S) (O := O) n adv)) true).toReal
  set c := (probOutput (PRGScheme.prgIdealExp adv) true).toReal
  have hgap : |b - c| ≤ collisionProb (S := S) (O := O) n := prfIdealGap_le_collisionProb adv
  calc
    |a - c| = |(a - b) + (b - c)| := by ring_nf
    _ ≤ |a - b| + |b - c| := (abs_add_le _ _)
    _ ≤ |a - b| + collisionProb (S := S) (O := O) n := by linarith


-- @@ L593-619 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [SampleableType S]
    [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O] in
/-- Caching a fresh (previously absent) key increases the live-entry count by exactly one. -/
private lemma enncard_cacheQuery_of_none
    (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) (s : S) (u : S × O)
    (hc : c s = none) : QueryCache.enncard (c.cacheQuery s u) = QueryCache.enncard c + 1 :=
  by
  unfold QueryCache.enncard
  have hset : (c.cacheQuery s u).toSet = insert ⟨s, u⟩ c.toSet :=
    by
    ext ⟨t', u'⟩
    by_cases ht : t' = s
    · subst ht
      simp only [QueryCache.mem_toSet, QueryCache.cacheQuery_self, Set.mem_insert_iff,
        Sigma.mk.injEq, heq_eq_eq, true_and]
      constructor
      · intro h
        exact Or.inl (Option.some.inj h).symm
      · rintro (rfl | h)
        · rfl
        · rw [hc] at h; exact absurd h (by simp)
    · rw [QueryCache.mem_toSet, QueryCache.cacheQuery_of_ne c u ht]
      simp [Set.mem_insert_iff, ht, QueryCache.mem_toSet]
  rw [hset]
  have hnotmem : (⟨s, u⟩ : (t : S) × S × O) ∉ c.toSet := by rw [QueryCache.mem_toSet, hc]; simp
  rw [Set.encard_insert_of_notMem hnotmem]
  push_cast
  ring


-- @@ L621-650 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [DecidableEq S] [SampleableType S]
    [Inhabited O] [Fintype O] [DecidableEq O] [SampleableType O] in
/-- For a finite state space, the live-entry count of a cache is the number of cached states. -/
private lemma enncard_eq_sum_isCached (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) :
    QueryCache.enncard c = ∑ s : S, (if c.isCached s then (1 : ℝ≥0∞) else 0) := by
  classical
  unfold QueryCache.enncard
  have himg : Sigma.fst '' c.toSet = {s : S | c.isCached s = true} :=
    by
    ext s
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨t, u⟩, ht, rfl⟩
      rw [QueryCache.mem_toSet] at ht
      simp [QueryCache.isCached, ht]
    · intro hs
      rw [QueryCache.isCached, Option.isSome_iff_exists] at hs
      obtain ⟨u, hu⟩ := hs
      exact ⟨⟨s, u⟩, hu, rfl⟩
  have hinj : Set.InjOn Sigma.fst c.toSet :=
    by
    rintro ⟨t₁, u₁⟩ h₁ ⟨t₂, u₂⟩ h₂ (rfl : t₁ = t₂)
    rw [QueryCache.mem_toSet] at h₁ h₂
    rw [h₁] at h₂
    obtain rfl := Option.some.inj h₂
    rfl
  have hencard : c.toSet.encard = {s : S | c.isCached s = true}.encard := by
    rw [← himg, hinj.encard_image]
  rw [hencard, Set.encard_eq_coe_toFinset_card, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [mul_one, mul_zero, add_zero, nsmul_eq_mul]
  rw [Set.toFinset_ofPred]
  norm_cast


-- @@ L652-682 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [Inhabited O]
    [Fintype O] [DecidableEq O] in
/-- **Domain-invariance of the collision probability.** The generalized collision experiment reads
the starting cache only through its domain (`isCached`): on the good path cached values are never
inspected, and on a hit the bad event has already fired. Hence two caches with the same domain give
the same collision probability. -/
private lemma probOutput_genCollisionExp_eq_of_isCached_agree (N : ℕ) (s : S)
    (c c' : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache)
    (h : ∀ x, c.isCached x = c'.isCached x) :
    probOutput (genCollisionExp N s c) true = probOutput (genCollisionExp N s c') true := by
  induction N generalizing s c c' with
  | zero => simp [genCollisionExp]
  | succ N ih =>
    cases hc : c.isCached s with
    | true =>
      rw [probOutput_genCollisionExp_succ_of_isCached N s c hc,
        probOutput_genCollisionExp_succ_of_isCached N s c' (by rw [← h s]; exact hc)]
    | false =>
      have hc' : c'.isCached s = false := by rw [← h s]; exact hc
      have hcnone : c s = none := by simpa [QueryCache.isCached] using hc
      have hc'none : c' s = none := by simpa [QueryCache.isCached] using hc'
      rw [genCollisionExp_succ_of_none N s c hcnone, genCollisionExp_succ_of_none N s c' hc'none,
        probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine tsum_congr fun p => ?_
      congr 1
      refine ih p.1 (c.cacheQuery s p) (c'.cacheQuery s p) fun x => ?_
      by_cases hx : x = s
      · subst hx; simp
      · rw [QueryCache.isCached_cacheQuery_of_ne c p hx,
          QueryCache.isCached_cacheQuery_of_ne c' p hx]
        exact h x


-- @@ L684-696 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Inhabited S] [Fintype S] [DecidableEq S]
    [Inhabited O] [Fintype O] [DecidableEq O] in
/-- Sampling a pair uniformly and discarding the second coordinate is the same as sampling the
first coordinate uniformly. -/
private lemma probOutput_bind_uniformSample_prod_fst (f : S → ProbComp Bool) (b : Bool) :
    probOutput
        (do
          let p ← uniformSample (S × O);
          f p.1)
        b =
      probOutput
        (do
          let s' ← uniformSample S;
          f s')
        b :=
  by
  have heq :
    (do
        let p ← uniformSample (S × O);
        f p.1) =
      (do
        let a ← uniformSample S;
        let _ ← uniformSample O;
        f a) :=
    by
    rw [uniformSample_prod_eq_bind]
    simp only [bind_assoc, pure_bind]
  rw [heq, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun a => ?_
  congr 1
  rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]


-- @@ L698-772 expanded
omit [Inhabited K] [Fintype K] [SampleableType K] [Fintype O] [DecidableEq O] in
/-- **Generalized averaged birthday bound.** Averaging over the uniform initial state, the
generalized collision probability of the length-`N` chain starting from cache `c` is bounded by
`∑_{j < N} (|c| + j) / |S|`. Proved by induction on `N` (generalizing `c`): a cache miss draws a
fresh uniform state, growing the cache by one and shifting the bound; the union over already-cached
states contributes the leading `|c| / |S|` term. -/
private lemma probOutput_genCollisionExp_bind_le (N : ℕ)
    (c : (OracleSpec.ofFn (ι := S) (fun _ => S × O)).QueryCache) :
    probOutput
        (do
          let s ← uniformSample S;
          genCollisionExp N s c)
        true ≤
      ∑ j ∈ Finset.range N, (QueryCache.enncard c + (j : ℝ≥0∞)) * (Fintype.card S : ℝ≥0∞)⁻¹ :=
  by
  induction N generalizing c with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, nonpos_iff_eq_zero]
    rw [probOutput_bind_eq_tsum]
    simp [genCollisionExp]
  | succ N ih =>
    set C : ℝ≥0∞ := (Fintype.card S : ℝ≥0∞) with hC
    have hCne : C ≠ 0 := by rw [hC]; exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hCtop : C ≠ ⊤ := by rw [hC]; exact ENNReal.natCast_ne_top _
    have hCcancel : C * C⁻¹ = 1 := ENNReal.mul_inv_cancel hCne hCtop
    set B : ℝ≥0∞ := ∑ j ∈ Finset.range N, (QueryCache.enncard c + 1 + (j : ℝ≥0∞)) * C⁻¹ with hB
    have hterm :
      ∀ s : S,
        probOutput (genCollisionExp (N + 1) s c) true ≤
          (if c.isCached s then (1 : ℝ≥0∞) else 0) + B :=
      by
      intro s
      cases hcs : c.isCached s with
      | true =>
        rw [probOutput_genCollisionExp_succ_of_isCached N s c hcs, if_pos rfl]
        exact le_self_add
      | false =>
        rw [if_neg (by simp), zero_add]
        have hcnone : c s = none := by simpa [QueryCache.isCached] using hcs
        rw [genCollisionExp_succ_of_none N s c hcnone]
          -- Replace each fresh cache value by a fixed one (domain invariance), then drop the
                  -- unused output coordinate.
          
        have hdom :
          probOutput ((uniformSample (S × O)) >>= fun p => genCollisionExp N p.1 (c.cacheQuery s p))
              true =
            probOutput
              ((uniformSample (S × O)) >>= fun p =>
                genCollisionExp N p.1 (c.cacheQuery s (default, default)))
              true :=
          by
          rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
          refine tsum_congr fun p => ?_
          congr 1
          refine probOutput_genCollisionExp_eq_of_isCached_agree N p.1 _ _ fun x => ?_
          by_cases hx : x = s
          · subst hx; simp
          ·
            rw [QueryCache.isCached_cacheQuery_of_ne c p hx,
              QueryCache.isCached_cacheQuery_of_ne c (default, default) hx]
        rw [hdom,
          probOutput_bind_uniformSample_prod_fst
            (fun s' => genCollisionExp N s' (c.cacheQuery s (default, default))) true]
        refine le_trans (ih (c.cacheQuery s (default, default))) (le_of_eq ?_)
        rw [hB]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [enncard_cacheQuery_of_none c s (default, default) hcnone]
    calc
      probOutput
            (do
              let s ← uniformSample S;
              genCollisionExp (N + 1) s c)
            true =
          ∑ s : S, probOutput (uniformSample S) s * probOutput (genCollisionExp (N + 1) s c) true :=
        probOutput_bind_eq_sum_fintype _ _ true
      _ ≤
          ∑ s : S,
            probOutput (uniformSample S) s * ((if c.isCached s then (1 : ℝ≥0∞) else 0) + B) :=
        by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left (hterm s) (by simp)
      _ = QueryCache.enncard c * C⁻¹ + B :=
        by
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        · rw [enncard_eq_sum_isCached, Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [probOutput_uniformSample, ← hC, mul_comm]
        · simp_rw [probOutput_uniformSample, ← hC, ← Finset.sum_mul]
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hC, hCcancel, one_mul]
      _ = ∑ j ∈ Finset.range (N + 1), (QueryCache.enncard c + (j : ℝ≥0∞)) * C⁻¹ :=
        by
        rw [Finset.sum_range_succ', hB]
        rw [Nat.cast_zero, add_zero]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast
        ring_nf


-- @@ L774-806 expanded
omit [Fintype O] [DecidableEq O] in
/-- **Birthday bound for the state-collision probability.** Over `n` rounds of the lazy random
oracle chain, each freshly sampled state is uniform over `S`, so the probability that the chain
revisits a state is at most `n·(n-1) / (2·|S|)` by a union bound over the at most `C(n,2)` pairs. -/
theorem collisionProb_le_birthday (n : ℕ) :
    collisionProb (S := S) (O := O) n ≤ ((n * (n - 1) : ℕ) : ℝ) / (2 * Fintype.card S) := by
  -- The collision probability equals the empty-cache averaged collision probability.
  
  have hseed : ∀ seed : S, genCollisionExp (O := O) n seed ∅ = seedCollisionExp (O := O) n seed :=
    by
    intro seed
    unfold genCollisionExp seedCollisionExp
    refine bind_congr fun states => ?_
    simp [QueryCache.isCached_empty]
  have hcomp :
    ((do
          let s ← uniformSample S;
          genCollisionExp (O := O) n s ∅) :
        ProbComp Bool) =
      idealCollisionExp (S := S) (O := O) n :=
    by
    rw [idealCollisionExp_eq_bind]
    exact bind_congr hseed
  have hbound :
    probOutput (idealCollisionExp (S := S) (O := O) n) true ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * (Fintype.card S : ℝ≥0∞)) :=
    by
    rw [← hcomp]
    refine le_trans (probOutput_genCollisionExp_bind_le n ∅) (le_of_eq ?_)
    simp only [QueryCache.enncard_empty, zero_add]
    exact
      ENNReal.gauss_sum_inv_eq n
        (Fintype.card S : ℝ≥0∞)
          -- Convert the ENNReal bound to a real bound.
          
  have hden : (2 * (Fintype.card S : ℝ≥0∞)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [collisionProb]
  refine
    le_trans (ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hden) hbound)
      (le_of_eq ?_)
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  norm_num


-- @@ L808-820 expanded
omit [Inhabited K] [Fintype K] [Fintype O] [DecidableEq O] in
/-- **Concrete security of the stream PRG.** The PRG distinguishing advantage is bounded by the
PRF advantage of the reduction plus the birthday term `n·(n-1) / (2·|S|)`, obtained by combining
`security` with `collisionProb_le_birthday`. -/
theorem security_birthday (hkey : evalSPMF prf.keygen = evalSPMF (uniformSample K))
    (adv : PRGAdversary (List.Vector O n)) :
    PRGScheme.prgAdvantage (streamPRG prf n) adv ≤
      PRFScheme.prfAdvantage prf (prfReduction (S := S) (O := O) n adv) +
        ((n * (n - 1) : ℕ) : ℝ) / (2 * Fintype.card S) :=
  by
  refine (security hkey adv).trans ?_
  have := collisionProb_le_birthday (S := S) (O := O) n
  linarith


-- @@ L822-822 verbatim
end streamPRG


-- @@ L824-824 verbatim
end PRGfromPRF
