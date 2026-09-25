/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Compatibility
public import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
public import VCVio.EvalDist.Inequalities


-- @@ L14-20 verbatim
/-!
# Fiat-Shamir reductions for Sigma protocols

This file exposes the CMA-to-NMA reduction used by the public Sigma security
theorem. The proof is discharged by the direct stateful game chain; callers
depend only on the reduction statement here.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace FiatShamir


-- @@ L26-26 verbatim
open OracleComp OracleSpec

-- @@ L27-27 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L29-32 verbatim
variable {Stmt Wit Commit PrvState Chal Resp : Type}
    [Fintype Stmt] [Fintype Commit] [Fintype Resp] [Fintype Chal]
    [Inhabited Stmt] [Inhabited Commit] [Inhabited Resp] [Inhabited Chal]
    {rel : Stmt → Wit → Bool}

-- @@ L33-34 verbatim
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)


-- @@ L36-38 expanded
noncomputable local instance instIsUniformSpecChalSingleton :
    IsUniformSpec ((OracleSpec.ofFn (ι := Unit) (fun _ => Chal)) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _


-- @@ L40-42 expanded
noncomputable local instance instIsUniformSpecChalFn (M Commit : Type) :
    IsUniformSpec ((OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _


-- @@ L44-85 expanded
omit [Fintype Stmt] [Fintype Commit] [Fintype Resp] [Fintype Chal] [Inhabited Stmt]
    [Inhabited Chal] in
/-- CMA-to-NMA reduction for Fiat-Shamir signatures built from a Sigma protocol.

The reduction runs the CMA adversary with simulated signing transcripts and a
managed random oracle, then appends a single explicit live random-oracle query
for the forgery's hash point so that the verification challenge is part of the
forkable transcript (the `nmaAdvFromCmaWithFinalQuery` wrapper). The quantitative
loss is the HVZK simulation cost plus the programming-collision term from
simulator commit predictability; no separate verifier-guessing slack is needed.

The bound is stated against `Fork.advantage σ hr M nmaAdv qH`: the wrapped
adversary issues `qH + 1` random-oracle queries, and `Fork.forkPoint qH`
indexes `Fin (qH + 1)`, which is exactly the right number of forkable slots
(the framework's structural `+1` in `Fin (qH + 1)` is precisely the wrapper's
verifier slot). The replay-forking denominator is therefore `qH + 1`. -/
theorem cma_to_nma_advantage_bound [DecidableEq M] [DecidableEq Commit] [SampleableType Stmt]
    [SampleableType Wit] [Finite Stmt] [Finite Commit] [Finite Resp] [Finite Chal] [Inhabited Chal]
    [SampleableType Chal] (simTranscript : Stmt → ProbComp (Commit × Chal × Resp)) (ζ_zk : ℝ)
    (hζ_zk : 0 ≤ ζ_zk) (hHVZK : σ.HVZK simTranscript ζ_zk) (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simTranscript β)
    (adv :
      SignatureAlg.unforgeableAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (qS qH : ℕ)
    (hQ :
      ∀ pk,
        signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (S' := Commit × Resp) (oa :=
          adv.main pk) qS qH) :
    ∃ nmaAdv :
      SignatureAlg.managedRoNmaAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M),
      adv.advantage (runtime M) ≤
        Fork.advantage σ hr M nmaAdv qH + ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * (qS + qH) * β :=
  ⟨Stateful.nmaAdvFromCmaWithFinalQuery σ hr M adv simTranscript,
    Stateful.cma_advantage_le_fork_bound_of_h1h2 σ hr M simTranscript ζ_zk hζ_zk hHVZK β hPredSim
      adv qS qH hQ
      (le_of_eq <|
        (Stateful.publicUnforgeableAdvantage_eq_statefulPostKeygenFreshAdvantage (σ := σ) (hr := hr)
              (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv).trans
          (Stateful.statefulPostKeygenFreshAdvantage_eq_cmaRealRunProb_signedFreshAdv (σ := σ)
            (hr := hr) (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) adv))⟩


-- @@ L87-87 verbatim
section evalSPMFBridge


-- @@ L89-89 verbatim
variable [SampleableType Chal]


-- @@ L91-105 expanded
/-- The `ofLift + uniformSampleImpl` simulation on `unifSpec + (Unit →ₒ Chal)` preserves
`evalSPMF`. Both oracle components sample uniformly from their range. -/
private lemma evalSPMF_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal))) α) :
    evalSPMF
        (simulateQ
          (QueryImpl.ofLift unifSpec ProbComp +
            (uniformSampleImpl (spec := (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))))
          oa) =
      evalSPMF oa :=
  by
  apply OracleComp.evalSPMF_simulateQ_eq_evalSPMF
  rintro (n | u)
  · simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply]
    rw [evalSPMF_query (spec := unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))]
    exact evalSPMF_query (spec := unifSpec) n
  · simp only [QueryImpl.add_apply_inr, uniformSampleImpl]
    exact
      show
        (evalSPMF (uniformSample ((ofFn fun _ : Unit => Chal).Range u)) :
            SPMF ((ofFn fun _ : Unit => Chal).Range u)) =
          _
        by rw [evalSPMF_uniformSample, evalSPMF_query]; rfl


-- @@ L107-112 expanded
/-- Corollary: `probEvent` is preserved by the `ofLift + uniformSampleImpl` simulation. -/
private lemma probEvent_simulateQ_unifChalImpl {α : Type}
    (oa : OracleComp (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal))) α) (p : α → Prop) :
    probEvent
        (simulateQ
          (QueryImpl.ofLift unifSpec ProbComp +
            (uniformSampleImpl (spec := (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))))
          oa)
        p =
      probEvent oa p :=
  probEvent_congr' (fun _ _ => Iff.rfl) (evalSPMF_simulateQ_unifChalImpl oa)


-- @@ L114-114 verbatim
end evalSPMFBridge


-- @@ L116-116 verbatim
section nmaToExtraction


-- @@ L118-118 verbatim
variable [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal]


-- @@ L120-124 verbatim
/-- Replay-fork query budget for the NMA reduction: forward the `.inl unifSpec` component
live and rewind only the counted challenge oracle on the `.inr` side. -/
private def nmaForkBudget (qH : ℕ) : ℕ ⊕ Unit → ℕ
  | .inl _ => 0
  | .inr () => qH


-- @@ L126-139 expanded
/-- Per-run invariant for the NMA replay fork. If `Fork.forkPoint qH` selects index `s`,
the cached RO value at `x.target`, the outer log's `s`-th counted-oracle response, and the
challenge under which `x.forgery` verifies all coincide. -/
private def forkSupportInvariant (qH : ℕ) (pk : Stmt)
    (x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (log : QueryLog (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))) : Prop :=
  ∀ s : Fin (qH + 1),
    Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH x = some s →
      ∃ ω : Chal,
        QueryLog.getQueryValue? log (Sum.inr ()) (↑s : ℕ) = some ω ∧
          x.roCache x.target = some ω ∧ σ.verify pk x.target.2 ω x.forgery.2.2 = true


-- @@ L141-141 verbatim
variable [SampleableType Wit] [SampleableType Chal]


-- @@ L143-162 expanded
/-- The branch the NMA extractor takes on a forking-lemma result: from two traces sharing a
commitment whose distinct cached challenges accept, run `σ.extract`; otherwise resample. This is
the post-`contextFork` continuation of `nmaForkExtract`. -/
private def nmaForkExtractBranch :
    Option
        (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
          Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) →
      OracleComp (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal))) Wit
  | none => liftComp (uniformSample Wit) (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))
  | some (x₁, x₂) =>
    let ⟨m₁, (c₁, s₁)⟩ := x₁.forgery
    let ⟨m₂, (c₂, s₂)⟩ := x₂.forgery
    if _hc : c₁ = c₂ then
      match x₁.roCache (m₁, c₁), x₂.roCache (m₂, c₂) with
      | some ω₁, some ω₂ =>
        if _hω : ω₁ ≠ ω₂ then
          liftComp (σ.extract ω₁ s₁ ω₂ s₂)
            (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))
        else liftComp (uniformSample Wit) (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))
      | _, _ =>
        liftComp (uniformSample Wit) (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))
    else liftComp (uniformSample Wit) (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))


-- @@ L164-173 expanded
/-- Witness-extraction computation used by the NMA reduction: replay the forking lemma, then
take the `nmaForkExtractBranch` continuation on the resulting trace pair. -/
private def nmaForkExtract
    (nmaAdv :
      SignatureAlg.managedRoNmaAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (qH : ℕ) (pk : Stmt) :
    OracleComp (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal))) Wit :=
  contextFork (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
      (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH) >>=
    nmaForkExtractBranch (M := M) (Chal := Chal) σ


-- @@ L175-182 expanded
/-- NMA reduction for `nma_to_hard_relation_bound`: simulate the challenge oracle of
`nmaForkExtract` down to `ProbComp`. -/
private def nmaReduction
    (nmaAdv :
      SignatureAlg.managedRoNmaAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (qH : ℕ) : Stmt → ProbComp Wit := fun pk =>
  simulateQ
    (QueryImpl.ofLift unifSpec ProbComp +
      (uniformSampleImpl (spec := (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))))
    (nmaForkExtract σ hr M nmaAdv qH pk)


-- @@ L184-212 expanded
omit [Fintype Stmt] [Fintype Commit] [Fintype Resp] [Fintype Chal] [Inhabited Stmt]
    [Inhabited Commit] [Inhabited Resp] [Inhabited Chal] [SampleableType Wit] in
/-- Every `(x, log)` in the support of `replayFirstRun (Fork.runTrace σ hr M nmaAdv pk)`
satisfies the per-run invariant `forkSupportInvariant`. -/
private theorem forkSupportInvariant_of_mem_replayFirstRun
    (nmaAdv :
      SignatureAlg.managedRoNmaAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (qH : ℕ) (pk : Stmt) {x : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)}
    {log : QueryLog (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))}
    (h : (x, log) ∈ support (replayFirstRun (Fork.runTrace σ hr M nmaAdv pk))) :
    forkSupportInvariant σ M qH pk x log := by
  classical
  intro s hs
  have htarget : x.queryLog[(↑s : ℕ)]? = some x.target :=
    Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)
      hs
  have hverified : x.verified = true :=
    Fork.verified_of_forkPoint_eq_some (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) hs
  obtain ⟨hslt, htgt_eq⟩ := List.getElem?_eq_some_iff.1 htarget
  obtain ⟨ω, hcache_idx, hlog⟩ :=
    Fork.runTrace_cache_outer_lockstep σ hr M nmaAdv pk h (↑s : ℕ) hslt
  rw [htgt_eq] at hcache_idx
  obtain ⟨ω', hcache', hverify⟩ :=
    Fork.exists_cached_verify_of_runTrace_verified σ hr M nmaAdv pk h hverified
  refine ⟨ω, hlog, hcache_idx, ?_⟩
  rwa [Option.some.inj (hcache'.symm.trans hcache_idx)] at hverify


-- @@ L214-295 expanded
omit [Fintype Stmt] [Fintype Commit] [Fintype Resp] [Inhabited Stmt] [Inhabited Commit]
    [Inhabited Resp] in
/-- Given the structural forking event on `pk`, the NMA reduction recovers a valid witness
with probability at least that of the fork event under `contextFork`. -/
private theorem perPk_extraction_bound
    (nmaAdv :
      SignatureAlg.managedRoNmaAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (qH : ℕ) (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, probFailure (σ.extract ω₁ p₁ ω₂ p₂) = 0) (pk : Stmt) :
    (probEvent
        (contextFork (Fork.runTrace σ hr M nmaAdv pk) (nmaForkBudget qH) (Sum.inr ())
          (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH))
        fun r :
          Option
            (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) ×
              Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) =>
        ∃ (x₁ x₂ : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) (s :
          Fin (qH + 1)) (log₁ log₂ :
          QueryLog (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))),
          r = some (x₁, x₂) ∧
            Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH x₁ =
                some s ∧
              Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH x₂ =
                  some s ∧
                QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
                    QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
                  forkSupportInvariant σ M qH pk x₁ log₁ ∧ forkSupportInvariant σ M qH pk x₂ log₂) ≤
      probEvent (nmaReduction σ hr M nmaAdv qH pk) fun w : Wit => rel pk w = true :=
  by
  classical
  let chalSpec : OracleSpec Unit := OracleSpec.ofFn (ι := Unit) (fun _ => Chal)
  let wrappedMain := Fork.runTrace σ hr M nmaAdv pk
  let cf := Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
  let qb : ℕ ⊕ Unit → ℕ := nmaForkBudget qH
  rw [show
      (probEvent (nmaReduction σ hr M nmaAdv qH pk) fun w : Wit => rel pk w = true) =
        probEvent (nmaForkExtract σ hr M nmaAdv qH pk) fun w : Wit => rel pk w = true
      by
      unfold nmaReduction
      exact probEvent_simulateQ_unifChalImpl _ _]
  set branchFn := nmaForkExtractBranch (M := M) (Chal := Chal) σ with hbranchFn_def
  have hforkExtract_eq :
    nmaForkExtract σ hr M nmaAdv qH pk = contextFork wrappedMain qb (Sum.inr ()) cf >>= branchFn :=
    rfl
  rw [hforkExtract_eq, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun r => ?_
  by_cases hE :
    ∃ (x₁ x₂ : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) (s :
      Fin (qH + 1)) (log₁ log₂ :
      QueryLog (unifSpec + (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))),
      r = some (x₁, x₂) ∧
        cf x₁ = some s ∧
          cf x₂ = some s ∧
            QueryLog.getQueryValue? log₁ (Sum.inr ()) ↑s ≠
                QueryLog.getQueryValue? log₂ (Sum.inr ()) ↑s ∧
              forkSupportInvariant σ M qH pk x₁ log₁ ∧ forkSupportInvariant σ M qH pk x₂ log₂
  swap
  · rw [if_neg hE]
    exact zero_le
  rw [if_pos hE]
  by_cases hsupp : r ∈ support (contextFork wrappedMain qb (Sum.inr ()) cf)
  swap
  · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]
  obtain ⟨x₁, x₂, s, log₁, log₂, hreq, hcf₁, hcf₂, hneq, hP₁, hP₂⟩ := hE
  obtain ⟨ω₁, hlog₁, hcache₁, hverify₁⟩ := hP₁ s hcf₁
  obtain ⟨ω₂, hlog₂, hcache₂, hverify₂⟩ := hP₂ s hcf₂
  simp only [Fork.Trace.target] at hcache₁ hcache₂ hverify₁ hverify₂
  have hω_ne : ω₁ ≠ ω₂ := fun heq =>
    hneq
      (by rw [hlog₁, hlog₂, heq])
        -- The two forgeries share a target hash point, so they share a commitment.
        
  have hc_eq : x₁.forgery.2.1 = x₂.forgery.2.1 :=
    congrArg Prod.snd <|
      Fork.runTrace_target_eq_of_mem_contextFork σ hr M nmaAdv qH pk x₁ x₂ s (hreq ▸ hsupp) hcf₁
        hcf₂
  have hbranch :
    branchFn r = liftComp (σ.extract ω₁ x₁.forgery.2.2 ω₂ x₂.forgery.2.2) (unifSpec + chalSpec) :=
    by
    rw [hbranchFn_def, hreq]
    simp only [chalSpec, nmaForkExtractBranch, hcache₁, hcache₂, dif_pos hc_eq, dif_pos hω_ne]
  rw [hbranch, probEvent_liftComp]
    -- The extractor returns a valid witness with probability one (special soundness).
    
  rw [show
      (probEvent (σ.extract ω₁ x₁.forgery.2.2 ω₂ x₂.forgery.2.2) fun w : Wit => rel pk w = true) = 1
      from
      probEvent_eq_one_iff.2
        ⟨hss_nf _ _ _ _, fun w hw =>
          SigmaProtocol.extract_sound_of_speciallySoundAt σ (hss pk) hω_ne hverify₁
            (hc_eq.symm ▸ hverify₂) hw⟩,
    mul_one]


-- @@ L297-297 verbatim
end nmaToExtraction


-- @@ L299-303 verbatim
/-- The challenge-space reciprocal `(Fintype.card Chal)⁻¹` is finite. -/
@[aesop (rule_sets := [finiteness]) safe apply]
lemma challengeSpaceInv_ne_top : challengeSpaceInv Chal ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top <|
    ENNReal.inv_le_one.2 (by exact_mod_cast Fintype.card_pos)


-- @@ L305-364 expanded
omit [Fintype Stmt] [Fintype Commit] [Fintype Resp] [Fintype Chal] [Inhabited Stmt]
    [Inhabited Commit] [Inhabited Resp] [Inhabited Chal] in
/-- NMA-to-extraction via the forking lemma and special soundness.

The parameter `qH` is the *fork slot parameter* passed to `Fork.forkPoint qH`,
i.e., the number of `Fin (qH + 1)` candidate target positions over which the
replay-forking lemma sums. It is *not* required to be a valid query bound on
the adversary: callers may supply a wrapped adversary with up to `qH + 1`
queries (the framework's structural `+1` in `Fin (qH + 1)` accommodates the
extra slot). -/
theorem nma_to_hard_relation_bound [DecidableEq M] [DecidableEq Commit] [SampleableType Wit]
    [SampleableType Chal] (hss : σ.SpeciallySound)
    (hss_nf : ∀ ω₁ p₁ ω₂ p₂, probFailure (σ.extract ω₁ p₁ ω₂ p₂) = 0) [Fintype Chal]
    [Inhabited Chal]
    (nmaAdv :
      SignatureAlg.managedRoNmaAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (qH : ℕ) :
    ∃ reduction : Stmt → ProbComp Wit,
      (Fork.advantage σ hr M nmaAdv qH *
          (Fork.advantage σ hr M nmaAdv qH / (qH + 1 : ENNReal) - challengeSpaceInv Chal)) ≤
        probOutput (hardRelationExp hr reduction) true :=
  by
  classical
  refine ⟨nmaReduction σ hr M nmaAdv qH, ?_⟩
  set acc : Stmt → ENNReal := fun pk =>
    probEvent (Fork.runTrace σ hr M nmaAdv pk) fun x =>
      (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH x).isSome with
    hacc_def
  have hAdv_eq_tsum :
    Fork.advantage σ hr M nmaAdv qH = ∑' pkw : Stmt × Wit, probOutput hr.gen pkw * acc pkw.1 := by
    simp only [Fork.advantage, Fork.exp, ← probEvent_eq_eq_probOutput,
      probEvent_simulateQ_unifChalImpl, probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map,
      Function.comp_def, probEvent_liftComp, acc]
  have hRHS_eq_tsum :
    probOutput (hardRelationExp hr (nmaReduction σ hr M nmaAdv qH)) true =
      ∑' pkw : Stmt × Wit,
        probOutput hr.gen pkw *
          probEvent (nmaReduction σ hr M nmaAdv qH pkw.1) fun w : Wit => rel pkw.1 w = true :=
    by
    simp only [hardRelationExp, ← probEvent_eq_eq_probOutput, bind_pure_comp,
      probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]
      -- The replay-forking bound feeds the per-`pk` witness-extraction bound.
      
  have hPerPkFinal :
    ∀ pk : Stmt,
      acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
        probEvent (nmaReduction σ hr M nmaAdv qH pk) fun w : Wit => rel pk w = true :=
    fun pk =>
    (Fork.replayForkingBound (σ := σ) (hr := hr) (M := M) nmaAdv qH pk (P_out :=
          forkSupportInvariant σ M qH pk) (hP := fun h =>
          forkSupportInvariant_of_mem_replayFirstRun σ hr M nmaAdv qH pk h) (hreach :=
          Fork.runTrace_forkPoint_CfReachable (σ := σ) (hr := hr) (M := M) nmaAdv qH pk)).trans
      (perPk_extraction_bound σ hr M nmaAdv qH hss hss_nf pk)
  rw [hAdv_eq_tsum, hRHS_eq_tsum]
  exact
    OracleComp.EvalDist.marginalized_jensen_forking_bound (mx := hr.gen) (acc := fun pkw =>
      acc pkw.1) (B := fun pkw =>
      probEvent (nmaReduction σ hr M nmaAdv qH pkw.1) fun w : Wit => rel pkw.1 w = true) (q :=
      (qH : ENNReal) + 1) (hinv := challengeSpaceInv Chal) (fun _ => probEvent_le_one)
      (fun pkw => hPerPkFinal pkw.1)


-- @@ L366-366 verbatim
end FiatShamir
