/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Hops
public import VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
public import VCVio.CryptoFoundations.FiatShamir.QueryBounds
public import VCVio.ProgramLogic.Relational.SimulateQ

import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Hops
import all VCVio.CryptoFoundations.FiatShamir.Sigma.CmaToNma
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
import all VCVio.CryptoFoundations.FiatShamir.QueryBounds
import all VCVio.ProgramLogic.Relational.SimulateQ


-- @@ L20-26 verbatim
/-!
# Native stateful Fiat-Shamir CMA-to-NMA chain

This file assembles the non-heap Fiat-Shamir EUF-CMA chain. The top-level
statement is factored so the H1/H2/H3 arithmetic is native immediately, while
the H5 replay-forking boundary can be ported as a focused lemma.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
universe u


-- @@ L32-32 verbatim
open ENNReal OracleSpec OracleComp ProbComp OracleComp.ProgramLogic.Relational


-- @@ L34-34 verbatim
namespace FiatShamir.Stateful


-- @@ L36-39 verbatim
/-! Tag the CMA-to-NMA simulator handler family from `Sigma/CmaToNma.lean`
into the local `fs_simp` simp set. These defs live upstream (not under
`Sigma/Stateful/`), so we attach the FS-stateful local attribute here rather
than at the definition sites. -/


-- @@ L41-47 verbatim
attribute [fs_simp]
  simulatedNmaFwd
  simulatedNmaUnifSim
  simulatedNmaRoSim
  simulatedNmaBaseSim
  simulatedNmaSigSim
  simulatedNmaImpl


-- @@ L49-49 verbatim
variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

-- @@ L50-50 verbatim
variable [SampleableType Stmt] [SampleableType Wit]

-- @@ L51-52 verbatim
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)


-- @@ L54-55 verbatim
variable [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
  [Finite Chal] [Inhabited Chal]


-- @@ L57-59 expanded
noncomputable local instance instIsUniformSpecChalSingleton [Fintype Chal] :
    IsUniformSpec ((OracleSpec.ofFn (ι := Unit) (fun _ => Chal)) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _


-- @@ L61-69 verbatim
private lemma simulateQ_id_add_uniform_query_inl
    {ι : Type*} (spec : OracleSpec ι) [∀ i, SampleableType (spec.Range i)]
    (n : unifSpec.Domain) :
    simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl (spec := spec))
        (liftM ((unifSpec + spec).query (Sum.inl n))) =
      liftM (unifSpec.query n) := by
  rw [simulateQ_spec_query]
  change (QueryImpl.id' unifSpec n) = _
  exact QueryImpl.id'_apply n


-- @@ L71-79 expanded
private lemma simulateQ_id_add_uniform_query_inr {ι : Type*} (spec : OracleSpec ι)
    [∀ i, SampleableType (spec.Range i)] (t : spec.Domain) :
    simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl (spec := spec))
        (liftM ((unifSpec + spec).query (Sum.inr t))) =
      uniformSample (spec.Range t) :=
  by
  rw [simulateQ_spec_query]
  change uniformSampleImpl (spec := spec) t = _
  exact uniformSampleImpl_apply t


-- @@ L81-81 verbatim
/-! ## CMA-to-NMA adversary -/


-- @@ L83-89 verbatim
/-- The CMA-to-NMA reduction at the managed random-oracle interface. -/
def nmaAdvFromCma
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    SignatureAlg.managedRoNmaAdv
      (SourceSigAlg (σ := σ) (hr := hr) (M := M)) :=
  FiatShamir.simulatedNmaAdv σ hr M simT adv


-- @@ L91-103 verbatim
omit [SampleableType Stmt] [SampleableType Wit] in
/-- Hash-query bound for `nmaAdvFromCma`. -/
theorem nmaAdvFromCma_nmaHashQueryBound
    [Finite Commit] [Finite Resp] [Inhabited Commit] [Inhabited Resp]
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ∀ pk, nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (nmaAdvFromCma σ hr M adv simT).main pk) qH := fun pk => by
  simpa [nmaHashQueryBound, nmaAdvFromCma] using
    FiatShamir.simulatedNmaAdv_hashQueryBound σ hr M simT adv qS qH hQ pk


-- @@ L105-128 expanded
/-- Wrapper around `nmaAdvFromCma` that issues one explicit live random-oracle
query for the forgery's hash point `(msg, commit)` after the source adversary
returns. The extra query makes the verification challenge part of the forkable
transcript: `Fork.runTrace` always sees `(msg, commit)` in the live `queryLog`,
so the replay-forking lemma can rewind at the verification position without any
auxiliary "fresh challenge accepts" assumption on the verifier.

The wrapped adversary issues `qH + 1` random-oracle queries (the source's `qH`
plus the appended verifier-point query). The H5 chain calls `Fork.advantage`
on this wrapper at slot parameter `qH`: `Fork.forkPoint qH` indexes
`Fin (qH + 1)`, which is exactly the right number of slots for `qH + 1`
queries (the framework's structural `+1` is precisely the wrapper's verifier
slot). The replay-forking denominator is therefore `qH + 1`, not `qH + 2`. -/
def nmaAdvFromCmaWithFinalQuery (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    SignatureAlg.managedRoNmaAdv (SourceSigAlg (σ := σ) (hr := hr) (M := M)) where
  main
    pk := do
    let result ← (nmaAdvFromCma σ hr M adv simT).main pk
    let _ ←
      (((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).query
            (.inr (result.1.1, result.1.2.1))) :
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))) Chal)
    pure result


-- @@ L130-130 verbatim
/-! ## Shifted CMA-to-NMA normal forms -/


-- @@ L132-148 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq Commit]
  [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- The stateful shifted form of `signedFreshAdv` splits at the
candidate/verifier boundary, preserving the `cmaToNma` signing log between the
two pieces. -/
theorem cmaToNma_shiftLeft_signedFreshAdv_eq_bind
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (cmaToNma M Commit Chal simT).shiftLeft ([] : List M)
        (signedFreshAdv σ hr M adv) =
      (simulateQ (cmaToNma M Commit Chal simT)
        (signedCandidateAdv σ hr M adv)).run ([] : List M) >>= fun (p, log') =>
          Prod.fst <$> (simulateQ (cmaToNma M Commit Chal simT)
            (verifyFreshComp (σ := σ) (hr := hr) (M := M)
              (Commit := Commit) (Chal := Chal) (Resp := Resp) p)).run log' := by
  simp [QueryImpl.Stateful.shiftLeft, QueryImpl.Stateful.run, signedFreshAdv,
    StateT.run'_eq, simulateQ_bind, StateT.run_bind, monad_norm]


-- @@ L150-150 verbatim
/-! ## H5 fork-side infrastructure -/


-- @@ L152-154 verbatim
private abbrev ForkBaseState (M Commit Chal : Type)
    [DecidableEq M] [DecidableEq Commit] :=
  (fsRoSpec M Commit Chal).QueryCache × Fork.SimState M Commit Chal


-- @@ L156-167 expanded
omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma mem_support_forkSim_pure_nested_iff {α : Type} (x : α)
    (cache : (fsRoSpec M Commit Chal).QueryCache) (liveSt : Fork.SimState M Commit Chal)
    (z : (α × (fsRoSpec M Commit Chal).QueryCache) × Fork.SimState M Commit Chal) :
    z ∈
        support
          ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
                ((pure x :
                      StateT (fsRoSpec M Commit Chal).QueryCache
                        (OracleComp
                          (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))))
                        α).run
                  cache)).run
            liveSt) ↔
      z = ((x, cache), liveSt) :=
  by rw [StateT.run_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff]


-- @@ L169-175 verbatim
@[fs_simp] private noncomputable def forkBaseImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal) (OracleComp (Fork.wrappedSpec Chal))) :=
  ((Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
    (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)).flattenStateT


-- @@ L177-186 verbatim
@[fs_simp] private def cmaOracleSignLogAux
    {S : Type}
    (t : (cmaOracleSpec M Commit Chal Resp).Domain)
    (_s : S)
    (_u : (cmaOracleSpec M Commit Chal Resp).Range t)
    (_s' : S) (signed : List M) :
    List M :=
  match t with
  | .inl _ => signed
  | .inr m => signed ++ [m]


-- @@ L188-197 verbatim
@[fs_simp] private noncomputable def forkLoggedImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal × List M)
        (OracleComp (Fork.wrappedSpec Chal))) :=
  QueryImpl.extendState
    (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))


-- @@ L199-201 verbatim
private abbrev SimLoggedState (M Commit Chal : Type)
    [DecidableEq M] [DecidableEq Commit] :=
  (fsRoSpec M Commit Chal).QueryCache × List M


-- @@ L203-214 expanded
@[fs_simp]
private noncomputable def simLoggedVerifyFreshComp
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) (pk : Stmt) (x : M × (Commit × Resp))
    (s : SimLoggedState M Commit Chal) : ProbComp Bool := do
  let msg := x.1
  let c := x.2.1
  let resp := x.2.2
  match s.1 (.inr (msg, c)) with
  | some ch =>
    pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)
  | none =>
    do
      let ch ← (uniformSample Chal : ProbComp Chal)
      pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)


-- @@ L216-219 expanded
@[fs_simp]
private noncomputable def fsUniformImpl : QueryImpl (fsRoSpec M Commit Chal) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))))


-- @@ L221-230 verbatim
@[fs_simp] private noncomputable def simulatedNmaLoggedProbImpl
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (SimLoggedState M Commit Chal) ProbComp) :=
  QueryImpl.extendState
    ((fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal)).mapStateTBase
      (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) simT pk))
    (cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp))


-- @@ L232-239 verbatim
@[fs_simp] private noncomputable def cmaSimLoggedImpl
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (List M × CmaState M Commit Chal Stmt Wit) ProbComp) :=
  ((cmaSim M Commit Chal hr simT).mapStateTBase
    (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt))).flattenStateT


-- @@ L241-254 verbatim
@[fs_simp] private noncomputable def cmaSimLoggedLeftImpl
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (List M × CmaState M Commit Chal Stmt Wit) ProbComp)
  | .inl (.inl n) =>
      cmaSimLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT (.unif n)
  | .inl (.inr mc) =>
      cmaSimLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT (.ro mc)
  | .inr m =>
      cmaSimLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT (.sign m)


-- @@ L256-259 verbatim
@[fs_simp] private def cmaSimLoggedProj
    (s : List M × CmaState M Commit Chal Stmt Wit) :
    SimLoggedState M Commit Chal :=
  ((s.2.1.2.1.inr : (fsRoSpec M Commit Chal).QueryCache), s.1)


-- @@ L261-264 verbatim
private def cmaSimFixedKeyInv
    (pk : Stmt) (sk : Wit)
    (s : List M × CmaState M Commit Chal Stmt Wit) : Prop :=
  s.2.1.2.2 = some (pk, sk)


-- @@ L266-268 verbatim
private def cmaSimFixedKeyInitialState
    (ps : Stmt × Wit) : List M × CmaState M Commit Chal Stmt Wit :=
  (([] : List M), ((([] : List M), (∅ : RoCache M Commit Chal), some ps), false))


-- @@ L270-295 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedImpl_liftAdv_run
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type} (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    (st : List M × CmaState M Commit Chal Stmt Wit) :
    (simulateQ (cmaSimLoggedImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
      hr simT)
      (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run st =
    (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
      hr simT) oa).run st := by
  simpa [cmaSimLoggedLeftImpl] using congrArg (fun x ↦ x.run st)
    (QueryImpl.simulateQ_liftM_eq_of_query
      (impl := cmaSimLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT)
      (impl₁ := cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT)
      (h := fun t ↦ by
        rcases t with ((n | mc) | m) <;>
          · change simulateQ _ (liftM ((cmaSpec M Commit Chal Resp Stmt).query _)) = _
            simp [cmaSimLoggedLeftImpl])
      (oa := oa))


-- @@ L297-322 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedImpl_liftAdv_run_expanded
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type} (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    (st : CmaState M Commit Chal Stmt Wit) :
    (simulateQ (cmaSim M Commit Chal hr simT)
      ((simulateQ (cmaSignLogImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
        (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α)).run
        ([] : List M))).run st =
    (fun z : α × (List M × CmaState M Commit Chal Stmt Wit) =>
      ((z.1, z.2.1), z.2.2)) <$>
    (simulateQ (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
      hr simT) oa).run (([] : List M), st) := by
  rw [← cmaSimLoggedImpl_liftAdv_run (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
    hr simT oa (([] : List M), st)]
  simpa [cmaSimLoggedImpl] using
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
      (outer := cmaSim M Commit Chal hr simT)
      (inner := cmaSignLogImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt))
      (oa := (liftM oa : OracleComp (cmaSpec M Commit Chal Resp Stmt) α))
      (s := ([] : List M)) (q := st)


-- @@ L324-353 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma nma_lift_unif_run
    (hr : GenerableRelation Stmt Wit rel)
    {α : Type} (oa : ProbComp α)
    (s : NmaState M Commit Chal Stmt Wit) :
    (simulateQ (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)
        (liftM oa : OracleComp (nmaSpec M Commit Chal Stmt) α)).run s =
      (fun a => (a, s)) <$> oa := by
  let impl₁ : QueryImpl unifSpec
      (StateT (NmaState M Commit Chal Stmt Wit) ProbComp) :=
    fun n => StateT.mk fun s => (fun a => (a, s)) <$> (unifSpec.query n)
  have himpl₁ : (simulateQ impl₁ oa).run s = (fun a => (a, s)) <$> oa := by
    induction oa using OracleComp.inductionOn generalizing s with
    | pure x =>
        simp [impl₁]
    | query_bind n k ih =>
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        simp only [monad_norm, StateT.run_mk, impl₁]
        refine bind_congr (m := ProbComp) fun u => ?_
        simpa only [impl₁, pure_bind, map_eq_bind_pure_comp, Function.comp_apply] using ih u s
  exact QueryImpl.simulateQ_liftM_eq_of_query
    (impl := nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)
    (impl₁ := impl₁)
    (h := fun n => by
      funext s'
      change ((nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr
        (.unif n)).run s') = (impl₁ n).run s'
      simp [impl₁, nma, nmaPublic])
    (oa := oa) ▸ himpl₁


-- @@ L355-373 verbatim
omit [Finite Chal] [Inhabited Chal] in
private lemma simulatedNmaUnifSim_fsUniform_run
    {α : Type} (oa : ProbComp α)
    (cache : (fsRoSpec M Commit Chal).QueryCache) :
    simulateQ (fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal))
        ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
          (Chal := Chal)) oa).run cache) =
      (fun a ↦ (a, cache)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x =>
      simp [fsUniformImpl]
  | query_bind n k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      simp only [fsUniformImpl, QueryImpl.ofLift_eq_id', simulatedNmaUnifSim,
        simulatedNmaFwd, QueryImpl.liftTarget_apply, add_apply_inl,
        HasQuery.toQueryImpl_apply, QueryImpl.toHasQuery_query, StateT.run_monadLift,
        monadLift_self, bind_pure_comp, simulateQ_map, bind_map_left, map_bind]
      exact bind_congr (m := ProbComp) fun u ↦ ih u cache


-- @@ L375-461 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimLoggedLeft_preserves_inv
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (sk : Wit) : ∀ t s,
    cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk s →
    ∀ z ∈ support (m := ProbComp)
      ((cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT t).run s),
      cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
        (Stmt := Stmt) (Wit := Wit) pk sk z.2 := by
    intro t s hs
    rcases s with ⟨signed, ⟨⟨log, cache, keypair⟩, bad⟩⟩
    simp only [cmaSimFixedKeyInv] at hs ⊢
    rcases t with ((n | mc) | m)
    · intro z hz
      obtain ⟨u, _hu, rfl⟩ := by
        simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
          QueryImpl.Stateful.linkWith] using hz
      exact hs
    · intro z hz
      cases hcache : cache mc with
      | some ch =>
          obtain ⟨rfl, rfl⟩ := by
            simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, hcache] using hz
          exact hs
      | none =>
          obtain ⟨ch, _hch, rfl⟩ := by
            simpa [fs_simp, cmaOracleSpec, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, hcache, uniformSampleImpl] using hz
          simpa [QueryCache.cacheQuery] using hs
    · subst keypair
      intro z hz
      have hz' := by
        simpa only [cmaOracleSpec, add_apply_inr, cmaSimLoggedLeftImpl, cmaSimLoggedImpl,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, cmaSim, cmaFrame, cmaOuterLens,
          Prod.mk.eta, cmaNmaLens, cmaSignLogImpl, bind_pure_comp, StateT.run_bind,
          StateT.run_get, StateT.run_monadLift, monadLift_self, StateT.run_map, StateT.run_set,
          map_pure, Functor.map_map, pure_bind, simulateQ_map, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.Stateful.linkWith,
          cmaToNma, cmaSignSim, liftComp_eq_liftM, PFunctor.Lens.State.mk_get, StateT.run_mk,
          simulateQ_bind, nma, nmaPublic, id_map, nmaProgram, map_bind,
          QueryImpl.Stateful.Frame.linkReshape, PFunctor.Lens.State.mk_put, support_bind,
          support_map, Set.mem_iUnion, Set.mem_image, Prod.exists, Bool.exists_bool, exists_prop]
          using hz
      rcases hz' with ⟨xCommit, xChal, xResp, xCache, xKeypair, hx⟩
      have state_eq (xBad : Bool)
          (hxmem : ((xCommit, xChal, xResp), xCache, xKeypair, xBad) ∈
            support ((simulateQ
              (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr)
              (liftM (simT pk))).run (cache, some (pk, sk), bad))) :
          (xCache, xKeypair, xBad) = (cache, some (pk, sk), bad) := by
        have hxmem' := hxmem
        rw [nma_lift_unif_run (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) hr (simT pk)
          (cache, some (pk, sk), bad), support_map] at hxmem'
        rcases hxmem' with ⟨x', _hx', hx'⟩
        exact congrArg Prod.snd hx'.symm
      rcases hx with ⟨hxmem, hnext⟩ | ⟨hxmem, hnext⟩
      · have hxinner := state_eq false hxmem
        have hxkey : xKeypair = some (pk, sk) :=
          congrArg (fun state => state.2.1) hxinner
        rcases hnext with ⟨u, nextCache, nextKeypair, hnext⟩
        rcases hnext with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
        all_goals
          cases htarget : xCache (m, xCommit)
          all_goals
            simp only [htarget, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
              Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, true_and] at hu
          all_goals exact hu.2.trans hxkey
      · have hxinner := state_eq true hxmem
        have hxkey : xKeypair = some (pk, sk) :=
          congrArg (fun state => state.2.1) hxinner
        rcases hnext with ⟨u, nextCache, nextKeypair, hnext⟩
        rcases hnext with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
        all_goals
          cases htarget : xCache (m, xCommit)
          all_goals
            simp only [htarget, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
              Bool.false_eq_true, and_false, and_true, true_and] at hu
          all_goals exact hu.2.trans hxkey

-- @@ L462-549 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma cmaSimLoggedLeft_project_step
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (sk : Wit) : ∀ t s,
    cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
      (Stmt := Stmt) (Wit := Wit) pk sk s →
    Prod.map id (cmaSimLoggedProj (M := M) (Commit := Commit)
        (Chal := Chal) (Stmt := Stmt) (Wit := Wit)) <$>
      (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT t).run s =
      (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk t).run
        (cmaSimLoggedProj (M := M) (Commit := Commit)
          (Chal := Chal) (Stmt := Stmt) (Wit := Wit) s) := by
    intro t s hs
    rcases s with ⟨signed, ⟨⟨log, cache, keypair⟩, bad⟩⟩
    simp only [cmaSimFixedKeyInv] at hs
    rcases t with ((n | mc) | m)
    · simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
        QueryImpl.Stateful.linkWith]
    · cases hcache : cache mc with
      | some ch =>
          simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
            QueryImpl.Stateful.linkWith, hcache]
      | none =>
          conv_lhs =>
            simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, QueryImpl.liftTarget_apply,
              QueryImpl.simulateQ_add_query_left, QueryImpl.simulateQ_add_query_right,
              QueryImpl.id'_apply, uniformSampleImpl, hcache]
          conv_rhs =>
            simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
              QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
              QueryImpl.Stateful.linkWith, QueryImpl.liftTarget_apply,
              QueryImpl.simulateQ_add_query_left, QueryImpl.simulateQ_add_query_right,
              QueryImpl.id'_apply, uniformSampleImpl, hcache]
    · subst keypair
      conv_lhs =>
        simp only [add_apply_inr, cmaSimLoggedLeftImpl, cmaSimLoggedImpl,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, cmaSim, cmaFrame,
          cmaOuterLens, Prod.mk.eta, cmaNmaLens, cmaSignLogImpl, bind_pure_comp,
          StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
          StateT.run_map, StateT.run_set, map_pure, Functor.map_map, pure_bind,
          simulateQ_map, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, QueryImpl.Stateful.linkWith, cmaToNma,
          cmaSignSim, liftComp_eq_liftM, PFunctor.Lens.State.mk_get,
          StateT.run_mk, simulateQ_bind, nma, nmaPublic, id_map, nmaProgram,
          map_bind, QueryImpl.Stateful.Frame.linkReshape,
          PFunctor.Lens.State.mk_put, Prod.map_apply, id_eq, cmaSimLoggedProj]
      conv_rhs =>
        simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, QueryImpl.Stateful.Frame.linkReshape,
          QueryImpl.Stateful.linkWith,
          StateT.run_bind, StateT.run_mk, StateT.run_map, StateT.run_monadLift,
          monadLift_self, simulateQ_bind, simulateQ_map, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map,
          bind_pure_comp, pure_bind, map_bind, Functor.map_map, Prod.map_apply,
          id_eq]
      let advCache : (fsRoSpec M Commit Chal).QueryCache := cache.inr
      have hright :
          simulateQ (fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal))
              ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
                (Chal := Chal)) (simT pk)).run advCache) =
            (fun a ↦ (a, advCache)) <$> simT pk :=
        simulatedNmaUnifSim_fsUniform_run (M := M)
          (Commit := Commit) (Chal := Chal) (oa := simT pk) (cache := advCache)
      rw [nma_lift_unif_run (M := M) (Commit := Commit)
        (Chal := Chal) (Stmt := Stmt) (Wit := Wit) hr (simT pk)
        (cache, some (pk, sk), bad)]
      simp only [monad_norm]
      conv_rhs =>
        lhs
        change simulateQ (fsUniformImpl (M := M) (Commit := Commit) (Chal := Chal))
          ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
            (Chal := Chal)) (simT pk)).run advCache)
        rw [hright]
      simp only [monad_norm]
      refine bind_congr (m := ProbComp) fun x => ?_
      cases htarget : cache (m, x.1) with
      | some old =>
          simp [advCache, htarget]
      | none =>
          simp [advCache, htarget]


-- @@ L551-569 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private def cmaSimLoggedLeftOrnament
    (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (sk : Wit) :
    QueryImpl.StateOrnament
      (cmaSimLoggedLeftImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit)
        hr simT)
      (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) where
  inv := cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal)
    (Stmt := Stmt) (Wit := Wit) pk sk
  proj := cmaSimLoggedProj (M := M) (Commit := Commit)
    (Chal := Chal) (Stmt := Stmt) (Wit := Wit)
  preserves_inv := cmaSimLoggedLeft_preserves_inv (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT pk sk
  project_step := cmaSimLoggedLeft_project_step (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) hr simT pk sk


-- @@ L571-591 expanded
omit [DecidableEq M] [DecidableEq Commit] [SampleableType Stmt] [SampleableType Wit]
    [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma cmaToNma_lift_ro_query_run (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (mc : M × Commit) (log : OuterState M) :
    (simulateQ (cmaToNma M Commit Chal simT)
            (liftM
                (liftM
                    (((OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).query mc) :
                      OracleQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) Chal) :
                  OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))
                    Chal) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run
        log =
      (fun ch => (ch, log)) <$>
        (((nmaSpec M Commit Chal Stmt).query (.ro mc)) :
          OracleComp (nmaSpec M Commit Chal Stmt) Chal) :=
  by
  change
    (simulateQ (cmaToNma M Commit Chal simT)
            (((cmaSpec M Commit Chal Resp Stmt).query (.ro mc)) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run
        log =
      (fun ch => (ch, log)) <$>
        (((nmaSpec M Commit Chal Stmt).query (.ro mc)) :
          OracleComp (nmaSpec M Commit Chal Stmt) Chal)
  simp [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, cmaToNma, StateT.run_mk,
    map_eq_bind_pure_comp]


-- @@ L593-629 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSim_lift_ro_query_run (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (mc : M × Commit)
    (s : CmaState M Commit Chal Stmt Wit) :
    (simulateQ (cmaSim M Commit Chal hr simT)
            (liftM
                (liftM
                    (((OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).query mc) :
                      OracleQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) Chal) :
                  OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))
                    Chal) :
              OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run
        s =
      match s.1.2.1 mc with
      | some ch => pure (ch, s)
      | none =>
        (fun ch => (ch, ((s.1.1, s.1.2.1.cacheQuery mc ch, s.1.2.2), s.2))) <$>
          (uniformSample Chal) :=
  by
  rcases s with ⟨⟨log, cache, keypair⟩, bad⟩
  unfold cmaSim
  rw [QueryImpl.Stateful.simulateQ_linkWith_run]
  change
    (cmaFrame M Commit Chal Stmt Wit).linkReshape ((log, cache, keypair), bad) <$>
        (simulateQ (nma M Commit Chal hr)
              ((simulateQ (cmaToNma M Commit Chal simT)
                    (liftM
                        (liftM
                            (((OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).query mc) :
                              OracleQuery (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))
                                Chal) :
                          OracleComp
                            (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))) Chal) :
                      OracleComp (cmaSpec M Commit Chal Resp Stmt) Chal)).run
                log)).run
          (cache, keypair, bad) =
      match cache mc with
      | some ch => pure (ch, (log, cache, keypair), bad)
      | none =>
        (fun ch => (ch, (log, cache.cacheQuery mc ch, keypair), bad)) <$> (uniformSample Chal)
  rw [cmaToNma_lift_ro_query_run (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt :=
      Stmt) simT mc log]
  cases hcache : cache mc with
  | none
  | some ch =>
    simp [nma, nmaPublic, cmaFrame, cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape,
      hcache, QueryCache.cacheQuery, monad_norm]


-- @@ L631-663 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma cmaSimVerifyFreshComp_project [Finite Chal] (hr : GenerableRelation Stmt Wit rel)
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) (x : M × (Commit × Resp))
    (st : List M × CmaState M Commit Chal Stmt Wit) :
    (fun a => !decide (x.1 ∈ st.1) && a.1) <$>
        (simulateQ (cmaSim M Commit Chal hr simT)
              (liftM
                  (((FiatShamir σ hr M).verify pk x.1 x.2) :
                    OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))
                      Bool) :
                OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool)).run
          st.2 =
      simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk x
        (cmaSimLoggedProj (M := M) (Commit := Commit) (Chal := Chal) (Stmt := Stmt) (Wit := Wit)
          st) :=
  by
  let : Fintype Chal := Fintype.ofFinite Chal
  rcases x with ⟨msg, c, resp⟩
  rcases st with ⟨signed, ⟨⟨log, cache, keypair⟩, bad⟩⟩
  cases hcache : cache (msg, c) with
  | some ch =>
    change Chal at ch
    simp [simLoggedVerifyFreshComp, cmaSimLoggedProj, _root_.FiatShamir, hcache,
      cmaSim_lift_ro_query_run (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt :=
          Stmt) (Wit := Wit) hr simT (msg, c) ((log, cache, keypair), bad)]
    congr 1
  |
    none =>
    simp [simLoggedVerifyFreshComp, cmaSimLoggedProj, _root_.FiatShamir, hcache,
      cmaSim_lift_ro_query_run (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt :=
          Stmt) (Wit := Wit) hr simT (msg, c) ((log, cache, keypair), bad)]
    congr 1


-- @@ L665-667 verbatim
private def forkFreshCacheInv (s : ForkBaseState M Commit Chal × List M) : Prop :=
  ∀ (mc : M × Commit) (ch : Chal),
    s.1.1 (.inr mc) = some ch → mc.1 ∉ s.2 → s.1.2.1 mc = some ch


-- @@ L669-670 verbatim
private def forkLiveCacheLogInv (s : ForkBaseState M Commit Chal × List M) : Prop :=
  ∀ (mc : M × Commit) (ch : Chal), s.1.2.1 mc = some ch → mc ∈ s.1.2.2


-- @@ L672-673 verbatim
private def forkLiveCacheAdvCacheInv (s : ForkBaseState M Commit Chal × List M) : Prop :=
  ∀ (mc : M × Commit) (ch : Chal), s.1.2.1 mc = some ch → s.1.1 (.inr mc) = some ch


-- @@ L675-677 verbatim
private def forkAwareInv (s : ForkBaseState M Commit Chal × List M) : Prop :=
  forkFreshCacheInv (M := M) (Commit := Commit) (Chal := Chal) s ∧
    forkLiveCacheLogInv (M := M) (Commit := Commit) (Chal := Chal) s


-- @@ L679-681 verbatim
@[fs_simp] private def forkLoggedProj (s : ForkBaseState M Commit Chal × List M) :
    SimLoggedState M Commit Chal :=
  (s.1.1, s.2)


-- @@ L683-688 expanded
private def forkInitialState (M Commit Chal : Type) [DecidableEq M] [DecidableEq Commit] :
    ForkBaseState M Commit Chal × List M :=
  (((∅ : (fsRoSpec M Commit Chal).QueryCache),
      ((∅ : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache),
        ([] : List (M × Commit)))),
    ([] : List M))


-- @@ L690-694 expanded
private def forkInitialBaseState (M Commit Chal : Type) [DecidableEq M] [DecidableEq Commit] :
    ForkBaseState M Commit Chal :=
  ((∅ : (fsRoSpec M Commit Chal).QueryCache),
    ((∅ : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache),
      ([] : List (M × Commit))))


-- @@ L696-700 verbatim
omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma forkInitialState_inv :
    forkAwareInv (M := M) (Commit := Commit) (Chal := Chal)
      (forkInitialState M Commit Chal) := by
  constructor <;> intro mc ch hcache <;> simp [forkInitialState] at hcache


-- @@ L702-727 verbatim
omit [SampleableType Chal] in
private lemma simulatedNmaUnifFork_flatten_preserves_state
    {α : Type} (A : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.SimState M Commit Chal)
    {z : α × ((fsRoSpec M Commit Chal).QueryCache × Fork.SimState M Commit Chal)}
    (hz : z ∈ support
      ((simulateQ
        ((Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
          (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))).flattenStateT
        A).run (advCache, liveSt))) :
    z.2 = (advCache, liveSt) := by
  let : Fintype Chal := Fintype.ofFinite Chal
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := ((Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
      (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))).flattenStateT)
    (inv := fun st => st = (advCache, liveSt))
    (hinv := by
      intro t st hst y hy
      subst hst
      have hy' := by
        simpa [QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          simulatedNmaUnifSim, simulatedNmaFwd, Fork.unifForward] using hy
      rcases hy' with ⟨u, _hu, b, hb, rfl⟩
      rfl)
    A (advCache, liveSt) rfl z hz


-- @@ L729-751 verbatim
omit [SampleableType Chal] in
private lemma simulatedNmaUnifFork_nested_preserves_state
    {α : Type} (A : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.SimState M Commit Chal)
    {z : (α × (fsRoSpec M Commit Chal).QueryCache) × Fork.SimState M Commit Chal}
    (hz : z ∈ support
      ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
        ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
          (Chal := Chal)) A).run advCache)).run liveSt)) :
    z.1.2 = advCache ∧ z.2 = liveSt := by
  let : Fintype Chal := Fintype.ofFinite Chal
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (outer := Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
    (inner := simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))
    (oa := A) (s := advCache) (q := liveSt), support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hstate := simulatedNmaUnifFork_flatten_preserves_state
    (M := M) (Commit := Commit) (Chal := Chal) A advCache liveSt hy
  rcases y with ⟨a, st⟩
  simp only at hstate
  subst st
  simp


-- @@ L753-787 expanded
omit [SampleableType Stmt] [Inhabited Chal] in
private lemma forkLoggedImpl_sign_support (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) (m : M) (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveCache : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache)
    (queryLog : List (M × Commit)) (signed : List M)
    {z : (Commit × Resp) × (ForkBaseState M Commit Chal × List M)}
    (hz :
      z ∈
        support
          ((forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk
                (.inr m)).run
            ((advCache, liveCache, queryLog), signed))) :
    ∃ xCommit xChal xResp xAdvCache xLiveCache xQueryLog,
      ((((xCommit, xChal, xResp), xAdvCache), (xLiveCache, xQueryLog)) ∈
          support
            ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
                  ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))
                        (simT pk)).run
                    advCache)).run
              (liveCache, queryLog))) ∧
        ((match xAdvCache (.inr (m, xCommit)) with
              | some _ => ((xCommit, xResp), xAdvCache)
              | none => ((xCommit, xResp), xAdvCache.cacheQuery (.inr (m, xCommit)) xChal)).1,
            ((match xAdvCache (.inr (m, xCommit)) with
                | some _ => ((xCommit, xResp), xAdvCache)
                | none => ((xCommit, xResp), xAdvCache.cacheQuery (.inr (m, xCommit)) xChal)).2,
              xLiveCache, xQueryLog),
            signed ++ [m]) =
          z :=
  by
  have hz' := by
    simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT, QueryImpl.mapStateTBase] using
      hz
  rcases hz' with ⟨xCommit, xChal, xResp, xAdvCache, xLiveCache, xQueryLog, hxmem, hout⟩
  refine ⟨xCommit, xChal, xResp, xAdvCache, xLiveCache, xQueryLog, hxmem, ?_⟩
  convert hout using 1
  congr 4
  all_goals cases xAdvCache (.inr (m, xCommit)) <;> rfl


-- @@ L789-971 verbatim
omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_inv_step
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    ∀ (t : (cmaOracleSpec M Commit Chal Resp).Domain)
      (s : ForkBaseState M Commit Chal × List M),
      forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) s →
      ∀ z ∈ support ((forkLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk t).run s),
        forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  intro t s hs z hz
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  rcases hs with ⟨hfreshInv, hlogInv⟩
  rcases t with ((n | mc) | m)
  · have hz' := by
      simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase] using hz
    rcases hz' with ⟨w, hw, rfl⟩
    exact And.intro hfreshInv hlogInv
  · by_cases hadv : advCache (.inr mc) = none
    · have hz' := by
        simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, hadv] using hz
      rcases hz' with ⟨ch, liveCache', queryLog', hw, rfl⟩
      by_cases hlive : liveCache mc = none
      · have hw' := hw
        rw [Fork.roImpl_run_none (M := M) (Commit := Commit) (Chal := Chal)
          mc liveCache queryLog hlive,
          ← Fork.simulateQ_unifForward_add_roImpl_query_inr_run_none
            (M := M) (Commit := Commit) (Chal := Chal)
            mc liveCache queryLog hlive] at hw'
        obtain ⟨v, heq⟩ :=
          (Fork.mem_support_simulateQ_unifForward_add_roImpl_query_inr_run_none_iff
          (M := M) (Commit := Commit) (Chal := Chal)
          mc liveCache queryLog hlive (ch, (liveCache', queryLog'))).mp hw'
        change Chal at v
        have hch : ch = v := congrArg Prod.fst heq
        have hst : (liveCache', queryLog') =
            (liveCache.cacheQuery mc v, queryLog ++ [mc]) :=
          congrArg Prod.snd heq
        have hliveCache' : liveCache' = liveCache.cacheQuery mc v :=
          congrArg Prod.fst hst
        have hqueryLog' : queryLog' = queryLog ++ [mc] :=
          congrArg Prod.snd hst
        subst ch
        subst liveCache'
        subst queryLog'
        constructor
        · intro mc' ch' hcache hfresh
          by_cases hmc : mc' = mc
          · subst mc'
            have hself := QueryCache.cacheQuery_self
              (cache := advCache) (Sum.inr mc) v
            have hv : v = ch' := Option.some.inj (hself.symm.trans hcache)
            have hlive_self := QueryCache.cacheQuery_self
              (cache := liveCache) mc v
            exact hlive_self.trans (congrArg some hv)
          · have hcache_old : advCache (.inr mc') = some ch' := by
              have hne : (Sum.inr mc' : (fsRoSpec M Commit Chal).Domain) ≠
                  Sum.inr mc := fun heq => hmc (Sum.inr.inj heq)
              have hne_cache := QueryCache.cacheQuery_of_ne
                (cache := advCache) (t := Sum.inr mc) (t' := Sum.inr mc') v hne
              exact hne_cache.symm.trans hcache
            have hlive_old := hfreshInv mc' ch' hcache_old hfresh
            have hne_cache := QueryCache.cacheQuery_of_ne
              (cache := liveCache) (t := mc) (t' := mc') v hmc
            exact hne_cache.trans hlive_old
        · intro mc' ch' hcache
          by_cases hmc : mc' = mc
          · subst mc'
            simp
          · have hcache_old : liveCache mc' = some ch' := by
              simpa [QueryCache.cacheQuery_of_ne, hmc] using hcache
            exact List.mem_append_left [mc] (hlogInv mc' ch' hcache_old)
      · rcases hlive' : liveCache mc with _ | liveCh
        · exact (hlive hlive').elim
        · have heq := by
            have hw' := hw
            rw [Fork.roImpl_run_some (M := M) (Commit := Commit) (Chal := Chal)
              mc liveCache queryLog liveCh hlive',
              ← Fork.simulateQ_unifForward_add_roImpl_query_inr_run_some
                (M := M) (Commit := Commit) (Chal := Chal)
                mc liveCache queryLog liveCh hlive'] at hw'
            exact
              (Fork.mem_support_simulateQ_unifForward_add_roImpl_query_inr_run_some_iff
                (M := M) (Commit := Commit) (Chal := Chal)
                mc liveCache queryLog liveCh hlive' (ch, (liveCache', queryLog'))).mp hw'
          have hch : ch = liveCh := congrArg Prod.fst heq
          have hst : (liveCache', queryLog') = (liveCache, queryLog) :=
            congrArg Prod.snd heq
          have hliveCache' : liveCache' = liveCache := congrArg Prod.fst hst
          have hqueryLog' : queryLog' = queryLog := congrArg Prod.snd hst
          subst ch
          subst liveCache'
          subst queryLog'
          constructor
          · intro mc' ch' hcache hfresh
            by_cases hmc : mc' = mc
            · subst mc'
              have hself := QueryCache.cacheQuery_self
                (cache := advCache) (Sum.inr mc) liveCh
              have hv : liveCh = ch' :=
                Option.some.inj (hself.symm.trans hcache)
              exact hlive'.trans (congrArg some hv)
            · exact hfreshInv mc' ch'
                (by
                  have hne : (Sum.inr mc' : (fsRoSpec M Commit Chal).Domain) ≠
                      Sum.inr mc := fun heq => hmc (Sum.inr.inj heq)
                  have hne_cache := QueryCache.cacheQuery_of_ne
                    (cache := advCache) (t := Sum.inr mc)
                    (t' := Sum.inr mc') liveCh hne
                  exact hne_cache.symm.trans hcache)
                hfresh
          · intro mc' ch' hcache
            exact hlogInv mc' ch' hcache
    · rcases hadv' : advCache (.inr mc) with _ | advCh
      · exact (hadv hadv').elim
      · have hz' := by
          simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, hadv'] using hz
        rcases hz' with ⟨w, hw, rfl⟩
        constructor
        · intro mc' ch' hcache' hfresh
          exact hfreshInv mc' ch' hcache' hfresh
        · intro mc' ch' hcache'
          exact hlogInv mc' ch' hcache'
  · have hz' := by
      exact forkLoggedImpl_sign_support (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk m advCache liveCache queryLog signed hz
    rcases hz' with ⟨xCommit, xChal, xResp, xAdvCache, xLiveCache,
      xQueryLog, hxmem, rfl⟩
    let x := (((xCommit, xChal, xResp), xAdvCache), (xLiveCache, xQueryLog))
    have _hx : x ∈ support
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
          ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
            (Chal := Chal)) (simT pk)).run advCache)).run (liveCache, queryLog)) := by
      simpa [x] using hxmem
    have hxstate := simulatedNmaUnifFork_nested_preserves_state
      (M := M) (Commit := Commit) (Chal := Chal) (simT pk) advCache
      (liveCache, queryLog) _hx
    rcases hxstate with ⟨hxadv, hxlive⟩
    have hxAdvCache : xAdvCache = advCache := by simpa [x] using hxadv
    have hxLiveState : (xLiveCache, xQueryLog) = (liveCache, queryLog) := by
      simpa [x] using hxlive
    have hxLiveCache : xLiveCache = liveCache := congrArg Prod.fst hxLiveState
    have hxQueryLog : xQueryLog = queryLog := congrArg Prod.snd hxLiveState
    subst xAdvCache
    subst xLiveCache
    subst xQueryLog
    constructor
    · intro mc ch hcache' hfresh
      by_cases hmc : mc = (m, x.1.1.1)
      · subst mc
        simp at hfresh
      · have hcache_old : advCache (.inr mc) = some ch := by
          have hsum :
              (Sum.inr mc : (fsRoSpec M Commit Chal).Domain) ≠
                Sum.inr (m, x.1.1.1) := by
            intro hsum
            exact hmc (by simpa using Sum.inr.inj hsum)
          cases htarget : advCache (Sum.inr (m, x.1.1.1)) with
          | none =>
              have hcache_update :
                  advCache.cacheQuery (Sum.inr (m, x.1.1.1)) x.1.1.2.1
                    (Sum.inr mc) = some ch := by
                simpa only [x, hxadv, htarget] using hcache'
              have hne_cache := QueryCache.cacheQuery_of_ne
                (cache := advCache) (t := Sum.inr (m, x.1.1.1))
                (t' := Sum.inr mc) x.1.1.2.1 hsum
              exact hne_cache.symm.trans hcache_update
          | some old =>
              simpa only [x, hxadv, htarget] using hcache'
        have hfresh_old : mc.1 ∉ signed := by
          intro hmem
          exact hfresh (by simp [hmem])
        have hlive_old := hfreshInv mc ch hcache_old hfresh_old
        simpa [hxlive] using hlive_old
    · intro mc ch hcache'
      have hcache_old : liveCache mc = some ch := by
        have hproj := congrArg (fun st => st.1 mc) hxlive
        exact hproj.symm.trans hcache'
      have hmem := hlogInv mc ch hcache_old
      have hlogeq := congrArg Prod.snd hxlive
      exact hlogeq.symm ▸ hmem


-- @@ L973-990 verbatim
omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_inv
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {α : Type} (A : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    {z : α × (ForkBaseState M Commit Chal × List M)}
    (hz : z ∈ support ((simulateQ (forkLoggedImpl (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) A).run
      (forkInitialState M Commit Chal))) :
    forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  let : Fintype Chal := Fintype.ofFinite Chal
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (inv := forkAwareInv (M := M) (Commit := Commit) (Chal := Chal))
    (hinv := forkLoggedImpl_preserves_inv_step (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) simT pk)
    A (forkInitialState M Commit Chal)
    (forkInitialState_inv (M := M) (Commit := Commit) (Chal := Chal)) z hz


-- @@ L992-1117 verbatim
omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_live_adv_inv_step
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    ∀ (t : (cmaOracleSpec M Commit Chal Resp).Domain)
      (s : ForkBaseState M Commit Chal × List M),
      forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) s →
      ∀ z ∈ support ((forkLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk t).run s),
        forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  let : Fintype Chal := Fintype.ofFinite Chal
  intro t s hs z hz
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  rcases t with ((n | mc) | m)
  · have hz' := by
      simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase] using hz
    rcases hz' with ⟨w, hw, rfl⟩
    exact hs
  · cases hadv : advCache (.inr mc) with
    | some ch =>
        have hz' := by
          simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, hadv] using hz
        rcases hz' with ⟨w, hw, rfl⟩
        simpa using hs
    | none =>
        cases hlive : liveCache mc with
        | some liveCh =>
            have hcontra : advCache (.inr mc) = some liveCh := hs mc liveCh hlive
            rw [hadv] at hcontra
            cases hcontra
        | none =>
            have hz' := by
              simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT,
                QueryImpl.mapStateTBase, hadv] using hz
            rcases hz' with ⟨ch, liveCache', queryLog', hw, rfl⟩
            have hw' := hw
            rw [Fork.roImpl_run_none (M := M) (Commit := Commit) (Chal := Chal)
              mc liveCache queryLog hlive,
              ← Fork.simulateQ_unifForward_add_roImpl_query_inr_run_none
                (M := M) (Commit := Commit) (Chal := Chal)
                mc liveCache queryLog hlive] at hw'
            obtain ⟨v, heq⟩ :=
              (Fork.mem_support_simulateQ_unifForward_add_roImpl_query_inr_run_none_iff
              (M := M) (Commit := Commit) (Chal := Chal)
              mc liveCache queryLog hlive (ch, (liveCache', queryLog'))).mp hw'
            change Chal at v
            have hch : ch = v := congrArg Prod.fst heq
            have hst : (liveCache', queryLog') =
                (liveCache.cacheQuery mc v, queryLog ++ [mc]) :=
              congrArg Prod.snd heq
            have hliveCache' : liveCache' = liveCache.cacheQuery mc v :=
              congrArg Prod.fst hst
            have hqueryLog' : queryLog' = queryLog ++ [mc] :=
              congrArg Prod.snd hst
            subst ch
            subst liveCache'
            subst queryLog'
            intro mc' ch' hcache'
            by_cases hmc : mc' = mc
            · subst mc'
              have hlive_self := QueryCache.cacheQuery_self
                (cache := liveCache) mc v
              have hv : v = ch' :=
                Option.some.inj (hlive_self.symm.trans hcache')
              have hadv_self := QueryCache.cacheQuery_self
                (cache := advCache) (Sum.inr mc) v
              exact hadv_self.trans (congrArg some hv)
            · have hlive_old : liveCache mc' = some ch' := by
                have hne_cache := QueryCache.cacheQuery_of_ne
                  (cache := liveCache) (t := mc) (t' := mc') v hmc
                exact hne_cache.symm.trans hcache'
              have hadv_old := hs mc' ch' hlive_old
              have hne : (Sum.inr mc' : (fsRoSpec M Commit Chal).Domain) ≠
                  Sum.inr mc := fun heq => hmc (Sum.inr.inj heq)
              have hne_cache := QueryCache.cacheQuery_of_ne
                (cache := advCache) (t := Sum.inr mc)
                (t' := Sum.inr mc') v hne
              exact hne_cache.trans hadv_old
  · have hz' := by
      exact forkLoggedImpl_sign_support (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk m advCache liveCache queryLog signed hz
    rcases hz' with ⟨xCommit, xChal, xResp, xAdvCache, xLiveCache,
      xQueryLog, hxmem, rfl⟩
    let x := (((xCommit, xChal, xResp), xAdvCache), (xLiveCache, xQueryLog))
    have _hx : x ∈ support
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
          ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
            (Chal := Chal)) (simT pk)).run advCache)).run (liveCache, queryLog)) := by
      simpa [x] using hxmem
    obtain ⟨hxadv, hxlive⟩ := simulatedNmaUnifFork_nested_preserves_state
      (M := M) (Commit := Commit) (Chal := Chal) (simT pk) advCache
      (liveCache, queryLog) _hx
    have hxAdvCache : xAdvCache = advCache := by simpa [x] using hxadv
    have hxLiveState : (xLiveCache, xQueryLog) = (liveCache, queryLog) := by
      simpa [x] using hxlive
    have hxLiveCache : xLiveCache = liveCache := congrArg Prod.fst hxLiveState
    have hxQueryLog : xQueryLog = queryLog := congrArg Prod.snd hxLiveState
    subst xAdvCache
    subst xLiveCache
    subst xQueryLog
    intro mc ch hcache'
    have hadv_old' : advCache (.inr mc) = some ch := by
      simpa using hs mc ch (by simpa [hxlive] using hcache')
    by_cases hmc : mc = (m, x.1.1.1)
    · subst mc
      cases htarget : advCache (.inr (m, x.1.1.1)) with
      | none =>
          rw [hadv_old'] at htarget
          cases htarget
      | some old =>
          simpa [hxadv, htarget] using hadv_old'
    · have hsum :
          (Sum.inr mc : (fsRoSpec M Commit Chal).Domain) ≠
            Sum.inr (m, x.1.1.1) := by
        intro hsum
        exact hmc (by simpa using Sum.inr.inj hsum)
      cases htarget : advCache (.inr (m, x.1.1.1)) with
      | none =>
          have hne_cache := QueryCache.cacheQuery_of_ne
            (cache := advCache) (t := Sum.inr (m, x.1.1.1))
            (t' := Sum.inr mc) x.1.1.2.1 hsum
          have hupdated := hne_cache.trans hadv_old'
          simpa only [hxadv, htarget] using hupdated
      | some old =>
          simpa [hxadv, htarget] using hadv_old'


-- @@ L1119-1139 verbatim
omit [SampleableType Stmt] in
private lemma forkLoggedImpl_preserves_live_adv_inv
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {α : Type} (A : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    {z : α × (ForkBaseState M Commit Chal × List M)}
    (hz : z ∈ support ((simulateQ (forkLoggedImpl (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) A).run
      (forkInitialState M Commit Chal))) :
    forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) z.2 := by
  let : Fintype Chal := Fintype.ofFinite Chal
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (impl := forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)
    (inv := forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal))
    (hinv := forkLoggedImpl_preserves_live_adv_inv_step (M := M)
      (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
    A (forkInitialState M Commit Chal)
    (by
      intro mc ch hcache
      simp [forkInitialState] at hcache)
    z hz


-- @@ L1141-1148 verbatim
omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
private lemma forkPoint_isSome_of_mem_verified_findIdx_le {qH : ℕ}
    (trace : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (hverified : trace.verified = true) (hmem : trace.target ∈ trace.queryLog)
    (hidx : trace.queryLog.findIdx (· == trace.target) ≤ qH) :
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH trace).isSome = true := by
  simp [Fork.forkPoint, hverified, hmem, hidx]


-- @@ L1150-1161 verbatim
omit [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- Convenience corollary: if the queryLog itself fits within `qH`, then the
target's `findIdx` is automatically `≤ qH` and `forkPoint qH trace` is some. -/
private lemma forkPoint_isSome_of_mem_verified_length {qH : ℕ}
    (trace : Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal))
    (hverified : trace.verified = true) (hmem : trace.target ∈ trace.queryLog)
    (hlen : trace.queryLog.length ≤ qH) :
    (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp)
      (Chal := Chal) qH trace).isSome = true := by
  refine forkPoint_isSome_of_mem_verified_findIdx_le (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) trace hverified hmem ?_
  exact (List.findIdx_lt_length_of_exists ⟨trace.target, hmem, by simp⟩).le.trans hlen


-- @@ L1163-1166 expanded
@[fs_simp]
private noncomputable def forkWrappedUniformImpl [Fintype Chal] :
    QueryImpl (Fork.wrappedSpec Chal) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (uniformSampleImpl (spec := (OracleSpec.ofFn (ι := Unit) (fun _ => Chal))))


-- @@ L1168-1181 verbatim
@[fs_simp] private noncomputable def forkVerifyFreshComp
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (x : M × (Commit × Resp))
    (s : ForkBaseState M Commit Chal × List M) :
    OracleComp (Fork.wrappedSpec Chal) Bool := do
  let msg := x.1
  let c := x.2.1
  let resp := x.2.2
  match s.1.1 (.inr (msg, c)) with
  | some ch => pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)
  | none => do
      let ch ← (((Fork.wrappedSpec Chal).query (Sum.inr ())) :
        OracleComp (Fork.wrappedSpec Chal) Chal)
      pure (!decide (msg ∈ s.2) && σ.verify pk c ch resp)


-- @@ L1183-1207 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
private lemma forkVerifyFreshComp_project [Fintype Chal] (pk : Stmt) (x : M × (Commit × Resp))
    (s : ForkBaseState M Commit Chal × List M) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk x s) =
      simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk x
        (forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal) s) :=
  by
  rcases x with ⟨msg, c, resp⟩
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  cases hcache : advCache (.inr (msg, c)) with
  | some ch =>
    change Chal at ch
    simp [forkVerifyFreshComp, simLoggedVerifyFreshComp, forkLoggedProj, forkWrappedUniformImpl,
      hcache]
    congr 1
  |
    none =>
    simp only [forkWrappedUniformImpl, QueryImpl.ofLift_eq_id', forkVerifyFreshComp, hcache,
      add_apply_inr, bind_pure_comp, simulateQ_map, simLoggedVerifyFreshComp, forkLoggedProj]
    congr 1
    exact simulateQ_id_add_uniform_query_inr (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)) ()


-- @@ L1209-1224 verbatim
private noncomputable def forkFinalQueryTrace
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (pk : Stmt) (x : M × (Commit × Resp))
    (s : ForkBaseState M Commit Chal × List M) :
    OracleComp (Fork.wrappedSpec Chal)
      (Fork.Trace (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal)) := do
  let y ← (Fork.roImpl M Commit Chal (x.1, x.2.1)).run s.1.2
  let ch := y.1
  let liveSt := y.2
  pure {
    forgery := x
    advCache := s.1.1
    roCache := liveSt.1
    queryLog := liveSt.2
    verified := σ.verify pk x.2.1 ch x.2.2
  }


-- @@ L1226-1293 expanded
omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] [Finite Chal] in
private lemma forkVerifyFreshComp_prob_true_le_finalQueryTrace_fresh [Fintype Chal] {qH : ℕ}
    {pk : Stmt} {msg : M} {c : Commit} {resp : Resp}
    {advCache : (fsRoSpec M Commit Chal).QueryCache}
    {liveCache : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache}
    {queryLog : List (M × Commit)} {signed : List M} (hsigned : msg ∉ signed)
    (hcache : advCache (.inr (msg, c)) = none) (hlive : liveCache (msg, c) = none)
    (hlenq : queryLog.length ≤ qH) :
    probOutput
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk
          (msg, (c, resp)) (((advCache, (liveCache, queryLog)), signed)))
        true ≤
      probOutput
        (forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk
            (msg, (c, resp)) (((advCache, (liveCache, queryLog)), signed)) >>=
          fun trace =>
          pure
            ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                trace).isSome))
        true :=
  by
  classical
  let : SampleableType Chal := SampleableType.ofFintype Chal
  calc
    probOutput
          (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk
            (msg, (c, resp)) (((advCache, (liveCache, queryLog)), signed)))
          true =
        probEvent
          (((Fork.wrappedSpec Chal).query (Sum.inr ())) : OracleComp (Fork.wrappedSpec Chal) Chal)
          fun ch : Chal => σ.verify pk c ch resp = true :=
      by
      conv_lhs => simp [forkVerifyFreshComp, hcache, hsigned]
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      apply probEvent_ext
      intro ch _
      simp only [Function.comp_apply]
    _ ≤
        probOutput
          (forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk
              (msg, (c, resp)) (((advCache, (liveCache, queryLog)), signed)) >>=
            fun trace =>
            pure
              ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                  trace).isSome))
          true :=
      by
      simp only [forkFinalQueryTrace, Fork.roImpl, StateT.run_bind, StateT.run_get, hlive,
        StateT.run_set, StateT.run_pure, monad_norm]
      rw [← probEvent_eq_eq_probOutput, bind_pure_comp, probEvent_map]
      rw [StateT.run_lift, bind_pure_comp, probEvent_map]
      refine
        _root_.probEvent_mono (mx :=
          (((Fork.wrappedSpec Chal).query (Sum.inr ())) : OracleComp (Fork.wrappedSpec Chal) Chal))
          (p := fun ch : Chal => σ.verify pk c ch resp = true) fun ch _hch hverify => ?_
      have hmem : (msg, c) ∈ queryLog ++ [(msg, c)] := by simp
      have hidx : (queryLog ++ [(msg, c)]).findIdx (· == (msg, c)) ≤ qH :=
        by
        have hlt :=
          List.findIdx_lt_length_of_exists (xs := queryLog ++ [(msg, c)]) (p := (· == (msg, c)))
            ⟨(msg, c), hmem, by simp⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hlt
        omega
      simpa [Function.comp_def] using
        forkPoint_isSome_of_mem_verified_findIdx_le (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (qH := qH)
          { forgery := (msg, (c, resp))
            advCache := advCache
            roCache := liveCache.cacheQuery (msg, c) ch
            queryLog := queryLog ++ [(msg, c)]
            verified := σ.verify pk c ch resp } (by simpa using hverify)
          (by simp [Fork.Trace.target, hmem]) (by simpa [Fork.Trace.target] using hidx)


-- @@ L1295-1362 expanded
omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] [Finite Chal] in
private lemma forkVerifyFreshComp_prob_true_le_finalQueryTrace [Fintype Chal] {qH : ℕ} {pk : Stmt}
    {x : M × (Commit × Resp)} {s : ForkBaseState M Commit Chal × List M}
    (hinv : forkAwareInv (M := M) (Commit := Commit) (Chal := Chal) s)
    (hliveAdv : forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal) s)
    (hlen : s.1.2.2.length ≤ qH) :
    probOutput
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk x s)
        true ≤
      probOutput
        (forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk x s >>=
          fun trace =>
          pure
            ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                trace).isSome))
        true :=
  by
  classical
  rcases x with ⟨msg, c, resp⟩
  rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
  have hlenq : queryLog.length ≤ qH := by simpa using hlen
  by_cases hsigned : msg ∈ signed
  · cases hcache : advCache (.inr (msg, c)) <;> simp [forkVerifyFreshComp, hcache, hsigned]
  ·
    cases hcache : advCache (.inr (msg, c)) with
    | some ch =>
      change Chal at ch
      have hlive : liveCache (msg, c) = some ch := hinv.1 (msg, c) ch hcache hsigned
      by_cases hverify : σ.verify pk c ch resp = true
      · have hfork :
          (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                { forgery := (msg, (c, resp))
                  advCache := advCache
                  roCache := liveCache
                  queryLog := queryLog
                  verified := σ.verify pk c ch resp }).isSome =
            true :=
          by
          have hmem : (msg, c) ∈ queryLog := hinv.2 (msg, c) ch hlive
          apply forkPoint_isSome_of_mem_verified_length
          · simp [hverify]
          · simpa [Fork.Trace.target]
          · exact hlenq
        have hfork' :
          (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                { forgery := (msg, (c, resp))
                  advCache := advCache
                  roCache := liveCache
                  queryLog := queryLog
                  verified := true }).isSome =
            true :=
          by simpa [hverify] using hfork
        simp [forkVerifyFreshComp, forkFinalQueryTrace, Fork.roImpl, hcache, hlive, hsigned,
          hverify, hfork']
      · have hverify_false : σ.verify pk c ch resp = false := Bool.not_eq_true _ ▸ hverify
        simp [forkVerifyFreshComp, hcache, hsigned, hverify_false]
    | none =>
      cases hlive : liveCache (msg, c) with
      | some
        liveCh =>
        have hcontra : advCache (.inr (msg, c)) = some liveCh := hliveAdv (msg, c) liveCh hlive
        rw [hcache] at hcontra
        cases hcontra
      | none =>
        exact
          forkVerifyFreshComp_prob_true_le_finalQueryTrace_fresh (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) σ hsigned hcache hlive hlenq


-- @@ L1364-1391 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma forkBase_finalQuery_runTrace_eq
    (adv :
      SignatureAlg.unforgeableAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk =
      ((simulateQ (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
              (adv.main pk)).run
          (forkInitialBaseState M Commit Chal) >>=
        fun z =>
        forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk z.1
          (z.2, ([] : List M))) :=
  by
  unfold Fork.runTrace nmaAdvFromCmaWithFinalQuery nmaAdvFromCma FiatShamir.simulatedNmaAdv
    forkBaseImpl forkInitialBaseState forkFinalQueryTrace
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    StateT.run_bind, QueryImpl.add_apply_inr, bind_assoc]
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (outer :=
      Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal) (inner :=
      simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) (oa :=
      adv.main pk) (s := (∅ : (fsRoSpec M Commit Chal).QueryCache)) (q :=
      ((∅ : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache),
        ([] : List (M × Commit))))]
  simp only [monad_norm]
  refine bind_congr fun z ↦ ?_
  obtain ⟨⟨msg, c, resp⟩, advCache, liveCache, queryLog⟩ := z
  cases hcache : liveCache (msg, c) <;> simp [Fork.roImpl, hcache]


-- @@ L1393-1399 verbatim
@[fs_simp] private noncomputable def forkLoggedProbImpl [Fintype Chal]
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    QueryImpl (cmaOracleSpec M Commit Chal Resp)
      (StateT (ForkBaseState M Commit Chal × List M) ProbComp) :=
  (forkWrappedUniformImpl (Chal := Chal)).mapStateTBase
    (forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) simT pk)


-- @@ L1401-1417 verbatim
omit [SampleableType Stmt] [Inhabited Chal] in
private lemma forkLoggedProbImpl_run [Fintype Chal]
    {α : Type}
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) α)
    (s : ForkBaseState M Commit Chal × List M) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT pk) oa).run s) =
      (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run s := by
  simpa [forkLoggedProbImpl] using
    QueryImpl.simulateQ_mapStateTBase_run
      (outer := forkWrappedUniformImpl (Chal := Chal))
      (inner := forkLoggedImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk)
      (oa := oa) (s := s)


-- @@ L1419-1432 expanded
omit [Finite Chal] [Inhabited Chal] in
private lemma forkWrappedUniform_forkSim_query_inl_run [Fintype Chal] (n : unifSpec.Domain)
    (liveSt : Fork.SimState M Commit Chal) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
              (liftM
                ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).query
                  (Sum.inl n)))).run
          liveSt) =
      (fun u => (u, liveSt)) <$>
        (liftM (unifSpec.query n) :
          ProbComp
            ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).Range (Sum.inl n))) :=
  by
  rw [Fork.simulateQ_unifForward_add_roImpl_query_inl_run]
  simp only [add_apply_inl, bind_pure_comp, simulateQ_map, Prod.mk.injEq, and_true, imp_self,
    implies_true, map_inj_right_of_nonempty]
  exact simulateQ_id_add_uniform_query_inl (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)) n


-- @@ L1434-1460 expanded
omit [Finite Chal] [Inhabited Chal] in
@[simp]
private lemma forkWrappedUniform_forkSim_query_inr_run_none [Fintype Chal] (mc : M × Commit)
    (cache : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache)
    (log : List (M × Commit)) (hcache : cache mc = none) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
              (liftM
                ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).query
                  (Sum.inr mc)))).run
          (cache, log)) =
      (fun v => (v, (cache.cacheQuery mc v, log ++ [mc]))) <$>
        ((uniformSample Chal) :
          ProbComp
            ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).Range
              (Sum.inr mc))) :=
  by
  rw [Fork.simulateQ_unifForward_add_roImpl_query_inr_run_none (M := M) (Commit := Commit) (Chal :=
      Chal) mc cache log hcache]
  change
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((Fork.wrappedChallengeQuery Chal >>= fun v =>
            pure (v, (cache.cacheQuery mc v, log ++ [mc]))) :
          OracleComp (Fork.wrappedSpec Chal) (Chal × Fork.SimState M Commit Chal)) =
      (fun v : Chal => (v, (cache.cacheQuery mc v, log ++ [mc]))) <$> (uniformSample Chal)
  simp only [simulateQ_bind, simulateQ_pure]
  have hquery := simulateQ_id_add_uniform_query_inr (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)) ()
  change
    simulateQ (forkWrappedUniformImpl (Chal := Chal)) (Fork.wrappedChallengeQuery Chal) =
      (uniformSample Chal) at hquery
  rw [hquery]
  exact
    (map_eq_bind_pure_comp ProbComp (fun v : Chal => (v, (cache.cacheQuery mc v, log ++ [mc])))
        (uniformSample Chal)).symm


-- @@ L1462-1478 expanded
omit [Finite Chal] [Inhabited Chal] in
private lemma forkWrappedUniform_forkSim_query_inr_run_none_map_fst [Fintype Chal] {β : Type}
    (f : Chal → β) (mc : M × Commit)
    (cache : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache)
    (log : List (M × Commit)) (hcache : cache mc = none) :
    (fun a => f a.1) <$>
        simulateQ (forkWrappedUniformImpl (Chal := Chal))
          ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
                (liftM
                  ((unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))).query
                    (Sum.inr mc)))).run
            (cache, log)) =
      f <$> (uniformSample Chal) :=
  by
  have hrun :=
    forkWrappedUniform_forkSim_query_inr_run_none (M := M) (Commit := Commit) (Chal := Chal) mc
      cache log hcache
  calc
    _ =
        (fun a => f a.1) <$>
          ((fun v => (v, (cache.cacheQuery mc v, log ++ [mc]))) <$> (uniformSample Chal)) :=
      congrArg (fun q => (fun a => f a.1) <$> q) hrun
    _ = _ := by rw [Functor.map_map]


-- @@ L1480-1509 verbatim
omit [Finite Chal] [Inhabited Chal] in
private lemma simulatedNmaUnifSim_forkWrapped_run
    [Fintype Chal]
    {α : Type} (oa : ProbComp α)
    (advCache : (fsRoSpec M Commit Chal).QueryCache)
    (liveSt : Fork.SimState M Commit Chal) :
    simulateQ (forkWrappedUniformImpl (Chal := Chal))
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
          ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
            (Chal := Chal)) oa).run advCache)).run liveSt) =
      (fun a ↦ ((a, advCache), liveSt)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing advCache liveSt with
  | pure x =>
      simp [forkWrappedUniformImpl]
  | query_bind n k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      simp only [simulatedNmaUnifSim, simulatedNmaFwd, QueryImpl.liftTarget_apply,
        add_apply_inl, HasQuery.toQueryImpl_apply, QueryImpl.toHasQuery_query,
        StateT.run_monadLift, monadLift_self, bind_pure_comp, simulateQ_map,
        StateT.run_map, bind_map_left, map_bind]
      have hquery := forkWrappedUniform_forkSim_query_inl_run
        (M := M) (Commit := Commit) (Chal := Chal) n liveSt
      refine (congrArg (fun q => q >>= fun a =>
        simulateQ (forkWrappedUniformImpl (Chal := Chal))
          ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
            ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit)
              (Chal := Chal)) (k a.1)).run advCache)).run a.2)) hquery).trans ?_
      rw [bind_map_left]
      exact bind_congr (m := ProbComp) fun u ↦ ih u advCache liveSt


-- @@ L1511-1525 expanded
omit [Finite Chal] in
private lemma evalSPMF_simulateQ_forkWrappedUniformImpl [Fintype Chal] {α : Type}
    (oa : OracleComp (Fork.wrappedSpec Chal) α) :
    evalSPMF (simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa) = evalSPMF oa :=
  by
  apply OracleComp.evalSPMF_simulateQ_eq_evalSPMF
  rintro (n | u)
  · simp only [forkWrappedUniformImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id',
      QueryImpl.id'_apply]
    rw [OracleComp.evalSPMF_query (spec := Fork.wrappedSpec Chal)]
    exact OracleComp.evalSPMF_query (spec := unifSpec) n
  · simp only [forkWrappedUniformImpl, QueryImpl.add_apply_inr, uniformSampleImpl_apply]
    exact evalSPMF_uniformSample_eq_query (spec := Fork.wrappedSpec Chal) (Sum.inr u)


-- @@ L1527-1533 verbatim
omit [Finite Chal] in
private lemma support_simulateQ_forkWrappedUniformImpl [Fintype Chal]
    {α : Type} (oa : OracleComp (Fork.wrappedSpec Chal) α) :
    support (simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa) =
      support oa :=
  Set.ext fun x => mem_support_iff_of_evalSPMF_eq
    (evalSPMF_simulateQ_forkWrappedUniformImpl oa) x


-- @@ L1535-1541 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [SampleableType Chal] [Finite Chal]
  [Inhabited Chal] in
private lemma forkInitialState_liveCacheAdvCacheInv :
    forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal)
      (forkInitialState M Commit Chal) := by
  intro mc ch hcache
  simp [forkInitialState] at hcache


-- @@ L1543-1624 expanded
omit [SampleableType Stmt] in
private def forkLoggedProbOrnament [Fintype Chal] (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (pk : Stmt) :
    QueryImpl.StateOrnament
      (forkLoggedProbImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
      (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
    where
  inv := forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal)
  proj := forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal)
  preserves_inv := by
    simpa only [forkLoggedProbImpl] using
      QueryImpl.mapStateTBase_preserves_inv (outer := forkWrappedUniformImpl (Chal := Chal))
        (inner := forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
        (inv := forkLiveCacheAdvCacheInv (M := M) (Commit := Commit) (Chal := Chal)) (houter :=
        support_simulateQ_forkWrappedUniformImpl (Chal := Chal)) (hinner :=
        forkLoggedImpl_preserves_live_adv_inv_step (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) simT pk)
  project_step := fun t s hs =>
    by
    rcases s with ⟨⟨advCache, liveCache, queryLog⟩, signed⟩
    rcases t with ((n | mc) | m)
    · have hleft :=
        forkWrappedUniform_forkSim_query_inl_run (M := M) (Commit := Commit) (Chal := Chal) n
          (liveCache, queryLog)
      have hright :=
        simulateQ_id_add_uniform_query_inl (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)) n
      have hleft' := congrArg (fun q => (fun a => (a.1, advCache, signed)) <$> q) hleft
      simp only [Functor.map_map] at hleft'
      have hright' := congrArg (fun q => (fun u => (u, advCache, signed)) <$> q) hright.symm
      simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT, QueryImpl.mapStateTBase] using
        hleft'.trans hright'
    ·
      cases hadv : advCache (.inr mc) with
      | some ch =>
        change Chal at ch
        simp [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          hadv]
      | none =>
        cases hlive : liveCache mc with
        | some
          liveCh =>
          have hcontra : advCache (.inr mc) = some liveCh := hs mc liveCh hlive
          rw [hadv] at hcontra
          cases hcontra
        |
          none =>
          have hleft :=
            forkWrappedUniform_forkSim_query_inr_run_none_map_fst (M := M) (Commit := Commit)
              (Chal := Chal) (fun v => (v, advCache.cacheQuery (.inr mc) v, signed)) mc liveCache
              queryLog hlive
          have hright :=
            simulateQ_id_add_uniform_query_inr (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal))
              mc
          simpa [fs_simp, QueryImpl.extendState, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
            hadv] using
            hleft.trans
              (congrArg (fun q => (fun v => (v, advCache.cacheQuery (.inr mc) v, signed)) <$> q)
                hright.symm)
    · simp only [add_apply_inr, fs_simp, QueryImpl.mapStateTBase, QueryImpl.ofLift_eq_id',
        QueryImpl.extendState, QueryImpl.flattenStateT, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_modifyGet, Prod.mk.eta, bind_pure_comp, simulateQ_map, StateT.run_mk,
        StateT.run_map, Functor.map_map, Prod.map_apply, id_eq]
      have hleft :
        simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
            ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
                  ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))
                        (simT pk)).run
                    advCache)).run
              (liveCache, queryLog)) =
          (fun a => ((a, advCache), (liveCache, queryLog))) <$> simT pk :=
        by
        simpa [forkWrappedUniformImpl] using
          (simulatedNmaUnifSim_forkWrapped_run (M := M) (Commit := Commit) (Chal := Chal) (oa :=
            simT pk) (advCache := advCache) (liveSt := (liveCache, queryLog)))
      have hright :
        simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
            ((simulateQ (simulatedNmaUnifSim (M := M) (Commit := Commit) (Chal := Chal))
                  (simT pk)).run
              advCache) =
          (fun a => (a, advCache)) <$> simT pk :=
        by
        simpa [fsUniformImpl] using
          (simulatedNmaUnifSim_fsUniform_run (M := M) (Commit := Commit) (Chal := Chal) (oa :=
            simT pk) (cache := advCache))
      simp [hleft, hright, Functor.map_map]


-- @@ L1626-1632 expanded
omit [Finite Chal] in
private lemma probOutput_simulateQ_forkWrappedUniformImpl [Fintype Chal] {α : Type}
    (oa : OracleComp (Fork.wrappedSpec Chal) α) (x : α) :
    probOutput (simulateQ (forkWrappedUniformImpl (Chal := Chal)) oa) x = probOutput oa x := by
  simpa only [probOutput_def] using
    congrFun (congrArg DFunLike.coe (evalSPMF_simulateQ_forkWrappedUniformImpl oa)) x


-- @@ L1634-1644 expanded
private noncomputable def forkH5Body
    (adv :
      SignatureAlg.unforgeableAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) : OracleComp (Fork.wrappedSpec Chal) Bool := do
  let (pk, _) ← OracleComp.liftComp hr.gen (Fork.wrappedSpec Chal)
  let z ←
    (simulateQ (forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
            (adv.main pk)).run
        (forkInitialState M Commit Chal)
  forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk z.1 z.2


-- @@ L1646-1655 expanded
private noncomputable def forkLoggedVerifyBody
    (adv :
      SignatureAlg.unforgeableAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) :
    OracleComp (Fork.wrappedSpec Chal) Bool := do
  let z ←
    (simulateQ (forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
            (adv.main pk)).run
        (forkInitialState M Commit Chal)
  forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk z.1 z.2


-- @@ L1657-1691 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma forkLogged_base_support
    (adv :
      SignatureAlg.unforgeableAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    {z : (M × (Commit × Resp)) × (ForkBaseState M Commit Chal × List M)}
    (hz :
      z ∈
        support
          ((simulateQ
                (forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
                (adv.main pk)).run
            (forkInitialState M Commit Chal))) :
    (z.1, z.2.1) ∈
      support
        ((simulateQ (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
              (adv.main pk)).run
          (forkInitialBaseState M Commit Chal)) :=
  by
  have hproj :=
    OracleComp.extendState_run_proj_eq (so :=
      forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) (aux :=
      cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)) (oa :=
      adv.main pk) (s := forkInitialBaseState M Commit Chal) (q := ([] : List M))
  have hmem :
    (z.1, z.2.1) ∈
      support
        (Prod.map id Prod.fst <$>
          (simulateQ
                (QueryImpl.extendState
                  (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
                  (cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)))
                (adv.main pk)).run
            (forkInitialBaseState M Commit Chal, ([] : List M))) :=
    by
    rw [support_map]
    exact ⟨z, by simpa [forkLoggedImpl, forkInitialState, forkInitialBaseState] using hz, rfl⟩
  rw [hproj] at hmem
  simpa [forkLoggedImpl, forkInitialState, forkInitialBaseState] using hmem


-- @@ L1693-1760 expanded
omit [SampleableType Stmt] [SampleableType Wit] in
private lemma forkLogged_queryLog_length_le [Finite Commit] [Finite Resp] [Inhabited Commit]
    [Inhabited Resp]
    (adv :
      SignatureAlg.unforgeableAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) {qS qH : ℕ}
    (hQ :
      ∀ pk,
        signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (S' := Commit × Resp) (oa :=
          adv.main pk) qS qH)
    {z : (M × (Commit × Resp)) × (ForkBaseState M Commit Chal × List M)}
    (hz :
      z ∈
        support
          ((simulateQ
                (forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
                (adv.main pk)).run
            (forkInitialState M Commit Chal))) :
    z.2.1.2.2.length ≤ qH :=
  by
  have hbase :=
    forkLogged_base_support (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ hr adv simT
      pk hz
  have hnested :
    ((z.1, z.2.1.1), z.2.1.2) ∈
      support
        ((simulateQ (Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal)
              ((simulateQ
                    (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT
                      pk)
                    (adv.main pk)).run
                (∅ : (fsRoSpec M Commit Chal).QueryCache))).run
          ((∅ : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache),
            ([] : List (M × Commit)))) :=
    by
    have hmap :
      ((z.1, z.2.1.1), z.2.1.2) ∈
        support
          ((fun y :
                (M × (Commit × Resp)) ×
                  ((fsRoSpec M Commit Chal).QueryCache × Fork.SimState M Commit Chal) =>
              ((y.1, y.2.1), y.2.2)) <$>
            (simulateQ
                  (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
                  (adv.main pk)).run
              (forkInitialBaseState M Commit Chal)) :=
      by
      rw [support_map]
      exact ⟨(z.1, z.2.1), hbase, rfl⟩
    have hmap_base := by simpa [forkBaseImpl, forkInitialBaseState] using hmap
    have hmap' :
      ((z.1, z.2.1.1), z.2.1.2) ∈
        support
          ((fun y :
                (M × (Commit × Resp)) ×
                  ((fsRoSpec M Commit Chal).QueryCache × Fork.SimState M Commit Chal) =>
              ((y.1, y.2.1), y.2.2)) <$>
            (simulateQ
                  ((Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal).mapStateTBase
                      (simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
                        simT pk)).flattenStateT
                  (adv.main pk)).run
              ((∅ : (fsRoSpec M Commit Chal).QueryCache),
                ((∅ : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache),
                  ([] : List (M × Commit))))) :=
      by
      rw [support_map]
      exact ⟨(z.1, z.2.1), hmap_base, rfl⟩
    rw [←
      OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (outer :=
        Fork.unifForward M Commit Chal + Fork.roImpl M Commit Chal) (inner :=
        simulatedNmaImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) (oa :=
        adv.main pk) (s := (∅ : (fsRoSpec M Commit Chal).QueryCache)) (q :=
        ((∅ : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache),
          ([] : List (M × Commit))))] at hmap'
    simpa using hmap'
  have hQnma :
    nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa :=
      (nmaAdvFromCma σ hr M adv simT).main pk) qH :=
    nmaAdvFromCma_nmaHashQueryBound σ hr M adv simT qS qH hQ pk
  have hlen :=
    Fork.queryLog_length_le_of_nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (oa :=
      (nmaAdvFromCma σ hr M adv simT).main pk) (Q := qH) hQnma
      ((∅ : (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)).QueryCache),
        ([] : List (M × Commit)))
      (z := ((z.1, z.2.1.1), z.2.1.2)) hnested
  simpa [nmaAdvFromCma, FiatShamir.simulatedNmaAdv] using hlen


-- @@ L1762-1874 expanded
omit [SampleableType Stmt] [SampleableType Wit] in
/-- The H5 verify body's success probability is bounded by the live `forkPoint`
event for the verify-wrapped adversary. The fork slot parameter is `qH`:
`Fork.forkPoint qH` indexes `Fin (qH + 1)`, accommodating the wrapped
adversary's source-`qH` plus verifier-point query. -/
private lemma forkLogged_verify_prob_true_le_forkPoint_run [Fintype Chal] [Finite Commit]
    [Finite Resp] [Inhabited Commit] [Inhabited Resp]
    (adv :
      SignatureAlg.unforgeableAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt) {qS qH : ℕ}
    (hQ :
      ∀ pk,
        signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (S' := Commit × Resp) (oa :=
          adv.main pk) qS qH) :
    probOutput
        (forkLoggedVerifyBody (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) adv simT pk)
        true ≤
      probOutput
        (Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk >>= fun trace =>
          pure
            ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                trace).isSome))
        true :=
  by
  let loggedRun :=
    ((simulateQ (forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
          (adv.main pk)).run
      (forkInitialState M Commit Chal))
  let finalRun :=
    loggedRun >>= fun z =>
      forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk z.1 z.2 >>=
        fun trace =>
        pure
          ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
              trace).isSome)
  have hbind :=
    probEvent_bind_congr_le_add (mx := loggedRun) (my := fun z =>
      forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk z.1 z.2)
      (oc := fun z =>
      forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk z.1 z.2 >>=
        fun trace =>
        pure
          ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
              trace).isSome))
      (q := fun b => b = true) (ε := 0)
      (by
        intro z hz
        have hinv :=
          forkLoggedImpl_preserves_inv (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
            simT pk (adv.main pk) hz
        have hliveAdv :=
          forkLoggedImpl_preserves_live_adv_inv (M := M) (Commit := Commit) (Chal := Chal) (Resp :=
            Resp) simT pk (adv.main pk) hz
        have hlen :=
          forkLogged_queryLog_length_le (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ
            hr adv simT pk hQ hz
        simpa [probEvent_eq_eq_probOutput] using
          forkVerifyFreshComp_prob_true_le_finalQueryTrace (M := M) (Commit := Commit) (Chal :=
            Chal) (Resp := Resp) σ (qH := qH) (pk := pk) (x := z.1) (s := z.2) hinv hliveAdv hlen)
  have hbind' :
    probOutput
        (forkLoggedVerifyBody (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) adv simT pk)
        true ≤
      probOutput finalRun true :=
    by simpa [forkLoggedVerifyBody, loggedRun, finalRun, probEvent_eq_eq_probOutput] using hbind
  have hproj :=
    OracleComp.extendState_run_proj_eq (so :=
      forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk) (aux :=
      cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)) (oa :=
      adv.main pk) (s := forkInitialBaseState M Commit Chal) (q := ([] : List M))
  have hpoint :
    probOutput finalRun true =
      probOutput
        (Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk >>= fun trace =>
          pure
            ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                trace).isSome))
        true :=
    by
    calc
      probOutput finalRun true =
          probOutput
            ((Prod.map id Prod.fst <$>
                (simulateQ
                      (QueryImpl.extendState
                        (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT
                          pk)
                        (cmaOracleSignLogAux (M := M) (Commit := Commit) (Chal := Chal) (Resp :=
                          Resp)))
                      (adv.main pk)).run
                  (forkInitialBaseState M Commit Chal, ([] : List M))) >>=
              fun z =>
              forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk z.1
                  (z.2, ([] : List M)) >>=
                fun trace =>
                pure
                  ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                      trace).isSome))
            true :=
        by
        simp [finalRun, loggedRun, forkLoggedImpl, forkInitialState, forkInitialBaseState,
          monad_norm, forkFinalQueryTrace]
      _ =
          probOutput
            ((simulateQ
                    (forkBaseImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT pk)
                    (adv.main pk)).run
                (forkInitialBaseState M Commit Chal) >>=
              fun z =>
              forkFinalQueryTrace (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk z.1
                  (z.2, ([] : List M)) >>=
                fun trace =>
                pure
                  ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                      trace).isSome))
            true :=
        by rw [hproj]
      _ =
          probOutput
            (Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk >>= fun trace =>
              pure
                ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
                    trace).isSome))
            true :=
        by
        rw [forkBase_finalQuery_runTrace_eq (M := M) (Commit := Commit) (Chal := Chal) (Resp :=
            Resp) σ hr adv simT pk]
        simp
  exact hbind'.trans_eq hpoint


-- @@ L1876-1924 expanded
omit [SampleableType Stmt] [SampleableType Wit] in
/-- The H5 body's success probability is bounded by the wrapped adversary's
fork advantage at slot parameter `qH`. The framework's `Fin (qH + 1)` indexing
provides exactly enough slots for the wrapped adversary's source-`qH` plus
verifier-point query. -/
private lemma forkH5Body_prob_true_le_fork_advantage [Fintype Chal] [Finite Commit] [Finite Resp]
    [Inhabited Commit] [Inhabited Resp]
    (adv :
      SignatureAlg.unforgeableAdv
        (FiatShamir (m :=
          OracleComp (unifSpec + (OracleSpec.ofFn (ι := M × Commit) (fun _ => Chal)))) σ hr M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) {qS qH : ℕ}
    (hQ :
      ∀ pk,
        signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (S' := Commit × Resp) (oa :=
          adv.main pk) qS qH) :
    probOutput (forkH5Body (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ hr adv simT)
        true ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH :=
  by
  have hbind :=
    probEvent_bind_congr_le_add (mx :=
      (OracleComp.liftComp hr.gen (Fork.wrappedSpec Chal) :
        OracleComp (Fork.wrappedSpec Chal) (Stmt × Wit)))
      (my := fun ps =>
      forkLoggedVerifyBody (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal := Chal) (Resp :=
        Resp) adv simT ps.1)
      (oc := fun ps =>
      Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) ps.1 >>= fun trace =>
        pure
          ((Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH
              trace).isSome))
      (q := fun b => b = true) (ε := 0)
      (by
        intro ps _hps
        simpa [probEvent_eq_eq_probOutput] using
          forkLogged_verify_prob_true_le_forkPoint_run (M := M) (Commit := Commit) (Chal := Chal)
            (Resp := Resp) σ hr adv simT ps.1 hQ)
  let pointBody : OracleComp (Fork.wrappedSpec Chal) Bool := do
    let (pk, _) ← OracleComp.liftComp hr.gen (Fork.wrappedSpec Chal)
    let trace ← Fork.runTrace σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) pk
    pure (Fork.forkPoint (M := M) (Commit := Commit) (Resp := Resp) (Chal := Chal) qH trace).isSome
  have hpoint :
    probOutput pointBody true =
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH :=
    by
    rw [← probOutput_simulateQ_forkWrappedUniformImpl (Chal := Chal) (oa := pointBody) true]
    simp [pointBody, forkWrappedUniformImpl, Fork.advantage, Fork.exp]
  have hbody :
    probOutput (forkH5Body (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ hr adv simT)
        true ≤
      probOutput pointBody true :=
    by simpa [forkH5Body, forkLoggedVerifyBody, pointBody, probEvent_eq_eq_probOutput] using hbind
  exact hbody.trans_eq hpoint


-- @@ L1926-1944 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
/-- Native H4 hop: running the linked simulated CMA game from the direct initial
state is the same as running the NMA game on the `cmaToNma`-shifted adversary.

The initial direct CMA state decomposes into the empty signing log for
`cmaToNma` and the initial NMA state for `nma`. -/
theorem cmaSim_run_eq_nma_run_shiftLeft_cmaToNma
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    {α : Type}
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) α) :
    (cmaSim M Commit Chal hr simT).run (cmaInit M Commit Chal Stmt Wit) A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).run
        (nmaInit M Commit Chal Stmt Wit)
        ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) A) := by
  unfold QueryImpl.Stateful.run QueryImpl.Stateful.shiftLeft cmaSim
  rw [StateT.run'_eq, StateT.run'_eq, QueryImpl.Stateful.simulateQ_linkWith_run,
    QueryImpl.Stateful.run, StateT.run'_eq, simulateQ_map, StateT.run_map]
  simp [cmaInit, nmaInit, cmaFrame, cmaOuterLens, cmaNmaLens,
    Functor.map_map]


-- @@ L1946-2000 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma forkLoggedProbImpl_run_bind_verify_eq_simulatedNma_aux [Fintype Chal]
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (pk : Stmt)
    (oa : OracleComp (cmaOracleSpec M Commit Chal Resp) (M × (Commit × Resp))) :
    ((simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        (forkInitialState M Commit Chal) >>= fun x =>
      simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x.1 x.2)) =
    ((simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>= fun x =>
      simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk x.1 x.2) := by
  obtain ⟨defaultChal, _⟩ := support_uniformSample_nonempty (α := Chal)
  let : Inhabited Chal := ⟨defaultChal⟩
  calc
    ((simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        (forkInitialState M Commit Chal) >>= fun x =>
      simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x.1 x.2))
        =
      (Prod.map id (forkLoggedProj (M := M) (Commit := Commit) (Chal := Chal)) <$>
        (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
          (Chal := Chal) (Resp := Resp) simT pk) oa).run
          (forkInitialState M Commit Chal)) >>= fun x =>
        simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) σ pk x.1 x.2 := by
          simp only [bind_map_left, Prod.map_fst, id_eq, Prod.map_snd]
          exact bind_congr fun x => forkVerifyFreshComp_project (M := M)
            (Commit := Commit) (Chal := Chal) (Resp := Resp) σ pk x.1 x.2
    _ =
      ((simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
        (Chal := Chal) (Resp := Resp) simT pk) oa).run
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>= fun x =>
      simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) σ pk x.1 x.2) := by
        rw [show
          Prod.map id (forkLoggedProj (M := M) (Commit := Commit)
            (Chal := Chal)) <$>
              (simulateQ (forkLoggedProbImpl (M := M) (Commit := Commit)
                (Chal := Chal) (Resp := Resp) simT pk) oa).run
                (forkInitialState M Commit Chal) =
            (simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit)
              (Chal := Chal) (Resp := Resp) simT pk) oa).run
              ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) by
          have hrun := (forkLoggedProbOrnament (M := M) (Commit := Commit)
            (Chal := Chal) (Resp := Resp) simT pk).run_eq oa
            (forkInitialState M Commit Chal)
            (forkInitialState_liveCacheAdvCacheInv (M := M) (Commit := Commit)
              (Chal := Chal))
          simpa [forkLoggedProj, forkInitialState, forkLoggedProbOrnament] using hrun]


-- @@ L2002-2143 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
private lemma nma_runProb_shiftLeft_signedFreshAdv_eq_forkH5Body [Fintype Chal]
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) (simT : Stmt → ProbComp (Commit × Chal × Resp)) :
    (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb (nmaInit M Commit Chal Stmt Wit)
        ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) (signedFreshAdv σ hr M adv)) =
      simulateQ (forkWrappedUniformImpl (Chal := Chal))
        (forkH5Body (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ hr adv simT) :=
  by
  unfold QueryImpl.Stateful.runProb
  rw [←
    cmaSim_run_eq_nma_run_shiftLeft_cmaToNma (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (Wit := Wit) simT (signedFreshAdv σ hr M adv)]
  unfold QueryImpl.Stateful.run signedFreshAdv signedCandidateAdv candidateAdv
  rw [StateT.run'_eq]
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
    id_map, StateT.run_bind, bind_assoc]
  conv_lhs =>
    simp [cmaSim, cmaToNma, nma, nmaPublic, postKeygenCandidateAdv, SourceSigAlg, _root_.FiatShamir,
      forkH5Body, forkWrappedUniformImpl, forkLoggedImpl, forkInitialState, forkVerifyFreshComp,
      forkBaseImpl, simulatedNmaImpl, simulatedNmaBaseSim, cmaInit, cmaDataInit, cmaFrame,
      cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape, Functor.map_map]
  conv_rhs =>
    simp [cmaSim, cmaToNma, nma, nmaPublic, postKeygenCandidateAdv, SourceSigAlg, _root_.FiatShamir,
      forkH5Body, forkWrappedUniformImpl, forkLoggedImpl, forkInitialState, forkVerifyFreshComp,
      forkBaseImpl, simulatedNmaImpl, simulatedNmaBaseSim, cmaInit, cmaDataInit, cmaFrame,
      cmaOuterLens, cmaNmaLens, QueryImpl.Stateful.Frame.linkReshape, Functor.map_map]
  have hkeyLiftComp :
    simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
        (OracleComp.liftComp (hr.gen : OracleComp unifSpec (Stmt × Wit)) (Fork.wrappedSpec Chal)) =
      (hr.gen : ProbComp (Stmt × Wit)) :=
    by
    simpa using
      QueryImpl.simulateQ_liftComp_left_eq_of_apply (impl :=
        QueryImpl.id' unifSpec +
          (uniformSampleImpl (spec := (OracleSpec.ofFn (ι := Unit) (fun _ => Chal)))))
        (impl₁ := QueryImpl.id' unifSpec) (h := fun t => by rfl) (oa :=
        (hr.gen : OracleComp unifSpec (Stmt × Wit)))
  rw (occs := .pos [1]) [← hkeyLiftComp]
  change
    (simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
          (OracleComp.liftComp (hr.gen : OracleComp unifSpec (Stmt × Wit))
            (Fork.wrappedSpec Chal)) >>=
        fun ps => _) =
      (simulateQ (QueryImpl.id' unifSpec + uniformSampleImpl)
          (OracleComp.liftComp (hr.gen : OracleComp unifSpec (Stmt × Wit))
            (Fork.wrappedSpec Chal)) >>=
        fun ps => _)
  apply bind_congr
  intro ps
  change
    _ =
      ((simulateQ (forkWrappedUniformImpl (Chal := Chal))
          ((simulateQ
                (forkLoggedImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT ps.1)
                (adv.main ps.1)).run
            (forkInitialState M Commit Chal))) >>=
        fun x =>
        simulateQ (forkWrappedUniformImpl (Chal := Chal))
          (forkVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ ps.1 x.1
            x.2))
  rw [forkLoggedProbImpl_run (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) simT ps.1
      (adv.main ps.1) (forkInitialState M Commit Chal),
    forkLoggedProbImpl_run_bind_verify_eq_simulatedNma_aux (M := M) (Commit := Commit) (Chal :=
      Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) σ simT ps.1 (adv.main ps.1)]
  let st0 : List M × CmaState M Commit Chal Stmt Wit :=
    cmaSimFixedKeyInitialState (M := M) (Commit := Commit) (Chal := Chal) (Stmt := Stmt) (Wit :=
      Wit) ps
  have hfixed :
    cmaSimFixedKeyInv (M := M) (Commit := Commit) (Chal := Chal) (Stmt := Stmt) (Wit := Wit) ps.1
      ps.2 st0 :=
    by simp [st0, cmaSimFixedKeyInitialState, cmaSimFixedKeyInv]
  have hproj0 :
    cmaSimLoggedProj (M := M) (Commit := Commit) (Chal := Chal) (Stmt := Stmt) (Wit := Wit) st0 =
      ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) :=
    by ext t <;> cases t <;> simp [st0, cmaSimLoggedProj, cmaSimFixedKeyInitialState]
  have hcmaRun :
    Prod.map id
          (cmaSimLoggedProj (M := M) (Commit := Commit) (Chal := Chal) (Stmt := Stmt) (Wit :=
            Wit)) <$>
        (simulateQ
              (cmaSimLoggedLeftImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
                (Stmt := Stmt) (Wit := Wit) hr simT)
              (adv.main ps.1)).run
          st0 =
      (simulateQ
            (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
              simT ps.1)
            (adv.main ps.1)).run
        ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) :=
    by
    let : Fintype Chal := Fintype.ofFinite Chal
    simpa [hproj0, cmaSimLoggedLeftOrnament] using
      (cmaSimLoggedLeftOrnament (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt :=
            Stmt) (Wit := Wit) hr simT ps.1 ps.2).run_eq
        (adv.main ps.1) st0 hfixed
  have hrunExpanded :
    (simulateQ
            (QueryImpl.Stateful.linkWith (cmaFrame M Commit Chal Stmt Wit)
              (cmaToNma M Commit Chal simT) (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr))
            ((simulateQ
                  (cmaSignLogImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) (Stmt :=
                    Stmt))
                  (liftM (adv.main ps.1) :
                    OracleComp (cmaSpec M Commit Chal Resp Stmt) (M × (Commit × Resp)))).run
              ([] : List M))).run
        ((([] : List M), (∅ : RoCache M Commit Chal), some ps), false) =
      (fun z : (M × (Commit × Resp)) × (List M × CmaState M Commit Chal Stmt Wit) =>
          ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ
              (cmaSimLoggedLeftImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
                (Stmt := Stmt) (Wit := Wit) hr simT)
              (adv.main ps.1)).run
          st0 :=
    by
    simpa [cmaSim, st0, cmaSimFixedKeyInitialState] using
      cmaSimLoggedImpl_liftAdv_run_expanded (M := M) (Commit := Commit) (Chal := Chal) (Resp :=
        Resp) (Stmt := Stmt) (Wit := Wit) hr simT (adv.main ps.1) st0.2
  unfold cmaFrame cmaOuterLens cmaNmaLens at hrunExpanded
  rw [hrunExpanded]
  calc
    _ =
        (Prod.map id
              (cmaSimLoggedProj (M := M) (Commit := Commit) (Chal := Chal) (Stmt := Stmt) (Wit :=
                Wit)) <$>
            (simulateQ
                  (cmaSimLoggedLeftImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
                    (Stmt := Stmt) (Wit := Wit) hr simT)
                  (adv.main ps.1)).run
              st0) >>=
          fun x =>
          simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ ps.1
            x.1 x.2 :=
      by
      simp only [bind_map_left]
      refine bind_congr fun x => ?_
      have hproject :=
        cmaSimVerifyFreshComp_project (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt) (Wit := Wit) simT ps.1 x.1 x.2
      simpa [cmaFrame, cmaOuterLens, cmaNmaLens, cmaSim, _root_.FiatShamir, monad_norm] using
        hproject
    _ =
        ((simulateQ
                (simulatedNmaLoggedProbImpl (M := M) (Commit := Commit) (Chal := Chal) (Resp :=
                  Resp) simT ps.1)
                (adv.main ps.1)).run
            ((∅ : (fsRoSpec M Commit Chal).QueryCache), ([] : List M)) >>=
          fun x =>
          simLoggedVerifyFreshComp (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ ps.1
            x.1 x.2) :=
      by rw [hcmaRun]


-- @@ L2145-2185 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] in
/-- H5 boundary in shifted-NMA form. This is the fork-side statement after the
native H4 normalization has moved `cmaSim` to `nma ∘ cmaToNma`. The bound is in
terms of the verify-wrapped adversary `nmaAdvFromCmaWithFinalQuery` at fork
slot parameter `qH` (the framework's `Fin (qH + 1)` indexing accommodates the
wrapper's verifier-point query). -/
theorem nma_runProb_shiftLeft_signedFreshAdv_le_fork [Finite Chal] [Finite Commit] [Finite Resp]
    [Inhabited Commit] [Inhabited Resp] (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (qS qH : ℕ)
    (hQ :
      ∀ pk,
        signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (S' := Commit × Resp) (oa :=
          adv.main pk) qS qH) :
    probOutput
        ((nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb (nmaInit M Commit Chal Stmt Wit)
          ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) (signedFreshAdv σ hr M adv)))
        true ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH :=
  by
  let : Fintype Chal := Fintype.ofFinite Chal
  have hbridge :
    probOutput
        ((nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb (nmaInit M Commit Chal Stmt Wit)
          ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) (signedFreshAdv σ hr M adv)))
        true =
      probOutput
        (forkH5Body (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ hr adv simT) true :=
    by
    rw [nma_runProb_shiftLeft_signedFreshAdv_eq_forkH5Body (σ := σ) (hr := hr) (M := M) (Commit :=
        Commit) (Chal := Chal) (Resp := Resp) adv simT]
    exact
      probOutput_simulateQ_forkWrappedUniformImpl (Chal := Chal) (oa :=
        forkH5Body (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp) σ hr adv simT) true
  have hbody :=
    forkH5Body_prob_true_le_fork_advantage (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal :=
      Chal) (Resp := Resp) adv simT hQ
  exact hbridge.trans_le hbody


-- @@ L2187-2187 verbatim
/-! ## H3 cost factoring -/


-- @@ L2189-2219 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [DecidableEq Commit]
  [SampleableType Chal] [Finite Chal] [Inhabited Chal] in
/-- The final freshness/verification continuation performs no signing queries,
hence contributes zero cumulative H3 signing cost. -/
private lemma verifyFreshComp_expectedQuerySlack_eq_zero
    (G : QueryImpl (cmaSpec M Commit Chal Resp Stmt)
      (StateT (CmaData M Commit Chal Stmt Wit × Bool) (OracleComp unifSpec)))
    (ε : CmaData M Commit Chal Stmt Wit → ℝ≥0∞)
    (p : (Stmt × (M × (Commit × Resp))) × List M)
    (qS : ℕ)
    (s : CmaData M Commit Chal Stmt Wit × Bool) :
    expectedQuerySlack G
      (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      ε
      (verifyFreshComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp) p)
      qS s = 0 := by
  rcases p with ⟨⟨pk, msg, sig⟩, signed⟩
  rcases sig with ⟨c, resp⟩
  rcases s with ⟨s, bad⟩
  cases bad
  · change expectedQuerySlack G
        (IsCostlyQuery (M := M) (Commit := Commit) (Chal := Chal)
          (Resp := Resp) (Stmt := Stmt))
        ε
        (liftM ((cmaSpec M Commit Chal Resp Stmt).query (.ro (msg, c))) >>= fun a =>
          pure (!decide (msg ∈ signed) && σ.verify pk c a resp))
        qS (s, false) = 0
    rw [expectedQuerySlack_query_bind, expectedQuerySlackStep_free] <;> simp [IsCostlyQuery]
  · simp [verifyFreshComp, expectedQuerySlack_bad_eq_zero]


-- @@ L2221-2280 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
/-- Tight native H3 bound for the freshness-preserving adversary, using the
candidate/verifier split so the final verifier hash query is not charged to H3
signing replacement. -/
private theorem signedFreshAdv_H3_bound
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ_zk β : ℝ≥0∞) (hζ_zk : ζ_zk < ∞)
    (hHVZK : σ.HVZK simT ζ_zk.toReal)
    (hCommit : σ.simCommitPredictability simT β)
    (qS qH : ℕ)
    (hQ : ∀ pk, signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (S' := Commit × Resp) (oa := adv.main pk) qS qH) :
    ENNReal.ofReal (cmaH3Advantage M Commit Chal σ hr simT
      (signedFreshAdv σ hr M adv)) ≤
      (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β := by
  let A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool :=
    signedFreshAdv σ hr M adv
  let Apre : OracleComp (cmaSpec M Commit Chal Resp Stmt)
      ((Stmt × (M × (Commit × Resp))) × List M) :=
    signedCandidateAdv σ hr M adv
  have h_cost_candidate :
      cmaH3ExpectedLoss M Commit Chal σ hr ζ_zk β Apre qS ≤
        (qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β :=
    cmaH3ExpectedLoss_le_queryBounds M Commit Chal σ hr ζ_zk β Apre
      (signedCandidateAdv_isQueryBoundP_costly (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        adv qS qH hQ)
      (signedCandidateAdv_isQueryBoundP_hash (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        adv qS qH hQ)
  have h_cost_bind :
      cmaH3ExpectedLoss M Commit Chal σ hr ζ_zk β A qS =
        cmaH3ExpectedLoss M Commit Chal σ hr ζ_zk β Apre qS := by
    simp only [A, Apre, signedFreshAdv, cmaH3ExpectedLoss]
    exact expectedQuerySlack_bind_eq_of_right_zero
      (cmaReal M Commit Chal σ hr)
      (cmaH3Costly (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) (Stmt := Stmt))
      (cmaSignEpsCore M Commit Chal ζ_zk β)
      (signedCandidateAdv σ hr M adv)
      (verifyFreshComp (σ := σ) (hr := hr) (M := M)
        (Commit := Commit) (Chal := Chal) (Resp := Resp))
      (fun x q p => verifyFreshComp_expectedQuerySlack_eq_zero (σ := σ) (hr := hr)
        (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
        (G := cmaReal M Commit Chal σ hr)
        (ε := cmaSignEpsCore M Commit Chal ζ_zk β) x q p)
      qS (cmaInit M Commit Chal Stmt Wit)
  exact cmaReal_cmaSim_advantage_le_H3_bound_of_expectedQuerySlack
    M Commit Chal σ hr simT ζ_zk β A qS
    ((qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β)
    (cmaH3StepFacts_of_hvzk_predictability M Commit Chal σ hr simT
      ζ_zk β hζ_zk hHVZK hCommit)
    (cmaH3RunFacts_of_queryBound_expectedLoss M Commit Chal σ hr ζ_zk β A qS
      ((qS : ℝ≥0∞) * ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + qH) * β)
      (by
        simpa [A] using signedFreshAdv_isQueryBoundP_costly (σ := σ) (hr := hr)
          (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
          adv qS qH hQ)
      (by rwa [h_cost_bind]))


-- @@ L2282-2282 verbatim
/-! ## H4: linked simulation as shifted NMA execution -/


-- @@ L2284-2296 verbatim
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] [Inhabited Chal] in
/-- Native H4 hop in probability form. -/
theorem cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma
    (simT : Stmt → ProbComp (Commit × Chal × Resp))
    (A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool) :
    (cmaSim M Commit Chal hr simT).runProb
        (cmaInit M Commit Chal Stmt Wit) A =
      (nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
        (nmaInit M Commit Chal Stmt Wit)
        ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) A) :=
  cmaSim_run_eq_nma_run_shiftLeft_cmaToNma (hr := hr)
    (M := M) (Commit := Commit) (Chal := Chal) (Resp := Resp)
    (Stmt := Stmt) (Wit := Wit) simT A


-- @@ L2298-2321 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
/-- Convert the shifted-NMA H5 boundary into the linked simulated-CMA form used
by the top-level chain. -/
theorem cmaSim_signedFreshAdv_le_fork_of_shifted_h5 (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (qH : ℕ)
    (hH5 :
      probOutput
          ((nma (Stmt := Stmt) (Wit := Wit) M Commit Chal hr).runProb
            (nmaInit M Commit Chal Stmt Wit)
            ((cmaToNma M Commit Chal simT).shiftLeft ([] : List M) (signedFreshAdv σ hr M adv)))
          true ≤
        Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH) :
    probOutput
        ((cmaSim M Commit Chal hr simT).runProb (cmaInit M Commit Chal Stmt Wit)
          (signedFreshAdv σ hr M adv))
        true ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH :=
  by
  rwa [cmaSim_runProb_eq_nma_runProb_shiftLeft_cmaToNma (hr := hr) (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) simT (signedFreshAdv σ hr M adv)]


-- @@ L2323-2344 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Finite Chal] in
/-- Native H5 boundary in the linked simulated-CMA form used by the top-level
chain. -/
theorem cmaSim_signedFreshAdv_le_fork [Finite Chal] [Finite Commit] [Finite Resp] [Inhabited Commit]
    [Inhabited Resp] (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (simT : Stmt → ProbComp (Commit × Chal × Resp)) (qS qH : ℕ)
    (hQ :
      ∀ pk,
        signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (S' := Commit × Resp) (oa :=
          adv.main pk) qS qH) :
    probOutput
        ((cmaSim M Commit Chal hr simT).runProb (cmaInit M Commit Chal Stmt Wit)
          (signedFreshAdv σ hr M adv))
        true ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH :=
  cmaSim_signedFreshAdv_le_fork_of_shifted_h5 (σ := σ) (hr := hr) (M := M) (Commit := Commit)
    (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) adv simT qH
    (nma_runProb_shiftLeft_signedFreshAdv_le_fork (σ := σ) (hr := hr) (M := M) (Commit := Commit)
      (Chal := Chal) (Resp := Resp) (Stmt := Stmt) (Wit := Wit) adv simT qS qH hQ)


-- @@ L2346-2346 verbatim
/-! ## Top-level chain factored over H5 -/


-- @@ L2348-2430 expanded
omit [SampleableType Stmt] [SampleableType Wit] [Inhabited Chal] in
/-- Native stateful top-level chain, assuming the H5 replay-forking boundary.

This theorem carries the H1/H2/H3/H4 arithmetic directly in the stateful chain.
The bound is in terms of the verify-wrapped adversary
`nmaAdvFromCmaWithFinalQuery` at fork slot parameter `qH`. -/
theorem cma_advantage_le_fork_bound_of_h5 (simT : Stmt → ProbComp (Commit × Chal × Resp)) (ζ_zk : ℝ)
    (hζ_zk : 0 ≤ ζ_zk) (hHVZK : σ.HVZK simT ζ_zk) (β : ENNReal)
    (hPredSim : σ.simCommitPredictability simT β) (adv : SourceAdv (σ := σ) (hr := hr) (M := M))
    (qS qH : ℕ)
    (hQ :
      ∀ pk,
        signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (S' := Commit × Resp) (oa :=
          adv.main pk) qS qH)
    (hH1H2 :
      adv.advantage (FiatShamir.runtime M) ≤
        probOutput
          ((cmaReal M Commit Chal σ hr).runProb (cmaInit M Commit Chal Stmt Wit)
            (signedFreshAdv σ hr M adv))
          true)
    (hH5 :
      probOutput
          ((cmaSim M Commit Chal hr simT).runProb (cmaInit M Commit Chal Stmt Wit)
            (signedFreshAdv σ hr M adv))
          true ≤
        Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH) :
    adv.advantage (FiatShamir.runtime M) ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
        (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β :=
  by
  let A : OracleComp (cmaSpec M Commit Chal Resp Stmt) Bool := signedFreshAdv σ hr M adv
  have hζ_zk_lt : ENNReal.ofReal ζ_zk < ∞ := ENNReal.ofReal_lt_top
  have hHVZK' : σ.HVZK simT (ENNReal.ofReal ζ_zk).toReal := by rwa [ENNReal.toReal_ofReal hζ_zk]
  have hH3_abs :
    ENNReal.ofReal
        (((cmaReal M Commit Chal σ hr).runProb (cmaInit M Commit Chal Stmt Wit) A).boolDistAdvantage
          ((cmaSim M Commit Chal hr simT).runProb (cmaInit M Commit Chal Stmt Wit) A)) ≤
      (qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β :=
    by
    simpa [A, cmaH3Advantage, QueryImpl.Stateful.advantage] using
      signedFreshAdv_H3_bound (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
        (Resp := Resp) adv simT (ENNReal.ofReal ζ_zk) β hζ_zk_lt hHVZK' hPredSim qS qH hQ
  have hH3_prob :
    probOutput ((cmaReal M Commit Chal σ hr).runProb (cmaInit M Commit Chal Stmt Wit) A) true ≤
      probOutput ((cmaSim M Commit Chal hr simT).runProb (cmaInit M Commit Chal Stmt Wit) A) true +
        ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
    le_trans
      (ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        ((cmaReal M Commit Chal σ hr).runProb (cmaInit M Commit Chal Stmt Wit) A)
        ((cmaSim M Commit Chal hr simT).runProb (cmaInit M Commit Chal Stmt Wit) A))
      (add_le_add le_rfl hH3_abs)
  calc
    adv.advantage (FiatShamir.runtime M) ≤
        probOutput ((cmaReal M Commit Chal σ hr).runProb (cmaInit M Commit Chal Stmt Wit) A) true :=
      by simpa [A] using hH1H2
    _ ≤
        probOutput ((cmaSim M Commit Chal hr simT).runProb (cmaInit M Commit Chal Stmt Wit) A)
            true +
          ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
      hH3_prob
    _ ≤
        Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
          ((qS : ℝ≥0∞) * ENNReal.ofReal ζ_zk + (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * β) :=
      (add_le_add hH5 le_rfl)
    _ =
        Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
            ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
          (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β :=
      by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg qS), ENNReal.ofReal_natCast]
      ring_nf


-- @@ L2432-2461 expanded
omit [SampleableType Stmt] [SampleableType Wit] in
/-- Native stateful chain with H5 discharged by the replay-forking boundary,
leaving only the public-to-stateful H1/H2 compatibility premise. -/
theorem cma_advantage_le_fork_bound_of_h1h2 [Finite Commit] [Finite Resp] [Inhabited Commit]
    [Inhabited Resp] (simT : Stmt → ProbComp (Commit × Chal × Resp)) (ζ_zk : ℝ) (hζ_zk : 0 ≤ ζ_zk)
    (hHVZK : σ.HVZK simT ζ_zk) (β : ENNReal) (hPredSim : σ.simCommitPredictability simT β)
    (adv : SourceAdv (σ := σ) (hr := hr) (M := M)) (qS qH : ℕ)
    (hQ :
      ∀ pk,
        signHashQueryBound (M := M) (Commit := Commit) (Chal := Chal) (S' := Commit × Resp) (oa :=
          adv.main pk) qS qH)
    (hH1H2 :
      adv.advantage (FiatShamir.runtime M) ≤
        probOutput
          ((cmaReal M Commit Chal σ hr).runProb (cmaInit M Commit Chal Stmt Wit)
            (signedFreshAdv σ hr M adv))
          true) :
    adv.advantage (FiatShamir.runtime M) ≤
      Fork.advantage σ hr M (nmaAdvFromCmaWithFinalQuery σ hr M adv simT) qH +
          ENNReal.ofReal ((qS : ℝ) * ζ_zk) +
        (qS : ENNReal) * ((qS : ENNReal) + (qH : ENNReal)) * β :=
  cma_advantage_le_fork_bound_of_h5 (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
    (Resp := Resp) (Stmt := Stmt) (Wit := Wit) simT ζ_zk hζ_zk hHVZK β hPredSim adv qS qH hQ hH1H2
    (cmaSim_signedFreshAdv_le_fork (σ := σ) (hr := hr) (M := M) (Commit := Commit) (Chal := Chal)
      (Resp := Resp) (Stmt := Stmt) (Wit := Wit) adv simT qS qH hQ)


-- @@ L2463-2463 verbatim
end FiatShamir.Stateful


-- @@ L2465-2465 verbatim
set_option linter.style.longFile 2600
