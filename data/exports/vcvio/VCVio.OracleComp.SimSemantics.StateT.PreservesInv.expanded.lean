/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.EvalDist.Monad.Basic


-- @@ L14-44 verbatim
/-!
# `StateT σ ProbComp` Invariant Theory

Support-based invariant reasoning for shared, stateful oracle simulations
(ROM/AGM/hybrids) whose handlers live in `StateT σ ProbComp`. A user-supplied
predicate `Inv : σ → Prop` is preserved by an implementation when every reachable
post-state satisfies it.

We use **support-based** formulations (rather than `Pr[ ...] = 1`) to keep
downstream proofs lightweight.

The `WriterT` analogue of this theory lives in
`SimSemantics/WriterT/PreservesInv.lean`.

## Main definitions

- `QueryImpl.PreservesInv` — every oracle query implementation step preserves `Inv`;
  `QueryImpl.PreservesInv.add` / `preservesInv_add_iff` split it over a sum of implementations
- `OracleComp.simulateQ_run_preservesInv` — simulating any oracle computation
  with a preserving implementation preserves `Inv` on the final state
- `InitSatisfiesInv` — every sampled initial state satisfies the invariant
- `StateT.StatePreserving` — computation never changes the state
- `StateT.PreservesInv` — computation preserves an invariant on the state; the structural
  rules `preservesInv_pure`/`_monadLift`/`_map`/`_bind`/`_get_bind`/`_set_of`/`_mapM` check a
  handler written in `do` notation clause by clause
- `StateT.NeverFailsUnder` — computation does not fail under an invariant
- `StateT.OutputIndependent` — output distribution is independent of the initial state
  under an invariant
- `StateT.outputIndependent_after_preservesInv` — non-interference: output-independent
  computation remains so after sequencing with an invariant-preserving computation
-/


-- @@ L46-46 verbatim
@[expose] public section


-- @@ L48-48 verbatim
noncomputable section


-- @@ L50-50 verbatim
open OracleComp OracleSpec


-- @@ L52-52 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L54-54 verbatim
namespace StateT


-- @@ L56-59 verbatim
/-- `PreservesInv mx Inv` means that starting from any state satisfying `Inv`, every reachable
post-state (support-wise) also satisfies `Inv`. -/
def PreservesInv {σ α : Type} (mx : StateT σ ProbComp α) (Inv : σ → Prop) : Prop :=
  ∀ σ0, Inv σ0 → ∀ z ∈ support (mx.run σ0), Inv z.2


-- @@ L61-61 verbatim
end StateT


-- @@ L63-63 verbatim
namespace QueryImpl


-- @@ L65-70 verbatim
/-- `PreservesInv impl Inv` means every oracle query implementation step preserves `Inv`
on all reachable post-states (support-based): each `impl t` is a `StateT.PreservesInv`
computation. -/
def PreservesInv {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop) : Prop :=
  ∀ t, StateT.PreservesInv (impl t) Inv


-- @@ L72-75 verbatim
lemma preservesInv_iff {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop) :
    PreservesInv impl Inv ↔ ∀ t, StateT.PreservesInv (impl t) Inv :=
  Iff.rfl


-- @@ L77-80 verbatim
lemma PreservesInv.trivial {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) :
    PreservesInv impl (fun _ => True) :=
  fun _ _ _ _ _ => True.intro


-- @@ L82-86 verbatim
lemma PreservesInv.and {ι : Type} {spec : OracleSpec ι} {σ : Type}
    {impl : QueryImpl spec (StateT σ ProbComp)} {P Q : σ → Prop}
    (hP : PreservesInv impl P) (hQ : PreservesInv impl Q) :
    PreservesInv impl (fun s => P s ∧ Q s) :=
  fun t σ0 ⟨hp, hq⟩ z hz => ⟨hP t σ0 hp z hz, hQ t σ0 hq z hz⟩


-- @@ L88-92 verbatim
lemma PreservesInv.of_forall {ι : Type} {spec : OracleSpec ι} {σ : Type}
    {impl : QueryImpl spec (StateT σ ProbComp)} {Inv : σ → Prop}
    (h : ∀ t σ0 z, z ∈ support ((impl t).run σ0) → Inv z.2) :
    PreservesInv impl Inv :=
  fun t σ0 _ z hz => h t σ0 z hz


-- @@ L94-100 verbatim
/-- A sum of implementations preserves `Inv` when both summands do. -/
lemma PreservesInv.add {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}
    {impl₁ : QueryImpl spec₁ (StateT σ ProbComp)} {impl₂ : QueryImpl spec₂ (StateT σ ProbComp)}
    {Inv : σ → Prop} (h₁ : PreservesInv impl₁ Inv) (h₂ : PreservesInv impl₂ Inv) :
    PreservesInv (impl₁ + impl₂) Inv
  | .inl t => by rw [add_apply_inl]; exact h₁ t
  | .inr t => by rw [add_apply_inr]; exact h₂ t


-- @@ L102-107 verbatim
lemma preservesInv_add_iff {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ : Type} (impl₁ : QueryImpl spec₁ (StateT σ ProbComp))
    (impl₂ : QueryImpl spec₂ (StateT σ ProbComp)) (Inv : σ → Prop) :
    PreservesInv (impl₁ + impl₂) Inv ↔ PreservesInv impl₁ Inv ∧ PreservesInv impl₂ Inv :=
  ⟨fun h => ⟨fun t => by simpa only [add_apply_inl] using h (.inl t),
    fun t => by simpa only [add_apply_inr] using h (.inr t)⟩, fun h => h.1.add h.2⟩


-- @@ L109-109 verbatim
end QueryImpl


-- @@ L111-111 verbatim
namespace OracleComp


-- @@ L113-113 verbatim
open QueryImpl


-- @@ L115-140 verbatim
/-- If `impl` preserves `Inv`, then simulating *any* oracle computation with `simulateQ impl`
preserves `Inv` on the final state (support-wise). -/
theorem simulateQ_run_preservesInv
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop)
    (himpl : QueryImpl.PreservesInv impl Inv) :
    ∀ oa : OracleComp spec α,
    ∀ σ0, Inv σ0 →
      ∀ z ∈ support ((simulateQ impl oa).run σ0), Inv z.2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro σ0 hσ0 z hz
      simp_all
  | query_bind t oa ih =>
      intro σ0 hσ0 z hz
      have hz' :
          z ∈ support
            (((simulateQ impl
                  (OracleSpec.query t : OracleComp spec (spec.Range t))).run σ0) >>=
              fun us => (simulateQ impl (oa us.1)).run us.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using hz
      rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
      have hus' : us ∈ support ((impl t).run σ0) := by
        simpa [simulateQ_spec_query] using hus
      exact ih us.1 us.2 (himpl t σ0 hσ0 us hus') z hzcont


-- @@ L142-142 verbatim
end OracleComp


-- @@ L144-144 verbatim
namespace QueryImpl


-- @@ L146-154 expanded
/-- If `so'` preserves `Inv`, then `so' ∘ₛ so` also preserves `Inv` for any `so`. -/
lemma PreservesInv.compose {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {σ : Type}
    {so' : QueryImpl spec' (StateT σ ProbComp)} {so : QueryImpl spec (OracleComp spec')}
    {Inv : σ → Prop} (h : PreservesInv so' Inv) : PreservesInv (QueryImpl.compose so' so) Inv :=
  fun t σ0 hσ0 z hz =>
  OracleComp.simulateQ_run_preservesInv so' Inv h (so t) σ0 hσ0 z
    (by simpa [apply_compose] using hz)


-- @@ L156-156 verbatim
end QueryImpl


-- @@ L158-161 verbatim
/-- `InitSatisfiesInv init Inv` means every possible initial state sampled by `init`
satisfies `Inv` (support-based). -/
def InitSatisfiesInv {σ : Type} (init : ProbComp σ) (Inv : σ → Prop) : Prop :=
  ∀ σ0 ∈ support init, Inv σ0


-- @@ L163-166 verbatim
/-! ## StateT invariant properties

These properties are useful for **non-interference** arguments in sequential composition proofs.
They are stated for general `StateT σ ProbComp` computations. -/


-- @@ L168-168 verbatim
namespace StateT


-- @@ L170-173 verbatim
/-- `StatePreserving mx` means `mx` never changes the state: for every starting state `σ0`,
every outcome in the support of `mx.run σ0` has final state equal to `σ0`. -/
def StatePreserving {σ α : Type} (mx : StateT σ ProbComp α) : Prop :=
  ∀ σ0, ∀ z ∈ support (mx.run σ0), z.2 = σ0


-- @@ L175-178 expanded
/-- `NeverFailsUnder mx Inv` means that starting from any state satisfying `Inv`, the computation
does not fail (its failure probability is `0`). -/
def NeverFailsUnder {σ α : Type} (mx : StateT σ ProbComp α) (Inv : σ → Prop) : Prop :=
  ∀ σ0, Inv σ0 → probFailure (mx.run σ0) = 0


-- @@ L180-186 expanded
/-- `OutputIndependent mx Inv` means the output distribution of `mx` does not depend on the
initial state, as long as the initial state satisfies `Inv`.

This is distributional equality of `run'` (which discards the final state). -/
def OutputIndependent {σ α : Type} (mx : StateT σ ProbComp α) (Inv : σ → Prop) : Prop :=
  ∀ σ0 σ1, Inv σ0 → Inv σ1 → evalSPMF (mx.run' σ0) = evalSPMF (mx.run' σ1)


-- @@ L188-191 verbatim
@[simp] lemma statePreserving_pure {σ α : Type} (a : α) :
    StatePreserving (pure a : StateT σ ProbComp α) := by
  intro σ0 z hz
  simp_all


-- @@ L193-196 verbatim
@[simp] lemma outputIndependent_pure {σ α : Type} (Inv : σ → Prop) (a : α) :
    OutputIndependent (pure a : StateT σ ProbComp α) Inv := by
  intro σ0 σ1 _ _
  simp


-- @@ L198-205 verbatim
lemma statePreserving_bind {σ α β : Type}
    (mx : StateT σ ProbComp α) (my : α → StateT σ ProbComp β)
    (h₁ : StatePreserving mx) (h₂ : ∀ a, StatePreserving (my a)) :
    StatePreserving (mx >>= my) := by
  intro σ0 z hz
  rw [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨us, hus, hcont⟩ := hz
  rw [h₂ us.1 us.2 z (by simpa using hcont), h₁ σ0 us hus]


-- @@ L207-211 verbatim
lemma preservesInv_of_statePreserving {σ α : Type}
    (mx : StateT σ ProbComp α) (Inv : σ → Prop) (h : StatePreserving mx) :
    PreservesInv mx Inv := by
  intro σ0 hσ0 z hz
  simp [h σ0 z hz, hσ0]


-- @@ L213-220 verbatim
lemma preservesInv_bind {σ α β : Type}
    (mx : StateT σ ProbComp α) (my : α → StateT σ ProbComp β)
    (Inv : σ → Prop) (h₁ : PreservesInv mx Inv) (h₂ : ∀ a, PreservesInv (my a) Inv) :
    PreservesInv (mx >>= my) Inv := by
  intro σ0 hσ0 z hz
  rw [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨us, hus, hcont⟩ := hz
  exact h₂ us.1 us.2 (h₁ σ0 hσ0 us hus) z hcont


-- @@ L222-224 verbatim
lemma preservesInv_pure {σ α : Type} (a : α) (Inv : σ → Prop) :
    PreservesInv (pure a : StateT σ ProbComp α) Inv :=
  preservesInv_of_statePreserving _ _ (statePreserving_pure a)


-- @@ L226-232 verbatim
lemma statePreserving_monadLift {σ α : Type} (mx : ProbComp α) :
    StatePreserving (monadLift mx : StateT σ ProbComp α) := by
  intro σ0 z hz
  simp only [StateT.run_monadLift, monadLift_eq_self, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨_, -, rfl⟩ := hz
  rfl


-- @@ L234-236 verbatim
lemma preservesInv_monadLift {σ α : Type} (mx : ProbComp α) (Inv : σ → Prop) :
    PreservesInv (monadLift mx : StateT σ ProbComp α) Inv :=
  preservesInv_of_statePreserving _ _ (statePreserving_monadLift mx)


-- @@ L238-243 verbatim
lemma preservesInv_map {σ α β : Type} (f : α → β) {mx : StateT σ ProbComp α} {Inv : σ → Prop}
    (h : PreservesInv mx Inv) : PreservesInv (f <$> mx) Inv := by
  intro σ0 hσ0 z hz
  rw [StateT.run_map, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact h σ0 hσ0 y hy


-- @@ L245-251 verbatim
/-- Reading the state first: the continuation only has to preserve `Inv` from states that
satisfy it, so a `get`-then-`match` handler is checked branch by branch. -/
lemma preservesInv_get_bind {σ α : Type} {my : σ → StateT σ ProbComp α} (Inv : σ → Prop)
    (h : ∀ s, Inv s → PreservesInv (my s) Inv) : PreservesInv (get >>= my) Inv := by
  intro σ0 hσ0 z hz
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact h σ0 hσ0 σ0 hσ0 z hz


-- @@ L253-258 verbatim
lemma preservesInv_set_of {σ : Type} {s' : σ} (Inv : σ → Prop) (h : Inv s') :
    PreservesInv (set s' : StateT σ ProbComp PUnit) Inv := by
  intro σ0 _ z hz
  rw [StateT.run_set, support_pure, Set.mem_singleton_iff] at hz
  rcases hz with rfl
  exact h


-- @@ L260-267 verbatim
lemma preservesInv_mapM {σ α β : Type} {f : α → StateT σ ProbComp β} (Inv : σ → Prop)
    (hf : ∀ a, PreservesInv (f a) Inv) (l : List α) : PreservesInv (l.mapM f) Inv := by
  induction l with
  | nil => simpa only [List.mapM_nil] using preservesInv_pure _ Inv
  | cons a l ih =>
    rw [List.mapM_cons]
    exact preservesInv_bind _ _ _ (hf a) fun _ =>
      preservesInv_bind _ _ _ ih fun _ => preservesInv_pure _ Inv


-- @@ L269-296 expanded
/-- If `mx` is output-independent on `Inv`, and `my` preserves `Inv` and never fails under `Inv`,
then the output distribution of `mx` is unchanged by running `my` first and then running `mx`
on the resulting state. -/
lemma outputIndependent_after_preservesInv {σ α β : Type} (mx : StateT σ ProbComp α)
    (my : StateT σ ProbComp β) (Inv : σ → Prop) (hmx : OutputIndependent mx Inv)
    (hmyInv : PreservesInv my Inv) (hmyNoFail : NeverFailsUnder my Inv) :
    ∀ σ0, Inv σ0 → evalSPMF ((my.run σ0) >>= fun us => mx.run' us.2) = evalSPMF (mx.run' σ0) :=
  by
  intro σ0 hσ0
  refine SPMF.ext fun a => ?_
  rw [← probOutput_def, ← probOutput_def]
  rw [probOutput_bind_eq_tsum]
  have hbind_eq :
    (∑' us : β × σ, probOutput (my.run σ0) us * probOutput (mx.run' us.2) a) =
      (∑' us : β × σ, probOutput (my.run σ0) us) * probOutput (mx.run' σ0) a :=
    by
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun us => ?_
    rcases eq_or_ne (probOutput (my.run σ0) us) 0 with hus | hus
    · rw [hus, zero_mul, zero_mul]
    · have hInv : Inv us.2 := hmyInv σ0 hσ0 us ((mem_support_iff _ _).2 hus)
      simp only [probOutput_def, hmx us.2 σ0 hInv hσ0]
  rw [hbind_eq]
  have hsum : (∑' us : β × σ, probOutput (my.run σ0) us) = 1 :=
    by
    have htotal := tsum_probOutput_add_probFailure (my.run σ0)
    rwa [hmyNoFail σ0 hσ0, add_zero] at htotal
  rw [hsum, one_mul]


-- @@ L298-298 verbatim
end StateT
