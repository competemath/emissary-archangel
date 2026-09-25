/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SecExp
public import VCVio.OracleComp.SimSemantics.StateT.StateSeparating


-- @@ L11-18 verbatim
/-!
# State-separating handlers: advantage and `evalSPMF` congruences

This file contains the probability-facing lower API for
`QueryImpl.Stateful`. It keeps the proof-theory layer close to the SSP
literature while leaving the core handler object as the unbundled
`QueryImpl.Stateful I E σ`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
universe uₑ


-- @@ L24-24 verbatim
open OracleSpec OracleComp ProbComp


-- @@ L26-26 verbatim
namespace QueryImpl.Stateful


-- @@ L28-28 verbatim
variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ} {σ : Type}


-- @@ L30-30 verbatim
/-! ## Bridging to `ProbComp` -/


-- @@ L32-36 verbatim
/-- Run a probability-only stateful handler from an explicit initial state. -/
@[reducible]
def runProb {α : Type} (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E α) : ProbComp α :=
  h.run s₀ A


-- @@ L38-42 verbatim
/-- Run a probability-only stateful handler from the default initial state. -/
@[reducible]
def runProb₀ {α : Type} [Inhabited σ] (h : QueryImpl.Stateful unifSpec E σ)
    (A : OracleComp E α) : ProbComp α :=
  h.run₀ A


-- @@ L44-47 verbatim
@[simp]
lemma runProb_eq_run {α : Type} (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E α) :
    h.runProb s₀ A = h.run s₀ A := rfl


-- @@ L49-49 verbatim
/-! ## Advantage and triangle inequality -/


-- @@ L51-57 verbatim
/-- Boolean distinguishing advantage between two probability-only stateful
handlers, with explicit initial states. -/
noncomputable def advantage {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁)
    (A : OracleComp E Bool) : ℝ :=
  (h₀.runProb s₀ A).boolDistAdvantage (h₁.runProb s₁ A)


-- @@ L59-64 verbatim
/-- Boolean distinguishing advantage from default initial states. -/
noncomputable def advantage₀ {σ₀ σ₁ : Type} [Inhabited σ₀] [Inhabited σ₁]
    (h₀ : QueryImpl.Stateful unifSpec E σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁)
    (A : OracleComp E Bool) : ℝ :=
  h₀.advantage default h₁ default A


-- @@ L66-70 verbatim
@[simp]
lemma advantage_self (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E Bool) :
    h.advantage s₀ h s₀ A = 0 := by
  simp [advantage, ProbComp.boolDistAdvantage]


-- @@ L72-77 verbatim
lemma advantage_symm {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁)
    (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A = h₁.advantage s₁ h₀ s₀ A := by
  simp [advantage, ProbComp.boolDistAdvantage, abs_sub_comm]


-- @@ L79-86 expanded
lemma advantage_eq_of_evalSPMF_runProb_eq {σ₀ σ₀' σ₁ : Type} {h₀ : QueryImpl.Stateful unifSpec E σ₀}
    {s₀ : σ₀} {h₀' : QueryImpl.Stateful unifSpec E σ₀'} {s₀' : σ₀'}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {A : OracleComp E Bool}
    (h_eq : evalSPMF (h₀.runProb s₀ A) = evalSPMF (h₀'.runProb s₀' A)) :
    h₀.advantage s₀ h₁ s₁ A = h₀'.advantage s₀' h₁ s₁ A := by
  simp only [advantage, ProbComp.boolDistAdvantage, probOutput_congr rfl h_eq]


-- @@ L88-95 expanded
lemma advantage_eq_of_evalSPMF_runProb_eq_right {σ₀ σ₁ σ₁' : Type}
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀} {h₁ : QueryImpl.Stateful unifSpec E σ₁}
    {s₁ : σ₁} {h₁' : QueryImpl.Stateful unifSpec E σ₁'} {s₁' : σ₁'} {A : OracleComp E Bool}
    (h_eq : evalSPMF (h₁.runProb s₁ A) = evalSPMF (h₁'.runProb s₁' A)) :
    h₀.advantage s₀ h₁ s₁ A = h₀.advantage s₀ h₁' s₁' A := by
  simp only [advantage, ProbComp.boolDistAdvantage, probOutput_congr rfl h_eq]


-- @@ L97-104 verbatim
lemma advantage_triangle {σ₀ σ₁ σ₂ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁)
    (h₂ : QueryImpl.Stateful unifSpec E σ₂) (s₂ : σ₂)
    (A : OracleComp E Bool) :
    h₀.advantage s₀ h₂ s₂ A ≤
      h₀.advantage s₀ h₁ s₁ A + h₁.advantage s₁ h₂ s₂ A :=
  ProbComp.boolDistAdvantage_triangle _ _ _


-- @@ L106-106 verbatim
/-! ## `evalSPMF` congruence for handlers -/


-- @@ L108-119 expanded
lemma simulateQ_evalSPMF_congr {α : Type} {h₁ h₂ : QueryImpl E ProbComp}
    (hh : ∀ (q : E.Domain), evalSPMF (h₁ q) = evalSPMF (h₂ q)) (A : OracleComp E α) :
    evalSPMF (simulateQ h₁ A) = evalSPMF (simulateQ h₂ A) := by
  induction A using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t k
    ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, evalSPMF_bind]
    rw [hh t]
    exact bind_congr ih


-- @@ L121-133 expanded
lemma simulateQ_StateT_evalSPMF_congr {α : Type} {h₁ h₂ : QueryImpl E (StateT σ ProbComp)}
    (hh : ∀ (q : E.Domain) (s : σ), evalSPMF ((h₁ q).run s) = evalSPMF ((h₂ q).run s))
    (A : OracleComp E α) (s : σ) :
    evalSPMF ((simulateQ h₁ A).run s) = evalSPMF ((simulateQ h₂ A).run s) := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k
    ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, evalSPMF_bind]
    rw [hh t s]
    exact bind_congr fun p => ih p.1 p.2


-- @@ L135-151 expanded
lemma simulateQ_StateT_evalSPMF_congr_of_bij {α : Type} {σ₁ σ₂ : Type}
    (h₁ : QueryImpl E (StateT σ₁ ProbComp)) (h₂ : QueryImpl E (StateT σ₂ ProbComp)) (φ : σ₁ ≃ σ₂)
    (hh :
      ∀ (q : E.Domain) (s : σ₁),
        evalSPMF ((h₁ q).run s) = evalSPMF (Prod.map id φ.symm <$> (h₂ q).run (φ s)))
    (A : OracleComp E α) (s : σ₁) :
    evalSPMF ((simulateQ h₁ A).run s) =
      evalSPMF (Prod.map id φ.symm <$> (simulateQ h₂ A).run (φ s)) :=
  by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k
    ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, map_bind, evalSPMF_bind, hh t s, monad_norm]
    refine bind_congr fun ⟨x, s'⟩ => ?_
    simpa [Equiv.apply_symm_apply, Function.comp_def] using ih x (φ.symm s')


-- @@ L153-153 verbatim
/-! ## Functoriality of `runProb` -/


-- @@ L155-158 verbatim
lemma runProb_map {α β : Type} (h : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (f : α → β) (A : OracleComp E α) :
    h.runProb s₀ (f <$> A) = f <$> h.runProb s₀ A := by
  simp [QueryImpl.Stateful.run]


-- @@ L160-160 verbatim
end QueryImpl.Stateful
