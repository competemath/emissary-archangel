/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.StateSeparating.Advantage


-- @@ L10-16 verbatim
/-!
# State-separating handlers: distributional equivalence

`QueryImpl.Stateful.DistEquiv h₀ s₀ h₁ s₁` says that two stateful handlers,
started from explicit initial states, produce the same output distribution
against every client computation.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
universe uᵢ uₑ uₘ


-- @@ L22-22 verbatim
open OracleSpec OracleComp


-- @@ L24-24 verbatim
namespace QueryImpl.Stateful


-- @@ L26-26 verbatim
variable {ιᵢ : Type uᵢ} {I : OracleSpec.{uᵢ, 0} ιᵢ}

-- @@ L27-27 verbatim
variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}


-- @@ L29-35 expanded
/-- Perfect distributional equivalence of two stateful handlers from explicit
initial states. -/
def DistEquiv [IsUniformSpec I] {σ₀ σ₁ : Type} (h₀ : QueryImpl.Stateful I E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful I E σ₁) (s₁ : σ₁) : Prop :=
  ∀ {α : Type} (A : OracleComp E α), evalSPMF (h₀.run s₀ A) = evalSPMF (h₁.run s₁ A)


-- @@ L37-39 verbatim
@[inherit_doc DistEquiv]
scoped notation:50 "(" h₀ ", " s₀ ")" " ≡ᵈ " "(" h₁ ", " s₁ ")" =>
  QueryImpl.Stateful.DistEquiv h₀ s₀ h₁ s₁


-- @@ L41-45 verbatim
/-- Perfect distributional equivalence from default initial states. -/
def DistEquiv₀ [IsUniformSpec I] {σ₀ σ₁ : Type}
    [Inhabited σ₀] [Inhabited σ₁]
    (h₀ : QueryImpl.Stateful I E σ₀) (h₁ : QueryImpl.Stateful I E σ₁) : Prop :=
  QueryImpl.Stateful.DistEquiv h₀ default h₁ default


-- @@ L47-48 verbatim
@[inherit_doc DistEquiv₀]
scoped infix:50 " ≡ᵈ₀ " => QueryImpl.Stateful.DistEquiv₀


-- @@ L50-50 verbatim
namespace DistEquiv


-- @@ L52-52 verbatim
variable {σ σ₀ σ₁ σ₂ : Type}

-- @@ L53-53 verbatim
variable [IsUniformSpec I]


-- @@ L55-66 expanded
private lemma simulateQ_StateT_evalSPMF_congr_import {α : Type}
    {h₀ h₁ : QueryImpl E (StateT σ (OracleComp I))}
    (hh : ∀ (q : E.Domain) (s : σ), evalSPMF ((h₀ q).run s) = evalSPMF ((h₁ q).run s))
    (A : OracleComp E α) (s : σ) :
    evalSPMF ((simulateQ h₀ A).run s) = evalSPMF ((simulateQ h₁ A).run s) := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k
    ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, evalSPMF_bind, hh t s]
    exact bind_congr fun p => ih p.1 p.2


-- @@ L68-68 verbatim
/-! ## Relation laws -/


-- @@ L70-71 verbatim
protected theorem refl (h : QueryImpl.Stateful I E σ) (s : σ) :
    (h, s) ≡ᵈ (h, s) := fun _ => rfl


-- @@ L73-77 verbatim
protected theorem symm
    {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful I E σ₁} {s₁ : σ₁}
    (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) : (h₁, s₁) ≡ᵈ (h₀, s₀) :=
  fun A => (h A).symm


-- @@ L79-85 verbatim
protected theorem trans
    {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful I E σ₁} {s₁ : σ₁}
    {h₂ : QueryImpl.Stateful I E σ₂} {s₂ : σ₂}
    (h₀₁ : (h₀, s₀) ≡ᵈ (h₁, s₁)) (h₁₂ : (h₁, s₁) ≡ᵈ (h₂, s₂)) :
    (h₀, s₀) ≡ᵈ (h₂, s₂) :=
  fun A => (h₀₁ A).trans (h₁₂ A)


-- @@ L87-87 verbatim
/-! ## Constructors -/


-- @@ L89-94 expanded
theorem of_run_evalSPMF {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀} {h₁ : QueryImpl.Stateful I E σ₁}
    {s₁ : σ₁}
    (h : ∀ {α : Type} (A : OracleComp E α), evalSPMF (h₀.run s₀ A) = evalSPMF (h₁.run s₁ A)) :
    (h₀, s₀) ≡ᵈ (h₁, s₁) := fun A => h A


-- @@ L96-100 expanded
theorem run_evalSPMF_eq {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀} {h₁ : QueryImpl.Stateful I E σ₁}
    {s₁ : σ₁} (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) {α : Type} (A : OracleComp E α) :
    evalSPMF (h₀.run s₀ A) = evalSPMF (h₁.run s₁ A) :=
  h A


-- @@ L102-107 expanded
theorem run₀_evalSPMF_eq {h₀ : QueryImpl.Stateful I E σ₀} {h₁ : QueryImpl.Stateful I E σ₁}
    [Inhabited σ₀] [Inhabited σ₁] (h : h₀ ≡ᵈ₀ h₁) {α : Type} (A : OracleComp E α) :
    evalSPMF (h₀.run₀ A) = evalSPMF (h₁.run₀ A) :=
  h A


-- @@ L109-114 expanded
theorem runProb_evalSPMF_eq {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) {α : Type}
    (A : OracleComp E α) : evalSPMF (h₀.runProb s₀ A) = evalSPMF (h₁.runProb s₁ A) := by
  simpa only [runProb_eq_run] using h A


-- @@ L116-121 expanded
theorem runProb₀_evalSPMF_eq {h₀ : QueryImpl.Stateful unifSpec E σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} [Inhabited σ₀] [Inhabited σ₁] (h : h₀ ≡ᵈ₀ h₁) {α : Type}
    (A : OracleComp E α) : evalSPMF (h₀.runProb₀ A) = evalSPMF (h₁.runProb₀ A) := by
  simpa only [runProb₀] using run₀_evalSPMF_eq h A


-- @@ L123-128 verbatim
theorem of_run_eq
    {h₀ : QueryImpl.Stateful I E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful I E σ₁} {s₁ : σ₁}
    (h : ∀ {α : Type} (A : OracleComp E α), h₀.run s₀ A = h₁.run s₁ A) :
    (h₀, s₀) ≡ᵈ (h₁, s₁) :=
  fun A => by rw [h A]


-- @@ L130-138 expanded
theorem of_step {h₀ h₁ : QueryImpl.Stateful I E σ}
    (h_impl : ∀ (q : E.Domain) (s : σ), evalSPMF ((h₀ q).run s) = evalSPMF ((h₁ q).run s))
    (s₀ : σ) : (h₀, s₀) ≡ᵈ (h₁, s₀) := by
  intro α A
  simp only [QueryImpl.Stateful.run, StateT.run'_eq, evalSPMF_map]
  exact congrArg _ (simulateQ_StateT_evalSPMF_congr_import h_impl A s₀)


-- @@ L140-151 expanded
theorem of_step_bij (h₀ : QueryImpl.Stateful unifSpec E σ₀) (h₁ : QueryImpl.Stateful unifSpec E σ₁)
    (φ : σ₀ ≃ σ₁)
    (h_impl :
      ∀ (q : E.Domain) (s : σ₀),
        evalSPMF ((h₀ q).run s) = evalSPMF (Prod.map id φ.symm <$> (h₁ q).run (φ s)))
    (s₀ : σ₀) : (h₀, s₀) ≡ᵈ (h₁, φ s₀) := by
  intro α A
  simp only [QueryImpl.Stateful.run, StateT.run'_eq, evalSPMF_map,
    simulateQ_StateT_evalSPMF_congr_of_bij h₀ h₁ φ h_impl A s₀, Functor.map_map, Prod.map_fst,
    id_eq]


-- @@ L153-153 verbatim
/-! ## Bridge to advantage -/


-- @@ L155-161 verbatim
theorem advantage_left
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₀' : QueryImpl.Stateful unifSpec E σ} {s₀' : σ}
    (h : (h₀, s₀) ≡ᵈ (h₀', s₀'))
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁) (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A = h₀'.advantage s₀' h₁ s₁ A :=
  advantage_eq_of_evalSPMF_runProb_eq (h A)


-- @@ L163-169 verbatim
theorem advantage_right
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {h₁' : QueryImpl.Stateful unifSpec E σ} {s₁' : σ}
    (h : (h₁, s₁) ≡ᵈ (h₁', s₁')) (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A = h₀.advantage s₀ h₁' s₁' A :=
  advantage_eq_of_evalSPMF_runProb_eq_right (h A)


-- @@ L171-176 verbatim
theorem advantage_zero
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A = 0 := by
  rw [advantage_left h h₁ s₁ A, advantage_self]


-- @@ L178-178 verbatim
/-! ## Compositional congruences -/


-- @@ L180-180 verbatim
section LinkCongr


-- @@ L182-182 verbatim
variable {ιₘ : Type uₘ} {M : OracleSpec.{uₘ, 0} ιₘ}

-- @@ L183-183 verbatim
variable {σ_P : Type}


-- @@ L185-194 verbatim
/-- `link` congruence on the inner handler: an inner-handler equivalence lifts to
an equivalence of the linked handlers with matching outer state and initial state. -/
theorem link_inner_congr (outer : QueryImpl.Stateful M E σ_P) (sP : σ_P)
    {inner₀ : QueryImpl.Stateful unifSpec M σ₀} {s₀ : σ₀}
    {inner₁ : QueryImpl.Stateful unifSpec M σ₁} {s₁ : σ₁}
    (h : (inner₀, s₀) ≡ᵈ (inner₁, s₁)) :
    (outer.link inner₀, (sP, s₀)) ≡ᵈ (outer.link inner₁, (sP, s₁)) := by
  intro α A
  rw [run_link_eq_run_shiftLeft, run_link_eq_run_shiftLeft]
  exact h (outer.shiftLeft sP A)


-- @@ L196-196 verbatim
end LinkCongr


-- @@ L198-198 verbatim
section ParCongr


-- @@ L200-205 verbatim
variable {ιᵢ₁ : Type uₘ} {ιᵢ₂ : Type uₘ}
  {I₁ : OracleSpec.{uₘ, 0} ιᵢ₁} {I₂ : OracleSpec.{uₘ, 0} ιᵢ₂}
  [IsUniformSpec I₁] [IsUniformSpec I₂]
  {ιₑ₁ : Type uₑ} {ιₑ₂ : Type uₑ}
  {E₁ : OracleSpec.{uₑ, 0} ιₑ₁} {E₂ : OracleSpec.{uₑ, 0} ιₑ₂}
  {σ₁ σ₂ : Type}


-- @@ L207-223 expanded
/-- `parSum` congruence on both sides from per-factor handler equivalences with
explicit initial states. -/
theorem parSum_congr {h₁ h₁' : QueryImpl.Stateful I₁ E₁ σ₁} {s₁ : σ₁}
    {h₂ h₂' : QueryImpl.Stateful I₂ E₂ σ₂} {s₂ : σ₂}
    (hh₁ : ∀ (q : E₁.Domain) (s : σ₁), evalSPMF ((h₁ q).run s) = evalSPMF ((h₁' q).run s))
    (hh₂ : ∀ (q : E₂.Domain) (s : σ₂), evalSPMF ((h₂ q).run s) = evalSPMF ((h₂' q).run s)) :
    (h₁.parSum h₂, (s₁, s₂)) ≡ᵈ (h₁'.parSum h₂', (s₁, s₂)) :=
  by
  refine of_step ?_ (s₁, s₂)
  intro q s
  rcases q with t | t
  ·
    exact
      evalSPMF_map_eq_of_evalSPMF_eq
        ((evalSPMF_liftComp _).trans ((hh₁ t s.1).trans (evalSPMF_liftComp _).symm)) _
  ·
    exact
      evalSPMF_map_eq_of_evalSPMF_eq
        ((evalSPMF_liftComp _).trans ((hh₂ t s.2).trans (evalSPMF_liftComp _).symm)) _


-- @@ L225-225 verbatim
end ParCongr


-- @@ L227-227 verbatim
end DistEquiv


-- @@ L229-229 verbatim
end QueryImpl.Stateful
