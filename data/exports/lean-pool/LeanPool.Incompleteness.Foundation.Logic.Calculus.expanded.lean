/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Basic


-- @@ L10-19 verbatim
/-!
# Sequent calculus and variants

This file defines a characterization of Tait style calculus and Gentzen style calculus.

## Main Definitions
* `LO.Tait`
* `LO.Gentzen`

-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace LO


-- @@ L25-28 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class OneSided (F : outParam Type*) (K : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Derivation : K → List F → Type*


-- @@ L30-31 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⟹ " => OneSided.Derivation


-- @@ L33-34 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.OneSided.Derivation₁ [OneSided F K] (𝓚 : K) (φ : F) : Type _ :=
  OneSided.Derivation 𝓚 [φ]


-- @@ L36-37 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⟹. " => OneSided.Derivation₁


-- @@ L39-40 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.OneSided.Derivable [OneSided F K] (𝓚 : K) (Δ : List F) : Prop :=
  Nonempty (OneSided.Derivation 𝓚 Δ)


-- @@ L42-43 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⟹! " => OneSided.Derivable


-- @@ L45-46 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.OneSided.Derivable₁ [OneSided F K] (𝓚 : K) (φ : F) : Prop :=
  Nonempty (OneSided.Derivation₁ 𝓚 φ)


-- @@ L48-49 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⟹!. " => OneSided.Derivable₁


-- @@ L51-55 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.OneSided.Derivable.get [OneSided F K] (𝓚 : K) (Δ : List F)
    (h : OneSided.Derivable 𝓚 Δ) : OneSided.Derivation 𝓚 Δ :=
  Classical.choice h


-- @@ L57-69 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Tait (F K : Type*) [LogicalConnective F] [DeMorgan F] [Collection F K] extends
    OneSided F K where
  /-- Imported declaration from the Incompleteness formalization. -/
  verum (𝓚 : K) (Δ : List F) : OneSided.Derivation 𝓚 (⊤ :: Δ)
  /-- Imported declaration from the Incompleteness formalization. -/
  and {𝓚 : K} {φ ψ : F} {Δ : List F} :
    OneSided.Derivation 𝓚 (φ :: Δ) →
      OneSided.Derivation 𝓚 (ψ :: Δ) → OneSided.Derivation 𝓚 (Wedge.wedge φ ψ :: Δ)
  /-- Imported declaration from the Incompleteness formalization. -/
  or {𝓚 : K} {φ ψ : F} {Δ : List F} :
    OneSided.Derivation 𝓚 (φ :: ψ :: Δ) → OneSided.Derivation 𝓚 (Vee.vee φ ψ :: Δ)
  /-- Imported declaration from the Incompleteness formalization. -/
  wk {𝓚 : K} {Δ Δ' : List F} : OneSided.Derivation 𝓚 Δ → Δ ⊆ Δ' → OneSided.Derivation 𝓚 Δ'
  /-- Imported declaration from the Incompleteness formalization. -/
  em {𝓚 : K} {φ} {Δ : List F} : φ ∈ Δ → Tilde.tilde φ ∈ Δ → OneSided.Derivation 𝓚 Δ


-- @@ L71-75 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Tait.Cut (F K : Type*) [LogicalConnective F] [DeMorgan F] [Collection F K]
    [Tait F K] where
  /-- Imported declaration from the Incompleteness formalization. -/
  cut {𝓚 : K} {Δ : List F} {φ} :
    OneSided.Derivation 𝓚 (φ :: Δ) →
      OneSided.Derivation 𝓚 (Tilde.tilde φ :: Δ) → OneSided.Derivation 𝓚 Δ


-- @@ L77-83 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Tait.Axiomatized (F K : Type*) [LogicalConnective F] [DeMorgan F] [Collection F K]
    [Tait F K] where
  /-- Imported declaration from the Incompleteness formalization. -/
  root {𝓚 : K} {φ} : φ ∈ 𝓚 → OneSided.Derivation₁ 𝓚 φ
  /-- Imported declaration from the Incompleteness formalization. -/
  trans {𝓚 𝓛 : K} {Γ} :
    ((ψ : F) → ψ ∈ 𝓚 → OneSided.Derivation₁ 𝓛 ψ) → OneSided.Derivation 𝓚 Γ → OneSided.Derivation 𝓛 Γ


-- @@ L85-85 verbatim
variable {F S K : Type*} [LogicalConnective F] [Collection F K]


-- @@ L87-87 verbatim
namespace OneSided


-- @@ L89-89 verbatim
variable [OneSided F K] {𝓚 : K} {Γ Δ : List F}


-- @@ L91-92 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev cast (d : OneSided.Derivation 𝓚 Δ) (e : Δ = Γ) : OneSided.Derivation 𝓚 Γ :=
  cast (congrArg _ e) d


-- @@ L94-94 verbatim
end OneSided


-- @@ L96-96 verbatim
namespace Tait


-- @@ L98-98 verbatim
open Entailment


-- @@ L100-100 verbatim
variable [DeMorgan F] [Tait F K]


-- @@ L102-102 verbatim
variable {𝓚 : K} {Γ Δ : List F} {φ ψ φ₁ φ₂ φ₃ φ₄ : F}


-- @@ L104-105 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ofEq (b : OneSided.Derivation 𝓚 Γ) (h : Γ = Δ) : OneSided.Derivation 𝓚 Δ :=
  h ▸ b


-- @@ L107-107 expanded
lemma of_eq (b : OneSided.Derivable 𝓚 Γ) (h : Γ = Δ) : OneSided.Derivable 𝓚 Δ :=
  h ▸ b


-- @@ L109-110 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def verum' (h : ⊤ ∈ Γ := by simp) : OneSided.Derivation 𝓚 Γ :=
  wk (verum 𝓚 Γ) (by simp [h])


-- @@ L112-112 expanded
lemma verum! (𝓚 : K) (Γ : List F) : OneSided.Derivable 𝓚 (⊤ :: Γ) :=
  ⟨verum _ _⟩


-- @@ L114-114 expanded
lemma verum'! (h : ⊤ ∈ Γ) : OneSided.Derivable 𝓚 Γ :=
  ⟨verum' h⟩


-- @@ L116-116 expanded
lemma and! (hp : OneSided.Derivable 𝓚 (φ :: Γ)) (hq : OneSided.Derivable 𝓚 (ψ :: Γ)) :
    OneSided.Derivable 𝓚 (Wedge.wedge φ ψ :: Γ) :=
  ⟨and hp.get hq.get⟩


-- @@ L118-118 expanded
lemma or! (h : OneSided.Derivable 𝓚 (φ :: ψ :: Γ)) : OneSided.Derivable 𝓚 (Vee.vee φ ψ :: Γ) :=
  ⟨or h.get⟩


-- @@ L120-120 expanded
lemma wk! (h : OneSided.Derivable 𝓚 Γ) (ss : Γ ⊆ Δ) : OneSided.Derivable 𝓚 Δ :=
  ⟨wk h.get ss⟩


-- @@ L122-122 expanded
lemma em! (hp : φ ∈ Γ) (hn : Tilde.tilde φ ∈ Γ) : OneSided.Derivable 𝓚 Γ :=
  ⟨em hp hn⟩


-- @@ L124-125 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def close (φ : F) (hp : φ ∈ Γ := by simp) (hn : Tilde.tilde φ ∈ Γ := by simp) :
    OneSided.Derivation 𝓚 Γ :=
  em hp hn


-- @@ L127-127 expanded
lemma close! (φ : F) (hp : φ ∈ Γ := by simp) (hn : Tilde.tilde φ ∈ Γ := by simp) :
    OneSided.Derivable 𝓚 Γ :=
  em! hp hn


-- @@ L129-131 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def and' {φ ψ : F} (h : Wedge.wedge φ ψ ∈ Γ) (dp : OneSided.Derivation 𝓚 (φ :: Γ))
    (dq : OneSided.Derivation 𝓚 (ψ :: Γ)) : OneSided.Derivation 𝓚 Γ :=
  wk (and dp dq) (by simp [h])


-- @@ L133-134 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def or' {φ ψ : F} (h : Vee.vee φ ψ ∈ Γ) (dpq : OneSided.Derivation 𝓚 (φ :: ψ :: Γ)) :
    OneSided.Derivation 𝓚 Γ :=
  wk (or dpq) (by simp [h])


-- @@ L136-137 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def wkTail (d : OneSided.Derivation 𝓚 Γ) : OneSided.Derivation 𝓚 (φ :: Γ) :=
  wk d (by simp)


-- @@ L139-140 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def rotate₁ (d : OneSided.Derivation 𝓚 (φ₂ :: φ₁ :: Γ)) : OneSided.Derivation 𝓚 (φ₁ :: φ₂ :: Γ) :=
  wk d (by simp)


-- @@ L142-146 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def rotate₂ (d : OneSided.Derivation 𝓚 (φ₃ :: φ₁ :: φ₂ :: Γ)) :
    OneSided.Derivation 𝓚 (φ₁ :: φ₂ :: φ₃ :: Γ) :=
  wk d
    (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, true_and]
      apply List.subset_cons_of_subset _ (List.subset_cons_of_subset _ <| by simp))


-- @@ L148-153 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def rotate₃ (d : OneSided.Derivation 𝓚 (φ₄ :: φ₁ :: φ₂ :: φ₃ :: Γ)) :
    OneSided.Derivation 𝓚 (φ₁ :: φ₂ :: φ₃ :: φ₄ :: Γ) :=
  wk d
    (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, true_and]
      apply
        List.subset_cons_of_subset _
          (List.subset_cons_of_subset _ <| List.subset_cons_of_subset _ <| by simp))


-- @@ L155-155 verbatim
variable {𝓚 𝓛 : K} {Γ : List F}


-- @@ L157-157 verbatim
alias cut := Tait.Cut.cut


-- @@ L159-159 verbatim
alias root := Tait.Axiomatized.root


-- @@ L161-161 expanded
lemma cut! [Tait.Cut F K] (hp : OneSided.Derivable 𝓚 (φ :: Δ))
    (hn : OneSided.Derivable 𝓚 (Tilde.tilde φ :: Δ)) : OneSided.Derivable 𝓚 Δ :=
  ⟨cut hp.get hn.get⟩


-- @@ L163-163 expanded
lemma root! [Tait.Axiomatized F K] {φ} (h : φ ∈ 𝓚) : OneSided.Derivable₁ 𝓚 φ :=
  ⟨root h⟩


-- @@ L165-168 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def byAxm [Tait.Axiomatized F K] (φ) (h : φ ∈ 𝓚) (hΓ : φ ∈ Γ := by simp) :
    OneSided.Derivation 𝓚 Γ :=
  wk (root h) (by simp_all)


-- @@ L170-172 expanded
lemma byAxm! [Tait.Axiomatized F K] (φ) (h : φ ∈ 𝓚) (hΓ : φ ∈ Γ := by simp) :
    OneSided.Derivable 𝓚 Γ :=
  ⟨byAxm φ h hΓ⟩


-- @@ L174-176 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ofAxiomSubset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) :
    OneSided.Derivation 𝓚 Γ → OneSided.Derivation 𝓛 Γ :=
  Tait.Axiomatized.trans fun _ hq ↦ Tait.Axiomatized.root (Collection.subset_iff.mp h _ hq)


-- @@ L178-180 expanded
lemma of_axiom_subset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) :
    OneSided.Derivable 𝓚 Γ → OneSided.Derivable 𝓛 Γ := fun b ↦ ⟨ofAxiomSubset h b.get⟩


-- @@ L182-182 expanded
instance system : Entailment F K :=
  ⟨(OneSided.Derivation₁ · ·)⟩


-- @@ L184-186 verbatim
instance [Tait.Axiomatized F K] : Entailment.Axiomatized K where
  prfAxm := fun hf ↦ Tait.Axiomatized.root <| hf
  weakening := Tait.ofAxiomSubset


-- @@ L188-189 expanded
lemma provable_bot_iff_derivable_nil [Tait.Cut F K] : OneSided.Derivable 𝓚 [] ↔ Provable 𝓚 ⊥ :=
  ⟨fun b ↦ wk! b (by simp), fun b ↦ cut! b (by simpa using verum! _ _)⟩


-- @@ L191-193 expanded
lemma waekerThan_of_subset [Tait.Axiomatized F K] (h : 𝓚 ⊆ 𝓛) : WeakerThan 𝓚 𝓛 :=
  ⟨fun _ ↦ Entailment.Axiomatized.weakening! h⟩


-- @@ L195-196 verbatim
instance [Tait.Axiomatized F K] : Entailment.StrongCut K K where
  cut {_ _ _ bs b} := Tait.Axiomatized.trans (fun _ hq ↦ bs hq) b


-- @@ L198-199 verbatim
instance [Tait.Cut F K] : DeductiveExplosion K where
  dexp {𝓚 b φ} := wk (Tait.Cut.cut b (by simpa using verum _ _)) (by simp)


-- @@ L201-204 expanded
lemma inconsistent_iff_provable [Tait.Cut F K] : Inconsistent 𝓚 ↔ OneSided.Derivable 𝓚 [] :=
  ⟨fun b ↦ ⟨cut (inconsistent_iff_provable_bot.mp b).get (by simpa using verum _ _)⟩, fun h ↦
    inconsistent_iff_provable_bot.mpr (wk! h (by simp))⟩


-- @@ L206-208 expanded
lemma consistent_iff_unprovable [Tait.Cut F K] :
    Consistent 𝓚 ↔ IsEmpty (OneSided.Derivation 𝓚 []) :=
  not_iff_not.mp <| by simp [not_consistent_iff_inconsistent, inconsistent_iff_provable]


-- @@ L210-254 expanded
instance [Tait.Cut F K] : Entailment.Classical 𝓚
    where
  mdp
    {φ ψ dpq
      dp} :=
    let dpq : OneSided.Derivation 𝓚 [Vee.vee (Tilde.tilde φ) ψ, ψ] :=
      wk dpq (by simp [DeMorgan.imply])
    let dnq : OneSided.Derivation 𝓚 [Tilde.tilde (Vee.vee (Tilde.tilde φ) ψ), ψ] :=
      let d : OneSided.Derivation 𝓚 [Wedge.wedge φ (Tilde.tilde ψ), ψ] :=
        and (wk dp <| by simp) (close ψ)
      ofEq d (by simp)
    cut dpq dnq
  negEquiv
    φ :=
    ofEq
      (show
        Entailment.Prf 𝓚
          (Wedge.wedge (Vee.vee φ (Vee.vee (Tilde.tilde φ) ⊥))
            (Vee.vee (Wedge.wedge φ ⊤) (Tilde.tilde φ)))
        from and (or <| rotate₁ <| or <| close φ) (or <| and (close φ) verum'))
      (by simp [Axioms.NegEquiv, DeMorgan.imply, LogicalConnective.iff])
  verum := verum _ _
  imply₁ φ
    ψ :=
    have : Entailment.Prf 𝓚 (Vee.vee (Tilde.tilde φ) (Vee.vee (Tilde.tilde ψ) φ)) :=
      or <| rotate₁ <| or <| close φ
    ofEq this (by simp [DeMorgan.imply])
  imply₂ φ ψ
    χ :=
    have :
      Entailment.Prf 𝓚
        (Vee.vee (Wedge.wedge φ (Wedge.wedge ψ (Tilde.tilde χ)))
          (Vee.vee (Wedge.wedge φ (Tilde.tilde ψ)) (Vee.vee (Tilde.tilde φ) χ))) :=
      or <|
        rotate₁ <|
          or <|
            rotate₁ <|
              or <| rotate₃ <| and (close φ) (and (rotate₃ <| and (close φ) (close ψ)) (close χ))
    ofEq this (by simp [DeMorgan.imply])
  and₁ φ
    ψ :=
    have : Entailment.Prf 𝓚 (Vee.vee (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ)) φ) :=
      or <| or <| close φ
    ofEq this (by simp [DeMorgan.imply])
  and₂ φ
    ψ :=
    have : Entailment.Prf 𝓚 (Vee.vee (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ)) ψ) :=
      or <| or <| close ψ
    ofEq this (by simp [DeMorgan.imply])
  and₃ φ
    ψ :=
    have : Entailment.Prf 𝓚 (Vee.vee (Tilde.tilde φ) (Vee.vee (Tilde.tilde ψ) (Wedge.wedge φ ψ))) :=
      or <| rotate₁ <| or <| rotate₁ <| and (close φ) (close ψ)
    ofEq this (by simp [DeMorgan.imply])
  or₁ φ
    ψ :=
    have : Entailment.Prf 𝓚 (Vee.vee (Tilde.tilde φ) (Vee.vee φ ψ)) :=
      or <| rotate₁ <| or <| close φ
    ofEq this (by simp [DeMorgan.imply])
  or₂ φ
    ψ :=
    have : Entailment.Prf 𝓚 (Vee.vee (Tilde.tilde ψ) (Vee.vee φ ψ)) :=
      or <| rotate₁ <| or <| close ψ
    ofEq this (by simp [DeMorgan.imply])
  or₃ φ ψ
    χ :=
    have :
      Entailment.Prf 𝓚
        (Vee.vee (Wedge.wedge φ (Tilde.tilde χ))
          (Vee.vee (Wedge.wedge ψ (Tilde.tilde χ))
            (Vee.vee (Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ)) χ))) :=
      or <|
        rotate₁ <|
          or <|
            rotate₁ <|
              or <| and (rotate₃ <| and (close φ) (close χ)) (rotate₂ <| and (close ψ) (close χ))
    ofEq this (by simp [DeMorgan.imply])
  dne
    φ :=
    have : Entailment.Prf 𝓚 (Vee.vee (Tilde.tilde φ) φ) := or <| close φ
    ofEq this (by simp [DeMorgan.imply])


-- @@ L256-256 verbatim
end Tait


-- @@ L258-258 verbatim
end LO
