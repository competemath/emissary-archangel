/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Semantics.Semantics
public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Calculus


-- @@ L11-11 verbatim
/-! # Soundness -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO


-- @@ L18-18 verbatim
namespace FirstOrder


-- @@ L20-20 verbatim
section «lp_section_1»

-- @@ L21-21 verbatim
open Semiformula


-- @@ L23-23 verbatim
variable {L : Language} {T : Theory L}


-- @@ L25-25 verbatim
namespace Derivation


-- @@ L27-67 expanded
lemma sound (M : Type*) [s : Structure L M] [Nonempty M] [ModelsTheory M T] (ε : ℕ → M)
    {Γ : Sequent L} : OneSided.Derivation T Γ → ∃ φ ∈ Γ, Evalfm M ε φ
  | @axL _ _ Δ _ r v => by
    by_cases h : s.rel r (Semiterm.valm M ![] ε ∘ v)
    · exact ⟨rel r v, by simp, h⟩
    · exact ⟨nrel r v, by simp, h⟩
  | verum Δ => ⟨⊤, by simp⟩
  | @or _ _ Δ φ ψ d =>
    by
    have : Evalfm M ε φ ∨ Evalfm M ε ψ ∨ ∃ ψ ∈ Δ, Evalfm M ε ψ := by simpa using sound M ε d
    rcases this with (hp | hq | ⟨r, hr, hhr⟩)
    · exact ⟨Vee.vee φ ψ, by simp, by simp [hp]⟩
    · exact ⟨Vee.vee φ ψ, by simp, by simp [hq]⟩
    · exact ⟨r, by simp [hr], hhr⟩
  | @and _ _ Δ φ ψ dp dq =>
    by
    have : Evalfm M ε φ ∨ ∃ r ∈ Δ, Evalfm M ε r := by simpa using sound M ε dp
    rcases this with (hp | ⟨r, hr, hhr⟩)
    · have : Evalfm M ε ψ ∨ ∃ r ∈ Δ, Evalfm M ε r := by simpa using sound M ε dq
      simp_all
    · exact ⟨r, by simp [hr], hhr⟩
  | @all _ _ Δ φ d =>
    by
    have : (∀ a : M, Evalm M ![a] ε φ) ∨ ∃ ψ ∈ Δ, Evalfm M ε ψ := by
      simpa [Rewriting.shifts, Matrix.vecConsLast_vecEmpty, forall_or_right] using fun a : M =>
        sound M (cases a ε) d
    simp_all
  | @ex _ _ Δ φ t d =>
    by
    have : Evalm M ![t.valm M ![] ε] ε φ ∨ ∃ φ ∈ Δ, Evalfm M ε φ := by
      simpa [eval_substs, Matrix.constant_eq_singleton] using sound M ε d
    rcases this with (hp | ⟨ψ, hq, hhq⟩)
    · exact ⟨ExQuantifier.ex φ, by simp, t.valm M ![] ε, hp⟩
    · exact ⟨ψ, by simp [hq], hhq⟩
  | @wk _ _ Γ Δ d ss => by
    have : ∃ φ ∈ Δ, Evalfm M ε φ := sound M ε d
    rcases this with ⟨φ, hp, h⟩
    exact ⟨φ, ss hp, h⟩
  | @cut _ _ Δ φ d dn =>
    by
    have h : Evalfm M ε φ ∨ ∃ ψ ∈ Δ, Evalfm M ε ψ := by simpa using sound M ε d
    have hn : ¬Evalfm M ε φ ∨ ∃ ψ ∈ Δ, Evalfm M ε ψ := by simpa using sound M ε dn
    rcases h with (h | ⟨ψ, h, hq⟩)
    · simp_all
    · exact ⟨ψ, by simp [h], hq⟩
  | root (φ := φ) h => ⟨φ, by simp, Theory.models M T h ε⟩


-- @@ L69-69 verbatim
end Derivation


-- @@ L71-71 verbatim
variable {φ : SyntacticFormula L}


-- @@ L73-78 expanded
theorem sound : Entailment.Prf T φ → Consequence (Struc.{v, u} L) T φ := fun b s hT f ↦
  by
  have : ModelsTheory s.Dom T := hT
  rcases Derivation.sound s.Dom f b with ⟨ψ, hp, h⟩
  have : ψ = φ := by simpa using hp
  rcases this
  exact h


-- @@ L80-80 expanded
theorem sound! : Provable T φ → Consequence (Struc.{v, u} L) T φ := fun ⟨b⟩ ↦ sound b


-- @@ L82-82 expanded
theorem sound₀ : Entailment.Prf T φ → Consequence T φ :=
  sound


-- @@ L84-84 expanded
theorem sound₀! : Provable T φ → Consequence T φ :=
  sound!


-- @@ L86-86 verbatim
instance (T : Theory L) : Sound T (Semantics.models (Struc.{v, u} L) T) := ⟨sound!⟩


-- @@ L88-93 expanded
lemma models_of_subtheory {T U : Theory L} [WeakerThan U T] {M : Type*} [Structure L M] [Nonempty M]
    (hM : ModelsTheory M T) : ModelsTheory M U :=
  ⟨fun {φ} hp ↦
    by
    have : Provable T φ := (inferInstance : WeakerThan U T).pbl (Entailment.by_axm _ hp)
    exact sound! this hM⟩


-- @@ L95-96 verbatim
lemma consistent_of_satidfiable (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    Entailment.Consistent T := Sound.consistent_of_satisfiable h


-- @@ L98-102 expanded
lemma unprovable_of_countermodel {M : Type*} [s : Structure L M] [Nonempty M]
    [hM : ModelsTheory M T] (f : ℕ → M) (φ : SyntacticFormula L) (c : ¬Semiformula.Evalfm M f φ) :
    Unprovable T φ :=
  by
  apply Sound.not_provable_of_countermodel (𝓜 := Semantics.models (Struc L) T) (𝓢 := T)
  intro h
  exact c (h hM f)


-- @@ L104-104 verbatim
end «lp_section_1»


-- @@ L106-106 verbatim
end FirstOrder


-- @@ L108-108 verbatim
end LO
