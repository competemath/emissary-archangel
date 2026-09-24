module
public import Foundation.FirstOrder.Basic.Semantics.Semantics
public import Foundation.FirstOrder.Basic.Calculus

-- @@ L4-4 verbatim
@[expose] public section


-- @@ L6-6 verbatim
/-! # Soundness theorem for first-order classical logic -/


-- @@ L8-8 verbatim
namespace FFL.FirstOrder


-- @@ L10-10 verbatim
open Semiformula


-- @@ L12-12 verbatim
variable {L : Language}


-- @@ L14-66 verbatim
namespace Derivation

lemma sound {M : Type*} [s : Structure L M] [Nonempty M] (f : ℕ → M) {Γ : Sequent L} :
    ⊢ᴸᴷ¹ Γ → ∃ φ ∈ Γ, φ.Evalf f
  | identity r v => by
    by_cases h : s.rel r (Semiterm.val ![] f ∘ v)
    · exact ⟨rel r v, by simp, h⟩
    · exact ⟨nrel r v, by simp, h⟩
  | verum => ⟨⊤, by simp⟩
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d => by
    rcases sound f d with ⟨r, hr, hhr⟩
    rcases Multiset.mem_add.mp hr with hr | hr
    · exact ⟨r, by simp [hr], hhr⟩
    · rcases Multiset.mem_add.mp hr with hr | hr
      · have : r = φ := by simpa using hr
        subst r
        exact ⟨φ ⋎ ψ, by simp, by simp [hhr]⟩
      · have : r = ψ := by simpa using hr
        subst r
        exact ⟨φ ⋎ ψ, by simp, by simp [hhr]⟩
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq => by
    have : (∃ r ∈ Γ, Evalf f r) ∨ Evalf f φ := by simpa using sound f dp
    rcases this with (⟨r, hr, hhr⟩ | hp)
    · exact ⟨r, by simp [hr], hhr⟩
    · have : (∃ r ∈ Γ, Evalf f r) ∨ Evalf f ψ := by simpa using sound f dq
      rcases this with (⟨r, hr, hhr⟩ | hq)
      · exact ⟨r, by simp [hr], hhr⟩
      · exact ⟨φ ⋏ ψ, by simp, by simp [hp, hq]⟩
  | all (Γ := Γ) (φ := φ) d => by
    have : (∃ ψ ∈ Γ, Evalf f ψ) ∨ ∀ a : M, Eval ![a] f φ := by
      simpa [Rewriting.shifts, Matrix.vecConsLast_vecEmpty, forall_or_left]
        using fun a : M ↦ sound (a :>ₙ f) d
    rcases this with (⟨ψ, hq, hhq⟩ | hp)
    · exact ⟨ψ, by simp [hq], hhq⟩
    · exact ⟨∀¹ φ, by simp, hp⟩
  | exs (Γ := Γ) (φ := φ) (t := t) d => by
    have : (∃ φ ∈ Γ, Evalf f φ) ∨ Eval ![t.val ![] f] f φ := by
      simpa [eval_substs, Matrix.constant_eq_singleton] using sound f d
    rcases this with (⟨ψ, hq, hhq⟩ | hp)
    · exact ⟨ψ, by simp [hq], hhq⟩
    · exact ⟨∃¹ φ, by simp, t.val ![] f, hp⟩
  | contraction (Δ := Δ) (Γ := Γ) d ss => by
    have : ∃ φ ∈ Δ, Evalf f φ := sound f d
    rcases this with ⟨φ, hp, h⟩
    exact ⟨φ, ss hp, h⟩
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d dn => by
    have h : (∃ ψ ∈ Γ, Evalf f ψ) ∨ Evalf f φ := by simpa using sound f d
    have hn : (∃ ψ ∈ Δ, Evalf f ψ) ∨ ¬Evalf f φ := by simpa using sound f dn
    rcases h with (⟨ψ, h, hq⟩ | h)
    · exact ⟨ψ, by simp [h], hq⟩
    · rcases hn with (⟨ψ, hn, hq⟩ | hn)
      · exact ⟨ψ, by simp [hn], hq⟩
      · contradiction


-- @@ L68-70 verbatim
@[simp] lemma nil_empty : IsEmpty (⊢ᴸᴷ¹ (0 : Sequent L)) := by
  refine ⟨fun b ↦ ?_⟩
  simpa using sound (fun _ ↦ ()) b


-- @@ L72-72 verbatim
end Derivation


-- @@ L74-75 verbatim
theorem LK.Proof.sound {M : Type*} [s : Structure L M] [Nonempty M] {φ : Proposition L} (f : ℕ → M) :
    𝐋𝐊¹ ⊢ φ → φ.Evalf f := fun b ↦ by simpa using Derivation.sound f b.get


-- @@ L77-77 verbatim
variable {T U : Theory L}


-- @@ L79-79 verbatim
namespace Theory


-- @@ L81-96 verbatim
theorem Proof.sound_proposition {M : Type*} [s : Structure L M] [Nonempty M] :
    T ⊢ φ → M↓[L] ⊧* T → φ.Realize M := fun b H ↦ by
  rcases Proof.provable_iff.mp b with ⟨Γ, hΓ, ⟨b⟩⟩
  let f : ℕ → M := fun _ ↦ Nonempty.some inferInstance
  have : φ.Realize M ∨ ∃ ψ, ∼ψ ∈ Sequent.embed Γ ∧ ψ.Evalf f := by simpa using b.sound f
  rcases this with (h | ⟨ψ, hψ, h⟩)
  · assumption
  · have : ∃ χ : Sentence L, ∼χ ∈ Γ ∧ ↑χ = ψ := by
      have : ∃ χ ∈ Γ, χ = ∼ψ := by simpa [Sequent.embed] using hψ
      rcases this with ⟨χ, hχ, e⟩
      refine ⟨∼χ, by simpa using hχ, by simp [e]⟩
    rcases this with ⟨χ, hχ, rfl⟩
    have : χ.Realize M := by simpa using h
    have : ¬χ.Realize M := by
      simpa [models_iff] using H.models _ (hΓ _ hχ)
    contradiction


-- @@ L98-102 verbatim
/-- Soundness theorem for first-order logic. -/
theorem Proof.sound {φ : Sentence L} :
    T ⊢ φ → T ⊨[Struc.{v, u} L] φ := fun b s hS ↦ by
  simpa [struc_models_iff_models (s := s), models_iff]
    using Proof.sound_proposition b hS


-- @@ L104-104 verbatim
theorem Proof.sound_small : T ⊢ φ → T ⊨ φ := Proof.sound


-- @@ L106-109 verbatim
instance (T : Theory L) : Sound T (Semantics.models (Struc.{v, u} L) T) := ⟨Theory.Proof.sound⟩

lemma consistent_of_satisfiable (h : Semantics.Satisfiable (Struc.{v, u} L) T) : Entailment.Consistent T :=
  Sound.consistent_of_satisfiable h


-- @@ L111-111 verbatim
end Theory


-- @@ L113-113 verbatim
section model


-- @@ L115-118 verbatim
variable (T) (M : Type*) [Nonempty M] [Structure L M]

lemma consistent_of_model [hM : M↓[L] ⊧* T] :
    Entailment.Consistent T := Theory.consistent_of_satisfiable ⟨M↓[L], hM⟩


-- @@ L120-124 verbatim
variable {M}

lemma unprovable_of_countermodel [hM : M↓[L] ⊧* T] {φ} : M↓[L] ⊭ φ → T ⊬ φ := by
  contrapose!; intro h
  exact Theory.Proof.sound h hM


-- @@ L126-132 verbatim
variable {T}

lemma models_of_provable (hT : M↓[L] ⊧* T) {φ : Sentence L} (h : T ⊢ φ) :
    M↓[L] ⊧ φ := consequence_iff.mp (Theory.Proof.sound h) M inferInstance

lemma models_of_subtheory [T ⪯ U] : M↓[L] ⊧* U → M↓[L] ⊧* T :=
  fun hM ↦ ⟨fun _ hφ ↦ Theory.Proof.sound (Entailment.WeakerThan.pbl (Entailment.by_axm hφ)) hM⟩


-- @@ L134-134 verbatim
end model


-- @@ L136-136 verbatim
end FirstOrder


-- @@ L138-138 verbatim
end FFL


-- @@ L140-140 verbatim
end
