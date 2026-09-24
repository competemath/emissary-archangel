module
public import Foundation.FirstOrder.Basic.Semantics.Semantics
public import Foundation.FirstOrder.Basic.Calculus

-- @@ L4-4 verbatim
@[expose] public section


-- @@ L6-6 verbatim
namespace FFL.FirstOrder


-- @@ L8-8 verbatim
variable {L : Language} {ξ : Type*}


-- @@ L10-10 verbatim
namespace Semiformula


-- @@ L12-12 verbatim
def padding (φ : Semiformula L ξ n) (k : ℕ) := φ ⋏ (List.replicate k ⊤).conj


-- @@ L14-17 verbatim
def getPaddingAux : Semiformula L ξ n → Option ℕ
  |     ⊤ => some 0
  | ⊤ ⋏ φ => φ.getPaddingAux.map fun x ↦ x + 1
  |     _ => none


-- @@ L19-21 verbatim
def getPadding : Semiformula L ξ n → Option ℕ
  | _ ⋏ φ => φ.getPaddingAux
  |     _ => none


-- @@ L23-25 verbatim
def getPaddingFormula : Semiformula L ξ n → Option (Semiformula L ξ n)
  | φ ⋏ _ => some φ
  |     _ => none


-- @@ L27-29 verbatim
@[simp] lemma getPadding_padding (φ : Semiformula L ξ n) : (φ.padding k).getPadding = some k := by
  suffices (List.replicate k (⊤ : Semiformula L ξ n)).conj.getPaddingAux = some k by simpa [getPadding, padding]
  induction k <;> simp [List.replicate_succ, getPaddingAux, *]


-- @@ L31-32 verbatim
@[simp] lemma getPaddingFormula_padding (φ : Semiformula L ξ n) : (φ.padding k).getPaddingFormula = some φ := by
  simp [padding, getPaddingFormula]


-- @@ L34-36 verbatim
@[simp] lemma padding_injective_iff {φ ψ : Semiformula L ξ n} :
    φ.padding k = ψ.padding m ↔ φ = ψ ∧ k = m :=
  ⟨fun h ↦ ⟨by simpa using congr_arg getPaddingFormula h, by simpa using congr_arg getPadding h⟩, by rintro ⟨rfl, rfl⟩; rfl⟩


-- @@ L38-41 verbatim
@[simp] lemma rew_padding (ω : Rew L ξ n ξ' n') (φ : Semiformula L ξ n) :
    ω ▹ φ.padding k = (ω ▹ φ).padding k := by
  simp [padding]
  induction k <;> simp [List.replicate_succ, *]


-- @@ L43-43 verbatim
end Semiformula


-- @@ L45-45 verbatim
open Entailment


-- @@ L47-57 verbatim
def Entailment.paddingIff [L.DecidableEq] [DecidableEq ξ] [Entailment S (Formula L ξ)] {𝓢 : S} [Entailment.Minimal 𝓢] (φ k) :
    𝓢 ⊢! φ.padding k 🡘 φ := by
  apply E!_intro
  · apply and₁!
  · apply right_K!_intro
    · apply C!_id
    · apply dhyp!
      apply Conj!_intro
      intro φ hφ
      have : k ≠ 0 ∧ φ = ⊤ := by simpa using hφ;
      exact this.2 ▸ HasAxiomVerum.verum!


-- @@ L59-60 verbatim
@[simp] theorem Entailment.padding_iff [L.DecidableEq] [DecidableEq ξ] [Entailment S (Formula L ξ)] {𝓢 : S} [Entailment.Minimal 𝓢] (φ k) :
    𝓢 ⊢ φ.padding k 🡘 φ := ⟨paddingIff φ k⟩


-- @@ L62-62 verbatim
end FFL.FirstOrder


-- @@ L64-64 verbatim
end
