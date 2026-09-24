module

public import Foundation.FirstOrder.Arithmetic.Prenex


-- @@ L5-10 verbatim
/-!
# Prenex normal form theorem over $\mathsf{I\Sigma_1}$

Every `Hierarchy 𝚺 1` formula is `𝗜𝚺₁`-provably equivalent to a formula of the form `∃¹ θ`
with `θ` in `Hierarchy 𝚺 0`, and dually for `Hierarchy 𝚷 1` and `∀¹ θ`.
-/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
open FFL

-- @@ L15-15 verbatim
open FFL.FirstOrder


-- @@ L17-17 verbatim
namespace FFL.FirstOrder.Arithmetic.ISigma1


-- @@ L19-37 verbatim
variable {n : ℕ} {φ : ArithmeticSemisentence n} {σ : ArithmeticSentence}

lemma hasPrenex (h : Hierarchy 𝚺 1 φ) :
    ∃ φ' : Prenex 𝚺 1 Empty n, 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 φ'.val) :=
  exists_prenex_of_hierarchy 𝗜𝚺₁ h

lemma exists_matrix_provable (h : Hierarchy 𝚺 1 φ) :
    ∃ θ : 𝚺₀.Semisentence (n + 1), 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∃¹ θ.val) := by
  obtain ⟨φ', hφ'⟩ := hasPrenex h;
  exact ⟨φ'.sigmaInv.matrix, Prenex.provable_iff_sigmaInv hφ'⟩

lemma exists_matrix_provable_pi (h : Hierarchy 𝚷 1 φ) :
    ∃ θ : 𝚺₀.Semisentence (n + 1), 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∀¹ θ.val) := by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_hierarchy 𝗜𝚺₁ h
  exact ⟨φ'.piInv.matrix, Prenex.provable_iff_piInv hφ'⟩

lemma exists_matrix_provable_of_sentence (h : Hierarchy 𝚺 1 σ) :
    ∃ θ : 𝚺₀.Semisentence 1, 𝗜𝚺₁ ⊢ σ 🡘 ∃¹ θ.val :=
  exists_matrix_provable h


-- @@ L39-39 verbatim
end FFL.FirstOrder.Arithmetic.ISigma1
