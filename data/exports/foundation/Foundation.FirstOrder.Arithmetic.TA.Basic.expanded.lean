module

public import Foundation.FirstOrder.Arithmetic.Basic


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-6 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L8-8 verbatim
abbrev FirstOrderTrueArith : ArithmeticTheory := Structure.theory ℒₒᵣ ℕ


-- @@ L10-10 verbatim
notation "𝗧𝗔" => FirstOrderTrueArith


-- @@ L12-12 verbatim
namespace TA


-- @@ L14-19 verbatim
instance : ℕ↓[ℒₒᵣ] ⊧* 𝗧𝗔 :=
  models_theory_iff.mpr fun {φ} ↦ by simp

lemma provable_iff {φ : ArithmeticSentence} :
    𝗧𝗔 ⊢ φ ↔ ℕ↓[ℒₒᵣ] ⊧ φ :=
  ⟨fun h ↦ consequence_iff'.mp (Theory.Proof.sound h) ℕ, fun h ↦ Entailment.by_axm h⟩


-- @@ L21-24 verbatim
instance (T : ArithmeticTheory) [ℕ↓[ℒₒᵣ] ⊧* T] : T ⪯ 𝗧𝗔 := ⟨by
  rintro φ h
  have : ℕ↓[ℒₒᵣ] ⊧ φ := consequence_iff'.mp (Theory.Proof.sound h) ℕ
  exact provable_iff.mpr this⟩


-- @@ L26-26 verbatim
end TA


-- @@ L28-28 verbatim
end FFL.FirstOrder.Arithmetic
