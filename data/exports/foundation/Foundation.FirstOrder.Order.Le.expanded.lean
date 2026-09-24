module

public import Foundation.FirstOrder.Completeness


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-6 verbatim
namespace FFL


-- @@ L8-8 verbatim
namespace FirstOrder


-- @@ L10-10 verbatim
variable {L : Language.{u}} [Semiformula.Operator.Eq L] [Semiformula.Operator.LT L]


-- @@ L12-12 verbatim
open Semiformula


-- @@ L14-17 verbatim
def LT.le : Operator L 2 := Semiformula.Operator.Eq.eq.or Semiformula.Operator.LT.lt

lemma le_eq (t₁ t₂ : Semiterm L μ n) : LT.le.operator ![t₁, t₂] = “!!t₁ = !!t₂ ∨ !!t₁ < !!t₂” := by
  simp [Operator.operator, Operator.or, LT.le, ←TransitiveRewriting.comp_app]


-- @@ L19-19 verbatim
namespace Order

-- @@ L20-20 verbatim
variable {T : Theory L} [𝗘𝗤 L ⪯ T]


-- @@ L22-22 verbatim
omit [𝗘𝗤 L ⪯ T] in

-- @@ L23-35 verbatim
theorem leIffEqOrLt : T ⊢ “∀ x y, x ≤ y ↔ x = y ∨ x < y” :=
  Theory.Proof.small_complete
    <| consequence_iff.mpr fun _ ↦ by simp [models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT]

lemma complete (φ : Sentence L)
  (H : ∀ (M : Type (max u w))
      [Nonempty M] [LT M]
      [Structure L M] [Structure.Eq L M] [Structure.LT L M]
      [M↓[L] ⊧* T],
      M↓[L] ⊧ φ) :
    T ⊢ φ := Theory.Proof.complete <| consequence_iff_eq.mpr fun M _ _ _ hT ↦
  letI : (Structure.Model L M)↓[L] ⊧* T := Structure.ElementaryEquiv.modelsTheory.mp hT
  Structure.ElementaryEquiv.models.mpr (H (Structure.Model L M))


-- @@ L37-37 verbatim
end Order


-- @@ L39-39 verbatim
end FirstOrder


-- @@ L41-41 verbatim
end FFL
