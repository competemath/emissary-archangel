module

public import Foundation.FirstOrder.Arithmetic.Basic.Misc


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-6 verbatim
namespace FFL.FirstOrder


-- @@ L8-8 verbatim
namespace Structure


-- @@ L10-11 verbatim
class Monotone (L : Language) (M : Type*) [LE M] [Structure L M] where
  monotone : ∀ {k} (f : L.Func k) (v₁ v₂ : Fin k → M), (∀ i, v₁ i ≤ v₂ i) → Structure.func f v₁ ≤ Structure.func f v₂


-- @@ L13-13 verbatim
namespace Monotone


-- @@ L15-20 verbatim
variable {L : Language} {M : Type*} [LE M] [Structure L M] [Monotone L M]

lemma term_monotone (t : Semiterm L ξ n) {fv₁ fv₂ : Fin n → M} {bv₁ bv₂ : ξ → M}
    (he : ∀ i, fv₁ i ≤ fv₂ i) (hε : ∀ i, bv₁ i ≤ bv₂ i) :
    t.val fv₁ bv₁ ≤ t.val fv₂ bv₂ := by
  induction t <;> simp [*, Semiterm.val_func, Monotone.monotone]


-- @@ L22-22 verbatim
end Monotone


-- @@ L24-24 verbatim
end Structure


-- @@ L26-26 verbatim
end FirstOrder
