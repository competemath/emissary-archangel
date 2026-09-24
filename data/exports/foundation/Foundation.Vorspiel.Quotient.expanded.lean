module

public import Foundation.Vorspiel.Fin.Matrix


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace Quotient

-- @@ L8-8 verbatim
open Matrix

-- @@ L9-9 verbatim
variable {α : Type u} [s : Setoid α] {β : Sort v}


-- @@ L11-14 verbatim
@[elab_as_elim]
lemma inductionOnVec {φ : (Fin n → Quotient s) → Prop} (v : Fin n → Quotient s)
  (h : ∀ v : Fin n → α, φ (fun i => Quotient.mk s (v i))) : φ v :=
  Quotient.induction_on_pi v h


-- @@ L16-26 verbatim
def liftVec : ∀ {n} (f : (Fin n → α) → β),
  (∀ v₁ v₂ : Fin n → α, (∀ n, v₁ n ≈ v₂ n) → f v₁ = f v₂) → (Fin n → Quotient s) → β
| 0,     f, _, _ => f ![]
| n + 1, f, h, v =>
  let ih : α → (Fin n → Quotient s) → β :=
    fun a v => liftVec (n := n) (fun v => f (a :> v))
      (fun v₁ v₂ hv => h (a :> v₁) (a :> v₂) (Fin.cases (by simp [cons_val_zero, Setoid.refl]) hv)) v
  Quot.liftOn (vecHead v) (ih · (vecTail v))
    (fun a b hab => by
      have : ∀ v, f (a :> v) = f (b :> v) := fun v ↦ h _ _ (Fin.cases hab (by simp [cons_val_succ, Setoid.refl]))
      simp [this, ih])


-- @@ L28-34 verbatim
@[simp] lemma liftVec_zero (f : (Fin 0 → α) → β) (h) (v : Fin 0 → Quotient s) : liftVec f h v = f ![] := rfl

lemma liftVec_mk {n} (f : (Fin n → α) → β) (h) (v : Fin n → α) :
    liftVec f h (Quotient.mk s ∘ v) = f v := by
  induction' n with n ih <;> simp [liftVec, empty_eq]
  simpa using! ih (fun v' => f (vecHead v :> v'))
    (fun v₁ v₂ hv => h (vecHead v :> v₁) (vecHead v :> v₂) (Fin.cases (refl _) hv)) (vecTail v)


-- @@ L36-37 verbatim
@[simp] lemma liftVec_mk₁ (f : (Fin 1 → α) → β) (h) (a : α) :
    liftVec f h ![Quotient.mk s a] = f ![a] := liftVec_mk f h ![a]


-- @@ L39-40 verbatim
@[simp] lemma liftVec_mk₂ (f : (Fin 2 → α) → β) (h) (a₁ a₂ : α) :
    liftVec f h ![Quotient.mk s a₁, Quotient.mk s a₂] = f ![a₁, a₂] := liftVec_mk f h ![a₁, a₂]


-- @@ L42-42 verbatim
end Quotient


-- @@ L44-44 verbatim
end
