/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Basic


-- @@ L10-35 verbatim
/-!
# Equivalences of Polynomial Functors

This file defines equivalences between polynomial functors and proves basic properties about them.

An equivalence between two polynomial functors `P` and `Q`, written `P ≃ₚ Q`, is given by an
equivalence of the `A` types and an equivalence between the `B` types for each `a : A`.

We provide various canonical equivalences for operations on polynomial functors, such as:
- Sum operations: `P + 0 ≃ₚ P`, `0 + P ≃ₚ P`
- Product operations and their properties
- Equivalences for sigma and pi constructions
- Universe lifting equivalences
- Tensor product equivalences
- Composition equivalences

## Main definitions

- `PFunctor.Equiv`: An equivalence between two polynomial functors
- `≃ₚ`: Notation for polynomial functor equivalences

## Main results

- Basic equivalence properties: reflexivity, symmetry, transitivity
- Canonical equivalences for sum, product, and other constructions on polynomial functors
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
universe u v uA uB uA' uB' uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄


-- @@ L41-41 verbatim
section find_home


-- @@ L43-45 verbatim
instance instIsEmptySigma {α : Sort u} {β : α → Sort v} [inst : IsEmpty α] :
    IsEmpty ((a : α) ×' β a) where
  false := fun a => inst.elim a.1


-- @@ L47-47 verbatim
end find_home


-- @@ L49-49 verbatim
namespace PFunctor


-- @@ L51-51 verbatim
namespace Equiv


-- @@ L53-53 verbatim
section Sum


-- @@ L55-56 verbatim
variable (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB})
  (R : PFunctor.{uA₃, uB}) (S : PFunctor.{uA₄, uB})


-- @@ L58-62 verbatim
/-- Addition with the zero functor on the left is equivalent to the original functor -/
@[simps]
def sumZero : P + 0 ≃ₚ P where
  equivA := Equiv.sumEmpty P.A PEmpty
  equivB := (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun a => a.elim))


-- @@ L64-68 verbatim
/-- Addition with the zero functor on the right is equivalent to the original functor -/
@[simps]
def zeroSum : 0 + P ≃ₚ P where
  equivA := Equiv.emptySum PEmpty P.A
  equivB := (Sum.casesOn · (fun a => a.elim) (fun _ => _root_.Equiv.refl _))


-- @@ L70-74 verbatim
/-- Sum of polynomial functors is commutative up to equivalence -/
@[simps]
def sumComm : (P + Q : PFunctor.{max uA₁ uA₂, uB}) ≃ₚ (Q + P : PFunctor.{max uA₁ uA₂, uB}) where
  equivA := _root_.Equiv.sumComm P.A Q.A
  equivB := (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _))


-- @@ L76-84 verbatim
/-- Sum of polynomial functors is associative up to equivalence -/
@[simps]
def sumAssoc :
    ((P + Q) + R : PFunctor.{max uA₁ uA₂ uA₃, uB}) ≃ₚ
    (P + (Q + R) : PFunctor.{max uA₁ uA₂ uA₃, uB}) where
  equivA := _root_.Equiv.sumAssoc P.A Q.A R.A
  equivB := (Sum.casesOn ·
    (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _))
    (fun _ => _root_.Equiv.refl _))


-- @@ L86-91 verbatim
/-- If `P ≃ₚ R` and `Q ≃ₚ S`, then `P + Q ≃ₚ R + S` -/
@[simps]
def sumCongr {P Q} {R : PFunctor.{uA₃, uB₁}} {S : PFunctor.{uA₄, uB₁}} (e₁ : P ≃ₚ R) (e₂ : Q ≃ₚ S) :
    P + Q ≃ₚ (R + S : PFunctor.{max uA₃ uA₄, uB₁}) where
  equivA := _root_.Equiv.sumCongr e₁.equivA e₂.equivA
  equivB := (Sum.casesOn · (e₁.equivB ·) (e₂.equivB ·))


-- @@ L93-100 verbatim
/-- Rearrangement of nested sums: `(P + Q) + (R + S) ≃ₚ (P + R) + (Q + S)` -/
def sumSumSumComm :
    ((P + Q) + (R + S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, uB}) ≃ₚ
    ((P + R) + (Q + S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, uB}) where
  equivA := _root_.Equiv.sumSumSumComm P.A Q.A R.A S.A
  equivB := (Sum.casesOn ·
    (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _))
    (Sum.casesOn · (fun _ => _root_.Equiv.refl _) (fun _ => _root_.Equiv.refl _)))


-- @@ L102-102 verbatim
end Sum


-- @@ L104-104 verbatim
section Prod


-- @@ L106-107 verbatim
variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})
  (S : PFunctor.{uA₄, uB₄})


-- @@ L109-112 verbatim
/-- Product with `0` on the right is `0` -/
def prodZero : P * 0 ≃ₚ 0 where
  equivA := Equiv.prodPEmpty P.A
  equivB := fun a => a.2.elim


-- @@ L114-117 verbatim
/-- Product with `0` on the left is `0` -/
def zeroProd : 0 * P ≃ₚ 0 where
  equivA := Equiv.pemptyProd P.A
  equivB := fun a => a.1.elim


-- @@ L119-123 verbatim
/-- Product with the unit functor on the right is equivalent to the original functor -/
@[simps]
def prodOne : P * 1 ≃ₚ P where
  equivA := _root_.Equiv.prodPUnit P.A
  equivB := fun a => _root_.Equiv.sumEmpty (P.B a.1) PEmpty


-- @@ L125-129 verbatim
/-- Product with the unit functor on the left is equivalent to the original functor -/
@[simps]
def oneProd : 1 * P ≃ₚ P where
  equivA := _root_.Equiv.punitProd P.A
  equivB := fun a => _root_.Equiv.emptySum PEmpty (P.B a.2)


-- @@ L131-137 verbatim
/-- Product of polynomial functors is commutative up to equivalence -/
@[simps]
def prodComm :
    (P * Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ≃ₚ
    (Q * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) where
  equivA := _root_.Equiv.prodComm P.A Q.A
  equivB := fun a => _root_.Equiv.sumComm (P.B a.1) (Q.B a.2)


-- @@ L139-145 verbatim
/-- Product of polynomial functors is associative up to equivalence -/
@[simps]
def prodAssoc :
    ((P * Q) * R : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) ≃ₚ
    (P * (Q * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) where
  equivA := _root_.Equiv.prodAssoc P.A Q.A R.A
  equivB := fun a => _root_.Equiv.sumAssoc (P.B a.1.1) (Q.B a.1.2) (R.B a.2)


-- @@ L147-152 verbatim
/-- Equivalence is preserved under product: if `P ≃ₚ R` and `Q ≃ₚ S`, then `P * Q ≃ₚ R * S` -/
@[simps]
def prodCongr {P Q} {R : PFunctor.{uA₃, uB₃}} {S : PFunctor.{uA₄, uB₄}}
    (e₁ : P ≃ₚ R) (e₂ : Q ≃ₚ S) : P * Q ≃ₚ (R * S : PFunctor.{max uA₃ uA₄, max uB₃ uB₄}) where
  equivA := _root_.Equiv.prodCongr e₁.equivA e₂.equivA
  equivB := fun a => _root_.Equiv.sumCongr (e₁.equivB a.1) (e₂.equivB a.2)


-- @@ L154-160 verbatim
/-- Rearrangement of nested products: `(P * Q) * (R * S) ≃ₚ (P * R) * (Q * S)` -/
@[simps]
def prodProdProdComm :
    ((P * Q) * (R * S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) ≃ₚ
    ((P * R) * (Q * S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) where
  equivA := _root_.Equiv.prodProdProdComm P.A Q.A R.A S.A
  equivB := fun a => _root_.Equiv.sumSumSumComm (P.B a.1.1) (Q.B a.1.2) (R.B a.2.1) (S.B a.2.2)


-- @@ L162-168 verbatim
/-- Sum distributes over product: `(P + Q) * R ≃ₚ (P * R) + (Q * R)` -/
def sumProdDistrib (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₁}) (R : PFunctor.{uA₃, uB₂}) :
    ((P + Q) * R : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) ≃ₚ
    ((P * R) + (Q * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  equivA := _root_.Equiv.sumProdDistrib P.A Q.A R.A
  equivB := fun
    | ⟨.inl _, _⟩ | ⟨.inr _, _⟩ => _root_.Equiv.refl _


-- @@ L170-189 verbatim
/-- Product distributes over sum: `P * (Q + R) ≃ₚ (P * Q) + (P * R)` -/
def prodSumDistrib (R : PFunctor.{uA₃, uB₂}) :
    (P * (Q + R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) ≃ₚ
    ((P * Q) + (P * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  equivA :=
    let commSum :
        ((Q * P) + (R * P) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) ≃ₚ
        ((P * Q) + (P * R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) := {
      equivA := _root_.Equiv.sumCongr
        (prodComm.{uA₂, uB₂, uA₁, uB₁} Q P).equivA
        (prodComm.{uA₃, uB₂, uA₁, uB₁} R P).equivA
      equivB := fun
        | .inl a => (prodComm.{uA₂, uB₂, uA₁, uB₁} Q P).equivB a
        | .inr a => (prodComm.{uA₃, uB₂, uA₁, uB₁} R P).equivB a
    }
    ((prodComm.{uA₁, uB₁, max uA₂ uA₃, uB₂} P (Q + R)).trans <|
      (sumProdDistrib.{uA₂, uB₂, uA₃, uB₁, uA₁} Q R P).trans <|
        commSum).equivA
  equivB := fun
    | ⟨_, .inl _⟩ | ⟨_, .inr _⟩ => _root_.Equiv.refl _


-- @@ L191-193 verbatim
@[simp, backward_defeq]
theorem prodSumDistrib_equivA (R : PFunctor.{uA₃, uB₂}) :
    (prodSumDistrib P Q R).equivA = _root_.Equiv.prodSumDistrib P.A Q.A R.A := rfl


-- @@ L195-198 verbatim
@[simp, backward_defeq]
theorem prodSumDistrib_equivB (R : PFunctor.{uA₃, uB₂}) (a : (P * (Q + R)).A) :
    (prodSumDistrib P Q R).equivB a = match a with
      | ⟨_, .inl _⟩ | ⟨_, .inr _⟩ => _root_.Equiv.refl _ := rfl


-- @@ L200-200 verbatim
end Prod


-- @@ L202-202 verbatim
section Sigma


-- @@ L204-204 verbatim
variable (P : PFunctor.{uA₁, uB₁}) {I : Type v} (F : I → PFunctor.{uA₂, uB₂})


-- @@ L206-207 verbatim
instance [inst : IsEmpty I] : IsEmpty (sigma F).A where
  false := fun a => inst.elim a.1


-- @@ L209-212 verbatim
/-- Sigma of an empty family is the zero functor. -/
def emptySigma [inst : IsEmpty I] : sigma F ≃ₚ 0 where
  equivA := Equiv.equivPEmpty _
  equivB := fun a => inst.elim a.1


-- @@ L214-220 verbatim
/-- Sigma over a subsingleton index type is the single functor `F default`. -/
def uniqueSigma [Unique I] : sigma F ≃ₚ F default where
  equivA := _root_.Equiv.uniqueSigma _
  equivB := fun ⟨i, a⟩ => by
    have hi := Unique.eq_default i
    subst hi
    exact _root_.Equiv.refl _


-- @@ L222-225 verbatim
/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself. -/
def punitSigma {F : PUnit → PFunctor.{uA, uB}} : sigma F ≃ₚ F PUnit.unit where
  equivA := _root_.Equiv.uniqueSigma _
  equivB := fun ⟨i, a⟩ => by cases i; exact _root_.Equiv.refl _


-- @@ L227-245 verbatim
/-- Left distributivity of sum over sigma. -/
def sumSigmaDistrib (F : I → PFunctor.{uA₂, uB₁}) [Unique I] :
    (P + sigma F : PFunctor.{max uA₁ uA₂ v, uB₁}) ≃ₚ
    sigma (fun i => (P + F i : PFunctor.{max uA₁ uA₂, uB₁})) where
  equivA := {
    toFun := fun
      | Sum.inl pa => ⟨default, Sum.inl pa⟩
      | Sum.inr ⟨i, fa⟩ => ⟨i, Sum.inr fa⟩
    invFun := fun
      | ⟨_, Sum.inl pa⟩ => Sum.inl pa
      | ⟨i, Sum.inr fa⟩ => Sum.inr ⟨i, fa⟩
    left_inv := by rintro (pa | ⟨i, fa⟩) <;> rfl
    right_inv := by
      rintro ⟨i, pa | fa⟩
      · cases (Unique.eq_default i)
        rfl
      · rfl
  }
  equivB := fun a => by rcases a with pa | ⟨i, fa⟩ <;> exact _root_.Equiv.refl _


-- @@ L247-266 verbatim
/-- Right distributivity of sum over sigma. -/
def sigmaSumDistrib (F : I → PFunctor.{uA₂, uB₁}) [Unique I] :
    (sigma F + P : PFunctor.{max uA₁ uA₂ v, uB₁}) ≃ₚ
    sigma (fun i => (F i + P : PFunctor.{max uA₁ uA₂, uB₁})) where
  equivA := {
    toFun := fun
      | Sum.inl ⟨i, fa⟩ => ⟨i, Sum.inl fa⟩
      | Sum.inr pa => ⟨default, Sum.inr pa⟩
    invFun := fun
      | ⟨i, Sum.inl fa⟩ => Sum.inl ⟨i, fa⟩
      | ⟨_, Sum.inr pa⟩ => Sum.inr pa
    left_inv := by rintro (⟨i, fa⟩ | pa) <;> rfl
    right_inv := by
      rintro ⟨i, fa | pa⟩
      · rfl
      · cases (Unique.eq_default i)
        rfl
  }
  -- exact (_root_.Equiv.sumSigmaDistrib _).symm
  equivB := fun a => by rcases a with ⟨i, fa⟩ | pa <;> exact _root_.Equiv.refl _


-- @@ L268-283 verbatim
/-- Left distributivity of product over sigma. -/
def prodSigmaDistrib : (P * sigma F : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₚ
    sigma (fun i => (P * F i : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) where
  equivA := {
    toFun := fun ⟨pa, ⟨i, fa⟩⟩ => ⟨i, ⟨pa, fa⟩⟩
    invFun := fun ⟨i, ⟨pa, fa⟩⟩ => ⟨pa, ⟨i, fa⟩⟩
    left_inv := by
      rintro ⟨pa, ⟨i, fa⟩⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨pa, fa⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨pa, ⟨i, fa⟩⟩
    exact _root_.Equiv.refl _


-- @@ L285-300 verbatim
/-- Right distributivity of product over sigma. -/
def sigmaProdDistrib : (sigma F * P : PFunctor.{max uA₁ uA₂ v, max uB₁ uB₂}) ≃ₚ
    sigma (fun i => (F i * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) where
  equivA := {
    toFun := fun ⟨⟨i, fa⟩, pa⟩ => ⟨i, ⟨fa, pa⟩⟩
    invFun := fun ⟨i, ⟨fa, pa⟩⟩ => ⟨⟨i, fa⟩, pa⟩
    left_inv := by
      rintro ⟨⟨i, fa⟩, pa⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨fa, pa⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨⟨i, fa⟩, pa⟩
    exact _root_.Equiv.refl _


-- @@ L302-317 verbatim
/-- Left distributivity of tensor product over sigma. -/
def tensorSigmaDistrib :
    P ⊗ sigma F ≃ₚ sigma (fun i => P ⊗ F i) where
  equivA := {
    toFun := fun ⟨pa, ⟨i, fa⟩⟩ => ⟨i, ⟨pa, fa⟩⟩
    invFun := fun ⟨i, ⟨pa, fa⟩⟩ => ⟨pa, ⟨i, fa⟩⟩
    left_inv := by
      rintro ⟨pa, ⟨i, fa⟩⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨pa, fa⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨pa, ⟨i, fa⟩⟩
    exact _root_.Equiv.refl _


-- @@ L319-334 verbatim
/-- Right distributivity of tensor product over sigma. -/
def sigmaTensorDistrib {I : Type v} (F : I → PFunctor.{uA₁, uB₁}) (P : PFunctor.{uA₂, uB₂}) :
    sigma F ⊗ P ≃ₚ sigma (fun i => F i ⊗ P) where
  equivA := {
    toFun := fun ⟨⟨i, fa⟩, pa⟩ => ⟨i, ⟨fa, pa⟩⟩
    invFun := fun ⟨i, ⟨fa, pa⟩⟩ => ⟨⟨i, fa⟩, pa⟩
    left_inv := by
      rintro ⟨⟨i, fa⟩, pa⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨fa, pa⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨⟨i, fa⟩, pa⟩
    exact _root_.Equiv.refl _


-- @@ L336-351 verbatim
/-- Right distributivity of composition over sigma. -/
def sigmaCompDistrib {I : Type v} (F : I → PFunctor.{uA₁, uB₁}) (P : PFunctor.{uA₂, uB₂}) :
    sigma F ◃ P ≃ₚ sigma (fun i => F i ◃ P) where
  equivA := {
    toFun := fun ⟨⟨i, fa⟩, pf⟩ => ⟨i, ⟨fa, pf⟩⟩
    invFun := fun ⟨i, ⟨fa, pf⟩⟩ => ⟨⟨i, fa⟩, pf⟩
    left_inv := by
      rintro ⟨⟨i, fa⟩, pf⟩
      rfl
    right_inv := by
      rintro ⟨i, ⟨fa, pf⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨⟨i, fa⟩, pf⟩
    exact _root_.Equiv.refl _


-- @@ L353-353 verbatim
end Sigma


-- @@ L355-355 verbatim
section Pi


-- @@ L357-388 verbatim
/-- Composition distributes over an indexed product on the left
(Spivak–Niu (6.51)):
`(Π i, F i) ◃ P ≃ₚ Π i, (F i ◃ P)`.

A position on the left chooses all `F i` positions and one continuation on
their dependent sum of directions. The equivalence curries that continuation
one index at a time; directions are reassociated dependent pairs. -/
def piCompDistrib {I : Type v} (F : I → PFunctor.{uA₁, uB₁})
    (P : PFunctor.{uA₂, uB₂}) :
    pi F ◃ P ≃ₚ pi (fun i => F i ◃ P) where
  equivA :=
    { toFun := fun ⟨f, k⟩ i => ⟨f i, fun d => k ⟨i, d⟩⟩
      invFun := fun g =>
        ⟨fun i => (g i).1, fun ⟨i, d⟩ => (g i).2 d⟩
      left_inv := by
        rintro ⟨f, k⟩
        apply Sigma.ext
        · rfl
        exact heq_of_eq <| by
          funext ⟨i, d⟩
          rfl
      right_inv := by
        intro g
        funext i
        rfl }
  equivB := fun x => by
    rcases x with ⟨f, k⟩
    exact
    { toFun := fun ⟨⟨i, d⟩, pd⟩ => ⟨i, d, pd⟩
      invFun := fun ⟨i, d, pd⟩ => ⟨⟨i, d⟩, pd⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }


-- @@ L390-394 verbatim
/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def piPUnit (P : PFunctor.{uA, uB}) :
    pi (fun (_ : PUnit) => P) ≃ₚ P where
  equivA := _root_.Equiv.punitArrowEquiv P.A
  equivB := fun f => _root_.Equiv.uniqueSigma (fun i : PUnit => P.B (f i))


-- @@ L396-396 verbatim
end Pi


-- @@ L398-398 verbatim
section ULift


-- @@ L400-400 verbatim
variable (P : PFunctor.{uA₁, uB₁})


-- @@ L402-405 verbatim
/-- Equivalence between a polynomial functor and its universe-lifted version -/
def uliftEquiv : P ≃ₚ (P.ulift : PFunctor.{max uA₁ u, max uB₁ v}) where
  equivA := _root_.Equiv.ulift.symm
  equivB := fun _ => _root_.Equiv.ulift.symm


-- @@ L407-410 verbatim
/-- Universe lifting is idempotent up to equivalence -/
def uliftUliftEquiv : P.ulift.ulift ≃ₚ P.ulift where
  equivA := _root_.Equiv.ulift
  equivB := fun _ => _root_.Equiv.ulift


-- @@ L412-421 verbatim
/-- Universe lifting commutes with sum -/
def uliftSumEquiv (Q : PFunctor.{uA₂, uB₁}) :
    (PFunctor.ulift.{_, _, u, v} (P + Q : PFunctor.{max uA₁ uA₂, uB₁})) ≃ₚ
    (PFunctor.ulift.{_, _, uA, uB} P + PFunctor.ulift.{_, _, uA', uB} Q :
      PFunctor.{max uA₁ uA uA₂ uA', max uB₁ uB}) where
  equivA := _root_.Equiv.ulift.trans
    (_root_.Equiv.sumCongr _root_.Equiv.ulift.symm _root_.Equiv.ulift.symm)
  equivB := fun a => by
    rcases a with ⟨a⟩
    cases a <;> exact _root_.Equiv.ulift.trans _root_.Equiv.ulift.symm


-- @@ L423-433 verbatim
/-- Universe lifting commutes with product. -/
def uliftProdEquiv (Q : PFunctor.{uA₂, uB₂}) :
    (PFunctor.ulift.{_, _, u, v} (P * Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂})) ≃ₚ
      (PFunctor.ulift.{_, _, uA, uB} P * PFunctor.ulift.{_, _, uA', uB'} Q :
        PFunctor.{max uA₁ uA₂ uA uA', max uB₁ uB₂ uB uB'}) where
  equivA := _root_.Equiv.ulift.trans
    (_root_.Equiv.prodCongr _root_.Equiv.ulift.symm _root_.Equiv.ulift.symm)
  equivB := fun a => by
    rcases a with ⟨⟨_, _⟩⟩
    exact _root_.Equiv.ulift.trans
      (_root_.Equiv.sumCongr _root_.Equiv.ulift.symm _root_.Equiv.ulift.symm)


-- @@ L435-435 verbatim
end ULift


-- @@ L437-437 verbatim
section Tensor


-- @@ L439-440 verbatim
variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})
  (S : PFunctor.{uA₄, uB₄})


-- @@ L442-445 verbatim
/-- Tensor product with `0` on the right is `0` -/
def tensorZero : P ⊗ 0 ≃ₚ 0 where
  equivA := Equiv.prodPEmpty P.A
  equivB := fun a => Equiv.prodPEmpty (P.B a.1)


-- @@ L447-450 verbatim
/-- Tensor product with `0` on the left is `0` -/
def zeroTensor : 0 ⊗ P ≃ₚ 0 where
  equivA := Equiv.pemptyProd P.A
  equivB := fun a => Equiv.pemptyProd (P.B a.2)


-- @@ L452-454 verbatim
instance {P} {a : (P ⊗ 1).A} : IsEmpty ((P ⊗ 1).B a) := by
  simpa [tensor, OfNat.ofNat, One.one] using
    (inferInstance : IsEmpty (P.B a.1 × PEmpty))


-- @@ L456-459 verbatim
/-- Tensor product with `1` on the right is equivalent to the constant functor -/
def tensorOne : P ⊗ 1 ≃ₚ C P.A where
  equivA := Equiv.prodPUnit P.A
  equivB := fun _ => Equiv.equivPEmpty _


-- @@ L461-463 verbatim
instance {P} {a : (1 ⊗ P).A} : IsEmpty ((1 ⊗ P).B a) := by
  simpa [tensor, OfNat.ofNat, One.one] using
    (inferInstance : IsEmpty (PEmpty × P.B a.2))


-- @@ L465-468 verbatim
/-- Tensor product with `1` on the left is equivalent to the constant functor -/
def oneTensor : 1 ⊗ P ≃ₚ C P.A where
  equivA := Equiv.punitProd P.A
  equivB := fun _ => Equiv.equivPEmpty _


-- @@ L470-474 verbatim
/-- Tensor product with the functor Y on the right -/
@[simps]
def tensorY : P ⊗ y ≃ₚ P where
  equivA := _root_.Equiv.prodPUnit P.A
  equivB := fun a => _root_.Equiv.prodPUnit (P.B a.1)


-- @@ L476-480 verbatim
/-- Tensor product with the functor Y on the left -/
@[simps]
def yTensor : y ⊗ P ≃ₚ P where
  equivA := _root_.Equiv.punitProd P.A
  equivB := fun a => _root_.Equiv.punitProd (P.B a.2)


-- @@ L482-482 verbatim
@[deprecated (since := "2026-08-17")] alias tensorX := tensorY

-- @@ L483-483 verbatim
@[deprecated (since := "2026-08-17")] alias xTensor := yTensor

-- @@ L484-484 verbatim
@[deprecated (since := "2026-08-17")] alias tensorX_equivA := tensorY_equivA

-- @@ L485-485 verbatim
@[deprecated (since := "2026-08-17")] alias tensorX_equivB := tensorY_equivB

-- @@ L486-486 verbatim
@[deprecated (since := "2026-08-17")] alias xTensor_equivA := yTensor_equivA

-- @@ L487-487 verbatim
@[deprecated (since := "2026-08-17")] alias xTensor_equivB := yTensor_equivB


-- @@ L489-495 verbatim
/-- Tensor product of polynomial functors is commutative up to equivalence -/
@[simps]
def tensorComm :
    (P ⊗ Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ≃ₚ
    (Q ⊗ P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) where
  equivA := _root_.Equiv.prodComm P.A Q.A
  equivB := fun a => _root_.Equiv.prodComm (P.B a.1) (Q.B a.2)


-- @@ L497-503 verbatim
/-- Tensor product of polynomial functors is associative up to equivalence -/
@[simps]
def tensorAssoc :
    ((P ⊗ Q) ⊗ R : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) ≃ₚ
    (P ⊗ (Q ⊗ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃}) where
  equivA := _root_.Equiv.prodAssoc P.A Q.A R.A
  equivB := fun a => _root_.Equiv.prodAssoc (P.B a.1.1) (Q.B a.1.2) (R.B a.2)


-- @@ L505-512 verbatim
/-- Tensor product preserves equivalences: if `P ≃ₚ R` and `Q ≃ₚ S`, then `P ⊗ Q ≃ₚ R ⊗ S` -/
@[simps]
def tensorCongr {P : PFunctor.{uA₁, uB₁}} {Q} {R : PFunctor.{uA₃, uB₃}} {S}
    (e₁ : P ≃ₚ R) (e₂ : Q ≃ₚ S) :
      (P ⊗ Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ≃ₚ
      (R ⊗ S : PFunctor.{max uA₃ uA₄, max uB₃ uB₄}) where
  equivA := _root_.Equiv.prodCongr e₁.equivA e₂.equivA
  equivB := fun a => _root_.Equiv.prodCongr (e₁.equivB a.1) (e₂.equivB a.2)


-- @@ L514-519 verbatim
/-- Rearrangement of nested tensor products: `(P ⊗ Q) ⊗ (R ⊗ S) ≃ₚ (P ⊗ R) ⊗ (Q ⊗ S)` -/
def tensorTensorTensorComm :
    ((P ⊗ Q) ⊗ (R ⊗ S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) ≃ₚ
    ((P ⊗ R) ⊗ (Q ⊗ S) : PFunctor.{max uA₁ uA₂ uA₃ uA₄, max uB₁ uB₂ uB₃ uB₄}) where
  equivA := _root_.Equiv.prodProdProdComm P.A Q.A R.A S.A
  equivB := fun a => _root_.Equiv.prodProdProdComm (P.B a.1.1) (Q.B a.1.2) (R.B a.2.1) (S.B a.2.2)


-- @@ L521-527 verbatim
/-- Sum distributes over tensor product: `(P + Q) ⊗ R ≃ₚ (P ⊗ R) + (Q ⊗ R)` -/
def sumTensorDistrib (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₁}) (R : PFunctor.{uA₃, uB₂}) :
    ((P + Q : PFunctor.{max uA₁ uA₂, uB₁}) ⊗ R) ≃ₚ
    ((P ⊗ R) + (Q ⊗ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  equivA := _root_.Equiv.sumProdDistrib P.A Q.A R.A
  equivB := fun
    | ⟨.inl _, _⟩ | ⟨.inr _, _⟩ => _root_.Equiv.refl _


-- @@ L529-535 verbatim
/-- Tensor product distributes over sum: `P ⊗ (Q + R) ≃ₚ (P ⊗ Q) + (P ⊗ R)` -/
def tensorSumDistrib (R : PFunctor.{uA₃, uB₂}) :
    (P ⊗ (Q + R : PFunctor.{max uA₂ uA₃, uB₂})) ≃ₚ
    ((P ⊗ Q) + (P ⊗ R) : PFunctor.{max uA₁ uA₂ uA₃, max uB₁ uB₂}) where
  equivA := _root_.Equiv.prodSumDistrib P.A Q.A R.A
  equivB := fun
    | ⟨_, .inl _⟩ | ⟨_, .inr _⟩ => _root_.Equiv.refl _


-- @@ L537-537 verbatim
end Tensor


-- @@ L539-539 verbatim
section Comp


-- @@ L541-541 verbatim
variable (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) (R : PFunctor.{uA₃, uB₃})


-- @@ L543-544 verbatim
instance : IsEmpty (0 ◃ P).A where
  false := fun a => a.1.elim


-- @@ L546-549 verbatim
/-- Composing the zero functor with `P` yields the zero functor. -/
def zeroComp : 0 ◃ P ≃ₚ 0 where
  equivA := Equiv.equivPEmpty _
  equivB := fun a => a.1.elim


-- @@ L551-552 verbatim
instance {a : (1 ◃ P).A} : IsEmpty ((1 ◃ P).B a) where
  false := fun a => a.1.elim


-- @@ L554-558 verbatim
/-- Composing the unit functor with `P` yields the unit functor. -/
def oneComp : (1 : PFunctor.{uA, uB}) ◃ P ≃ₚ 1 where
  equivA := (@_root_.Equiv.uniqueSigma _ (fun i => B 1 i → P.A)
    (instUniqueAOfNatOne.{uA, uB})).trans (Equiv.pemptyArrowEquivPUnit _)
  equivB := fun _ => Equiv.equivPEmpty _


-- @@ L560-582 verbatim
/-- Associativity of composition -/
def compAssoc : (P ◃ Q) ◃ R ≃ₚ P ◃ (Q ◃ R) where
  equivA := {
    toFun := fun ⟨⟨pa, qf⟩, rf⟩ => ⟨pa, fun pb => ⟨qf pb, fun qb => rf ⟨pb, qb⟩⟩⟩
    invFun := fun ⟨pa, g⟩ => ⟨⟨pa, fun pb => (g pb).1⟩, fun ⟨pb, qb⟩ => (g pb).2 qb⟩
    left_inv := by
      rintro ⟨⟨pa, qf⟩, rf⟩
      simp [comp]
    right_inv := by
      rintro ⟨pa, g⟩
      simp only [comp]
      apply Sigma.ext rfl
      apply heq_of_eq
      funext pb
      rcases g pb with ⟨qa, qf⟩
      apply Sigma.ext rfl
      apply heq_of_eq
      funext qb
      rfl
  }
  equivB := fun ⟨⟨pa, qf⟩, rf⟩ =>
    _root_.Equiv.sigmaAssoc (fun pb qb => R.B (rf ⟨pb, qb⟩))
  -- Equiv.sigmaProdDistrib _ _


-- @@ L584-587 verbatim
/-- Composition with `y` is identity (right) -/
def compY : P ◃ y ≃ₚ P where
  equivA := Equiv.sigmaUnique P.A (fun a => P.B a → PUnit.{_ + 1})
  equivB := fun _ => _root_.Equiv.sigmaPUnit _


-- @@ L589-592 verbatim
/-- Composition with `y` is identity (left) -/
def yComp : y ◃ P ≃ₚ P where
  equivA := (_root_.Equiv.uniqueSigma _).trans (Equiv.punitArrowEquiv P.A)
  equivB := fun _ => by exact _root_.Equiv.uniqueSigma _


-- @@ L594-594 verbatim
@[deprecated (since := "2026-08-17")] alias compX := compY

-- @@ L595-595 verbatim
@[deprecated (since := "2026-08-17")] alias XComp := yComp


-- @@ L597-617 verbatim
/-- Distributivity of composition over sum on the right -/
def sumCompDistrib (Q : PFunctor.{uA₂, uB₁}) :
    (P + Q : PFunctor.{max uA₁ uA₂, uB₁}) ◃ R ≃ₚ
    ((P ◃ R) + (Q ◃ R) : PFunctor.{max uA₁ uA₂ uA₃ uB₁, max uB₁ uB₃}) where
  equivA := {
    toFun := fun
      | ⟨Sum.inl pa, pf⟩ => Sum.inl ⟨pa, pf⟩
      | ⟨Sum.inr qa, pf⟩ => Sum.inr ⟨qa, pf⟩
    invFun := fun
      | Sum.inl ⟨pa, pf⟩ => ⟨Sum.inl pa, pf⟩
      | Sum.inr ⟨qa, pf⟩ => ⟨Sum.inr qa, pf⟩
    left_inv := by
      rintro ⟨a, pf⟩
      cases a <;> rfl
    right_inv := by
      intro a
      cases a <;> rfl
  }
  equivB := fun a => by
    rcases a with ⟨a, pf⟩
    cases a <;> exact _root_.Equiv.refl _


-- @@ L619-655 verbatim
/-- Composition distributes over product on the left. -/
def prodCompDistrib :
    (P * Q : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}) ◃ R ≃ₚ
      ((P ◃ R) * (Q ◃ R) : PFunctor.{max uA₁ uA₂ uA₃ uB₁ uB₂, max uB₁ uB₂ uB₃}) where
  equivA := {
    toFun := fun ⟨⟨pa, qa⟩, f⟩ =>
      (⟨pa, fun pb => f (Sum.inl pb)⟩, ⟨qa, fun qb => f (Sum.inr qb)⟩)
    invFun := fun ⟨⟨pa, fp⟩, ⟨qa, fq⟩⟩ =>
      ⟨⟨pa, qa⟩, Sum.elim fp fq⟩
    left_inv := by
      rintro ⟨⟨pa, qa⟩, f⟩
      apply Sigma.ext
      · rfl
      exact heq_of_eq <| by
        funext b
        cases b <;> rfl
    right_inv := by
      rintro ⟨⟨pa, fp⟩, ⟨qa, fq⟩⟩
      rfl
  }
  equivB := fun a => by
    rcases a with ⟨⟨pa, qa⟩, f⟩
    exact {
      toFun := fun s => match s with
        | ⟨Sum.inl pb, rb⟩ => Sum.inl ⟨pb, rb⟩
        | ⟨Sum.inr qb, rb⟩ => Sum.inr ⟨qb, rb⟩
      invFun := fun s => match s with
        | Sum.inl ⟨pb, rb⟩ => ⟨Sum.inl pb, rb⟩
        | Sum.inr ⟨qb, rb⟩ => ⟨Sum.inr qb, rb⟩
      left_inv := by
        intro s
        rcases s with ⟨b, rb⟩
        cases b <;> rfl
      right_inv := by
        intro s
        cases s <;> rfl
    }


-- @@ L657-657 verbatim
end Comp


-- @@ L659-659 verbatim
end Equiv


-- @@ L661-661 verbatim
end PFunctor
