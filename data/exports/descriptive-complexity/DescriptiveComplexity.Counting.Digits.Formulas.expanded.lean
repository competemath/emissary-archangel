/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Digits.Tower


-- @@ L8-31 verbatim
/-!
# Arithmetic on numbers given by formulas

A number is given by a formula `ν` with a distinguished block of `ℓ` variables,
the *position*: under a valuation of the other variables, `ν` holds of the
positions of the digits `1`, a position being an `ℓ`-tuple of elements and
the positions being ordered lexicographically. This file builds, from such
formulas, the formulas of

* the sum (`DescriptiveComplexity.Digits.addF`), by carry lookahead;
* the double (`DescriptiveComplexity.Digits.dblF`), a shift by one position;
* the number one (`DescriptiveComplexity.Digits.oneF`);

and identifies what they hold of (`DescriptiveComplexity.Digits.AddSet`,
`DescriptiveComplexity.Digits.DblSet`) with the digits of the sum and of the
double (`DescriptiveComplexity.Digits.addSet_tupBits`,
`DescriptiveComplexity.Digits.dblSet_tupBits`). The numbers are read modulo
`2 ^ (n ^ ℓ)`, `n` being the size of the structure, and the operations are
exact modulo that.

The vocabulary `N` of the formulas is arbitrary; it receives the ordered
vocabulary through a map `ι`, along which the order formulas of
`DescriptiveComplexity.OrderWalk` are read.
-/


-- @@ L33-33 verbatim
namespace DescriptiveComplexity


-- @@ L35-35 verbatim
open FirstOrder


-- @@ L37-37 verbatim
open Language Structure


-- @@ L39-39 verbatim
namespace Digits


-- @@ L41-41 verbatim
/-! ### Sets of positions -/


-- @@ L43-43 verbatim
section Sem


-- @@ L45-45 verbatim
variable {A : Type} [LinearOrder A] {ℓ : ℕ}


-- @@ L47-50 verbatim
/-- The positions of the digits `1` of a number, the positions being the
`ℓ`-tuples in lexicographic order. -/
def tupBits (n : ℕ) (p : Fin ℓ → A) : Prop :=
  bitsOf n (toLex p)


-- @@ L52-56 verbatim
/-- The sum of two sets of positions, by carry lookahead. -/
def AddSet (X Y : (Fin ℓ → A) → Prop) (p : Fin ℓ → A) : Prop :=
  Xor (Xor (X p) (Y p))
    (∃ q : Fin ℓ → A, toLex q < toLex p ∧ X q ∧ Y q ∧
      ∀ r : Fin ℓ → A, toLex q < toLex r → toLex r < toLex p → X r ∨ Y r)


-- @@ L58-60 verbatim
/-- The double of a set of positions: its shift by one position. -/
def DblSet (X : (Fin ℓ → A) → Prop) (p : Fin ℓ → A) : Prop :=
  ∃ q : Fin ℓ → A, toLex q ⋖ toLex p ∧ X q


-- @@ L62-62 verbatim
variable [Finite A]


-- @@ L64-73 verbatim
theorem addSet_tupBits (m n : ℕ) :
    AddSet (tupBits m) (tupBits n) = (tupBits (m + n) : (Fin ℓ → A) → Prop) := by
  funext p
  refine propext ((bitsOf_add m n (toLex p)).trans ?_).symm
  refine iff_of_eq (congrArg _ (propext ?_))
  constructor
  · rintro ⟨q, hq, hm, hn, hall⟩
    exact ⟨ofLex q, hq, hm, hn, fun r => hall (toLex r)⟩
  · rintro ⟨q, hq, hm, hn, hall⟩
    exact ⟨toLex q, hq, hm, hn, fun r => hall (ofLex r)⟩


-- @@ L75-83 verbatim
theorem dblSet_tupBits (n : ℕ) :
    DblSet (tupBits n) = (tupBits (2 * n) : (Fin ℓ → A) → Prop) := by
  funext p
  refine propext ((bitsOf_two_mul n (toLex p)).trans ?_).symm
  constructor
  · rintro ⟨q, hq, h⟩
    exact ⟨ofLex q, hq, h⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨toLex q, hq, h⟩


-- @@ L85-87 verbatim
theorem tupBits_one (p : Fin ℓ → A) :
    tupBits 1 p ↔ ∀ c : Lex (Fin ℓ → A), toLex p ≤ c :=
  bitsOf_one (toLex p)


-- @@ L89-92 verbatim
theorem tupBits_congr {m n : ℕ}
    (h : m % 2 ^ Nat.card (Lex (Fin ℓ → A)) = n % 2 ^ Nat.card (Lex (Fin ℓ → A))) :
    (tupBits m : (Fin ℓ → A) → Prop) = tupBits n :=
  funext fun p => congrFun (bitsOf_congr h) (toLex p)


-- @@ L94-94 verbatim
end Sem


-- @@ L96-96 verbatim
/-! ### The formulas -/


-- @@ L98-98 verbatim
section Formulas


-- @@ L100-100 verbatim
variable {K N : Language.{0, 0}} (ι : K.sum Language.order →ᴸ N) {ℓ : ℕ} {γ : Type}


-- @@ L102-104 verbatim
/-- The exclusive or of two formulas. -/
def xorF (φ ψ : N.Formula γ) : N.Formula γ :=
  (φ ⊓ ∼ψ) ⊔ (ψ ⊓ ∼φ)


-- @@ L106-109 verbatim
/-- A number formula, read at the position bound by one more quantifier
block. -/
def atQ (ν : N.Formula (γ ⊕ Fin ℓ)) : N.Formula ((γ ⊕ Fin ℓ) ⊕ Fin ℓ) :=
  Formula.relabel (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) ν


-- @@ L111-114 verbatim
/-- A number formula, read at the position bound by a second quantifier
block. -/
def atR (ν : N.Formula (γ ⊕ Fin ℓ)) : N.Formula (((γ ⊕ Fin ℓ) ⊕ Fin ℓ) ⊕ Fin ℓ) :=
  Formula.relabel (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr) ν


-- @@ L116-124 verbatim
/-- The carry into a position: some lower position generates it, and every
position in between propagates it. -/
noncomputable def carryF (ν₁ ν₂ : N.Formula (γ ⊕ Fin ℓ)) : N.Formula (γ ⊕ Fin ℓ) :=
  Formula.iExs (Fin ℓ)
    (((ι.onFormula (lexSelLtF Sum.inr (Sum.inl ∘ Sum.inr)) ⊓ atQ ν₁) ⊓ atQ ν₂) ⊓
      Formula.iAlls (Fin ℓ)
        ((ι.onFormula (lexSelLtF (Sum.inl ∘ Sum.inr) Sum.inr) ⊓
            ι.onFormula (lexSelLtF Sum.inr (Sum.inl ∘ Sum.inl ∘ Sum.inr))).imp
          (atR ν₁ ⊔ atR ν₂)))


-- @@ L126-128 verbatim
/-- **The sum of two numbers.** -/
noncomputable def addF (ν₁ ν₂ : N.Formula (γ ⊕ Fin ℓ)) : N.Formula (γ ⊕ Fin ℓ) :=
  xorF (xorF ν₁ ν₂) (carryF ι ν₁ ν₂)


-- @@ L130-132 verbatim
/-- **The double of a number.** -/
noncomputable def dblF (ν : N.Formula (γ ⊕ Fin ℓ)) : N.Formula (γ ⊕ Fin ℓ) :=
  Formula.iExs (Fin ℓ) (ι.onFormula (succTupF Sum.inr (Sum.inl ∘ Sum.inr)) ⊓ atQ ν)


-- @@ L134-136 verbatim
/-- **The number one.** -/
noncomputable def oneF : N.Formula (γ ⊕ Fin ℓ) :=
  ι.onFormula (minTupF Sum.inr)


-- @@ L138-138 verbatim
variable {A : Type} [K.Structure A] [LinearOrder A] [N.Structure A] [ι.IsExpansionOn A]


-- @@ L140-145 verbatim
omit [K.Structure A] [LinearOrder A] in
theorem realize_xorF (φ ψ : N.Formula γ) (v : γ → A) :
    (xorF φ ψ).Realize v ↔ Xor (φ.Realize v) (ψ.Realize v) := by
  rw [xorF, Formula.realize_sup, Formula.realize_inf, Formula.realize_inf,
    Formula.realize_not, Formula.realize_not]
  rfl


-- @@ L147-150 verbatim
/-- An order formula, read in the vocabulary `N`. -/
theorem realize_lift {δ : Type} (φ : (K.sum Language.order).Formula δ) (v : δ → A) :
    (ι.onFormula φ).Realize v ↔ φ.Realize v :=
  LHom.realize_onFormula ι φ


-- @@ L152-158 verbatim
omit [K.Structure A] [LinearOrder A] [ι.IsExpansionOn A] in
theorem realize_atQ (ν : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p q : Fin ℓ → A) :
    (atQ ν).Realize (Sum.elim (Sum.elim g p) q) ↔ ν.Realize (Sum.elim g q) := by
  rw [atQ, Formula.realize_relabel]
  refine iff_of_eq (congrArg _ ?_)
  funext x
  rcases x with x | x <;> rfl


-- @@ L160-166 verbatim
omit [K.Structure A] [LinearOrder A] [ι.IsExpansionOn A] in
theorem realize_atR (ν : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p q r : Fin ℓ → A) :
    (atR ν).Realize (Sum.elim (Sum.elim (Sum.elim g p) q) r) ↔ ν.Realize (Sum.elim g r) := by
  rw [atR, Formula.realize_relabel]
  refine iff_of_eq (congrArg _ ?_)
  funext x
  rcases x with x | x <;> rfl


-- @@ L168-180 verbatim
theorem realize_carryF (ν₁ ν₂ : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p : Fin ℓ → A) :
    (carryF ι ν₁ ν₂).Realize (Sum.elim g p) ↔
      ∃ q : Fin ℓ → A, toLex q < toLex p ∧ ν₁.Realize (Sum.elim g q) ∧
        ν₂.Realize (Sum.elim g q) ∧ ∀ r : Fin ℓ → A, toLex q < toLex r → toLex r < toLex p →
          ν₁.Realize (Sum.elim g r) ∨ ν₂.Realize (Sum.elim g r) := by
  rw [carryF, Formula.realize_iExs]
  refine exists_congr fun q => ?_
  rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_inf, realize_lift,
    realize_lexSelLtF, realize_atQ, realize_atQ, Formula.realize_iAlls, and_assoc, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun r => ?_)))
  rw [Formula.realize_imp, Formula.realize_inf, realize_lift, realize_lift,
    realize_lexSelLtF, realize_lexSelLtF, Formula.realize_sup, realize_atR, realize_atR]
  exact and_imp


-- @@ L182-186 verbatim
theorem realize_addF (ν₁ ν₂ : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p : Fin ℓ → A) :
    (addF ι ν₁ ν₂).Realize (Sum.elim g p) ↔
      AddSet (fun p' => ν₁.Realize (Sum.elim g p')) (fun p' => ν₂.Realize (Sum.elim g p')) p := by
  rw [addF, realize_xorF, realize_xorF, realize_carryF]
  rfl


-- @@ L188-193 verbatim
theorem realize_dblF (ν : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A) (p : Fin ℓ → A) :
    (dblF ι ν).Realize (Sum.elim g p) ↔ DblSet (fun p' => ν.Realize (Sum.elim g p')) p := by
  rw [dblF, Formula.realize_iExs]
  refine exists_congr fun q => ?_
  rw [Formula.realize_inf, realize_lift, realize_succTupF, realize_atQ, tupSucc_iff_covBy]
  rfl


-- @@ L195-199 verbatim
theorem realize_oneF (g : γ → A) (p : Fin ℓ → A) :
    (oneF ι : N.Formula (γ ⊕ Fin ℓ)).Realize (Sum.elim g p) ↔
      ∀ c : Lex (Fin ℓ → A), toLex p ≤ c := by
  rw [oneF, realize_lift, realize_minTupF, tup_isBot_iff]
  rfl


-- @@ L201-201 verbatim
end Formulas


-- @@ L203-203 verbatim
/-! ### A quantifier block before the position -/


-- @@ L205-205 verbatim
section ExMid


-- @@ L207-207 verbatim
variable {N : Language.{0, 0}} {γ : Type} {ℓ m : ℕ}


-- @@ L209-213 verbatim
/-- Existential quantification over a block of variables that is not the last
one: the position stays last. -/
noncomputable def exMid (ξ : N.Formula ((γ ⊕ Fin m) ⊕ Fin ℓ)) : N.Formula (γ ⊕ Fin ℓ) :=
  Formula.iExs (Fin m)
    (Formula.relabel (Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)) ξ)


-- @@ L215-224 verbatim
theorem realize_exMid {A : Type} [N.Structure A] (ξ : N.Formula ((γ ⊕ Fin m) ⊕ Fin ℓ))
    (g : γ → A) (p : Fin ℓ → A) :
    (exMid ξ).Realize (Sum.elim g p) ↔
      ∃ u : Fin m → A, ξ.Realize (Sum.elim (Sum.elim g u) p) := by
  rw [exMid, Formula.realize_iExs]
  refine exists_congr fun u => ?_
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg _ ?_)
  funext x
  rcases x with (x | x) | x <;> rfl


-- @@ L226-228 verbatim
/-- A formula that does not mention a block of variables. -/
def weaken (ν : N.Formula (γ ⊕ Fin ℓ)) : N.Formula ((γ ⊕ Fin m) ⊕ Fin ℓ) :=
  Formula.relabel (Sum.map Sum.inl id) ν


-- @@ L230-236 verbatim
theorem realize_weaken {A : Type} [N.Structure A] (ν : N.Formula (γ ⊕ Fin ℓ)) (g : γ → A)
    (u : Fin m → A) (p : Fin ℓ → A) :
    (weaken ν).Realize (Sum.elim (Sum.elim g u) p) ↔ ν.Realize (Sum.elim g p) := by
  rw [weaken, Formula.realize_relabel]
  refine iff_of_eq (congrArg _ ?_)
  funext x
  rcases x with x | x <;> rfl


-- @@ L238-238 verbatim
end ExMid


-- @@ L240-240 verbatim
end Digits


-- @@ L242-242 verbatim
end DescriptiveComplexity
