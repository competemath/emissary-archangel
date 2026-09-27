/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Union
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific


-- @@ L21-24 verbatim
/-! ## Syntax of Basic Modal Logic

Here we supply basic definitions, abbreviations, and lemmas about the syntax of BML.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
namespace Lean4GlCoalgebras


-- @@ L30-40 verbatim
/-- Type of BML Formulas. -/
inductive Formula : Type
  | bottom : Formula
  | top : Formula
  | atom : Nat → Formula
  | negAtom : Nat → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | box : Formula → Formula
  | diamond : Formula → Formula
deriving Repr,DecidableEq


-- @@ L42-43 verbatim
/-- A sequent is a finite set of formulas, read disjunctively. -/
abbrev Sequent := Finset Formula


-- @@ L45-45 verbatim
namespace Formula


-- @@ L47-48 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:70 "at" => atom

-- @@ L49-50 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:70 "na" => negAtom

-- @@ L51-52 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:70 "□" => box

-- @@ L53-54 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:70 "◇" => diamond

-- @@ L55-56 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
infixr:6 "&" => and

-- @@ L57-58 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
infixr:6 "v" => or


-- @@ L60-60 verbatim
@[simp] instance instBot : Bot (Formula) where bot := Formula.bottom

-- @@ L61-61 verbatim
@[simp] instance instTop : Top (Formula) where top := Formula.top


-- @@ L63-72 expanded
/-- Negation of a BML Formula. -/
@[simp]
def neg : Formula → Formula
  | ⊥ => ⊤
  | ⊤ => ⊥
  | atom n => negAtom n
  | negAtom n => atom n
  | and φ ψ => or (neg φ) (neg ψ)
  | or φ ψ => and (neg φ) (neg ψ)
  | box φ => diamond (neg φ)
  | diamond φ => box (neg φ)


-- @@ L74-75 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:50 "~" => Formula.neg

-- @@ L76-77 expanded
/-- Auxiliary declaration used in the GL coalgebra development. -/
notation:55 φ:56 " ↣ " ψ:55 => or (Formula.neg φ) ψ


-- @@ L78-79 expanded
/-- Auxiliary declaration used in the GL coalgebra development. -/
notation:55 φ:56 " ⟷ " ψ:55 => and (or (Formula.neg φ) ψ) (or (Formula.neg ψ) φ)


-- @@ L80-81 expanded
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:50 " ⊡ " => fun φ ↦ and φ (box φ)


-- @@ L83-83 verbatim
/-! # Basic operations and simp lemmas for Formulas -/


-- @@ L85-88 expanded
/-- Returns `true` if the formula is a propositional atom `at n`. -/
def isAtomic : Formula → Bool
  | atom _ => true
  | _ => false


-- @@ L90-93 expanded
/-- Returns `true` if the formula is a negated atom `na n`. -/
def isNegAtomic : Formula → Bool
  | negAtom _ => true
  | _ => false


-- @@ L95-98 expanded
/-- Returns `true` if the formula is a diamond formula `◇ φ`. -/
def isDiamond : Formula → Bool
  | diamond _ => true
  | _ => false


-- @@ L100-103 expanded
/-- Returns `some φ` if the formula is `◇ φ`, otherwise `none`. -/
def opUnDi (φ : Formula) : Option Formula :=
  match φ with
  | diamond φ => Option.some φ
  | _ => none


-- @@ L105-106 expanded
@[simp]
lemma opUnDi_eq {φ ψ : Formula} : φ.opUnDi = some ψ ↔ φ = diamond ψ := by
  cases φ <;> simp [Formula.opUnDi]


-- @@ L108-110 expanded
/-- Extracts `φ` from `◇ φ`, given a proof that the formula is a diamond. -/
def unDi (φ : Formula) (h : φ.isDiamond) : Formula :=
  match φ with
  | diamond φ => φ


-- @@ L112-115 expanded
/-- Returns `true` if the formula is a box formula `□ φ`. -/
def isBox : Formula → Bool
  | box _ => true
  | _ => false


-- @@ L118-123 expanded
/-- Negation is injective. -/
lemma neg_eq {φ ψ : Formula} : (Formula.neg φ) = (Formula.neg ψ) → φ = ψ :=
  by
  intro mpp
  cases φ <;> cases ψ <;> simp [Formula.neg] at mpp <;> try grind
  case and.and | or.or => grind [neg_eq mpp.1, neg_eq mpp.2]
  case box.box | diamond.diamond => grind [neg_eq mpp]


-- @@ L125-128 expanded
/-- Negation is involutive. -/
@[simp]
lemma neg_neg_eq (φ : Formula) : (Formula.neg (Formula.neg φ)) = φ := by
  induction φ <;> simp_all [Formula.neg] <;> rfl


-- @@ L130-139 expanded
/-- Length of a BML Formula. -/
def length : Formula → Nat
  | ⊥ => 0
  | ⊤ => 0
  | atom _ => 1
  | negAtom _ => 1
  | and φ ψ => length φ + length ψ + 1
  | or φ ψ => length φ + length ψ + 1
  | box φ => length φ + 1
  | diamond φ => length φ + 1


-- @@ L142-151 expanded
/-- Vocab of a BML Formula. Expressed as underlying natural numbers. -/
def vocab : Formula → Finset Nat
  | ⊥ => ∅
  | ⊤ => ∅
  | atom n => { n }
  | negAtom n => { n }
  | and φ ψ => vocab φ ∪ vocab ψ
  | or φ ψ => vocab φ ∪ vocab ψ
  | box φ => vocab φ
  | diamond φ => vocab φ


-- @@ L153-162 expanded
/-- Atoms of a BML Formula. Expressed as underlying natural numbers. -/
def atoms : Formula → Finset Nat
  | ⊥ => ∅
  | ⊤ => ∅
  | atom n => { n }
  | negAtom _ => ∅
  | and φ ψ => vocab φ ∪ vocab ψ
  | or φ ψ => vocab φ ∪ vocab ψ
  | box φ => vocab φ
  | diamond φ => vocab φ


-- @@ L164-173 expanded
/-- Literals of a BML Formula. Expressed as underlying natural numbers. -/
def lit : Formula → Finset (Nat ⊕ Nat)
  | ⊥ => ∅
  | ⊤ => ∅
  | atom n => {Sum.inl n}
  | negAtom n => {Sum.inr n}
  | and φ ψ => lit φ ∪ lit ψ
  | or φ ψ => lit φ ∪ lit ψ
  | box φ => lit φ
  | diamond φ => lit φ


-- @@ L175-184 expanded
/-- Get a fresh variable not occuring in a BML Formula. -/
def freshVar : Formula → Nat
  | ⊤ => 0
  | ⊥ => 0
  | atom n => n + 1
  | negAtom n => n + 1
  | and φ ψ => max (freshVar φ) (freshVar ψ)
  | or φ ψ => max (freshVar φ) (freshVar ψ)
  | box φ => freshVar φ
  | diamond φ => freshVar φ


-- @@ L186-195 expanded
/-- Fischer-Ladner closure of a BML Formula. -/
def FL : Formula → Sequent
  | ⊥ => {⊥}
  | ⊤ => {⊤}
  | atom n => {atom n}
  | negAtom n => {negAtom n}
  | or φ ψ => {or φ ψ} ∪ FL φ ∪ FL ψ
  | and φ ψ => {and φ ψ} ∪ FL φ ∪ FL ψ
  | box φ => {box φ} ∪ FL φ
  | diamond φ => {diamond φ} ∪ FL φ


-- @@ L197-197 verbatim
/-! # Lemmas about FL Closure of BML Formulas -/


-- @@ L199-201 verbatim
/-- Fischer-Ladner closure is reflexive. -/
lemma FL_refl {φ : Formula} : φ ∈ FL φ := by
  cases φ <;> simp [FL] <;> rfl


-- @@ L203-221 verbatim
/-- Fischer-Ladner closure is monotone. -/
lemma FL_mon {φ ψ : Formula} (ψ_sub_φ : ψ ∈ FL φ) : FL ψ ⊆ FL φ := by
  cases φ <;>
    simp only [FL, Finset.mem_singleton, Finset.mem_union, Finset.subset_iff] at ψ_sub_φ ⊢
  case bottom | top | atom | negAtom =>
    intro x x_in
    subst ψ
    simpa only [FL, Finset.mem_singleton] using x_in
  case and | or =>
    intro x x_in
    rcases ψ_sub_φ with (rfl | ψ_sub) | ψ_sub
    · simpa only [FL, Finset.mem_singleton, Finset.mem_union] using x_in
    · exact Or.inl (Or.inr (FL_mon ψ_sub x_in))
    · exact Or.inr (FL_mon ψ_sub x_in)
  case box | diamond =>
    intro x x_in
    rcases ψ_sub_φ with rfl | ψ_sub
    · simpa only [FL, Finset.mem_singleton, Finset.mem_union] using x_in
    · exact Or.inr (FL_mon ψ_sub x_in)


-- @@ L223-223 verbatim
end Formula


-- @@ L225-225 verbatim
namespace Sequent


-- @@ L227-227 verbatim
/-! # Basic operations and simp lemmas for Sequents -/

-- @@ L228-231 verbatim
/-- Length of a sequent. -/
def length (Γ : Sequent) : Nat := Finset.sum Γ Formula.length

/- Vocabulary of a sequent. -/

-- @@ L232-235 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
def vocab (Γ : Sequent) : Finset Nat := Finset.biUnion Γ Formula.vocab

/- Literals of a sequent. -/

-- @@ L236-239 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
def lit (Γ : Sequent) : Finset (Nat ⊕ Nat) := Finset.biUnion Γ Formula.lit

/- Negation of a sequent. -/

-- @@ L240-243 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
def neg (Γ : Sequent) : Finset Formula := Finset.biUnion Γ (fun φ ↦ {Formula.neg φ})

/- Given a sequent `Γ`, finds a variable not in `Γ`-/

-- @@ L244-248 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
def freshVar (Γ : Finset Formula) : Nat :=
  if h : Γ = {} then 0 else Finset.max' (Γ.image (Formula.freshVar)) (by
    by_contra con
    simp_all)


-- @@ L250-254 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
def D (Γ : Sequent) : Sequent := Finset.filter (
  fun x => decide (Formula.isDiamond x)) Γ
       ∪ Finset.filterMap Formula.opUnDi Γ (by
  simp_all)


-- @@ L256-257 verbatim
lemma form_in_seq_size_le {A : Formula} {Δ : Sequent} : A ∈ Δ → A.length ≤ Δ.length :=
  fun A_in ↦ Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.2 A_in) (by simp)


-- @@ L259-260 verbatim
/-- Fischer-Ladner closure of a sequent. -/
def FL : Sequent → Sequent := fun Δ ↦ Finset.biUnion Δ Formula.FL


-- @@ L262-264 verbatim
/-! # Lemmas about FL Closure of Sequents -/

/- Fischer-Ladner closure is reflexive. -/

-- @@ L265-269 verbatim
lemma FL_refl {Δ : Sequent} : Δ ⊆ FL Δ := by
  intro x x_in
  exact Finset.mem_biUnion.mpr ⟨x, x_in, Formula.FL_refl⟩

/- Fischer-Ladner closure is monotone. -/

-- @@ L270-275 verbatim
lemma FL_mon {Δ Γ : Sequent} (Δ_sub_Γ : Δ ⊆ Γ) : FL Δ ⊆ FL Γ := by
  intro φ φ_in
  rcases Finset.mem_biUnion.mp φ_in with ⟨ψ, ψ_in_Δ, φ_sub_ψ⟩
  exact Finset.mem_biUnion.mpr ⟨ψ, Δ_sub_Γ ψ_in_Δ, φ_sub_ψ⟩

/- Fischer-Ladner closure is idempotent. -/

-- @@ L276-282 verbatim
lemma FL_idem {Δ : Sequent} : FL (FL Δ) = FL Δ := by
  apply Finset.Subset.antisymm
  · intro φ φ_in
    rcases Finset.mem_biUnion.mp φ_in with ⟨ψ, ψ_in, φ_sub_ψ⟩
    rcases Finset.mem_biUnion.mp ψ_in with ⟨χ, χ_in_Δ, ψ_sub_χ⟩
    exact Finset.mem_biUnion.mpr ⟨χ, χ_in_Δ, Formula.FL_mon ψ_sub_χ φ_sub_ψ⟩
  · exact FL_mon FL_refl



-- @@ L285-285 verbatim
end Sequent


-- @@ L287-288 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
abbrev SplitFormula := Formula ⊕ Formula

-- @@ L289-290 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
abbrev SplitSequent := Finset SplitFormula


-- @@ L292-292 verbatim
/-! # Basic operations and simp lemmas for Split Sequents -/


-- @@ L294-294 verbatim
namespace SplitFormula

-- @@ L295-299 expanded
/-- Auxiliary declaration used in the GL coalgebra development. -/
def isDiamond : SplitFormula → Bool
  | Sum.inl (diamond _) => true
  | Sum.inr (diamond _) => true
  | _ => false


-- @@ L301-308 expanded
/-- Auxiliary declaration used in the GL coalgebra development. -/
def opUnDi (φ : SplitFormula) : Option SplitFormula :=
  match φ with
  | Sum.inl (diamond ψ) => Option.some (Sum.inl ψ)
  | Sum.inr (diamond ψ) => Option.some (Sum.inr ψ)
  | _ => none


-- @@ L309-314 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
def length : (Formula ⊕ Formula) → Nat
  | Sum.inl φ => φ.length
  | Sum.inr φ => φ.length

/- Fischer-Ladner closure of a Split Formula (preserving the formula annotation). -/

-- @@ L315-332 expanded
/-- Auxiliary declaration used in the GL coalgebra development. -/
def FL : SplitFormula → SplitSequent
  | Sum.inl ⊥ => {Sum.inl ⊥}
  | Sum.inr ⊥ => {Sum.inr ⊥}
  | Sum.inl ⊤ => {Sum.inl ⊤}
  | Sum.inr ⊤ => {Sum.inr ⊤}
  | Sum.inl (atom n) => {Sum.inl (atom n)}
  | Sum.inr (atom n) => {Sum.inr (atom n)}
  | Sum.inl (negAtom n) => {Sum.inl (negAtom n)}
  | Sum.inr (negAtom n) => {Sum.inr (negAtom n)}
  | Sum.inl (or φ ψ) => {Sum.inl (or φ ψ)} ∪ FL (Sum.inl φ) ∪ FL (Sum.inl ψ)
  | Sum.inr (or φ ψ) => {Sum.inr (or φ ψ)} ∪ FL (Sum.inr φ) ∪ FL (Sum.inr ψ)
  | Sum.inl (and φ ψ) => {Sum.inl (and φ ψ)} ∪ FL (Sum.inl φ) ∪ FL (Sum.inl ψ)
  | Sum.inr (and φ ψ) => {Sum.inr (and φ ψ)} ∪ FL (Sum.inr φ) ∪ FL (Sum.inr ψ)
  | Sum.inl (box φ) => {Sum.inl (box φ)} ∪ FL (Sum.inl φ)
  | Sum.inr (box φ) => {Sum.inr (box φ)} ∪ FL (Sum.inr φ)
  | Sum.inl (diamond φ) => {Sum.inl (diamond φ)} ∪ FL (Sum.inl φ)
  | Sum.inr (diamond φ) => {Sum.inr (diamond φ)} ∪ FL (Sum.inr φ)


-- @@ L334-334 verbatim
/-! # Lemmas about FL Closure of Split Formulas -/


-- @@ L336-338 verbatim
lemma FL_SplitFormula_left_eq_FL_Formula_map (φ : Formula) :
  FL (Sum.inl φ) = φ.FL.map ⟨Sum.inl, Sum.inl_injective⟩ := by
  induction φ <;> simp_all [FL, Formula.FL, Finset.map_union]


-- @@ L340-342 verbatim
lemma FL_SplitFormula_right_eq_FL_Formula_map (φ : Formula) :
  FL (Sum.inr φ) = φ.FL.map ⟨Sum.inr, Sum.inr_injective⟩ := by
  induction φ <;> simp_all [FL, Formula.FL, Finset.map_union]


-- @@ L344-346 verbatim
lemma in_FL_SplitFormula_left {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inl φ)) : ψ.isLeft := by
  induction φ <;> simp_all [FL] <;> grind


-- @@ L348-350 verbatim
lemma in_FL_SplitFormula_right {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inr φ)) : ψ.isRight := by
  induction φ <;> simp_all [FL] <;> grind


-- @@ L352-354 verbatim
lemma in_FL_of_in_FL_SplitFormula_left {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inl φ)) : ψ.elim id id ∈ φ.FL := by
  rcases ψ with ψ | ψ <;> induction φ <;> simp_all [FL, Formula.FL] <;> grind


-- @@ L356-358 verbatim
lemma in_FL_of_in_FL_SplitFormula_right {φ : Formula} {ψ : SplitFormula}
  (ψ_sub_φ : ψ ∈ FL (Sum.inr φ)) : ψ.elim id id ∈ φ.FL := by
  rcases ψ with ψ | ψ <;> induction φ <;> simp_all [FL, Formula.FL] <;> grind


-- @@ L360-362 verbatim
/-- Fischer-Ladner Closure is reflexive. -/
lemma FL_refl {φ : SplitFormula} : φ ∈ FL φ := by
  rcases φ with φ | φ <;> cases φ <;> simp [FL] <;> rfl


-- @@ L364-382 verbatim
/-- Fischer-Ladner Closure is monotone. -/
lemma FL_mon {φ ψ : SplitFormula} (ψ_sub_φ : ψ ∈ FL φ) : FL ψ ⊆ FL φ := by
  rcases φ with φ | φ
  · rcases ψ with ψ | ψ
    · rw [FL_SplitFormula_left_eq_FL_Formula_map φ, FL_SplitFormula_left_eq_FL_Formula_map ψ]
      intro x x_in
      rcases Finset.mem_map.mp x_in with ⟨χ, χ_in, rfl⟩
      exact Finset.mem_map.mpr
        ⟨χ, Formula.FL_mon (in_FL_of_in_FL_SplitFormula_left ψ_sub_φ) χ_in, rfl⟩
    · have is_left := in_FL_SplitFormula_left ψ_sub_φ
      simp_all
  · rcases ψ with ψ | ψ
    · have is_right := in_FL_SplitFormula_right ψ_sub_φ
      simp_all
    · rw [FL_SplitFormula_right_eq_FL_Formula_map φ, FL_SplitFormula_right_eq_FL_Formula_map ψ]
      intro x x_in
      rcases Finset.mem_map.mp x_in with ⟨χ, χ_in, rfl⟩
      exact Finset.mem_map.mpr
        ⟨χ, Formula.FL_mon (in_FL_of_in_FL_SplitFormula_right ψ_sub_φ) χ_in, rfl⟩


-- @@ L384-384 verbatim
end SplitFormula


-- @@ L386-386 verbatim
namespace SplitSequent


-- @@ L388-388 verbatim
/-! # Lemmas about FL Closure of Split Sequents -/

-- @@ L389-390 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
def FL : SplitSequent → SplitSequent := fun Δ ↦ Finset.biUnion Δ SplitFormula.FL


-- @@ L392-395 verbatim
/-- Fischer-Ladner Closure is reflexive. -/
lemma FL_refl {Δ : SplitSequent} : Δ ⊆ FL Δ := by
  intro x x_in
  exact Finset.mem_biUnion.mpr ⟨x, x_in, SplitFormula.FL_refl⟩


-- @@ L397-401 verbatim
/-- Fischer-Ladner Closure is monotone. -/
lemma FL_mon {Δ Γ : SplitSequent} (Δ_sub_Γ : Δ ⊆ Γ) : FL Δ ⊆ FL Γ := by
  intro φ φ_in
  rcases Finset.mem_biUnion.mp φ_in with ⟨ψ, ψ_in_Δ, φ_sub_ψ⟩
  exact Finset.mem_biUnion.mpr ⟨ψ, Δ_sub_Γ ψ_in_Δ, φ_sub_ψ⟩


-- @@ L403-410 verbatim
/-- Fischer-Ladner Closure is idempotent. -/
lemma FL_idem {Δ : SplitSequent} : FL (FL Δ) = FL Δ := by
  apply Finset.Subset.antisymm
  · intro φ φ_in
    rcases Finset.mem_biUnion.mp φ_in with ⟨ψ, ψ_in, φ_sub_ψ⟩
    rcases Finset.mem_biUnion.mp ψ_in with ⟨χ, χ_in_Δ, ψ_sub_χ⟩
    exact Finset.mem_biUnion.mpr ⟨χ, χ_in_Δ, SplitFormula.FL_mon ψ_sub_χ φ_sub_ψ⟩
  · exact FL_mon FL_refl


-- @@ L412-422 verbatim
/-- □₄⁻¹ operator for Split Sequents. -/
def D (Γ : SplitSequent) : SplitSequent
  := Finset.filter (fun x => decide (SplitFormula.isDiamond x)) Γ
                         ∪ Finset.filterMap SplitFormula.opUnDi Γ (by
  intro φ ψ C C_in_A C_in_B
  rcases φ with φ | φ <;> rcases ψ with ψ | ψ <;> rcases C with C | C
  all_goals
    simp_all
    cases φ <;> cases ψ
    all_goals
      simp_all [SplitFormula.opUnDi])


-- @@ L424-424 verbatim
/-! # Basic operations and simp lemmas for Split Sequents -/


-- @@ L426-427 verbatim
/-- Find underlying Sequent of a Split Sequent. -/
def toSequent (Δ : SplitSequent) : Sequent := Finset.image (Sum.elim id id) Δ


-- @@ L429-430 verbatim
/-- Length of a Split Sequent. -/
def length (Δ : SplitSequent) : Nat := Finset.sum Δ (SplitFormula.length)


-- @@ L432-435 expanded
@[simp]
lemma opUnDi_eqₗₗ {φ ψ : Formula} :
    SplitFormula.opUnDi (Sum.inl φ) = some (Sum.inl ψ) ↔ φ = diamond ψ := by
  cases φ <;> simp [SplitFormula.opUnDi]


-- @@ L437-440 expanded
@[simp]
lemma opUnDi_eqᵣᵣ {φ ψ : Formula} :
    SplitFormula.opUnDi (Sum.inr φ) = some (Sum.inr ψ) ↔ φ = diamond ψ := by
  cases φ <;> simp [SplitFormula.opUnDi]


-- @@ L442-444 verbatim
@[simp]
lemma opUnDi_eqₗᵣ {φ ψ : Formula} : ¬ (SplitFormula.opUnDi (Sum.inl φ) = some (Sum.inr ψ)) := by
  cases φ <;> simp [SplitFormula.opUnDi]


-- @@ L446-448 verbatim
@[simp]
lemma opUnDi_eqᵣₗ {φ ψ : Formula} : ¬ (SplitFormula.opUnDi (Sum.inr φ) = some (Sum.inl ψ)) := by
  cases φ <;> simp [SplitFormula.opUnDi]


-- @@ L450-454 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
@[simp]
noncomputable def filterLeft : SplitSequent → SplitSequent := @Finset.filter _
  (fun | Sum.inl _ => true | Sum.inr _ => false)
  (fun | Sum.inl _ => isTrue (by simp) | Sum.inr _ => isFalse (by simp))


-- @@ L456-460 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
@[simp]
noncomputable def filterRight : SplitSequent → SplitSequent := @Finset.filter _
  (fun | Sum.inl _ => false | Sum.inr _ => true)
  (fun | Sum.inl _ => isFalse (by simp) | Sum.inr _ => isTrue (by simp))


-- @@ L462-463 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
def left (Γ : SplitSequent) : Sequent := Γ.filterMap (Sum.getLeft?) (by aesop)

-- @@ L464-465 verbatim
/-- Auxiliary declaration used in the GL coalgebra development. -/
def right (Γ : SplitSequent) : Sequent := Γ.filterMap (Sum.getRight?) (by aesop)


-- @@ L467-467 verbatim
end SplitSequent


-- @@ L469-469 verbatim
/-! # Properties of Substitutions -/


-- @@ L471-482 expanded
/-- Substiting `p` with `ψ` in `φ` (`φ[ψ/p]`). -/
def single (n : Nat) (ψ : Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | atom k => if k == n then ψ else atom k
  | negAtom k => if k == n then Formula.neg ψ else negAtom k
  | and φ₁ φ₂ => and (single n ψ φ₁) (single n ψ φ₂)
  | or φ₁ φ₂ => or (single n ψ φ₁) (single n ψ φ₂)
  | box φ => box (single n ψ φ)
  | diamond φ =>
    diamond
      (single n ψ φ)
        /- Single substitution preserves negation. -/


-- @@ L483-486 expanded
lemma single_neg (n : Nat) (φ ψ : Formula) :
    single n ψ (Formula.neg φ) = (Formula.neg (single n ψ φ)) := by
  induction φ <;> simp [Formula.neg, single] <;>
    aesop
      /- Single substitution preserves implication. -/


-- @@ L487-491 expanded
lemma single_imp (n : Nat) (C D E : Formula) :
    single n C (or (Formula.neg D) E) = or (Formula.neg (single n C D)) (single n C E) := by
  simp [single, single_neg]
    /- Single substitution preserves bi-implication. -/


-- @@ L492-494 expanded
lemma single_iff (n : Nat) (C D E : Formula) :
    single n C (and (or (Formula.neg D) E) (or (Formula.neg E) D)) =
      and (or (Formula.neg (single n C D)) (single n C E))
        (or (Formula.neg (single n C E)) (single n C D)) :=
  by simp [single, single_neg]


-- @@ L496-498 expanded
@[simp]
lemma single_identity (n : ℕ) (φ : Formula) : (single n (atom n) φ) = φ := by
  induction φ <;> simp_all [single] <;> rfl


-- @@ L500-509 expanded
/-- Simultaneous substitution for `p` meeting criteria `c`. -/
def partial_ {c : Nat → Prop} [DecidablePred c] (σ : Subtype c → Formula) : Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | atom n => if h : c n then σ ⟨n, h⟩ else atom n
  | negAtom n => if h : c n then Formula.neg (σ ⟨n, h⟩) else negAtom n
  | and A B => and (partial_ σ A) (partial_ σ B)
  | or A B => or (partial_ σ A) (partial_ σ B)
  | box A => box (partial_ σ A)
  | diamond A => diamond (partial_ σ A)


-- @@ L511-525 expanded
/-- Full substitution of all `p`. -/
def full (σ : Nat → Formula) (A : Formula) : Formula :=
  match A with
  | ⊥ => ⊥
  | ⊤ => ⊤
  | atom n => σ n
  | negAtom n => Formula.neg (σ n)
  | and A B => and (full σ A) (full σ B)
  | or A B => or (full σ A) (full σ B)
  | box A => box (full σ A)
  | diamond A => diamond (full σ A)
termination_by Formula.length A
decreasing_by
  all_goals
    simp [Formula.length]
    try linarith


-- @@ L527-529 verbatim
/-! # Properties of Vocab -/

/- `p` is in the vocabulary of `φ` if and only if `p` is in the vocabulary of `~φ`. -/

-- @@ L530-531 expanded
@[simp]
lemma in_neg_voc_iff {n : Nat} {φ : Formula} : n ∈ (Formula.neg φ).vocab ↔ n ∈ φ.vocab := by
  induction φ <;> simp_all [Formula.vocab]


-- @@ L533-559 verbatim
lemma in_single_voc (m n : Nat) (φ ψ : Formula) :
  m ∉ φ.vocab → (m ≠ n → m ∉ ψ.vocab) → n ∉ φ.vocab → m ∉ (single n φ ψ).vocab := by
    intro mp
    induction ψ <;>
      simp_all only [single, Formula.vocab, Finset.notMem_empty, Finset.mem_singleton,
        Finset.mem_union, not_or, beq_iff_eq, ne_eq]
    case atom k =>
      intro hψ hn m_in
      by_cases hk : k = n
      · simp_all
      · by_cases hm : m = n
        · subst m
          exact (Ne.symm hk) (by
            simpa only [hk, ite_false, Formula.vocab, Finset.mem_singleton] using m_in)
        · exact hψ hm (by
            simpa only [hk, ite_false, Formula.vocab, Finset.mem_singleton] using m_in)
    case negAtom k =>
      intro hψ hn m_in
      by_cases hk : k = n
      · simp_all
      · by_cases hm : m = n
        · subst m
          exact (Ne.symm hk) (by
            simpa only [hk, ite_false, Formula.vocab, Finset.mem_singleton] using m_in)
        · exact hψ hm (by
            simpa only [hk, ite_false, Formula.vocab, Finset.mem_singleton] using m_in)
    all_goals aesop


-- @@ L561-564 verbatim
lemma not_in_single_voc (n : Nat) (φ ψ : Formula) :
  n ∉ φ.vocab → (single n ψ φ) = φ := by
  intro h
  induction φ <;> simp_all [single, Formula.vocab] <;> aesop


-- @@ L566-570 verbatim
lemma not_in_single_top_voc (n : ℕ) (φ : Formula) : n ∉ (single n ⊤ φ).vocab := by
  apply in_single_voc n n ⊤ φ
  · simpa only [Formula.instTop, Formula.vocab] using Finset.notMem_empty n
  · simp_all
  · simpa only [Formula.instTop, Formula.vocab] using Finset.notMem_empty n


-- @@ L572-576 verbatim
lemma not_in_single_bot_voc (n : ℕ) (φ : Formula) : n ∉ (single n ⊥ φ).vocab := by
  apply in_single_voc n n ⊥ φ
  · simpa only [Formula.instBot, Formula.vocab] using Finset.notMem_empty n
  · simp_all
  · simpa only [Formula.instBot, Formula.vocab] using Finset.notMem_empty n


-- @@ L578-583 verbatim
lemma in_single_voc' {m n : ℕ} {φ ψ : Formula} :
    m ∈ (single n φ ψ).vocab →
      (m ∈ φ.vocab ∧ n ∈ ψ.vocab) ∨ (m ∈ ψ.vocab ∧ m ≠ n) := by
  intro m_in
  induction ψ <;> simp_all [single] <;>
    try grind [Formula.vocab, in_neg_voc_iff, Formula.instTop, Formula.instBot]



-- @@ L586-590 verbatim
/-! # Some very specific lemmas about Finset.sum

Ideally grind or aesop or some other tactic could sort out these simple helper lemmas, but I could
not figure out how.
-/


-- @@ L592-592 verbatim
lemma sub_add_left {n m l : Nat} : n + m = l → n = l - m := by omega


-- @@ L594-594 verbatim
lemma lt_and_le_imp_add_lt {a b c : ℕ} : b ≤ a → c < b → (a - b) + c < a := by omega


-- @@ L596-611 verbatim
lemma Finset.sum_diff_singleton_lt {α : Type} [DecidableEq α] {A C : Finset α} {b : α} {f : α → Nat}
  : b ∈ A → C.sum f < f b → Finset.sum ((A \ {b}) ∪ C) f < Finset.sum A f := by
  intro b_in_A C_lt_B
  calc
    _ ≤ Finset.sum (A \ {b}) f + Finset.sum C f := by
      simp [sub_add_left <| @Finset.sum_union_inter _ _ (A \ {b}) C _ f _]
    _ = Finset.sum A f - Finset.sum {b} f + Finset.sum C f := by
      have singleton_subset : {b} ⊆ A := Finset.singleton_subset_iff.2 b_in_A
      simp [sub_add_left <| @Finset.sum_sdiff α Nat {b} A _ f _ singleton_subset]
    _ < Finset.sum A f := by
      apply lt_and_le_imp_add_lt
      · exact
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.singleton_subset_iff.2 b_in_A)
            (by simp)
      · exact C_lt_B

-- @@ L612-612 verbatim
end Lean4GlCoalgebras
