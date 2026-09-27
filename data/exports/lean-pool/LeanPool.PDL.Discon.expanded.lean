/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Semantics
public import LeanPool.PDL.Vocab
public import Mathlib.Data.Finset.Sort


-- @@ L13-16 verbatim
/-! # (Big) Disjunction and Conjunction

Here we define ⋀ and ⋁ on formulas and seveal helper lemmas.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace PDL


-- @@ L22-22 verbatim
/-! ## Conjunction -/


-- @@ L24-29 verbatim
/-- Conjunction of a list of formulas, with the empty conjunction equal to truth. -/
@[simp]
def con : List Formula → Formula
  | [] => ⊤
  | [f] => f
  | f :: rest => f⋀con rest


-- @@ L31-31 verbatim
theorem conempty : con ∅ = (⊤ : Formula) := by rfl


-- @@ L33-34 verbatim
@[simp]
theorem consingle {f : Formula} : con [f] = f := by rfl


-- @@ L36-37 verbatim
theorem listEq_to_conEq : l1 = l2 → con l1 = con l2 := by
  aesop


-- @@ L39-44 verbatim
theorem conEvalHT {X f W M} {w : W} :
    evaluate M w (con (f :: X)) ↔ evaluate M w f ∧ evaluate M w (con X) :=
  by
  induction X
  · simp
  · simp


-- @@ L46-53 verbatim
theorem conEval {W M X} {w : W} : evaluate M w (con X) ↔ ∀ f ∈ X, evaluate M w f :=
  by
  induction X
  · simp
  · rw [conEvalHT]
    simp only [List.mem_cons, forall_eq_or_imp, and_congr_right_iff]
    intro _
    assumption


-- @@ L55-65 verbatim
/-- Vocabulary of Conjunction -/
theorem in_voc_con n (L : List Formula) :
    n ∈ (con L).voc ↔ ∃ φ ∈ L, n ∈ φ.voc := by
  induction L
  · simp [con, Formula.voc]
  case cons h t IH =>
    induction t -- needed to select case in `Con`
    · simp [con]
    case cons h t IH =>
      simp only [List.mem_cons, exists_eq_or_imp, con, Formula.voc, Finset.mem_union] at *
      rw [← IH]


-- @@ L67-68 verbatim
/-- The conjunction of a `Finset` of formulas, via `Finset.pdlSort`. -/
def _root_.Finset.pdlCon (X : Finset Formula) : Formula := _root_.PDL.con X.pdlSort


-- @@ L70-72 verbatim
@[simp]
theorem Finset.con_empty : Finset.pdlCon ∅ = (⊤ : Formula) := by
  simp [Finset.pdlCon, Finset.pdlSort]


-- @@ L74-76 verbatim
@[simp]
theorem Finset.con_singleton {f : Formula} : Finset.pdlCon {f} = f := by
  simp [Finset.pdlCon, Finset.pdlSort]


-- @@ L78-80 verbatim
theorem Finset.conEval {W M} {X : Finset Formula} {w : W} :
    evaluate M w X.pdlCon ↔ ∀ f ∈ X, evaluate M w f := by
  simp [Finset.pdlCon, _root_.PDL.conEval]


-- @@ L82-86 verbatim
/-- Evaluating a conjunction does not care about sorting. -/
lemma evaluate_con_sort (X : Finset Formula) :
    evaluate M w (con (X.sort fun a b ↦ a ≤ b)) ↔ ∀ φ ∈ X, evaluate M w φ := by
  rw [conEval]
  simp


-- @@ L88-91 verbatim
/-- Vocabulary of the conjunction of a `Finset`. -/
theorem Finset.in_voc_con n (X : Finset Formula) :
    n ∈ X.pdlCon.voc ↔ ∃ φ ∈ X, n ∈ φ.voc := by
  simp [Finset.pdlCon, _root_.PDL.in_voc_con]


-- @@ L93-93 verbatim
/-! ## Disjunction -/


-- @@ L95-100 verbatim
/-- Disjunction of a list of formulas, with the empty disjunction equal to falsity. -/
@[simp]
def dis : List Formula → Formula
  | [] => ⊥
  | [f] => f
  | f :: rest => f ⋁ dis rest


-- @@ L102-103 verbatim
@[simp]
theorem disempty : dis ∅ = (⊥ : Formula) := rfl


-- @@ L105-106 verbatim
@[simp]
theorem dissingle {f : Formula} : dis [f] = f := rfl


-- @@ L108-109 verbatim
theorem listEq_to_disEq : l1 = l2 → dis l1 = dis l2 := by
  aesop


-- @@ L111-117 verbatim
theorem disEvalHT {X f W M} {w : W} :
    evaluate M w (dis (f :: X)) ↔ evaluate M w f ∨ evaluate M w (dis X) :=
  by
  induction X
  · simp
  · simp
    tauto


-- @@ L119-124 verbatim
theorem disEval {W M X} {w : W} : evaluate M w (dis X) ↔ ∃ f ∈ X, evaluate M w f :=
  by
  induction X
  · simp
  · rw [disEvalHT]
    simp_all


-- @@ L126-137 verbatim
/-- Vocabulary of Disjunction -/
theorem in_voc_dis n (L : List Formula) :
    n ∈ (dis L).voc ↔ ∃ φ ∈ L, n ∈ φ.voc := by
  induction L
  · simp [dis, Formula.voc]
  case cons h t IH =>
    induction t -- needed to select case in `dis`
    · simp [dis]
    case cons h t IH =>
      simp only [List.mem_cons, exists_eq_or_imp, dis, Formula.or, Formula.voc, Finset.mem_union]
        at *
      rw [← IH]


-- @@ L139-140 verbatim
/-- The disjunction of a `Finset` of formulas, via `Finset.pdlSort`. -/
def _root_.Finset.pdlDis (X : Finset Formula) : Formula := _root_.PDL.dis X.pdlSort


-- @@ L142-144 verbatim
@[simp]
theorem Finset.dis_empty : Finset.pdlDis ∅ = (⊥ : Formula) := by
  simp [Finset.pdlDis, Finset.pdlSort]


-- @@ L146-148 verbatim
@[simp]
theorem Finset.dis_singleton {f : Formula} : Finset.pdlDis {f} = f := by
  simp [Finset.pdlDis, Finset.pdlSort]


-- @@ L150-152 verbatim
theorem Finset.disEval {W M} {X : Finset Formula} {w : W} :
    evaluate M w X.pdlDis ↔ ∃ f ∈ X, evaluate M w f := by
  simp [Finset.pdlDis, _root_.PDL.disEval]


-- @@ L154-157 verbatim
/-- Vocabulary of the disjunction of a `Finset`. -/
theorem Finset.in_voc_dis n (X : Finset Formula) :
    n ∈ X.pdlDis.voc ↔ ∃ φ ∈ X, n ∈ φ.voc := by
  simp [Finset.pdlDis, _root_.PDL.in_voc_dis]


-- @@ L159-159 verbatim
/-! ## Disjunction of Conjunctions -/


-- @@ L161-166 verbatim
/-- Disjunction of the conjunctions represented by a list of formula lists. -/
@[simp]
def discon : List (List Formula) → Formula
  | [] => ⊥
  | [X] => con X
  | X :: rest => con X ⋁ discon rest


-- @@ L168-168 verbatim
theorem disconempty : discon {∅} = (⊤ : Formula) := by rfl


-- @@ L170-171 verbatim
@[simp]
theorem disconsingle {f : Formula} : discon [[f]] = f := by rfl


-- @@ L173-177 verbatim
theorem disconEvalHT {X} : ∀ XS, discon (X :: XS) ≡ con X ⋁ discon XS :=
  by
  unfold semEquiv
  intro XS W M w
  cases XS <;> simp


-- @@ L179-215 verbatim
/-- Variant of `disconEval` for a specific length of `XS` to be provable by induction. -/
theorem disconEval' {W M} {w : W} :
    ∀ {N : Nat} XS,
      List.length XS = N → (evaluate M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, evaluate M w f) := by
  intro N
  induction N using Nat.strong_induction_on
  case h n IH =>
    intro XS def_n
    subst def_n
    rcases XS with _ | ⟨X,XS⟩
    · simp
    specialize IH XS.length (by simp) XS (by rfl)
    rw [disconEvalHT]
    rw [evalDis]
    rw [IH]
    constructor
    · -- →
      intro lhs
      rcases lhs with lhs|lhs
      · use X
        simp only [List.mem_cons, true_or, true_and]
        rw [conEval] at lhs
        tauto
      · rcases lhs with ⟨Y,claim⟩
        use Y
        simp only [List.mem_cons]
        tauto
    · -- ←
      intro rhs
      rcases rhs with ⟨Y,Y_in,Ysat⟩
      simp only [List.mem_cons] at Y_in
      rcases Y_in with Y_in|Y_in
      · left
        subst Y_in
        rw [conEval]; tauto
      · right
        use Y


-- @@ L217-222 verbatim
theorem disconEval {W M} {w : W} :
    ∀ XS,
      (evaluate M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, evaluate M w f) :=
  by
    intro XS
    apply disconEval' XS rfl


-- @@ L224-257 verbatim
theorem disconOr {XS YS} : discon (XS ∪ YS) ≡ discon XS ⋁ discon YS :=
  by
  unfold semEquiv
  intro W M w
  rw [disconEval (XS ∪ YS)]
  simp only [List.mem_union_iff, Formula.or, evaluate.eq_3, evaluate, not_and, not_not]
  rw [disconEval XS]
  rw [disconEval YS]
  constructor
  · -- →
    intro lhs
    rcases lhs with ⟨Z, Z_in, w_sat_Z⟩
    intro notL
    simp only [not_exists, not_and, not_forall] at notL
    cases Z_in
    case inl Z_in_XS =>
      specialize notL Z Z_in_XS
      rcases notL with ⟨f, f_in_Z, w_not_f⟩
      specialize w_sat_Z f f_in_Z
      absurd w_sat_Z
      exact w_not_f
    use Z
  · -- ←
    intro rhs
    cases (Classical.em (∃ Y, Y ∈ XS ∧ ∀ (f : Formula), f ∈ Y → evaluate M w f))
    case inl hyp =>
      rcases hyp with ⟨X, X_in, satX⟩
      use X
      exact ⟨Or.inl X_in, satX⟩
    case inr nothyp =>
      specialize rhs nothyp
      rcases rhs with ⟨Y, Y_in, satY⟩
      use Y
      exact ⟨Or.inr Y_in, satY⟩


-- @@ L259-265 verbatim
/-! ### Sorting lists of formulas

To also sort a `Finset (Finset Formula)` we need an order on `List Formula`.
We use the lexicographic order `List.le` coming from the order on formulas.

TODO: these could be moved to `Pdl.Syntax`, next to `Finset.pdlSort`.
-/


-- @@ L267-284 verbatim
/-- The linear order on formulas, bundling the results from `Pdl.Syntax`.
This is only used locally, to get the lexicographic order on `List Formula`. -/
@[instance_reducible]
def Formula.linearOrder : LinearOrder Formula where
  le := Formula.le
  lt := fun φ ψ => φ ≠ ψ ∧ φ.le ψ
  le_refl := Formula.le_rfl
  le_trans := Formula.le_trans
  le_antisymm := Formula.le_antisymm
  le_total := Formula.le_total
  lt_iff_le_not_ge := by
    intro φ ψ
    constructor
    · rintro ⟨hne, hle⟩
      exact ⟨hle, fun hba => hne (Formula.le_antisymm _ _ hle hba)⟩
    · rintro ⟨hle, hnot⟩
      exact ⟨by rintro rfl; exact hnot (Formula.le_rfl _), hle⟩
  toDecidableLE := Formula.decLe


-- @@ L286-286 verbatim
attribute [local instance] Formula.linearOrder


-- @@ L288-292 verbatim
/-- The lexicographic `List.le` on `List Formula` agrees with the `≤` coming from
the linear order `Formula.linearOrder`. -/
lemma List.le_iff_le_formula (l1 l2 : List Formula) : List.le l1 l2 ↔ l1 ≤ l2 := by
  change ¬ (l2 < l1) ↔ l1 ≤ l2
  exact not_lt


-- @@ L294-295 verbatim
instance : DecidableRel (@List.le Formula instLTFormula) :=
  fun l1 l2 => decidable_of_iff _ (List.le_iff_le_formula l1 l2).symm


-- @@ L297-299 verbatim
instance : IsTrans (List Formula) List.le :=
  ⟨fun _ _ _ h12 h23 => (List.le_iff_le_formula _ _).2
    (le_trans ((List.le_iff_le_formula _ _).1 h12) ((List.le_iff_le_formula _ _).1 h23))⟩


-- @@ L301-303 verbatim
instance : Std.Antisymm (@List.le Formula instLTFormula) :=
  ⟨fun _ _ h12 h21 => le_antisymm ((List.le_iff_le_formula _ _).1 h12)
    ((List.le_iff_le_formula _ _).1 h21)⟩


-- @@ L305-307 verbatim
instance : Std.Total (@List.le Formula instLTFormula) :=
  ⟨fun l1 l2 => (le_total l1 l2).imp (List.le_iff_le_formula _ _).2
    (List.le_iff_le_formula _ _).2⟩


-- @@ L309-313 verbatim
/-- The disjunction of conjunctions given by a `Finset (Finset Formula)`.
The inner sets are sorted with `Finset.pdlSort` and the outer set is then sorted
lexicographically with `List.le`. -/
def _root_.Finset.pdlDiscon : Finset (Finset Formula) → Formula
  | XS => _root_.PDL.discon ((XS.image Finset.pdlSort).sort List.le)


-- @@ L315-323 verbatim
theorem Finset.disconEval {W M} {w : W} (XS : Finset (Finset Formula)) :
    evaluate M w XS.pdlDiscon ↔ ∃ Y ∈ XS, ∀ f ∈ Y, evaluate M w f := by
  rw [Finset.pdlDiscon, _root_.PDL.disconEval]
  simp only [Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨l, ⟨Y, Y_in, rfl⟩, hl⟩
    exact ⟨Y, Y_in, fun f f_in => hl f (Formula.mem_pdlSort.2 f_in)⟩
  · rintro ⟨Y, Y_in, hY⟩
    exact ⟨Y.pdlSort, ⟨Y, Y_in, rfl⟩, fun f f_in => hY f (Formula.mem_pdlSort.1 f_in)⟩


-- @@ L325-325 verbatim
/-! ## Pairwise Union -/


-- @@ L327-330 verbatim
/-- All concatenations of one formula list from each input family. -/
@[simp]
def pairunionList : List (List Formula) → List (List Formula) → List (List Formula)
  | xls, yls => List.flatten (xls.map fun xl => yls.map fun yl => xl ++ yl)


-- @@ L332-335 verbatim
/-- All unions of one formula finset from each input family. -/
@[simp]
def pairunionFinset : Finset (Finset Formula) → Finset (Finset Formula) → Finset (Finset Formula)
  | X, Y => X.biUnion fun ga => Y.biUnion fun gb => {ga ∪ gb}


-- @@ L337-340 verbatim
/-- Containers supporting pairwise combination of families of formula collections. -/
class HasUplus (α : Type → Type) where
  /-- Combine every collection from the first family with every collection from the second. -/
  pairunion : α (α Formula) → α (α Formula) → α (α Formula)


-- @@ L342-343 verbatim
/-- Pairwise combination of two families of formula collections. -/
scoped infixl:77 "⊎" => HasUplus.pairunion


-- @@ L345-346 verbatim
@[simp]
instance listHasUplus : HasUplus List := ⟨pairunionList⟩

-- @@ L347-348 verbatim
@[simp]
instance finsetHasUplus : HasUplus Finset := ⟨pairunionFinset⟩


-- @@ L350-359 verbatim
theorem disconAnd {XS YS} : discon (XS ⊎ YS) ≡ discon XS ⋀ discon YS :=
  by
  unfold semEquiv
  intro W M w
  rw [disconEval (XS ⊎ YS)]
  simp only [HasUplus.pairunion, pairunionList, List.mem_flatten, List.mem_map,
    exists_exists_and_eq_and, exists_exists_and_exists_and_eq_and, List.mem_append, evaluate]
  rw [disconEval XS]
  rw [disconEval YS]
  aesop


-- @@ L361-366 verbatim
theorem union_elem_uplus {XS YS : Finset (Finset Formula)} {X Y : Finset Formula} :
  X ∈ XS → Y ∈ YS → ((X ∪ Y) ∈ (XS ⊎ YS)) :=
  by
  intro X_in Y_in
  simp only [HasUplus.pairunion, pairunionFinset, Finset.mem_biUnion, Finset.mem_singleton]
  exact ⟨X, X_in, Y, Y_in, rfl⟩


-- @@ L368-374 verbatim
/-- Helper for `oneSidedLocalRuleTruth`, used with `g = Yset`. -/
theorem mapCon_mapForall (M : KripkeModel W) w φ
    (g : (List Formula × List Program) → Formula → List Formula) :
    (∃ f ∈ List.map (fun Fδ => con (g Fδ φ)) X, evaluate M w f) ↔
    ∃ fs ∈ List.map (fun Fδ => g Fδ φ) X, ∀ f ∈ fs, evaluate M w f := by
  simp_all only [List.mem_map, Prod.exists, ↓existsAndEq, and_true]
  constructor <;> grind [conEval]


-- @@ L376-376 verbatim
end PDL
