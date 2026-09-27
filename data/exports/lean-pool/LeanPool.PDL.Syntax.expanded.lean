/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Sort


-- @@ L12-12 verbatim
/-! # Syntax (Section 2.1) -/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace PDL


-- @@ L18-37 verbatim
mutual
  /-- PDL formulas, mutually defined with programs to support tests and boxes. -/
  inductive Formula : Type
    | bottom : Formula
    | atom_prop : Nat → Formula
    | neg : Formula → Formula
    | and : Formula → Formula → Formula
    | box : Program → Formula → Formula
  deriving Repr,DecidableEq
  /-- PDL programs with atomic actions, composition, choice, iteration, and tests. -/
  inductive Program : Type
    | atom_prog : Nat → Program
    | sequence : Program → Program → Program
    | union : Program → Program → Program
    | star : Program → Program
    | test : Formula → Program
  deriving Repr,DecidableEq
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.

-- @@ L38-38 verbatim
end PDL


-- @@ L40-40 verbatim
namespace PDL


-- @@ L42-42 verbatim
/-! ## Abbreviations and Notation  -/


-- @@ L44-47 verbatim
/-- Disjunction encoded using conjunction and negation. -/
@[simp]
def Formula.or : Formula → Formula → Formula
  | f, g => Formula.neg (Formula.and (Formula.neg f) (Formula.neg g))


-- @@ L49-51 verbatim
/-- □(αs,φ) -/
def Formula.boxes : List Program → Formula → Formula
| δ, χ => List.foldr (fun β φ => Formula.box β φ) χ δ


-- @@ L53-57 verbatim
/-- Sequential composition of a list of programs, with a true test as the empty sequence. -/
@[simp]
def Program.steps : List Program → Program
  | [] => Program.test (Formula.neg Formula.bottom)
  | (p :: ps) => Program.sequence p (Program.steps ps)


-- @@ L59-60 verbatim
/-- An atomic proposition with the given natural-number index. -/
scoped prefix:70 "·" => Formula.atom_prop

-- @@ L61-62 verbatim
/-- An atomic program with the given natural-number index. -/
scoped prefix:70 "·" => Program.atom_prog

-- @@ L63-64 verbatim
/-- Formula negation. -/
scoped prefix:69 "~" => Formula.neg


-- @@ L66-67 verbatim
@[simp]
instance Formula.instBot : Bot Formula := ⟨Formula.bottom⟩

-- @@ L68-69 verbatim
@[simp]
instance Formula.insTop : Top Formula := ⟨Formula.neg Formula.bottom⟩


-- @@ L71-72 verbatim
/-- Formula conjunction. -/
scoped infixr:66 " ⋀ " => Formula.and

-- @@ L73-74 verbatim
/-- Formula disjunction. -/
scoped infixr:60 " ⋁ " => Formula.or

-- @@ L75-76 verbatim
/-- Material implication between formulas. -/
scoped notation:55 φ:56 " ↣ " ψ:55 => ~ (φ ⋀ (~ψ))

-- @@ L77-78 verbatim
/-- Material equivalence between formulas. -/
scoped notation:55 φ:56 " ⟷ " ψ:55 => (φ ↣ ψ) ⋀ (ψ ↣ φ)

-- @@ L79-80 verbatim
/-- The box modality of a program. -/
scoped notation "⌈" α "⌉" P => Formula.box α P

-- @@ L81-82 verbatim
/-- Iterated box modalities for a list of programs. -/
scoped notation "⌈⌈" as "⌉⌉" P => Formula.boxes as P


-- @@ L84-85 verbatim
/-- Sequential composition of programs. -/
scoped infixl:33 ";'" => Program.sequence -- avoiding plain ";" which has a meaning in Lean 4

-- @@ L86-87 verbatim
/-- Nondeterministic choice between programs. -/
scoped infixl:33 "⋓" => Program.union

-- @@ L88-89 verbatim
/-- Kleene iteration of a program. -/
scoped prefix:33 "∗" => Program.star

-- @@ L90-91 verbatim
/-- The test program associated with a formula. -/
scoped prefix:33 "?'" => Program.test -- avoiding plain "?" which has a meaning in Lean 4


-- @@ L93-98 verbatim
/-- Union of a list of programs. The empty union is `?'⊥`, a program that cannot be
executed, so that `[(⋃ ∅)*]φ` is equivalent to `φ`. -/
def _root_.PDL.Program.unions : List Program → Program
  | [] => ?'⊥
  | [α] => α
  | α :: rest => α ⋓ Program.unions rest


-- @@ L100-111 verbatim
/-- A basic formula is of the form `¬⊥`, `p`, `¬p`, `[a]_` or `¬[a]_`.
Note: in the article also `⊥` is basic, but not here because we want
to apply `OneSidedLocalRule.bot` to it. -/
@[simp]
def Formula.basic : Formula → Bool
  | ⊥ => False
  | ~⊥ => True
  | ·_ => True
  | ~·_ => True
  | ⌈·_⌉_ => True
  | ~⌈·_⌉_ => True
  | _ => False


-- @@ L113-116 verbatim
/-- Whether a program is an atomic action. -/
def Program.isAtomic : Program → Prop
| ·_ => true
| _ => false


-- @@ L118-123 verbatim
lemma Formula.neq_neg_self (φ : Formula) : φ ≠ ~φ := by
  intro h
  cases φ <;> simp_all only [reduceCtorEq, neg.injEq]
  case neg φ => absurd h; exact Formula.neq_neg_self φ

-- Note: to make `decide` work we use `decidable_of_decidable_of_iff`.

-- @@ L124-129 verbatim
instance : DecidablePred Program.isAtomic
| ·_ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : True ↔ _)
| _;' _ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)
| a ⋓ _ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)
| ∗_ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)
| ?'_ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)


-- @@ L131-132 verbatim
theorem Program.isAtomic_iff {α : Program} : α.isAtomic ↔ ∃ a, α = (·a : Program) := by
  cases α <;> simp_all [isAtomic]


-- @@ L134-137 verbatim
/-- Whether a program has an outer Kleene-star constructor. -/
def Program.isStar : Program → Prop
| ∗_ => true
| _ => false


-- @@ L139-144 verbatim
instance : DecidablePred Program.isStar := by
  intro α
  cases α <;> simp only [Program.isStar, Bool.false_eq_true] <;>
  all_goals
    try exact instDecidableTrue
    try exact instDecidableFalse


-- @@ L146-147 verbatim
theorem Program.isStar_iff {α : Program} : α.isStar ↔ ∃ β, α = (∗β) := by
  cases α <;> simp_all [isStar]


-- @@ L149-149 verbatim
/-! ## Tools for Box Formulas -/


-- @@ L151-152 verbatim
@[simp]
theorem Formula.boxes_nil {φ : Formula} : Formula.boxes [] φ = φ := by simp [Formula.boxes]


-- @@ L154-156 verbatim
@[simp]
theorem Formula.boxes_cons {β δ φ} : Formula.boxes (β :: δ) φ = ⌈β⌉(Formula.boxes δ φ) := by
  simp [Formula.boxes]


-- @@ L158-160 verbatim
@[simp]
lemma Formula.boxes_injective {αs φ ψ} : (⌈⌈αs⌉⌉φ) = (⌈⌈αs⌉⌉ψ) ↔ φ = ψ := by
  induction αs <;> simp_all


-- @@ L162-164 verbatim
theorem boxes_last {δ α φ} : Formula.boxes (δ ++ [α]) φ = Formula.boxes δ (⌈α⌉φ) :=
  by
  induction δ <;> simp [Formula.boxes]


-- @@ L166-169 verbatim
theorem boxes_append {as bs P} :
    Formula.boxes (as ++ bs) P = Formula.boxes as (Formula.boxes bs P) :=
  by
  induction as <;> simp [Formula.boxes]


-- @@ L171-174 verbatim
/-- Separate a formula's leading boxes from its remaining formula. -/
def boxesOf : Formula → List Program × Formula
| (Formula.box prog nextf) => let (rest,endf) := boxesOf nextf; ⟨prog::rest, endf⟩
| f => ([], f)


-- @@ L176-182 verbatim
lemma def_of_boxesOf_def {φ γ ψ} (h : boxesOf φ = (γ, ψ)) : φ = ⌈⌈γ⌉⌉ψ := by
  induction γ generalizing φ
  · unfold boxesOf at h
    cases φ <;> simp_all
  case cons α αs IH =>
    simp only [Formula.boxes_cons]
    cases φ <;> grind [boxesOf]


-- @@ L184-187 verbatim
/-- Whether a formula has an outer box constructor. -/
def Formula.isBox : Formula → Prop
| (Formula.box _ _ ) => True
| _ => False


-- @@ L189-197 verbatim
lemma boxesOf_def_of_def_of_nonBox {φ γ ψ} (h : φ = ⌈⌈γ⌉⌉ψ) (nonBox : ¬ ψ.isBox) :
    boxesOf φ = (γ, ψ) := by
  induction γ generalizing φ
  · unfold boxesOf
    cases φ <;> simp_all [Formula.isBox]; aesop
  case cons α αs IH =>
    subst h
    unfold boxesOf
    simp_all


-- @@ L199-206 verbatim
@[simp]
lemma boxesOf_output_not_isBox {φ : Formula} : ¬ (boxesOf φ).2.isBox := by
  cases φ
  case box α φ =>
    have := @boxesOf_output_not_isBox φ
    simp_all [boxesOf, Formula.isBox]
  all_goals
    simp_all [boxesOf, Formula.isBox]


-- @@ L208-209 verbatim
lemma nonBox_of_boxesOf_def {φ L ψ} (bdef : boxesOf φ = (L, ψ)) : ¬ ψ.isBox := by
  have := @boxesOf_output_not_isBox φ; simp_all


-- @@ L211-212 verbatim
lemma boxesOf_nonBox {φ} (notBox : ¬ φ.isBox) : boxesOf φ = ([], φ) := by
  cases φ <;> simp_all [Formula.isBox, boxesOf]


-- @@ L214-223 verbatim
/-- If φ is not a box then we know the result of `boxesOf (⌈⌈δs⌉⌉⌈α⌉φ)`.
A more general version without α should also hold. -/
lemma defs_of_boxesOf_last_of_nonBox {φ}
    (notBox : ¬ φ.isBox) δs α : boxesOf (⌈⌈δs⌉⌉⌈α⌉φ) = (δs ++ [α], φ) := by
  cases δs
  case nil =>
    simp_all [boxesOf, boxesOf_nonBox notBox]
  case cons δ δs =>
    have IH := defs_of_boxesOf_last_of_nonBox notBox δs
    simp_all [boxesOf]


-- @@ L225-237 verbatim
lemma Formula.boxes_cons_neq_self φ β δ : (⌈β⌉⌈⌈δ⌉⌉φ) ≠ φ := by
  cases φ <;> try grind [Formula.boxes]
  case box α φ =>
    rw [← boxes_last]
    simp only [ne_eq, box.injEq, not_and]
    intro β_eq_α
    rw [boxes_last]
    cases δ
    · exact @Formula.boxes_cons_neq_self φ α []
    case cons γ δ =>
      simp only [boxes_cons]
      rw [← boxes_last]
      exact @Formula.boxes_cons_neq_self φ γ (δ ++ [α])


-- @@ L239-244 verbatim
lemma Formula.boxesOf_boxes_prefix (αs : List Program) φ : αs <+: (boxesOf (⌈⌈αs⌉⌉φ)).1 := by
  induction αs
  · simp_all
  case cons α αs IH =>
    simp only [boxes_cons, boxesOf, List.cons_prefix_cons, true_and]
    exact IH


-- @@ L246-250 verbatim
/-! ## Loaded Formulas

Loaded formulas consist of a non-empty sequence of loading boxes, and a normal formula.
For loading boxes we write `⌊α⌋` instead of `⌈α⌉`.
-/


-- @@ L252-263 verbatim
mutual
/-- An ordinary formula or a formula with a distinguished loaded modal path. -/
inductive AnyFormula : Type
  | normal : Formula → AnyFormula -- φ
  | loaded : LoadFormula → AnyFormula -- χ
  deriving Repr, DecidableEq

/-- A box whose continuation may itself carry a loaded path. -/
inductive LoadFormula : Type
  | box : Program → AnyFormula → LoadFormula -- ⌊α⌋χ
  deriving Repr, DecidableEq
end


-- @@ L265-265 verbatim
end PDL


-- @@ L267-267 verbatim
namespace PDL


-- @@ L269-269 verbatim
instance : Coe Formula AnyFormula := ⟨AnyFormula.normal⟩

-- @@ L270-270 verbatim
instance : Coe LoadFormula AnyFormula := ⟨AnyFormula.loaded⟩


-- @@ L272-274 verbatim
/-- Negation of an ordinary or loaded formula. -/
inductive AnyNegFormula
| neg : AnyFormula → AnyNegFormula


-- @@ L276-278 verbatim
/-- Load a nonempty modal sequence given its prefix and final program. -/
def loadMulti : List Program → Program → Formula → LoadFormula
| bs, α, φ => List.foldr (fun β lf => LoadFormula.box β lf) (LoadFormula.box α φ) bs


-- @@ L280-281 verbatim
@[simp]
theorem loadMulti_nil {α φ} : loadMulti [] α φ = LoadFormula.box α φ := by simp [loadMulti]


-- @@ L283-285 verbatim
@[simp]
theorem loadMulti_cons {β δ α φ} :
    loadMulti (β :: δ) α φ = LoadFormula.box β (loadMulti δ α φ) := by simp [loadMulti]


-- @@ L287-289 verbatim
/-- Prepend a list of loaded boxes to a loaded continuation. -/
def LoadFormula.boxes : List Program → LoadFormula → LoadFormula
| δ, χ => List.foldr (fun β lf => LoadFormula.box β lf) χ δ


-- @@ L291-292 verbatim
@[simp]
lemma LoadFormula.boxes_nil {χ} : LoadFormula.boxes [] χ = χ := by simp [LoadFormula.boxes]


-- @@ L294-297 verbatim
lemma LoadFormula.boxes_cons {b bs φ} :
    LoadFormula.boxes (b :: bs) φ = LoadFormula.box b (LoadFormula.boxes bs φ) :=
  by
  induction bs <;> simp [LoadFormula.boxes]


-- @@ L299-303 verbatim
/-- Erase loading annotations to obtain an ordinary formula. -/
@[simp]
def LoadFormula.unload : LoadFormula → Formula
| LoadFormula.box α (.normal φ) => ⌈α⌉φ
| LoadFormula.box α (.loaded χ) => ⌈α⌉(unload χ)


-- @@ L305-309 verbatim
@[simp]
theorem unload_loadMulti : (loadMulti δ α φ).unload  = ⌈⌈δ⌉⌉⌈α⌉φ := by
  induction δ
  · simp [Formula.boxes, loadMulti]
  · simpa [Formula.boxes, LoadFormula.boxes, loadMulti]


-- @@ L311-314 verbatim
/-- A negated loaded formula. -/
inductive NegLoadFormula : Type -- ¬χ
  | neg : LoadFormula → NegLoadFormula
  deriving Repr, DecidableEq


-- @@ L316-317 verbatim
/-- A loaded box modality. -/
scoped notation "⌊" α "⌋" χ => LoadFormula.box α χ

-- @@ L318-319 verbatim
/-- Iterated loaded boxes for a list of programs. -/
scoped notation "⌊⌊" αs "⌋⌋" χ => LoadFormula.boxes αs χ

-- @@ L320-321 verbatim
/-- Negation of a loaded formula. -/
scoped notation "~'" χ => NegLoadFormula.neg χ

-- @@ L322-323 verbatim
/-- Negation of an ordinary or loaded formula. -/
scoped notation "~''" φ:arg => AnyNegFormula.neg φ


-- @@ L325-328 verbatim
/-- Erase loading annotations from a negated loaded formula. -/
@[simp]
def negUnload : NegLoadFormula → Formula
| NegLoadFormula.neg χ => ~ χ.unload


-- @@ L330-330 verbatim
example : NegLoadFormula := ~'(⌊((·1);' (·2))⌋(⊤ : Formula))

-- @@ L331-331 verbatim
example : NegLoadFormula := ~'(⌊⌊[·1, ·2]⌋⌋⌊·1⌋(⊤ : Formula))


-- @@ L333-336 verbatim
theorem loadBoxes_append {as bs P} :
    LoadFormula.boxes (as ++ bs) P = LoadFormula.boxes as (LoadFormula.boxes bs P) :=
  by
  induction as <;> simp [LoadFormula.boxes]


-- @@ L338-341 verbatim
theorem loadBoxes_last {a as c P} :
    (~'⌊a⌋LoadFormula.boxes (as ++ [c]) P) = (~'⌊a⌋LoadFormula.boxes as (⌊c⌋P)) :=
  by
  induction as <;> simp [LoadFormula.boxes]


-- @@ L343-347 verbatim
@[simp]
theorem unload_boxes {δ φ} : (⌊⌊δ⌋⌋φ).unload = ⌈⌈δ⌉⌉φ.unload := by
  induction δ
  · simp only [LoadFormula.boxes, List.foldr_nil, Formula.boxes]
  · simpa [Formula.boxes, LoadFormula.boxes]


-- @@ L349-351 verbatim
@[simp]
theorem unload_neg_loaded {α χ} : (~'⌊α⌋(.loaded χ)).1.unload = ⌈α⌉(χ.unload) := by
  simp [LoadFormula.unload]


-- @@ L353-355 verbatim
@[simp]
theorem unload_neg_normal {α φ} : (~'⌊α⌋(.normal φ)).1.unload = ⌈α⌉φ := by
  simp [LoadFormula.unload]


-- @@ L357-360 verbatim
/-- Load a possibly already loaded formula χ with a sequence δ of boxes.
The result is loaded iff δ≠[] or χ was loaded. -/
def AnyFormula.loadBoxes : List Program → AnyFormula → AnyFormula
| δ, χ => List.foldr (fun β lf => LoadFormula.box β lf) χ δ


-- @@ L362-364 verbatim
@[simp]
lemma AnyFormula.boxes_nil {ξ} : AnyFormula.loadBoxes [] ξ = ξ := by
  simp [AnyFormula.loadBoxes]


-- @@ L366-369 verbatim
@[simp]
lemma AnyFormula.loadBoxes_cons {α γ ξ} :
    AnyFormula.loadBoxes (α :: γ) ξ = ⌊α⌋ (AnyFormula.loadBoxes γ ξ) := by
  simp [AnyFormula.loadBoxes]


-- @@ L371-374 verbatim
theorem AnyFormula.loadBoxes_append {as bs φ} :
    AnyFormula.loadBoxes (as ++ bs) φ = AnyFormula.loadBoxes as (AnyFormula.loadBoxes bs φ) :=
  by
  induction as <;> simp [AnyFormula.loadBoxes]


-- @@ L376-383 verbatim
lemma AnyFormula.loadBoxes_loaded_eq_loaded_boxes {δ χ} :
    AnyFormula.loadBoxes δ (AnyFormula.loaded χ) = AnyFormula.loaded (⌊⌊δ⌋⌋χ) := by
  induction δ
  · simp
  case cons IH =>
    simp only [loadBoxes_cons, loaded.injEq]
    rw [IH]
    rfl


-- @@ L385-388 verbatim
/-- Erase loading annotations, leaving ordinary formulas unchanged. -/
def AnyFormula.unload : AnyFormula → Formula
  | .normal φ => φ
  | .loaded χ => χ.unload


-- @@ L390-401 verbatim
lemma box_loadBoxes_append_eq_of_loaded_eq_loadBoxes {αs}
    (h : AnyFormula.loaded χ' = AnyFormula.loadBoxes αs (AnyFormula.normal φ))
    : (⌊d⌋AnyFormula.loadBoxes (δ ++ αs) (AnyFormula.normal φ)) = ⌊⌊d :: δ⌋⌋χ' := by
  cases αs
  · exfalso
    simp_all
  case cons α αs =>
    simp only [AnyFormula.loadBoxes_cons, AnyFormula.loaded.injEq] at h
    subst h
    rw [LoadFormula.boxes_cons,AnyFormula.loadBoxes_append,AnyFormula.loadBoxes_cons]
    simp only [LoadFormula.box.injEq, true_and] -- d gone
    apply AnyFormula.loadBoxes_loaded_eq_loaded_boxes


-- @@ L403-407 verbatim
@[simp]
lemma AnyFormulaBoxBoxes_eq_FormulaBoxLoadBoxes_inside_unload {αs} :
      ((⌊α⌋  AnyFormula.loadBoxes αs (AnyFormula.normal φ)).unload)
    = ( ⌈α⌉((AnyFormula.loadBoxes αs (AnyFormula.normal φ)).unload)) := by
  cases αs <;> simp_all [AnyFormula.loadBoxes, AnyFormula.unload]


-- @@ L409-416 verbatim
lemma AnyFormula.loadBoxes_unload_eq_boxes {βs φ} :
    (AnyFormula.loadBoxes βs (AnyFormula.normal φ)).unload = ⌈⌈βs⌉⌉φ := by
  induction βs
  · simp [unload]
  case cons ih =>
    simp only [unload, loadBoxes_cons, AnyFormulaBoxBoxes_eq_FormulaBoxLoadBoxes_inside_unload,
      Formula.boxes_cons, Formula.box.injEq, true_and];
    exact ih


-- @@ L418-434 verbatim
lemma loaded_eq_to_unload_eq χ αs φ
    (h : AnyFormula.loaded χ = AnyFormula.loadBoxes αs (AnyFormula.normal φ))
    : χ.unload = ⌈⌈αs⌉⌉φ
    := by
  cases αs
  · simp_all
  case cons α1 αs =>
    cases αs
    · simp_all
    case cons α2 αs =>
      simp only [Formula.boxes_cons]
      rcases χ with  ⟨β, af⟩
      simp only [AnyFormula.loadBoxes_cons, AnyFormula.loaded.injEq, LoadFormula.box.injEq] at h
      rcases h with ⟨β_eq_α1, af_def⟩
      have := loaded_eq_to_unload_eq ((⌊α2⌋AnyFormula.loadBoxes αs (.normal φ))) (α2 :: αs) _ rfl
      subst_eqs
      simp_all


-- @@ L436-436 verbatim
/-! ## Spliting of loaded formulas -/


-- @@ L438-449 verbatim
mutual
/-- Split any formula into the list of loaded boxes and the free formula. -/
@[simp]
def AnyFormula.split : (af : AnyFormula) → List Program × Formula
| .loaded lf => lf.split
| .normal f => ([], f)

/-- Split a loaded formula into the list of loaded boxes and the free formula. -/
@[simp]
def LoadFormula.split : (lf : LoadFormula) → List Program × Formula
| .box α af => (fun (δ,f) => (α :: δ, f)) af.split
end


-- @@ L451-451 verbatim
end PDL


-- @@ L453-453 verbatim
namespace PDL


-- @@ L455-462 verbatim
lemma LoadFormula.split_boxes_cons {βs α φ} :
    (⌊⌊βs⌋⌋⌊α⌋AnyFormula.normal φ).split = (βs ++ [α], φ) := by
  induction βs
  · simp_all
  · rw [List.cons_append]
    rw [LoadFormula.boxes_cons]
    simp only [split, AnyFormula.split, Prod.mk.injEq, List.cons.injEq, true_and]
    grind


-- @@ L464-466 verbatim
@[simp]
theorem AnyFormula.split_normal (φ : Formula) : (AnyFormula.normal φ).split = ([],φ) := by
  simp [AnyFormula.split]


-- @@ L468-469 verbatim
theorem AnyFormula.split_eq_nil_is_normal (ξ φ) : ξ.split = ([],φ) → ξ = AnyFormula.normal φ := by
  rcases ξ with _|⟨_,_⟩ <;> simp [AnyFormula.split]


-- @@ L471-494 verbatim
mutual
lemma LoadFormula.split_inj {ξ ξ' : LoadFormula} (h : ξ.split = ξ'.split) : ξ = ξ' := by
  rcases ξ with ⟨α, ξ⟩
  rcases ξ' with ⟨α', ξ'⟩
  simp only [LoadFormula.split, Prod.mk.injEq, List.cons.injEq, LoadFormula.box.injEq] at *
  constructor
  · tauto
  case right =>
    apply AnyFormula.split_inj
    aesop

lemma AnyFormula.split_inj {ξ ξ' : AnyFormula} (h : ξ.split = ξ'.split) : ξ = ξ' := by
  rcases ξ with φ|ξ <;> rcases ξ' with φ'|ξ'
  case normal.normal =>
    simp_all
  case normal.loaded =>
    simp_all only [AnyFormula.split, reduceCtorEq]
    cases ξ'; simp_all
  case loaded.normal =>
    cases ξ; simp_all
  case loaded.loaded =>
    simp_all only [AnyFormula.split, AnyFormula.loaded.injEq]
    exact LoadFormula.split_inj h
end


-- @@ L496-496 verbatim
end PDL


-- @@ L498-498 verbatim
namespace PDL


-- @@ L500-502 verbatim
theorem AnyFormula.box_split (af : AnyFormula) :
  (⌊α⌋af).split = (α :: af.split.1, af.split.2) := by
  cases af <;> simp


-- @@ L504-507 verbatim
@[simp]
theorem LoadFormula.split_list_not_empty (lf : LoadFormula) : lf.split.1 ≠ [] := by
  cases lf
  simp [LoadFormula.split]


-- @@ L509-514 verbatim
/-- Construct a loaded modal sequence from a list known to be nonempty. -/
@[simp]
def loadMultiNonEmpty : (δ : List Program) → (h : δ ≠ []) → Formula → LoadFormula
| [ ],           h, _ => by exfalso; simp at *
| (α :: []),     _, φ => LoadFormula.box α φ
| (α :: d :: δ), _, φ => LoadFormula.box α (loadMultiNonEmpty (d :: δ) (by simp) φ)


-- @@ L516-521 verbatim
@[simp]
theorem loadMulti_nonEmpty_box (h : δ ≠ []) :
    loadMultiNonEmpty (α :: δ) h' φ = ⌊α⌋(loadMultiNonEmpty δ h φ) := by
  cases δ
  · absurd h; rfl
  · simp at *


-- @@ L523-525 verbatim
@[simp]
lemma loadMulti_split {αs} : (loadMulti αs α φ).split = (αs ++ [α], φ) := by
  induction αs <;> simp_all


-- @@ L527-533 verbatim
@[simp]
lemma loadMulti_nonEmpty_unload {δ h φ} : (loadMultiNonEmpty δ h φ).unload  = ⌈⌈δ⌉⌉φ := by
  induction δ
  · exfalso; absurd h; rfl
  case cons α αs IH =>
    unfold loadMultiNonEmpty
    cases αs <;> simp_all


-- @@ L535-569 verbatim
theorem LoadFormula.split_eq_loadMulti_nonEmpty {δ φ} (lf : LoadFormula) : (h : lf.split = (δ,φ)) →
    lf = loadMultiNonEmpty δ (by have := split_list_not_empty lf; simp_all) φ := by
  induction δ generalizing φ lf
  all_goals
    rcases lf_def : lf with ⟨α,af⟩
    intro h
  · simp [LoadFormula.split] at h
  case cons β δ IH =>
    cases af
    · unfold LoadFormula.split at h
      simp only [AnyFormula.split, Prod.mk.injEq, List.cons.injEq, List.nil_eq] at h
      rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
      subst_eqs
      simp_all
    case loaded lf2 =>
      specialize @IH φ lf2 ?_
      · rw [AnyFormula.box_split] at h
        simp only [AnyFormula.split, Prod.mk.injEq, List.cons.injEq] at *
        rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
        subst_eqs
        simp
      · rw [loadMulti_nonEmpty_box ?_]
        · simp only [box.injEq, AnyFormula.loaded.injEq]
          rw [AnyFormula.box_split] at h
          simp only [AnyFormula.split, Prod.mk.injEq, List.cons.injEq] at *
          rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
          subst_eqs
          simp only [true_and]
          convert IH
        · simp only [ne_eq]
          rw [AnyFormula.box_split] at h
          simp only [AnyFormula.split, Prod.mk.injEq, List.cons.injEq] at *
          rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
          subst_eqs
          simp


-- @@ L571-574 verbatim
theorem LoadFormula.split_eq_loadMulti_nonEmpty' {δ φ} (lf : LoadFormula) (h : δ ≠ [])
    (h2 : lf.split = (δ, φ)) : lf = loadMultiNonEmpty δ h φ := by
  have := LoadFormula.split_eq_loadMulti_nonEmpty lf h2
  rw [this]


-- @@ L576-578 verbatim
theorem loadMulti_nonEmpty_eq_loadMulti {δ α h φ} :
    loadMultiNonEmpty (δ ++ [α]) h φ = loadMulti δ α φ := by
  induction δ <;> simp_all


-- @@ L580-583 verbatim
theorem LoadFormula.split_eq_loadMulti (lf : LoadFormula) {δ α φ}
    (h : lf.split = (δ ++ [α], φ)) : lf = loadMulti δ α φ := by
  rw [LoadFormula.split_eq_loadMulti_nonEmpty' lf (by simp) h]
  apply loadMulti_nonEmpty_eq_loadMulti


-- @@ L585-597 verbatim
theorem LoadFormula.exists_splitLast (lf : LoadFormula) :
    ∃ δ α, lf.split.1 = δ ++ [α] := by
  rcases lf with ⟨α, af⟩
  cases af
  case normal =>
    use [], α
    simp
  case loaded lf =>
    rcases LoadFormula.exists_splitLast lf with ⟨δ', α', IH⟩
    simp only [split, AnyFormula.split]
    rw [IH]
    use α :: δ', α'
    simp


-- @@ L599-607 verbatim
theorem LoadFormula.exists_loadMulti (lf : LoadFormula) :
    ∃ δ α φ, lf = loadMulti δ α φ := by
  rcases LoadFormula.exists_splitLast lf with ⟨δ, α, split1_def⟩
  use δ, α
  use lf.split.2
  apply LoadFormula.split_eq_loadMulti lf
  cases lfs_def : lf.split
  rw [lfs_def] at split1_def
  simp_all


-- @@ L609-612 verbatim
lemma loadMulti_eq_of_some (h : δ.head? = some d) :
    loadMulti δ β φ = ⌊d⌋AnyFormula.loaded (loadMulti δ.tail β φ) := by
  cases δ
  <;> simp_all


-- @@ L614-616 verbatim
lemma loadMulti_eq_loadBoxes :
    AnyFormula.loaded (loadMulti δ α φ) = AnyFormula.loadBoxes (δ ++ [α]) φ := by
  induction δ <;> aesop


-- @@ L618-618 verbatim
/-! ## splitLast -/


-- @@ L620-625 verbatim
/-- Helper function for `YsetLoad'` to get last list element. -/
def splitLast : List α → Option (List α × α)
| [] => none
| (x :: xs) => some <| match splitLast xs with
  | none => ([], x)
  | some (ys, y) => (x::ys, y)


-- @@ L627-628 verbatim
@[simp]
theorem splitLast_nil : splitLast [] = (none : Option (List α × α)) := by simp [splitLast]


-- @@ L630-631 verbatim
theorem nil_of_splitLast_none {δs : List α} : splitLast δs = none → δs = [] := by
  cases δs <;> simp [splitLast]


-- @@ L633-641 verbatim
theorem splitLast_cons_eq_some (x : α) (xs : List α) :
    splitLast (x :: xs) = some ((x :: xs).dropLast, (x :: xs).getLast (List.cons_ne_nil x xs)) := by
  cases xs
  · simp [splitLast]
  case cons y ys =>
    have := splitLast_cons_eq_some y ys -- recursion!
    unfold splitLast
    rw [this]
    simp


-- @@ L643-646 verbatim
@[simp]
theorem splitLast_append_singleton {α} {xs : List α} {x : α} :
    splitLast (xs ++ [x]) = some (xs, x) := by
  induction xs <;> simp_all [splitLast]


-- @@ L648-656 verbatim
lemma splitLast_inj {α} {xs ys : List α} (h : splitLast xs = splitLast ys) :
    xs = ys := by
  induction xs using List.reverseRecOn <;> induction ys using List.reverseRecOn
  · rfl
  · exfalso
    simp_all
  · exfalso
    simp_all
  aesop


-- @@ L658-666 verbatim
lemma LoadFormula.split_splitLast_to_loadBoxes {δs φ δs_ δ ξ}
    (ξsp_def : ξ.split = (δs, φ))
    (sp_def : splitLast δs = some (δs_, δ))
    : ξ = AnyFormula.loadBoxes (δs_ ++ [δ]) (AnyFormula.normal φ) := by
  rw [← splitLast_append_singleton] at sp_def
  rw [splitLast_inj sp_def, ← loadMulti_split] at ξsp_def
  have : (loadMulti δs_ δ φ).split = AnyFormula.split (loadMulti δs_ δ φ) := rfl
  have := AnyFormula.split_inj (this ▸ ξsp_def)
  exact this ▸ loadMulti_eq_loadBoxes


-- @@ L668-678 verbatim
lemma splitLast_undo_of_some {αs : List α} {βs_b : List α × α} (h : splitLast αs = some βs_b) :
    βs_b.1 ++ [βs_b.2] = αs := by
  rcases αs with _ |⟨α,αs⟩
  · exfalso
    simp_all
  have := @splitLast_cons_eq_some _ α αs
  rw [h] at this
  simp only [Option.some.injEq] at this
  subst this
  simp only
  apply List.dropLast_append_getLast


-- @@ L680-704 verbatim
lemma loadMulti_of_splitLast_cons {α αs βs β φ} (h : splitLast (α :: αs) = some ⟨βs, β⟩) :
    loadMulti βs β φ = ⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ) := by
  have : (α :: αs) = βs ++ [β] := by
    rw [← @splitLast_append_singleton] at h
    exact splitLast_inj h
  cases αs
  · unfold splitLast at h
    simp only [splitLast_nil, Option.some.injEq, Prod.mk.injEq, List.nil_eq] at h
    cases h
    subst_eqs
    simp at *
  case cons α2 αs =>
    have ⟨δβ2, new_h⟩ : ∃ δ2_β2, splitLast (α2 :: αs) = some δ2_β2 := by simp [splitLast]
    rw [AnyFormula.loadBoxes_cons]
    have IH := @loadMulti_of_splitLast_cons α2 αs _ _ φ new_h
    rw [← IH]; clear IH
    cases βs
    · exfalso
      unfold splitLast at h
      simp only [Option.some.injEq] at h
      cases h
    case cons β2 βs =>
      simp_all
      subst new_h
      simp_all


-- @@ L706-706 verbatim
/-! ## Measures -/


-- @@ L708-725 verbatim
mutual
  /-- The syntactic length of a program, mutually defined with formula length. -/
  @[simp, implicit_reducible]
  def lengthOfProgram : Program → Nat
    | ·_ => 1
    | α;'β => 1 + lengthOfProgram α + lengthOfProgram β
    | α⋓β => 1 + lengthOfProgram α + lengthOfProgram β
    | ∗α => 1 + lengthOfProgram α
    | ?'φ => 2 + lengthOfFormula φ -- 2 not 1, to make F^ℓ go down;-)
  /-- The syntactic length of a formula, mutually defined with program length. -/
  @[simp, implicit_reducible]
  def lengthOfFormula : Formula → Nat
    | Formula.bottom => 1
    | ·_ => 1
    | ~φ => 1 + lengthOfFormula φ
    | φ⋀ψ => 1 + lengthOfFormula φ + lengthOfFormula ψ
    | ⌈α⌉φ => 1 + lengthOfProgram α + lengthOfFormula φ
end


-- @@ L727-727 verbatim
end PDL


-- @@ L729-729 verbatim
namespace PDL


-- @@ L731-732 verbatim
lemma lengthOfProgram_gt_zero (α : Program) : 0 < lengthOfProgram α := by
  cases α <;> simp <;> omega


-- @@ L734-737 verbatim
/-- Types equipped with a natural-valued syntactic length. -/
class HasLength (α : Type) where
  /-- The syntactic length of an object. -/
  lengthOf : α → ℕ


-- @@ L739-739 verbatim
open HasLength

-- @@ L740-741 verbatim
@[simp]
instance formulaHasLength : HasLength Formula := ⟨lengthOfFormula⟩

-- @@ L742-743 verbatim
@[simp]
instance setFormulaHasLength : HasLength (Finset Formula) := ⟨fun X => X.sum lengthOfFormula⟩

-- @@ L744-745 verbatim
@[simp]
instance listFormulaHasLength : HasLength (List Formula) := ⟨fun X => (X.map lengthOfFormula).sum⟩

-- @@ L746-747 verbatim
@[simp]
instance programHasLength : HasLength Program := ⟨lengthOfProgram⟩

-- @@ L748-749 verbatim
@[simp]
instance setProgramHasLength : HasLength (Finset Program) := ⟨fun X => X.sum lengthOfProgram⟩


-- @@ L751-753 verbatim
/-- No formula is its own double negation. -/
lemma Formula.ne_neg_neg_self (φ : Formula) : φ ≠ ~~φ := by
  intro h; have := congrArg lengthOfFormula h; simp at this; omega


-- @@ L755-761 verbatim
/-- A pair `{φ, ~φ}` is never a singleton. -/
lemma pair_neg_ne_singleton (φ ψ : Formula) : ({φ, ~φ} : Finset Formula) ≠ {ψ} := by
  intro h
  have h1 : φ ∈ ({ψ} : Finset Formula) := h ▸ (by simp)
  have h2 : (~φ) ∈ ({ψ} : Finset Formula) := h ▸ (by simp)
  simp only [Finset.mem_singleton] at h1 h2
  exact Formula.neq_neg_self φ (h1.trans h2.symm)


-- @@ L763-772 verbatim
/-- The pairs `{φ, ~φ}` determine `φ`. -/
lemma pair_neg_inj {φ ψ : Formula} (h : ({φ, ~φ} : Finset Formula) = {ψ, ~ψ}) : φ = ψ := by
  have h1 : φ ∈ ({ψ, ~ψ} : Finset Formula) := h ▸ (by simp)
  have h2 : (~φ) ∈ ({ψ, ~ψ} : Finset Formula) := h ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact absurd (h2.symm.trans (congrArg Formula.neg h1)) (Formula.ne_neg_neg_self ψ)
    · exact Formula.neg.inj h2


-- @@ L774-779 verbatim
/-! ## Sorting formulas

Needed to convert a `Finset Formula` to `List Formula`.

TODO: make this a separate file
-/


-- @@ L781-831 verbatim
mutual

/-- Order: ⊥ < p < ¬φ < φ1∧φ2 < [α]φ

Note that we want this to be antisymmetric later, so we cannot just use < on some measure.
An alternative approach here would be to even go for `Denumerable`.
-/
def Formula.le : Formula → Formula → Prop
  | .bottom, .bottom => True
  | .bottom, _ => True
  | .atom_prop _, .bottom => False
  | .atom_prop p, .atom_prop p' => p ≤ p'
  | .atom_prop _, _ => True
  | .neg _, .bottom => False
  | .neg _, .atom_prop _ => False
  | .neg φ, .neg φ' => φ.le φ'
  | .neg _, _ => True
  | .and _ _, .bottom => False
  | .and _ _, .atom_prop _ => False
  | .and _ _, .neg _ => False
  | .and φ1 φ2, .and φ1' φ2' => φ1.le φ1' ∧ ((φ1 = φ1') → φ2.le φ2')
  | .and _ _, .box _ _ => True
  | .box _ _, .bottom => False
  | .box _ _, .atom_prop _ => False
  | .box _ _, .neg _ => False
  | .box _ _, .and _ _  => False
  | .box α φ, .box α' φ' => α.le α' ∧ ((α = α') → φ.le φ')

/-- The recursive ordering of program syntax used for finite enumerations. -/
def Program.le : Program → Program → Prop
  | .atom_prog a, .atom_prog a' => a ≤ a'
  | .atom_prog _, _ => True
  | .sequence _ _, .atom_prog _ => False
  | .sequence α β, .sequence α' β' => α.le α' ∧ ((α = α') → β.le β')
  | .sequence _ _, _ => True
  | .union _ _ , .atom_prog _ => False
  | .union _ _, .sequence _ _ => False
  | .union α β, .union α' β' => α.le α' ∧ ((α = α') → β.le β')
  | .union _ _, .star _ => True
  | .union _ _, .test _ => True
  | .star _, .atom_prog _ => False
  | .star _, .sequence _ _ => False
  | .star _, .union _ _ => False
  | .star α, .star α' => α.le α'
  | .star _, .test _ => True
  | .test _, .atom_prog _ => False
  | .test _, .sequence _ _ => False
  | .test _, .union _ _ => False
  | .test _, .star _ => False
  | .test τ, .test τ' => τ.le τ'
end


-- @@ L833-833 verbatim
end PDL


-- @@ L835-835 verbatim
namespace PDL


-- @@ L837-837 verbatim
open HasLength


-- @@ L839-839 verbatim
instance instLEFormula : LE Formula := ⟨Formula.le⟩

-- @@ L840-840 verbatim
instance instLTFormula : LT Formula := ⟨fun φ1 φ2 ↦ φ1 ≠ φ2 ∧ φ1.le φ2⟩


-- @@ L842-842 verbatim
instance instLEProgram : LE Program := ⟨Program.le⟩

-- @@ L843-843 verbatim
instance instLTProgram : LT Program := ⟨fun α α' ↦ α ≠ α' ∧ α.le α'⟩


-- @@ L845-845 verbatim
/-! ### Deciding the order -/


-- @@ L847-912 verbatim
mutual

/-- The order on formulas is decidable. -/
def Formula.decLe : (f g : Formula) → Decidable (Formula.le f g)
  | .bottom, .bottom => isTrue trivial
  | .bottom, .atom_prop _ => isTrue trivial
  | .bottom, .neg _ => isTrue trivial
  | .bottom, .and _ _ => isTrue trivial
  | .bottom, .box _ _ => isTrue trivial
  | .atom_prop _, .bottom => isFalse not_false
  | .atom_prop p, .atom_prop p' => Nat.decLe p p'
  | .atom_prop _, .neg _ => isTrue trivial
  | .atom_prop _, .and _ _ => isTrue trivial
  | .atom_prop _, .box _ _ => isTrue trivial
  | .neg _, .bottom => isFalse not_false
  | .neg _, .atom_prop _ => isFalse not_false
  | .neg φ, .neg φ' => Formula.decLe φ φ'
  | .neg _, .and _ _ => isTrue trivial
  | .neg _, .box _ _ => isTrue trivial
  | .and _ _, .bottom => isFalse not_false
  | .and _ _, .atom_prop _ => isFalse not_false
  | .and _ _, .neg _ => isFalse not_false
  | .and φ1 φ2, .and φ1' φ2' =>
      @instDecidableAnd _ _ (Formula.decLe φ1 φ1')
        (@instDecidableForall _ _ inferInstance (Formula.decLe φ2 φ2'))
  | .and _ _, .box _ _ => isTrue trivial
  | .box _ _, .bottom => isFalse not_false
  | .box _ _, .atom_prop _ => isFalse not_false
  | .box _ _, .neg _ => isFalse not_false
  | .box _ _, .and _ _ => isFalse not_false
  | .box α φ, .box α' φ' =>
      @instDecidableAnd _ _ (Program.decLe α α')
        (@instDecidableForall _ _ inferInstance (Formula.decLe φ φ'))

/-- The order on programs is decidable. -/
def Program.decLe : (α β : Program) → Decidable (Program.le α β)
  | .atom_prog a, .atom_prog a' => Nat.decLe a a'
  | .atom_prog _, .sequence _ _ => isTrue trivial
  | .atom_prog _, .union _ _ => isTrue trivial
  | .atom_prog _, .star _ => isTrue trivial
  | .atom_prog _, .test _ => isTrue trivial
  | .sequence _ _, .atom_prog _ => isFalse not_false
  | .sequence α β, .sequence α' β' =>
      @instDecidableAnd _ _ (Program.decLe α α')
        (@instDecidableForall _ _ inferInstance (Program.decLe β β'))
  | .sequence _ _, .union _ _ => isTrue trivial
  | .sequence _ _, .star _ => isTrue trivial
  | .sequence _ _, .test _ => isTrue trivial
  | .union _ _, .atom_prog _ => isFalse not_false
  | .union _ _, .sequence _ _ => isFalse not_false
  | .union α β, .union α' β' =>
      @instDecidableAnd _ _ (Program.decLe α α')
        (@instDecidableForall _ _ inferInstance (Program.decLe β β'))
  | .union _ _, .star _ => isTrue trivial
  | .union _ _, .test _ => isTrue trivial
  | .star _, .atom_prog _ => isFalse not_false
  | .star _, .sequence _ _ => isFalse not_false
  | .star _, .union _ _ => isFalse not_false
  | .star α, .star α' => Program.decLe α α'
  | .star _, .test _ => isTrue trivial
  | .test _, .atom_prog _ => isFalse not_false
  | .test _, .sequence _ _ => isFalse not_false
  | .test _, .union _ _ => isFalse not_false
  | .test _, .star _ => isFalse not_false
  | .test τ, .test τ' => Formula.decLe τ τ'
end


-- @@ L914-914 verbatim
end PDL


-- @@ L916-916 verbatim
namespace PDL


-- @@ L918-918 verbatim
open HasLength


-- @@ L920-920 verbatim
instance : DecidableRel Formula.le := Formula.decLe

-- @@ L921-921 verbatim
instance : DecidableRel Program.le := Program.decLe


-- @@ L923-923 verbatim
instance : DecidableRel (fun (a b : Formula) ↦ a ≤ b) := Formula.decLe

-- @@ L924-924 verbatim
instance : DecidableRel (fun (a b : Program) ↦ a ≤ b) := Program.decLe


-- @@ L926-926 verbatim
/-! ### The order is a linear order -/


-- @@ L928-931 verbatim
/-- Helper for the lexicographic clauses: reflexivity. -/
private theorem lex_rfl {A B : Type} {leA : A → A → Prop} {leB : B → B → Prop}
    {a : A} {b : B} (ha : leA a a) (hb : leB b b) :
    leA a a ∧ ((a = a) → leB b b) := ⟨ha, fun _ => hb⟩


-- @@ L933-945 verbatim
/-- Helper for the lexicographic clauses: totality. -/
private theorem lex_total {A B : Type} {leA : A → A → Prop} {leB : B → B → Prop}
    {a a' : A} {b b' : B} (hrefl : leA a a)
    (hA : leA a a' ∨ leA a' a) (hB : leB b b' ∨ leB b' b) :
    (leA a a' ∧ ((a = a') → leB b b')) ∨ (leA a' a ∧ ((a' = a) → leB b' b)) := by
  by_cases he : a = a'
  · subst he
    rcases hB with h | h
    · exact Or.inl ⟨hrefl, fun _ => h⟩
    · exact Or.inr ⟨hrefl, fun _ => h⟩
  · rcases hA with h | h
    · exact Or.inl ⟨h, fun hc => absurd hc he⟩
    · exact Or.inr ⟨h, fun hc => absurd hc.symm he⟩


-- @@ L947-964 verbatim
mutual

/-- The order on formulas is reflexive. -/
theorem Formula.le_rfl : ∀ (φ : Formula), φ.le φ
  | .bottom => trivial
  | .atom_prop p => Nat.le_refl p
  | .neg φ => Formula.le_rfl φ
  | .and φ1 φ2 => lex_rfl (Formula.le_rfl φ1) (Formula.le_rfl φ2)
  | .box α φ => lex_rfl (Program.le_rfl α) (Formula.le_rfl φ)

/-- The order on programs is reflexive. -/
theorem Program.le_rfl : ∀ (α : Program), α.le α
  | .atom_prog a => Nat.le_refl a
  | .sequence α β => lex_rfl (Program.le_rfl α) (Program.le_rfl β)
  | .union α β => lex_rfl (Program.le_rfl α) (Program.le_rfl β)
  | .star α => Program.le_rfl α
  | .test τ => Formula.le_rfl τ
end


-- @@ L966-966 verbatim
end PDL


-- @@ L968-968 verbatim
namespace PDL


-- @@ L970-970 verbatim
open HasLength


-- @@ L972-1045 verbatim
mutual

/-- The order on formulas is antisymmetric. -/
theorem Formula.le_antisymm : ∀ (φ ψ : Formula), φ.le ψ → ψ.le φ → φ = ψ
  | .bottom, .bottom, _, _ => rfl
  | .bottom, .atom_prop _, _, h2 => (h2 : False).elim
  | .bottom, .neg _, _, h2 => (h2 : False).elim
  | .bottom, .and _ _, _, h2 => (h2 : False).elim
  | .bottom, .box _ _, _, h2 => (h2 : False).elim
  | .atom_prop _, .bottom, h1, _ => (h1 : False).elim
  | .atom_prop _, .atom_prop _, h1, h2 => by
      simp only [Formula.atom_prop.injEq]
      exact Nat.le_antisymm h1 h2
  | .atom_prop _, .neg _, _, h2 => (h2 : False).elim
  | .atom_prop _, .and _ _, _, h2 => (h2 : False).elim
  | .atom_prop _, .box _ _, _, h2 => (h2 : False).elim
  | .neg _, .bottom, h1, _ => (h1 : False).elim
  | .neg _, .atom_prop _, h1, _ => (h1 : False).elim
  | .neg φ, .neg ψ, h1, h2 => by rw [Formula.le_antisymm φ ψ h1 h2]
  | .neg _, .and _ _, _, h2 => (h2 : False).elim
  | .neg _, .box _ _, _, h2 => (h2 : False).elim
  | .and _ _, .bottom, h1, _ => (h1 : False).elim
  | .and _ _, .atom_prop _, h1, _ => (h1 : False).elim
  | .and _ _, .neg _, h1, _ => (h1 : False).elim
  | .and φ1 φ2, .and ψ1 ψ2, h1, h2 => by
      have e1 : φ1 = ψ1 := Formula.le_antisymm φ1 ψ1 h1.1 h2.1
      subst e1
      rw [Formula.le_antisymm φ2 ψ2 (h1.2 rfl) (h2.2 rfl)]
  | .and _ _, .box _ _, _, h2 => (h2 : False).elim
  | .box _ _, .bottom, h1, _ => (h1 : False).elim
  | .box _ _, .atom_prop _, h1, _ => (h1 : False).elim
  | .box _ _, .neg _, h1, _ => (h1 : False).elim
  | .box _ _, .and _ _, h1, _ => (h1 : False).elim
  | .box α φ, .box β ψ, h1, h2 => by
      have e1 : α = β := Program.le_antisymm α β h1.1 h2.1
      subst e1
      rw [Formula.le_antisymm φ ψ (h1.2 rfl) (h2.2 rfl)]

/-- The order on programs is antisymmetric. -/
theorem Program.le_antisymm : ∀ (α β : Program), α.le β → β.le α → α = β
  | .atom_prog _, .atom_prog _, h1, h2 => by
      simp only [Program.atom_prog.injEq]
      exact Nat.le_antisymm h1 h2
  | .atom_prog _, .sequence _ _, _, h2 => (h2 : False).elim
  | .atom_prog _, .union _ _, _, h2 => (h2 : False).elim
  | .atom_prog _, .star _, _, h2 => (h2 : False).elim
  | .atom_prog _, .test _, _, h2 => (h2 : False).elim
  | .sequence _ _, .atom_prog _, h1, _ => (h1 : False).elim
  | .sequence α1 α2, .sequence β1 β2, h1, h2 => by
      have e1 : α1 = β1 := Program.le_antisymm α1 β1 h1.1 h2.1
      subst e1
      rw [Program.le_antisymm α2 β2 (h1.2 rfl) (h2.2 rfl)]
  | .sequence _ _, .union _ _, _, h2 => (h2 : False).elim
  | .sequence _ _, .star _, _, h2 => (h2 : False).elim
  | .sequence _ _, .test _, _, h2 => (h2 : False).elim
  | .union _ _, .atom_prog _, h1, _ => (h1 : False).elim
  | .union _ _, .sequence _ _, h1, _ => (h1 : False).elim
  | .union α1 α2, .union β1 β2, h1, h2 => by
      have e1 : α1 = β1 := Program.le_antisymm α1 β1 h1.1 h2.1
      subst e1
      rw [Program.le_antisymm α2 β2 (h1.2 rfl) (h2.2 rfl)]
  | .union _ _, .star _, _, h2 => (h2 : False).elim
  | .union _ _, .test _, _, h2 => (h2 : False).elim
  | .star _, .atom_prog _, h1, _ => (h1 : False).elim
  | .star _, .sequence _ _, h1, _ => (h1 : False).elim
  | .star _, .union _ _, h1, _ => (h1 : False).elim
  | .star α, .star β, h1, h2 => by rw [Program.le_antisymm α β h1 h2]
  | .star _, .test _, _, h2 => (h2 : False).elim
  | .test _, .atom_prog _, h1, _ => (h1 : False).elim
  | .test _, .sequence _ _, h1, _ => (h1 : False).elim
  | .test _, .union _ _, h1, _ => (h1 : False).elim
  | .test _, .star _, h1, _ => (h1 : False).elim
  | .test τ, .test σ, h1, h2 => by rw [Formula.le_antisymm τ σ h1 h2]
end


-- @@ L1047-1047 verbatim
end PDL


-- @@ L1049-1049 verbatim
namespace PDL


-- @@ L1051-1051 verbatim
open HasLength


-- @@ L1053-1114 verbatim
mutual

/-- The order on formulas is total. -/
theorem Formula.le_total : ∀ (φ ψ : Formula), φ.le ψ ∨ ψ.le φ
  | .bottom, .bottom => Or.inl trivial
  | .bottom, .atom_prop _ => Or.inl trivial
  | .bottom, .neg _ => Or.inl trivial
  | .bottom, .and _ _ => Or.inl trivial
  | .bottom, .box _ _ => Or.inl trivial
  | .atom_prop _, .bottom => Or.inr trivial
  | .atom_prop p, .atom_prop p' => Nat.le_total p p'
  | .atom_prop _, .neg _ => Or.inl trivial
  | .atom_prop _, .and _ _ => Or.inl trivial
  | .atom_prop _, .box _ _ => Or.inl trivial
  | .neg _, .bottom => Or.inr trivial
  | .neg _, .atom_prop _ => Or.inr trivial
  | .neg φ, .neg ψ => Formula.le_total φ ψ
  | .neg _, .and _ _ => Or.inl trivial
  | .neg _, .box _ _ => Or.inl trivial
  | .and _ _, .bottom => Or.inr trivial
  | .and _ _, .atom_prop _ => Or.inr trivial
  | .and _ _, .neg _ => Or.inr trivial
  | .and φ1 φ2, .and ψ1 ψ2 =>
      lex_total (Formula.le_rfl φ1) (Formula.le_total φ1 ψ1) (Formula.le_total φ2 ψ2)
  | .and _ _, .box _ _ => Or.inl trivial
  | .box _ _, .bottom => Or.inr trivial
  | .box _ _, .atom_prop _ => Or.inr trivial
  | .box _ _, .neg _ => Or.inr trivial
  | .box _ _, .and _ _ => Or.inr trivial
  | .box α φ, .box β ψ =>
      lex_total (Program.le_rfl α) (Program.le_total α β) (Formula.le_total φ ψ)

/-- The order on programs is total. -/
theorem Program.le_total : ∀ (α β : Program), α.le β ∨ β.le α
  | .atom_prog a, .atom_prog a' => Nat.le_total a a'
  | .atom_prog _, .sequence _ _ => Or.inl trivial
  | .atom_prog _, .union _ _ => Or.inl trivial
  | .atom_prog _, .star _ => Or.inl trivial
  | .atom_prog _, .test _ => Or.inl trivial
  | .sequence _ _, .atom_prog _ => Or.inr trivial
  | .sequence α1 α2, .sequence β1 β2 =>
      lex_total (Program.le_rfl α1) (Program.le_total α1 β1) (Program.le_total α2 β2)
  | .sequence _ _, .union _ _ => Or.inl trivial
  | .sequence _ _, .star _ => Or.inl trivial
  | .sequence _ _, .test _ => Or.inl trivial
  | .union _ _, .atom_prog _ => Or.inr trivial
  | .union _ _, .sequence _ _ => Or.inr trivial
  | .union α1 α2, .union β1 β2 =>
      lex_total (Program.le_rfl α1) (Program.le_total α1 β1) (Program.le_total α2 β2)
  | .union _ _, .star _ => Or.inl trivial
  | .union _ _, .test _ => Or.inl trivial
  | .star _, .atom_prog _ => Or.inr trivial
  | .star _, .sequence _ _ => Or.inr trivial
  | .star _, .union _ _ => Or.inr trivial
  | .star α, .star β => Program.le_total α β
  | .star _, .test _ => Or.inl trivial
  | .test _, .atom_prog _ => Or.inr trivial
  | .test _, .sequence _ _ => Or.inr trivial
  | .test _, .union _ _ => Or.inr trivial
  | .test _, .star _ => Or.inr trivial
  | .test τ, .test σ => Formula.le_total τ σ
end


-- @@ L1116-1116 verbatim
end PDL


-- @@ L1118-1118 verbatim
namespace PDL


-- @@ L1120-1120 verbatim
open HasLength


-- @@ L1122-1162 verbatim
mutual

/-- The order on formulas is transitive. -/
theorem Formula.le_trans_aux : ∀ (φ ψ χ : Formula), φ.le ψ → ψ.le χ → φ.le χ := by
  intro φ ψ χ h1 h2
  cases φ <;> cases ψ <;> cases χ <;>
    try first
      | exact trivial
      | exact (h1 : False).elim
      | exact (h2 : False).elim
  case atom_prop.atom_prop.atom_prop => exact Nat.le_trans h1 h2
  case neg.neg.neg φ ψ χ => exact Formula.le_trans_aux φ ψ χ h1 h2
  case and.and.and φ1 φ2 ψ1 ψ2 χ1 χ2 =>
    refine ⟨Formula.le_trans_aux φ1 ψ1 χ1 h1.1 h2.1, fun he => ?_⟩
    have e : φ1 = ψ1 := Formula.le_antisymm φ1 ψ1 h1.1 (by rw [he]; exact h2.1)
    exact Formula.le_trans_aux φ2 ψ2 χ2 (h1.2 e) (h2.2 (by rw [← e]; exact he))
  case box.box.box α φ β ψ γ χ =>
    refine ⟨Program.le_trans_aux α β γ h1.1 h2.1, fun he => ?_⟩
    have e : α = β := Program.le_antisymm α β h1.1 (by rw [he]; exact h2.1)
    exact Formula.le_trans_aux φ ψ χ (h1.2 e) (h2.2 (by rw [← e]; exact he))

/-- The order on programs is transitive. -/
theorem Program.le_trans_aux : ∀ (α β γ : Program), α.le β → β.le γ → α.le γ := by
  intro α β γ h1 h2
  cases α <;> cases β <;> cases γ <;>
    try first
      | exact trivial
      | exact (h1 : False).elim
      | exact (h2 : False).elim
  case atom_prog.atom_prog.atom_prog => exact Nat.le_trans h1 h2
  case sequence.sequence.sequence α1 α2 β1 β2 γ1 γ2 =>
    refine ⟨Program.le_trans_aux α1 β1 γ1 h1.1 h2.1, fun he => ?_⟩
    have e : α1 = β1 := Program.le_antisymm α1 β1 h1.1 (by rw [he]; exact h2.1)
    exact Program.le_trans_aux α2 β2 γ2 (h1.2 e) (h2.2 (by rw [← e]; exact he))
  case union.union.union α1 α2 β1 β2 γ1 γ2 =>
    refine ⟨Program.le_trans_aux α1 β1 γ1 h1.1 h2.1, fun he => ?_⟩
    have e : α1 = β1 := Program.le_antisymm α1 β1 h1.1 (by rw [he]; exact h2.1)
    exact Program.le_trans_aux α2 β2 γ2 (h1.2 e) (h2.2 (by rw [← e]; exact he))
  case star.star.star α β γ => exact Program.le_trans_aux α β γ h1 h2
  case test.test.test τ σ ρ => exact Formula.le_trans_aux τ σ ρ h1 h2
end


-- @@ L1164-1164 verbatim
end PDL


-- @@ L1166-1166 verbatim
namespace PDL


-- @@ L1168-1168 verbatim
open HasLength


-- @@ L1170-1171 verbatim
lemma Formula.le_trans : ∀ (f g h : Formula), f ≤ g → g ≤ h → f ≤ h :=
  Formula.le_trans_aux


-- @@ L1173-1174 verbatim
instance instIsTransFormulaLe : IsTrans Formula (fun (a b : Formula) ↦ a ≤ b) :=
  ⟨Formula.le_trans⟩


-- @@ L1176-1176 verbatim
instance : Std.Antisymm (fun (a b : Formula) ↦ a ≤ b) := ⟨Formula.le_antisymm⟩


-- @@ L1178-1178 verbatim
instance : Std.Total (fun (a b : Formula) ↦ a ≤ b) := ⟨Formula.le_total⟩


-- @@ L1180-1181 verbatim
/-- List the elements of a formula finset in the fixed formula order. -/
def _root_.Finset.pdlSort : Finset Formula → List Formula | FS => FS.sort


-- @@ L1183-1184 verbatim
@[simp]
lemma Formula.mem_pdlSort {X : Finset Formula} : φ ∈ X.pdlSort ↔ φ ∈ X := by simp [Finset.pdlSort]


-- @@ L1186-1186 verbatim
end PDL
