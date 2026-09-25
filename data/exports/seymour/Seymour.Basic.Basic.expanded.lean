import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.RowCol
import Mathlib.Tactic
import Linters


-- @@ L6-11 verbatim
/-!
# Basics

This is the stem file (imported by every other file in this project).
This file provides notation used throughout the project, some very basic lemmas, and a little bit of configuration.
-/


-- @@ L13-13 verbatim
/-! ## Notation -/


-- @@ L15-16 verbatim
/-- The finite field on 2 elements; write `Z2` for "value" type but `Fin 2` for "indexing" type. -/
abbrev Z2 : Type := ZMod 2


-- @@ L18-19 verbatim
/-- The finite field on 3 elements; write `Z3` for "value" type but `Fin 3` for "indexing" type. -/
abbrev Z3 : Type := ZMod 3


-- @@ L21-22 verbatim
/-- Roughly speaking `a ᕃ A` is `A ∪ {a}`. -/
infixr:66 " ᕃ " => Insert.insert


-- @@ L24-25 verbatim
/-- Writing `X ⫗ Y` is slightly more general than writing `X ∩ Y = ∅`. -/
infix:61 " ⫗ " => Disjoint


-- @@ L27-28 verbatim
/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp


-- @@ L30-31 verbatim
/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr


-- @@ L33-34 verbatim
/-- Writing `↓t` is slightly more general than writing `Function.const _ t`. -/
notation:max "↓"t:arg => (fun _ => t)


-- @@ L36-37 verbatim
/-- We denote the cardinality of a `Fintype` the same way the cardinality of a `Finset` is denoted. -/
prefix:max "#" => Fintype.card


-- @@ L39-40 verbatim
/-- Canonical bijection between subtypes corresponding to equal sets. -/
postfix:max ".≃" => Equiv.setCongr


-- @@ L42-43 verbatim
/-- The trivial bijection (identity). -/
notation "=.≃" => Equiv.refl _


-- @@ L45-46 verbatim
/-- The "left" or "top" variant. -/
prefix:max "◩" => Sum.inl


-- @@ L48-49 verbatim
/-- The "right" or "bottom" variant. -/
prefix:max "◪" => Sum.inr


-- @@ L51-52 verbatim
/-- Glue rows of two matrices. -/
infixl:63 " ⊟ " => Matrix.fromRows


-- @@ L54-55 verbatim
/-- Glue cols of two matrices. -/
infixl:63 " ◫ " => Matrix.fromCols


-- @@ L57-58 verbatim
/-- Glue four matrices into one block matrix. -/
notation "⊞ " => Matrix.fromBlocks


-- @@ L60-61 verbatim
/-- Convert vector to a single-row matrix. -/
notation:64 "▬"r:81 => Matrix.replicateRow Unit r


-- @@ L63-64 verbatim
/-- Convert vector to a single-col matrix. -/
notation:64 "▮"c:81 => Matrix.replicateCol Unit c


-- @@ L66-67 verbatim
/-- Outer product of two vectors (the column vector comes on left; the row vector comes on right). -/
abbrev outerProduct {X Y α : Type*} [Mul α] (c : X → α) (r : Y → α) := Matrix.of (fun i : X => fun j : Y => c i * r j)


-- @@ L69-70 verbatim
@[inherit_doc]
infix:67 " ⊗ " => outerProduct


-- @@ L72-74 verbatim
/-- Element-wise product of two matrices (rarely used). -/
abbrev entrywiseProduct {X Y α β : Type*} [SMul α β] (A : Matrix X Y α) (B : Matrix X Y β) :=
  Matrix.of (fun i : X => fun j : Y => A i j • B i j)


-- @@ L76-77 verbatim
@[inherit_doc]
infixr:66 " ⊡ " => entrywiseProduct


-- @@ L79-80 verbatim
/-- The set of possible outputs of a function. -/
abbrev Function.range {α ι : Type*} (f : ι → α) : Set α := Set.range f


-- @@ L82-85 verbatim
@[app_unexpander Function.range]
def Function.range_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f) => `($(f).$(Lean.mkIdent `range))
  | _ => throw ()


-- @@ L87-90 verbatim
@[app_unexpander Function.support]
def Function.support_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f) => `($(f).$(Lean.mkIdent `support))
  | _ => throw ()



-- @@ L93-93 verbatim
/-! ## Basic stuff -/


-- @@ L95-95 verbatim
variable {α : Type*}


-- @@ L97-98 verbatim
lemma Function.range_eq {ι : Type} (f : ι → α) : f.range = { a : α | ∃ i : ι, f i = a } :=
  rfl


-- @@ L100-101 verbatim
lemma dite_of_true {P : Prop} [Decidable P] (p : P) {f : P → α} {a : α} : (if hp : P then f hp else a) = f p := by
  simp [p]


-- @@ L103-104 verbatim
lemma dite_of_false {P : Prop} [Decidable P] (p : ¬P) {f : P → α} {a : α} : (if hp : P then f hp else a) = a := by
  simp [p]


-- @@ L106-107 verbatim
abbrev Equiv.leftCongr {ι₁ ι₂ : Type*} (e : ι₁ ≃ ι₂) : ι₁ ⊕ α ≃ ι₂ ⊕ α :=
  Equiv.sumCongr e (Equiv.refl α)


-- @@ L109-110 verbatim
abbrev Equiv.rightCongr {ι₁ ι₂ : Type*} (e : ι₁ ≃ ι₂) : α ⊕ ι₁ ≃ α ⊕ ι₂ :=
  Equiv.sumCongr (Equiv.refl α) e


-- @@ L112-114 expanded
@[simp]
lemma Equiv.image_symm_apply {β : Type*} {X : Set α} (e : α ≃ β) (x : X) :
    (e.image X).symm ⟨e x.val, by simp⟩ = x :=
  (Iff.mpr (e.image X).symm_apply_eq) rfl


-- @@ L116-123 expanded
lemma Finset.sum_of_single_nonzero {ι : Type*} (s : Finset ι) [AddCommMonoid α] (f : ι → α) (a : ι)
    (ha : a ∈ s) (hf : ∀ i ∈ s, i ≠ a → f i = 0) : s.sum f = f a :=
  by
  rw [← Finset.sum_subset ((Iff.mpr s.singleton_subset_iff) ha)]
  · simp
  intro x hxs hxa
  apply hf x hxs
  rwa [Finset.not_mem_singleton] at hxa


-- @@ L125-128 verbatim
lemma fintype_sum_of_single_nonzero {ι : Type*} [Fintype ι] [AddCommMonoid α] (f : ι → α) (a : ι)
    (hf : ∀ i : ι, i ≠ a → f i = 0) :
    Finset.univ.sum f = f a :=
  Finset.univ.sum_of_single_nonzero f a (Finset.mem_univ a) (by simpa using hf)


-- @@ L130-139 verbatim
lemma sum_elem_of_single_nonzero {ι : Type*} [AddCommMonoid α] {f : ι → α} {S : Set ι} [Fintype S] {a : ι} (haS : a ∈ S)
    (hf : ∀ i : ι, i ≠ a → f i = 0) :
    ∑ i : S.Elem, f i = f a := by
  apply fintype_sum_of_single_nonzero (fun s : S.Elem => f s.val) ⟨a, haS⟩
  intro i hi
  apply hf
  intro contr
  apply hi
  ext
  exact contr


-- @@ L141-145 verbatim
lemma sum_over_fin_succ_of_only_zeroth_nonzero {n : ℕ} [AddCommMonoid α] {f : Fin n.succ → α}
    (hf : ∀ i : Fin n.succ, i ≠ 0 → f i = 0) :
    Finset.univ.sum f = f 0 := by
  apply fintype_sum_of_single_nonzero
  exact hf



-- @@ L148-148 verbatim
/-! ## Aesop modifiers -/


-- @@ L150-150 verbatim
attribute [aesop apply safe] Classical.choose_spec


-- @@ L152-153 verbatim
/-- Nonterminal `aesop` (dangerous). -/
macro "aesopnt" : tactic => `(tactic| aesop (config := {warnOnNonterminal := false}))
