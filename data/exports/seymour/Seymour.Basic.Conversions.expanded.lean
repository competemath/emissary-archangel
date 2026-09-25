import Seymour.Basic.Basic


-- @@ L3-7 verbatim
/-!
# Conversion between set-based notions and type-based notions

These conversions are frequently used throughout the project.
-/


-- @@ L9-9 verbatim
variable {α : Type*} {X Y : Set α}


-- @@ L11-14 verbatim
/-- Given `X ⊆ Y` cast an element of `X` as an element of `Y`. -/
@[simp low]
def HasSubset.Subset.elem (hXY : X ⊆ Y) (x : X.Elem) : Y.Elem :=
  ⟨x.val, hXY x.property⟩


-- @@ L16-17 verbatim
lemma HasSubset.Subset.elem_range (hXY : X ⊆ Y) : hXY.elem.range = { a : Y.Elem | a.val ∈ X } := by
  aesop


-- @@ L19-22 verbatim
lemma HasSubset.Subset.elem_injective (hXY : X ⊆ Y) : hXY.elem.Injective := by
  intro x y hxy
  ext
  simpa using hxy


-- @@ L24-26 verbatim
/-- Given `X ⊆ Y` provide an embedding (i.e., bundled injective function) from `X` into `Y`. -/
abbrev HasSubset.Subset.embed (hXY : X ⊆ Y) : X.Elem ↪ Y.Elem :=
  ⟨hXY.elem, hXY.elem_injective⟩


-- @@ L28-32 expanded
/-- Convert `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem`. -/
def Subtype.toSum [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) :
    X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then Sum.inl ⟨i, hiX⟩
  else if hiY : i.val ∈ Y then Sum.inr ⟨i, hiY⟩ else (i.property.elim hiX hiY).elim


-- @@ L34-37 verbatim
@[app_unexpander Subtype.toSum]
def Subtype.toSum_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $i) => `($(i).$(Lean.mkIdent `toSum))
  | _ => throw ()


-- @@ L39-43 expanded
@[simp]
lemma toSum_left [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] {x : (X ∪ Y).Elem}
    (hx : x.val ∈ X) : x.toSum = Sum.inl ⟨x.val, hx⟩ := by simp [Subtype.toSum, hx]


-- @@ L45-49 expanded
@[simp]
lemma toSum_right [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] {y : (X ∪ Y).Elem}
    (hyX : y.val ∉ X) (hyY : y.val ∈ Y) : y.toSum = Sum.inr ⟨y.val, hyY⟩ := by
  simp [Subtype.toSum, hyY, hyX]


-- @@ L51-63 expanded
lemma val_eq_val_of_toSum_eq_left [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] {x : X}
    {x' : (X ∪ Y).Elem} (hxx : x'.toSum = Sum.inl x) : x.val = x'.val :=
  by
  obtain ⟨x₀, hx₀⟩ := x
  obtain ⟨x₁, hx₁⟩ := x'
  unfold Subtype.toSum at hxx
  split at hxx
  · simpa using hxx.symm
  split at hxx
  · simp at hxx
  exfalso
  generalize_proofs imposs at hxx
  exact imposs


-- @@ L65-77 expanded
lemma val_eq_val_of_toSum_eq_right [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] {y : Y}
    {y' : (X ∪ Y).Elem} (hyy : y'.toSum = Sum.inr y) : y.val = y'.val :=
  by
  obtain ⟨y₀, hy₀⟩ := y
  obtain ⟨y₁, hy₁⟩ := y'
  unfold Subtype.toSum at hyy
  split at hyy
  · simp at hyy
  split at hyy
  · simpa using hyy.symm
  exfalso
  generalize_proofs imposs at hyy
  exact imposs


-- @@ L79-81 verbatim
/-- Convert `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem`. -/
def Sum.toUnion (i : X.Elem ⊕ Y.Elem) : (X ∪ Y).Elem :=
  i.casesOn Set.subset_union_left.elem Set.subset_union_right.elem


-- @@ L83-85 expanded
@[simp]
lemma toUnion_left (x : X.Elem) :
    @Sum.toUnion α X Y (Sum.inl x) = ⟨x.val, Set.subset_union_left x.property⟩ :=
  rfl


-- @@ L87-89 expanded
@[simp]
lemma toUnion_right (y : Y.Elem) :
    @Sum.toUnion α X Y (Sum.inr y) = ⟨y.val, Set.subset_union_right y.property⟩ :=
  rfl


-- @@ L91-91 verbatim
variable [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)]


-- @@ L93-103 verbatim
/-- Converting `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem` and back to `(X ∪ Y).Elem` gives the original element. -/
@[simp]
lemma toSum_toUnion (i : (X ∪ Y).Elem) :
    i.toSum.toUnion = i := by
  if hiX : i.val ∈ X then
    simp [hiX]
  else if hiY : i.val ∈ Y then
    simp [hiX, hiY]
  else
    exfalso
    exact i.property.elim hiX hiY


-- @@ L105-111 expanded
/--
Converting `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem` and back to `X.Elem ⊕ Y.Elem` gives the original element, assuming that
    `X` and `Y` are disjoint. -/
@[simp]
lemma toUnion_toSum (hXY : Disjoint X Y) (i : X.Elem ⊕ Y.Elem) : i.toUnion.toSum = i :=
  by
  rw [Set.disjoint_right] at hXY
  cases i <;> simp [hXY]


-- @@ L113-115 expanded
/-- Equivalence between `X.Elem ⊕ Y.Elem` and `(X ∪ Y).Elem` (i.e., a bundled bijection). -/
def Disjoint.equivSumUnion (hXY : Disjoint X Y) : X.Elem ⊕ Y.Elem ≃ (X ∪ Y).Elem :=
  ⟨Sum.toUnion, Subtype.toSum, toUnion_toSum hXY, toSum_toUnion⟩


-- @@ L117-120 expanded
@[simp]
lemma equivSumUnion_apply_left (hXY : Disjoint X Y) (x : X.Elem) :
    hXY.equivSumUnion (Sum.inl x) = ⟨x.val, Set.subset_union_left x.property⟩ :=
  rfl


-- @@ L122-125 expanded
@[simp]
lemma equivSumUnion_apply_right (hXY : Disjoint X Y) (y : Y.Elem) :
    hXY.equivSumUnion (Sum.inr y) = ⟨y.val, Set.subset_union_right y.property⟩ :=
  rfl


-- @@ L127-130 expanded
@[simp]
lemma equivSumUnion_symm_apply_left (hXY : Disjoint X Y) {x : (X ∪ Y).Elem} (hx : x.val ∈ X) :
    hXY.equivSumUnion.symm x = Sum.inl ⟨x.val, hx⟩ :=
  toSum_left hx


-- @@ L132-135 expanded
@[simp]
lemma equivSumUnion_symm_apply_right (hXY : Disjoint X Y) {y : (X ∪ Y).Elem} (hy : y.val ∈ Y) :
    hXY.equivSumUnion.symm y = Sum.inr ⟨y.val, hy⟩ :=
  toSum_right (hXY.symm.not_mem_of_mem_left hy) hy

