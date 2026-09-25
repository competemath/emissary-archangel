import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Conversions
import Seymour.Matrix.Determinants
import Seymour.Matrix.PartialUnimodularity
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Regularity


-- @@ L8-12 verbatim
/-!
# Matroid 2-sum

Here we study the 2-sum of matroids (starting with the 2-sum of matrices).
-/


-- @@ L14-14 verbatim
/-! ## Shorthands for convenience -/


-- @@ L16-16 verbatim
/-! All declarations in this section are private. -/


-- @@ L18-19 verbatim
private abbrev Eq._ₗ {α : Type*} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : X :=
  ⟨a, Set.mem_of_mem_inter_left (ha.symm.subset rfl)⟩


-- @@ L21-24 verbatim
@[app_unexpander Eq._ₗ]
private def Eq._ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `_ₗ))
  | _ => throw ()


-- @@ L26-27 verbatim
private abbrev Eq._ᵣ {α : Type*} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : Y :=
  ⟨a, Set.mem_of_mem_inter_right (ha.symm.subset rfl)⟩


-- @@ L29-32 verbatim
@[app_unexpander Eq._ᵣ]
private def Eq._ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `_ᵣ))
  | _ => throw ()


-- @@ L34-36 verbatim
private abbrev Matrix.dropRow {α R : Type*} {X Y : Set α} (A : Matrix X Y R) (a : α) :
    Matrix (X \ {a}).Elem Y.Elem R :=
  A ∘ Set.diff_subset.elem


-- @@ L38-41 verbatim
@[app_unexpander Matrix.dropRow]
private def Matrix.dropRow_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `dropRow))
  | _ => throw ()


-- @@ L43-45 verbatim
private abbrev Matrix.dropCol {α R : Type*} {X Y : Set α} (A : Matrix X Y R) (a : α) :
    Matrix X.Elem (Y \ {a}).Elem R :=
  (A · ∘ Set.diff_subset.elem)


-- @@ L47-50 verbatim
@[app_unexpander Matrix.dropCol]
private def Matrix.dropCol_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `dropCol))
  | _ => throw ()


-- @@ L52-54 verbatim
private abbrev Matrix.interRow {α R : Type*} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : X ∩ Z = {a}) :
    Y.Elem → R :=
  A ha._ₗ


-- @@ L56-59 verbatim
@[app_unexpander Matrix.interRow]
private def Matrix.interRow_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `interRow))
  | _ => throw ()


-- @@ L61-63 verbatim
private abbrev Matrix.interCol {α R : Type*} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : Z ∩ Y = {a}) :
    X.Elem → R :=
  (A · ha._ᵣ)


-- @@ L65-68 verbatim
@[app_unexpander Matrix.interCol]
private def Matrix.interCol_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `interCol))
  | _ => throw ()


-- @@ L70-72 expanded
private abbrev Matrix.reglueRow {α R : Type*} {X Y Z : Set α} (A : Matrix X Y R) {a : α}
    (ha : X ∩ Z = { a }) : Matrix ((X \ { a }).Elem ⊕ Unit) Y.Elem R :=
  Matrix.fromRows (A.dropRow a) (Matrix.replicateRow Unit (A.interRow ha))


-- @@ L74-77 verbatim
@[app_unexpander Matrix.reglueRow]
private def Matrix.reglueRow_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `reglueRow))
  | _ => throw ()


-- @@ L79-81 expanded
private abbrev Matrix.reglueCol {α R : Type*} {X Y Z : Set α} (A : Matrix X Y R) {a : α}
    (ha : Z ∩ Y = { a }) : Matrix X.Elem (Unit ⊕ (Y \ { a }).Elem) R :=
  Matrix.fromCols (Matrix.replicateCol Unit (A.interCol ha)) (A.dropCol a)


-- @@ L83-86 verbatim
@[app_unexpander Matrix.reglueCol]
private def Matrix.reglueCol_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `reglueCol))
  | _ => throw ()


-- @@ L88-90 expanded
private lemma Matrix.reglueRow_eq {α R : Type*} [CommRing R] {X Y Z : Set α} {A : Matrix X Y R}
    {a : α} (ha : X ∩ Z = { a }) :
    A.reglueRow ha = A.submatrix (·.casesOn Set.diff_subset.elem (fun _ => ha._ₗ)) id := by aesop


-- @@ L92-94 expanded
private lemma Matrix.reglueCol_eq {α R : Type*} {X Y Z : Set α} (A : Matrix X Y R) {a : α}
    (ha : Z ∩ Y = { a }) :
    A.reglueCol ha = A.submatrix id (·.casesOn (fun _ => ha._ᵣ) Set.diff_subset.elem) := by aesop


-- @@ L96-100 verbatim
private lemma Matrix.IsTotallyUnimodular.reglueRow {α R : Type*} [CommRing R] {X Y Z : Set α} {A : Matrix X Y R}
    (hA : A.IsTotallyUnimodular) {a : α} (ha : X ∩ Z = {a}) :
    (A.reglueRow ha).IsTotallyUnimodular := by
  rw [A.reglueRow_eq ha]
  apply hA.submatrix


-- @@ L102-106 verbatim
private lemma Matrix.IsTotallyUnimodular.reglueCol {α R : Type*} [CommRing R] {X Y Z : Set α} {A : Matrix X Y R}
    (hA : A.IsTotallyUnimodular) {a : α} (ha : Z ∩ Y = {a}) :
    (A.reglueCol ha).IsTotallyUnimodular := by
  rw [A.reglueCol_eq ha]
  apply hA.submatrix



-- @@ L109-109 verbatim
/-! ## Definition -/


-- @@ L111-115 expanded
/--
`Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
def matrixSum2 {R : Type*} [Semiring R] {Xₗ Yₗ Xᵣ Yᵣ : Type*} (Aₗ : Matrix Xₗ Yₗ R) (r : Yₗ → R)
    (Aᵣ : Matrix Xᵣ Yᵣ R) (c : Xᵣ → R) : Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  Matrix.fromBlocks Aₗ 0 (outerProduct c r) Aᵣ


-- @@ L117-142 expanded
/-- `StandardRepr`-level 2-sum of two matroids. Returns the result only if valid. -/
noncomputable def standardReprSum2 {α : Type*} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x y : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = { x }) (hYY : Sₗ.Y ∩ Sᵣ.Y = { y }) (hXY : Disjoint Sₗ.X Sᵣ.Y)
    (hYX : Disjoint Sₗ.Y Sᵣ.X) : Option (StandardRepr α Z2) :=
  open scoped Classical in
    if Sₗ.B.interRow hXX ≠ 0 ∧ Sᵣ.B.interCol hYY ≠ 0 then
      some
        ⟨
          -- row indices(Sₗ.X \ { x }) ∪ Sᵣ.X,
          -- col indicesSₗ.Y ∪ (Sᵣ.Y \ { y }),
          -- row and col indices are disjointunion_disjoint_union Sₗ.hXY.disjoint_sdiff_left
            Sᵣ.hXY.disjoint_sdiff_right hXY.disjoint_sdiff_left.disjoint_sdiff_right hYX,
          -- standard representation matrix(matrixSum2 (Sₗ.B.dropRow x) (Sₗ.B.interRow hXX)
              (Sᵣ.B.dropCol y) (Sᵣ.B.interCol hYY)).toMatrixUnionUnion,
          -- decidability of row indicesinferInstance,
          -- decidability of col indicesinferInstance⟩
    else none


-- @@ L144-155 expanded
/-- Binary matroid `M` is a result of 2-summing `Mₗ` and `Mᵣ` in some way. -/
def Matroid.IsSum2of {α : Type*} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
    ∃ x y : α,
      ∃ hXX : Sₗ.X ∩ Sᵣ.X = { x },
        ∃ hYY : Sₗ.Y ∩ Sᵣ.Y = { y },
          ∃ hXY : Disjoint Sₗ.X Sᵣ.Y,
            ∃ hYX : Disjoint Sₗ.Y Sᵣ.X,
              standardReprSum2 hXX hYY hXY hYX = some S ∧
                S.toMatroid = M ∧ Sₗ.toMatroid = Mₗ ∧ Sᵣ.toMatroid = Mᵣ


-- @@ L158-158 verbatim
/-! ## Specifics about pivoting for the proof of 2-sum regularity -/


-- @@ L160-160 verbatim
/-! All declarations in this section are private. -/


-- @@ L162-165 expanded
private abbrev shortTableauPivotOtherRow {Y Y' R : Type*} [DecidableEq Y'] [DivisionRing R]
    (p : Y → R) (r : Y' → R) (g : Y' → Y) (y' : Y') : Y' → R :=
  -- `p` is the pivot row; `r` is the other row; `g` is a map from the columns of `r` to the columns of `p`
  (Matrix.fromRows (Matrix.replicateRow Unit (p ∘ g))
        (Matrix.replicateRow Unit r)).shortTableauPivot
    (Sum.inl ⟨⟩) y' (Sum.inr ⟨⟩)


-- @@ L167-178 verbatim
private lemma Matrix.shortTableauPivot_otherRow_eq {X Y Y' R : Type*}
    [Field R] [DecidableEq X] [DecidableEq Y] [DecidableEq Y']
    (A : Matrix X Y R) (x : X) (y' : Y') {i : X} (hix : i ≠ x) {g : Y' → Y} (hg : g.Injective) :
    (A.shortTableauPivot x (g y')) i ∘ g = shortTableauPivotOtherRow (A x) (A i ∘ g) g y' := by
  ext j'
  simp only [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.replicateRow_apply, Matrix.of_apply,
    Matrix.shortTableauPivot_eq, shortTableauPivotOtherRow, Function.comp_apply, one_div, reduceCtorEq, hix]
  if hj' : j' = y' then
    simp only [hj']
  else
    simp only [hj', ↓reduceIte, ite_eq_right_iff]
    exact (False.elim <| hj' <| hg ·)


-- @@ L180-191 expanded
private lemma Matrix.shortTableauPivot_outer {X Y X' Y' F : Type*} [DecidableEq X] [DecidableEq Y]
    [DecidableEq Y'] [Field F] (A : Matrix X Y F) (x : X) (y' : Y') (f : X' → X) (g : Y' → Y)
    (hf : x ∉ f.range) (hg : g.Injective) (r : Y' → F) (c : X' → F)
    (hBfg : A.submatrix f g = (outerProduct c r)) :
    (A.shortTableauPivot x (g y')).submatrix f g =
      (outerProduct c (shortTableauPivotOtherRow (A x) r g y')) :=
  by
  ext i j
  have hfig : A (f i) ∘ g = (c i * r ·) := congr_fun hBfg i
  have hAgfg :=
    hfig ▸
      Function.comp_apply ▸
        congr_fun
          (A.shortTableauPivot_otherRow_eq x y' (ne_of_mem_of_not_mem (Set.mem_range_self i) hf) hg)
          j
  rw [Matrix.submatrix_apply, hAgfg]
  by_cases hj : j = y' <;> simp [shortTableauPivotOtherRow, Matrix.shortTableauPivot_eq, hj] <;>
    ring


-- @@ L193-206 expanded
private lemma matrixSum2_shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Yₗ]
    [DecidableEq Xᵣ] [DecidableEq Yᵣ] (Aₗ : Matrix Xₗ Yₗ ℚ) (r : Yₗ → ℚ) (Aᵣ : Matrix Xᵣ Yᵣ ℚ)
    (c : Xᵣ → ℚ) {i : Xₗ} {j : Yₗ} :
    (matrixSum2 Aₗ r Aᵣ c).shortTableauPivot (Sum.inl i) (Sum.inl j) =
      matrixSum2 (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) r id j) Aᵣ c :=
  ((matrixSum2 Aₗ r Aᵣ c).shortTableauPivot (Sum.inl i) (Sum.inl j)).fromBlocks_toBlocks ▸
    (matrixSum2 (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) r id j) Aᵣ
          c).fromBlocks_toBlocks ▸
      (Iff.mpr Matrix.fromBlocks_inj)
        ⟨((matrixSum2 Aₗ r Aᵣ c).submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective i
              j).symm,
          Matrix.ext
            ((matrixSum2 Aₗ r Aᵣ c).shortTableauPivot_zero i (Sum.inl j) Sum.inl Sum.inr (by simp)
              (by simp [matrixSum2])),
          (matrixSum2 Aₗ r Aᵣ c).shortTableauPivot_outer (Sum.inl i) j Sum.inr Sum.inl (by simp)
            Sum.inl_injective r c rfl,
          (matrixSum2 Aₗ r Aᵣ c).shortTableauPivot_submatrix_zero_external_row (Sum.inl i)
            (Sum.inl j) Sum.inr Sum.inr (by simp) (by simp) (fun _ => rfl)⟩


-- @@ L208-211 expanded
private lemma Matrix.shortTableauPivot_adjoinRow_eq {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y ℚ) (r : Y → ℚ) (x : X) (y : Y) (j : Y) :
    (Matrix.fromRows (Matrix.replicateRow Unit (A x))
            (Matrix.replicateRow Unit r)).shortTableauPivot
        (Sum.inl ⟨⟩) y (Sum.inr ⟨⟩) j =
      (Matrix.fromRows A (Matrix.replicateRow Unit r)).shortTableauPivot (Sum.inl x) y (Sum.inr ⟨⟩)
        j :=
  by by_cases hj : j = y <;> simp [hj, Matrix.shortTableauPivot, Matrix.longTableauPivot]


-- @@ L213-220 expanded
private lemma Matrix.IsTotallyUnimodular.fromRows_pivot {α : Type*} [DecidableEq α] {X Y : Set α}
    {A : Matrix X Y ℚ} {r : Y → ℚ}
    (hAr : (Matrix.fromRows A (Matrix.replicateRow Unit r)).IsTotallyUnimodular) {x : X} {y : Y}
    (hAxy : A x y ≠ 0) :
    (Matrix.fromRows (A.shortTableauPivot x y)
        (Matrix.replicateRow Unit (shortTableauPivotOtherRow (A x) r id y))).IsTotallyUnimodular :=
  by
  have hArxy : (Matrix.fromRows A (Matrix.replicateRow Unit r)) (Sum.inl x) y ≠ 0 := hAxy
  convert hAr.shortTableauPivot hArxy
  exact
    Matrix.ext
      (·.casesOn
        (congr_fun₂
          ((Matrix.fromRows A (Matrix.replicateRow Unit r)).submatrix_shortTableauPivot
            Sum.inl_injective Function.injective_id x y))
        (fun _ => (A.shortTableauPivot_adjoinRow_eq r x y)))


-- @@ L223-223 verbatim
/-! ## Total unimodularity after adjoining an outer product -/


-- @@ L225-225 verbatim
/-! All declarations in this section are private. -/


-- @@ L227-234 expanded
private lemma Matrix.IsTotallyUnimodular.fromCols_pnz {X Y : Type*} [DecidableEq Y]
    {A : Matrix X Y ℚ} {c : X → ℚ}
    (hAc : (Matrix.fromCols A (Matrix.replicateCol Unit c)).IsTotallyUnimodular) :
    (Matrix.fromCols
        (Matrix.fromCols (Matrix.fromCols A (Matrix.replicateCol Unit c))
          (Matrix.replicateCol Unit (-c)))
        (Matrix.replicateCol Unit 0)).IsTotallyUnimodular :=
  by
  have hAcc :
    (Matrix.fromCols (Matrix.fromCols A (Matrix.replicateCol Unit c))
        (Matrix.replicateCol Unit c)).IsTotallyUnimodular
  · convert hAc.comp_cols (Sum.casesOn · id Sum.inr)
    ext (_ | _) <;> simp
  convert
    (hAcc.mul_cols
          (show ∀ j, (·.casesOn 1 (-1)) j ∈ SignType.cast.range by
            rintro (_ | _) <;> simp)).fromCols_zero
      Unit
  ext _ (_ | _) <;> simp


-- @@ L236-254 expanded
private lemma Matrix.IsTotallyUnimodular.fromCols_outer {X Yᵣ Y' : Type*} [DecidableEq Yᵣ]
    {A : Matrix X Yᵣ ℚ} {r : Y' → ℚ} {c : X → ℚ}
    (hAc : (Matrix.fromCols A (Matrix.replicateCol Unit c)).IsTotallyUnimodular)
    (hr : ∀ j' : Y', r j' ∈ SignType.cast.range) : (A ◫ (outerProduct c r)).IsTotallyUnimodular :=
  by
  convert
    hAc.fromCols_pnz.comp_cols
      (fun j : Yᵣ ⊕ Y' =>
        j.casesOn (Sum.inl ∘ Sum.inl ∘ Sum.inl)
          (fun j : Y' =>
            if h0 : r j = 0 then Sum.inr ⟨⟩
            else
              if h1 : r j = 1 then Sum.inl (Sum.inl (Sum.inr ⟨⟩))
              else
                if h9 : r j = -1 then Sum.inl (Sum.inr ⟨⟩)
                else False.elim (by obtain ⟨s, hs⟩ := hr j; cases s <;> simp_all)))
  ext (_ | j)
  · simp
  · obtain ⟨s, hs⟩ := hr j
    simp only [Matrix.fromCols_apply_inr, Matrix.replicateCol_zero, Function.comp_apply]
    split_ifs
    all_goals try simp [*]
    exfalso
    cases s <;> simp_all


-- @@ L256-260 expanded
private lemma matrixSum2_bottom_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Yᵣ]
    [DecidableEq Yₗ] {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Matrix.fromRows Aₗ (Matrix.replicateRow Unit r)).IsTotallyUnimodular)
    (hAc : (Matrix.fromCols (Matrix.replicateCol Unit c) Aᵣ).IsTotallyUnimodular) :
    ((outerProduct c r) ◫ Aᵣ).IsTotallyUnimodular :=
  (hAc.fromCols_comm.fromCols_outer (hAr.apply (Sum.inr ⟨⟩))).fromCols_comm


-- @@ L263-263 verbatim
/-! ## Proof of regularity of the 2-sum -/


-- @@ L265-265 verbatim
variable {α : Type*}


-- @@ L267-279 expanded
private lemma matrixSum2_isPartiallyUnimodular_1 {Xₗ Yₗ Xᵣ Yᵣ : Set α} {Aₗ : Matrix Xₗ Yₗ ℚ}
    {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Matrix.fromRows Aₗ (Matrix.replicateRow Unit r)).IsTotallyUnimodular)
    (hAc : (Matrix.fromCols (Matrix.replicateCol Unit c) Aᵣ).IsTotallyUnimodular) :
    (matrixSum2 Aₗ r Aᵣ c).IsPartiallyUnimodular 1 :=
  by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  cases f 0 with
  | inl iₗ =>
    cases g 0 with
    | inl jₗ => exact (hAr.comp_rows Sum.inl).apply iₗ jₗ
    | inr jᵣ => exact zero_in_signTypeCastRange
  | inr iᵣ =>
    cases g 0 with
    | inl jₗ =>
      exact
        in_signTypeCastRange_mul_in_signTypeCastRange (hAc.apply iᵣ (Sum.inl ⟨⟩))
          (hAr.apply (Sum.inr ⟨⟩) jₗ)
    | inr jᵣ => exact (hAc.comp_cols Sum.inr).apply iᵣ jᵣ


-- @@ L281-281 verbatim
variable [DecidableEq α]


-- @@ L283-329 expanded
private lemma matrixSum2_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Set α} {Aₗ : Matrix Xₗ Yₗ ℚ}
    {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Matrix.fromRows Aₗ (Matrix.replicateRow Unit r)).IsTotallyUnimodular)
    (hAc : (Matrix.fromCols (Matrix.replicateCol Unit c) Aᵣ).IsTotallyUnimodular) :
    (matrixSum2 Aₗ r Aᵣ c).IsTotallyUnimodular :=
  by
  rw [Matrix.isTotallyUnimodular_iff_forall_isPartiallyUnimodular]
  intro k
  cases k with
  | zero => simp [Matrix.IsPartiallyUnimodular]
  | succ m =>
    induction m generalizing Aₗ r Aᵣ c with
    | zero => exact matrixSum2_isPartiallyUnimodular_1 hAr hAc
    | succ n ih =>
      intro f g
      wlog hf : f.Injective
      ·
        exact
          (matrixSum2 Aₗ r Aᵣ c).submatrix_det_zero_of_not_injective_rows g hf ▸
            zero_in_signTypeCastRange
      wlog hg : g.Injective
      ·
        exact
          (matrixSum2 Aₗ r Aᵣ c).submatrix_det_zero_of_not_injective_cols f hg ▸
            zero_in_signTypeCastRange
      wlog hfₗ : ∃ iₗ : Fin (n + 2), ∃ xₗ : Xₗ, f iₗ = Sum.inl xₗ
      · push_neg at hfₗ
        convert (matrixSum2_bottom_isTotallyUnimodular hAr hAc).det (fn_of_sum_ne_inl hfₗ) g using 2
        ext
        rewrite [Matrix.submatrix_apply, Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfₗ]
        rfl
      obtain ⟨iₗ, xₗ, hfiₗ⟩ := hfₗ
      wlog hgₗ : ∃ j₀ : Fin (n + 2), ∃ y₀ : Yₗ, g j₀ = Sum.inl y₀ ∧ Aₗ xₗ y₀ ≠ 0
      · push_neg at hgₗ
        convert zero_in_signTypeCastRange
        apply ((matrixSum2 Aₗ r Aᵣ c).submatrix f g).det_eq_zero_of_row_eq_zero iₗ
        intro j
        cases hgj : g j with
        | inl => exact Matrix.submatrix_apply .. ▸ hgj ▸ hfiₗ ▸ hgₗ j _ hgj
        | inr => exact Matrix.submatrix_apply .. ▸ hgj ▸ hfiₗ ▸ rfl
      obtain ⟨j₀, y₀, hgj₀, hAxy0⟩ := hgₗ
      have hAxy1 : Aₗ xₗ y₀ = 1 ∨ Aₗ xₗ y₀ = -1
      · obtain ⟨s, hs⟩ := (hAr.comp_rows Sum.inl).apply xₗ y₀
        cases s with
        | zero => exact (hAxy0 hs.symm).elim
        | pos => exact Or.inl hs.symm
        | neg => exact Or.inr hs.symm
      have hArAc1 :
        ((matrixSum2 Aₗ r Aᵣ c).submatrix f g) iₗ j₀ = 1 ∨
          ((matrixSum2 Aₗ r Aᵣ c).submatrix f g) iₗ j₀ = -1
      · rw [Matrix.submatrix_apply, hfiₗ, hgj₀]
        exact hAxy1
      obtain ⟨f', g', hArAc⟩ :=
        ((matrixSum2 Aₗ r Aᵣ c).submatrix f g).abs_det_eq_shortTableauPivot_submatrix_abs_det hArAc1
      rw [in_signTypeCastRange_iff_abs, hArAc,
        (matrixSum2 Aₗ r Aᵣ c).submatrix_shortTableauPivot hf hg iₗ j₀, hfiₗ, hgj₀,
        Matrix.submatrix_submatrix, matrixSum2_shortTableauPivot Aₗ r Aᵣ c, ←
        in_signTypeCastRange_iff_abs]
      exact ih (hAr.fromRows_pivot hAxy0) hAc (f ∘ f') (g ∘ g')


-- @@ L331-337 expanded
private lemma standardReprSum2_X_x {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α}
    {hx : Sₗ.X ∩ Sᵣ.X = { x }} {hy : Sₗ.Y ∩ Sᵣ.Y = { y }} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hS : standardReprSum2 hx hy hXY hYX = some S) :
    S.X = (Sₗ.X \ { x }) ∪ Sᵣ.X :=
  by
  simp_rw [standardReprSum2, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.X hSSS.symm


-- @@ L339-348 expanded
lemma standardReprSum2_X_eq {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α} {hx : Sₗ.X ∩ Sᵣ.X = { x }}
    {hy : Sₗ.Y ∩ Sᵣ.Y = { y }} {hXY : Disjoint Sₗ.X Sᵣ.Y} {hYX : Disjoint Sₗ.Y Sᵣ.X}
    (hS : standardReprSum2 hx hy hXY hYX = some S) : S.X = Sₗ.X ∪ Sᵣ.X :=
  by
  rw [standardReprSum2_X_x hS]
  ext a
  if a = x then simp [*, singleton_inter_in_right hx] else simp [*]


-- @@ L350-356 expanded
private lemma standardReprSum2_Y_y {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α}
    {hx : Sₗ.X ∩ Sᵣ.X = { x }} {hy : Sₗ.Y ∩ Sᵣ.Y = { y }} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hS : standardReprSum2 hx hy hXY hYX = some S) :
    S.Y = Sₗ.Y ∪ (Sᵣ.Y \ { y }) :=
  by
  simp_rw [standardReprSum2, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.Y hSSS.symm


-- @@ L358-367 expanded
lemma standardReprSum2_Y_eq {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α} {hx : Sₗ.X ∩ Sᵣ.X = { x }}
    {hy : Sₗ.Y ∩ Sᵣ.Y = { y }} {hXY : Disjoint Sₗ.X Sᵣ.Y} {hYX : Disjoint Sₗ.Y Sᵣ.X}
    (hS : standardReprSum2 hx hy hXY hYX = some S) : S.Y = Sₗ.Y ∪ Sᵣ.Y :=
  by
  rw [standardReprSum2_Y_y hS]
  ext a
  if a = y then simp [*, singleton_inter_in_left hy] else simp [*]


-- @@ L369-388 expanded
lemma standardReprSum2_hasTuSigning {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α}
    {hx : Sₗ.X ∩ Sᵣ.X = { x }} {hy : Sₗ.Y ∩ Sᵣ.Y = { y }} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning)
    (hS : standardReprSum2 hx hy hXY hYX = some S) : S.B.HasTuSigning :=
  by
  have ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  have ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  have hSX : S.X = Sₗ.X \ { x } ∪ Sᵣ.X := standardReprSum2_X_x hS
  have hSY : S.Y = Sₗ.Y ∪ Sᵣ.Y \ { y } := standardReprSum2_Y_y hS
  have hSB :
    S.B =
      (matrixSum2 (Sₗ.B.dropRow x) (Sₗ.B.interRow hx) (Sᵣ.B.dropCol y)
            (Sᵣ.B.interCol hy)).toMatrixElemElem
        hSX hSY
  · simp_rw [standardReprSum2, Option.ite_none_right_eq_some] at hS
    aesop
  use
    (matrixSum2 (Bₗ.dropRow x) (Bₗ.interRow hx) (Bᵣ.dropCol y) (Bᵣ.interCol hy)).toMatrixElemElem
      hSX hSY,
    (matrixSum2_isTotallyUnimodular (hBₗ.reglueRow hx) (hBᵣ.reglueCol hy)).toMatrixElemElem hSX hSY
  rw [hSB]
  intro i j
  simp only [Matrix.toMatrixElemElem_apply]
  exact
    (hSX ▸ i).toSum.casesOn
      (fun iₗ => (hSY ▸ j).toSum.casesOn (hBBₗ (Set.diff_subset.elem iₗ)) (fun _ => abs_zero))
      (fun iᵣ =>
        (hSY ▸ j).toSum.casesOn (abs_mul_eq_zmod_cast (hBBᵣ iᵣ hy._ᵣ) <| hBBₗ hx._ₗ ·)
          (hBBᵣ iᵣ <| Set.diff_subset.elem ·))


-- @@ L390-396 verbatim
lemma Matroid.IsSum2of.E_eq (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hMMM : M.IsSum2of Mₗ Mᵣ) :
    M.E = Mₗ.E ∪ Mᵣ.E := by
  obtain ⟨S, _, _, _, _, _, _, _, _, hS, rfl, rfl, rfl⟩ := hMMM
  have hX := standardReprSum2_X_eq hS
  have hY := standardReprSum2_Y_eq hS
  simp only [StandardRepr.toMatroid_E]
  tauto_set


-- @@ L398-408 verbatim
/-- Any 2-sum of regular matroids is a regular matroid.
    This is part two (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsSum2of.isRegular {M Mₗ Mᵣ : Matroid α}
    (hMMM : M.IsSum2of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨S, Sₗ, Sᵣ, _, _, _, _, _, _, hSSS, rfl, rfl, rfl⟩ := hMMM
  have hX : Finite S.X := S.finite_X_of_toMatroid_rankFinite hM
  obtain ⟨hXₗ, hXᵣ⟩ : Finite Sₗ.X ∧ Finite Sᵣ.X
  · simpa [standardReprSum2_X_eq hSSS, Set.finite_coe_iff] using hX
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum2_hasTuSigning hMₗ hMᵣ hSSS
