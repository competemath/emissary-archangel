import Seymour.Matrix.LinearIndependenceBlock
import Seymour.Matroid.Regularity


-- @@ L4-8 verbatim
/-!
# Matroid 1-sum

Here we study the 1-sum of matroids (starting with the 1-sum of matrices).
-/


-- @@ L10-10 verbatim
/-! ## Definition -/


-- @@ L12-16 expanded
/--
`Matrix`-level 1-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
def matrixSum1 {R : Type*} [Zero R] {Xₗ Yₗ Xᵣ Yᵣ : Type*} (Aₗ : Matrix Xₗ Yₗ R)
    (Aᵣ : Matrix Xᵣ Yᵣ R) : Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  Matrix.fromBlocks Aₗ 0 0 Aᵣ


-- @@ L18-18 verbatim
variable {α : Type*} [DecidableEq α]


-- @@ L20-40 expanded
/-- `StandardRepr`-level 1-sum of two matroids. Returns the result only if valid. -/
noncomputable def standardReprSum1 {Sₗ Sᵣ : StandardRepr α Z2} (hXY : Disjoint Sₗ.X Sᵣ.Y)
    (hYX : Disjoint Sₗ.Y Sᵣ.X) : Option (StandardRepr α Z2) :=
  open scoped Classical in
    if Disjoint Sₗ.X Sᵣ.X ∧ Disjoint Sₗ.Y Sᵣ.Y then
      some
        ⟨
          -- row indicesSₗ.X ∪ Sᵣ.X,
          -- col indicesSₗ.Y ∪ Sᵣ.Y,
          -- row and col indices are disjointunion_disjoint_union Sₗ.hXY Sᵣ.hXY hXY hYX,
          -- standard representation matrix(matrixSum1 Sₗ.B Sᵣ.B).toMatrixUnionUnion,
          -- decidability of row indicesinferInstance,
          -- decidability of col indicesinferInstance⟩
    else none


-- @@ L42-50 expanded
/-- Binary matroid `M` is a result of 1-summing `Mₗ` and `Mᵣ` in some way. -/
def Matroid.IsSum1of (M : Matroid α) (Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
    ∃ hXY : Disjoint Sₗ.X Sᵣ.Y,
      ∃ hYX : Disjoint Sₗ.Y Sᵣ.X,
        standardReprSum1 hXY hYX = some S ∧ S.toMatroid = M ∧ Sₗ.toMatroid = Mₗ ∧ Sᵣ.toMatroid = Mᵣ


-- @@ L53-53 verbatim
/-! ## API -/


-- @@ L55-59 expanded
lemma standardReprSum1_disjoint_X {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hS : standardReprSum1 hXY hYX = some S) : Disjoint Sₗ.X Sᵣ.X :=
  by
  simp [standardReprSum1] at hS
  tauto


-- @@ L61-65 expanded
lemma standardReprSum1_disjoint_Y {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hS : standardReprSum1 hXY hYX = some S) : Disjoint Sₗ.Y Sᵣ.Y :=
  by
  simp [standardReprSum1] at hS
  tauto


-- @@ L67-72 expanded
lemma standardReprSum1_X_eq {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hS : standardReprSum1 hXY hYX = some S) : S.X = Sₗ.X ∪ Sᵣ.X :=
  by
  simp_rw [standardReprSum1, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.X hSSS.symm


-- @@ L74-79 expanded
lemma standardReprSum1_Y_eq {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hS : standardReprSum1 hXY hYX = some S) : S.Y = Sₗ.Y ∪ Sᵣ.Y :=
  by
  simp_rw [standardReprSum1, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.Y hSSS.symm


-- @@ L81-87 verbatim
lemma Matroid.IsSum1of.E_eq {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum1of Mₗ Mᵣ) :
    M.E = Mₗ.E ∪ Mᵣ.E := by
  obtain ⟨S, _, _, _, _, hS, rfl, rfl, rfl⟩ := hMMM
  have hX := standardReprSum1_X_eq hS
  have hY := standardReprSum1_Y_eq hS
  simp only [StandardRepr.toMatroid_E]
  tauto_set


-- @@ L89-93 expanded
lemma standardReprSum1_disjoint_E {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hS : standardReprSum1 hXY hYX = some S) :
    Disjoint Sₗ.toMatroid.E Sᵣ.toMatroid.E := by
  simp
  exact ⟨⟨standardReprSum1_disjoint_X hS, hYX⟩, ⟨hXY, standardReprSum1_disjoint_Y hS⟩⟩


-- @@ L95-98 expanded
lemma Matroid.IsSum1of.disjoint_E {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum1of Mₗ Mᵣ) :
    Disjoint Mₗ.E Mᵣ.E := by
  obtain ⟨S, _, _, _, _, hS, _, rfl, rfl⟩ := hMMM
  exact standardReprSum1_disjoint_E hS


-- @@ L101-101 verbatim
/-! ## Results -/


-- @@ L103-164 expanded
private lemma standardReprSum1_eq_disjointSum_aux_aux_aux {Xₗ Yₗ Xᵣ Yᵣ I : Set α} {R : Type}
    [Ring R] [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)]
    [∀ a, Decidable (a ∈ Yᵣ)] (hSₗ : Disjoint Xₗ Yₗ) (hSᵣ : Disjoint Xᵣ Yᵣ) (hXX : Disjoint Xₗ Xᵣ)
    (hYY : Disjoint Yₗ Yᵣ) (hXY : Disjoint Xₗ Yᵣ) (hYX : Disjoint Yₗ Xᵣ) (Bₗ : Matrix Xₗ Yₗ R)
    (Bᵣ : Matrix Xᵣ Yᵣ R) (hI : I ⊆ (Yₗ ∪ Yᵣ) ∪ (Xₗ ∪ Xᵣ)) (hIₗ : I ∩ (Yₗ ∪ Xₗ) ⊆ Yₗ ∪ Xₗ)
    (hIᵣ : I ∩ (Yᵣ ∪ Xᵣ) ⊆ Yᵣ ∪ Xᵣ) :
    LinearIndepOn R
        ((Matrix.fromRows 1 (Matrix.fromBlocks Bₗ 0 0 Bᵣ).toMatrixUnionUnion) ∘ Subtype.toSum)
        hI.elem.range ↔
      LinearIndepOn R ((Matrix.fromRows 1 Bₗ) ∘ Subtype.toSum) hIₗ.elem.range ∧
        LinearIndepOn R ((Matrix.fromRows 1 Bᵣ) ∘ Subtype.toSum) hIᵣ.elem.range :=
  by
  have hYXYX : Disjoint (Yₗ ∪ Xₗ) (Yᵣ ∪ Xᵣ) := union_disjoint_union_aux hYY hXX hXY hYX
  have hYYXXYXYX : (Yₗ ∪ Yᵣ) ∪ (Xₗ ∪ Xᵣ) = (Yₗ ∪ Xₗ) ∪ (Yᵣ ∪ Xᵣ) :=
    Set.union_union_union_comm Yₗ Yᵣ Xₗ Xᵣ
  rw [←
    linearIndepOn_toMatrixUnionUnion_elem_range_iff (union_disjoint_union_aux hYY hXX hXY hYX) hYY
      ((Matrix.fromRows 1 Bₗ) ∘ Subtype.toSum) ((Matrix.fromRows 1 Bᵣ) ∘ Subtype.toSum)
      (hYYXXYXYX ▸ hI) hIₗ hIᵣ]
  apply linearIndepOn_matrix_elem_range_iff_subst hYYXXYXYX
  show
    _ =
      (Matrix.fromBlocks ((Matrix.fromRows 1 Bₗ) ∘ Subtype.toSum) 0 0
            ((Matrix.fromRows 1 Bᵣ) ∘ Subtype.toSum)).toMatrixElemElem
        hYYXXYXYX rfl
  ext i j
  have hBBij :
    ((Matrix.fromRows 1 (Matrix.fromBlocks Bₗ 0 0 Bᵣ).toMatrixUnionUnion) ∘ Subtype.toSum) i j =
      (Matrix.fromBlocks ((Matrix.fromRows 1 Bₗ) ∘ Subtype.toSum) 0 0
            ((Matrix.fromRows 1 Bᵣ) ∘ Subtype.toSum)).toMatrixUnionUnion
        (hYYXXYXYX ▸ i) j
  ·
    cases hi : i.toSum with
    | inl i₁ =>
      rw [hYY.matrix_one_eq_fromBlocks_toMatrixUnionUnion]
      cases hi₁ : i₁.toSum with
      | inl
        iₗ =>
        have hi' : (hYYXXYXYX ▸ i).toSum = Sum.inl ⟨iₗ, Set.mem_union_left Xₗ iₗ.property⟩
        · have hiₗ : iₗ.val = i.val :=
            (val_eq_val_of_toSum_eq_left hi₁).trans (val_eq_val_of_toSum_eq_left hi)
          have hi' : (hYYXXYXYX ▸ i).val = i.val := i.subst_elem hYYXXYXYX
          have hi'' : i.val ∈ Yₗ ∪ Xₗ := hiₗ ▸ Set.mem_union_left Xₗ iₗ.property
          simp [*]
        cases hj : j.toSum <;> simp [*, Matrix.toMatrixUnionUnion, -Matrix.fromBlocks_one]
      | inr
        iᵣ =>
        have hi' : (hYYXXYXYX ▸ i).toSum = Sum.inr ⟨iᵣ, Set.mem_union_left Xᵣ iᵣ.property⟩
        · have hiᵣ : iᵣ.val = i.val :=
            (val_eq_val_of_toSum_eq_right hi₁).trans (val_eq_val_of_toSum_eq_left hi)
          have hi' : (hYYXXYXYX ▸ i).val = i.val := i.subst_elem hYYXXYXYX
          have hi'' : i.val ∈ Yᵣ ∪ Xᵣ := hiᵣ ▸ Set.mem_union_left Xᵣ iᵣ.property
          have hi_' : i.val ∉ Yₗ ∪ Xₗ := hYXYX.ni_left_of_in_right hi''
          simp [*]
        cases hj : j.toSum <;> simp [*, Matrix.toMatrixUnionUnion, -Matrix.fromBlocks_one]
    | inr i₂ =>
      cases hi₂ : i₂.toSum with
      | inl
        iₗ =>
        have hi' : (hYYXXYXYX ▸ i).toSum = Sum.inl ⟨iₗ, Set.mem_union_right Yₗ iₗ.property⟩
        · have hiₗ : iₗ.val = i.val :=
            (val_eq_val_of_toSum_eq_left hi₂).trans (val_eq_val_of_toSum_eq_right hi)
          have hi' : (hYYXXYXYX ▸ i).val = i.val := i.subst_elem hYYXXYXYX
          have hi'' : i.val ∈ Yₗ ∪ Xₗ := hiₗ ▸ Set.mem_union_right Yₗ iₗ.property
          simp [*]
        have hiₗ : iₗ.val ∉ Yₗ := hSₗ.ni_right_of_in_left iₗ.property
        cases hj : j.toSum <;> simp [*, Matrix.toMatrixUnionUnion]
      | inr
        iᵣ =>
        have hi' : (hYYXXYXYX ▸ i).toSum = Sum.inr ⟨iᵣ, Set.mem_union_right Yᵣ iᵣ.property⟩
        · have hiᵣ : iᵣ.val = i.val :=
            (val_eq_val_of_toSum_eq_right hi₂).trans (val_eq_val_of_toSum_eq_right hi)
          have hi' : (hYYXXYXYX ▸ i).val = i.val := i.subst_elem hYYXXYXYX
          have hi'' : i.val ∈ Yᵣ ∪ Xᵣ := hiᵣ ▸ Set.mem_union_right Yᵣ iᵣ.property
          have hi_' : i.val ∉ Yₗ ∪ Xₗ := hYXYX.ni_left_of_in_right hi''
          simp [*]
        have hiᵣ : iᵣ.val ∉ Yᵣ := hSᵣ.ni_right_of_in_left iᵣ.property
        cases hj : j.toSum <;> simp [*, Matrix.toMatrixUnionUnion]
  rewrite [hBBij, Matrix.toMatrixElemElem_apply]
  rfl


-- @@ L166-176 expanded
private lemma standardReprSum1_eq_disjointSum_aux_aux {Xₗ Yₗ Xᵣ Yᵣ I : Set α} {R : Type} [Ring R]
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)]
    [∀ a, Decidable (a ∈ Yᵣ)] (hSₗ : Disjoint Xₗ Yₗ) (hSᵣ : Disjoint Xᵣ Yᵣ) (hXX : Disjoint Xₗ Xᵣ)
    (hYY : Disjoint Yₗ Yᵣ) (hXY : Disjoint Xₗ Yᵣ) (hYX : Disjoint Yₗ Xᵣ) (Bₗ : Matrix Xₗ Yₗ R)
    (Bᵣ : Matrix Xᵣ Yᵣ R) (hI : I ⊆ (Xₗ ∪ Xᵣ) ∪ (Yₗ ∪ Yᵣ)) (hIₗ : I ∩ (Xₗ ∪ Yₗ) ⊆ Xₗ ∪ Yₗ)
    (hIᵣ : I ∩ (Xᵣ ∪ Yᵣ) ⊆ Xᵣ ∪ Yᵣ) :
    LinearIndepOn R
        ((Matrix.fromRows 1 (Matrix.fromBlocks Bₗ 0 0 Bᵣ).toMatrixUnionUnion.transpose) ∘
          Subtype.toSum)
        hI.elem.range ↔
      LinearIndepOn R ((Matrix.fromRows 1 Bₗ.transpose) ∘ Subtype.toSum) hIₗ.elem.range ∧
        LinearIndepOn R ((Matrix.fromRows 1 Bᵣ.transpose) ∘ Subtype.toSum) hIᵣ.elem.range :=
  (Matrix.fromBlocks Bₗ 0 0 Bᵣ).toMatrixUnionUnion_transpose ▸
    Matrix.fromBlocks_transpose .. ▸
      standardReprSum1_eq_disjointSum_aux_aux_aux hSₗ.symm hSᵣ.symm hYY hXX hYX hXY Bₗ.transpose
        Bᵣ.transpose hI hIₗ hIᵣ


-- @@ L178-189 expanded
private lemma standardReprSum1_eq_disjointSum_aux {Xₗ Yₗ Xᵣ Yᵣ X Y I : Set α} {R : Type} [Ring R]
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)]
    [∀ a, Decidable (a ∈ Yᵣ)] (hSₗ : Disjoint Xₗ Yₗ) (hSᵣ : Disjoint Xᵣ Yᵣ) (hXX : Disjoint Xₗ Xᵣ)
    (hYY : Disjoint Yₗ Yᵣ) (hXY : Disjoint Xₗ Yᵣ) (hYX : Disjoint Yₗ Xᵣ) (hXXX : X = Xₗ ∪ Xᵣ)
    (hYYY : Y = Yₗ ∪ Yᵣ) (Bₗ : Matrix Xₗ Yₗ R) (Bᵣ : Matrix Xᵣ Yᵣ R) (hI : I ⊆ X ∪ Y)
    (hIₗ : I ∩ (Xₗ ∪ Yₗ) ⊆ Xₗ ∪ Yₗ) (hIᵣ : I ∩ (Xᵣ ∪ Yᵣ) ⊆ Xᵣ ∪ Yᵣ) :
    have : ∀ a : α, Decidable (a ∈ X) := hXXX ▸ (Set.decidableUnion Xₗ Xᵣ ·)
    have : ∀ a : α, Decidable (a ∈ Y) := hYYY ▸ (Set.decidableUnion Yₗ Yᵣ ·)
    LinearIndepOn R
        ((Matrix.fromRows 1 ((Matrix.fromBlocks Bₗ 0 0 Bᵣ).toMatrixElemElem hXXX hYYY).transpose) ∘
          Subtype.toSum)
        hI.elem.range ↔
      LinearIndepOn R ((Matrix.fromRows 1 Bₗ.transpose) ∘ Subtype.toSum) hIₗ.elem.range ∧
        LinearIndepOn R ((Matrix.fromRows 1 Bᵣ.transpose) ∘ Subtype.toSum) hIᵣ.elem.range :=
  by
  subst hXXX hYYY
  convert standardReprSum1_eq_disjointSum_aux_aux hSₗ hSᵣ hXX hYY hXY hYX Bₗ Bᵣ hI hIₗ hIᵣ


-- @@ L191-206 expanded
lemma standardReprSum1_eq_disjointSum {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hS : standardReprSum1 hXY hYX = some S) :
    S.toMatroid = (standardReprSum1_disjoint_E hS).matroidSum :=
  by
  have hXXX := standardReprSum1_X_eq hS
  have hYYY := standardReprSum1_Y_eq hS
  simp only [standardReprSum1, Option.ite_none_right_eq_some] at hS
  ext I hIS
  · aesop
  · rw [Matroid.disjointSum_indep_iff]
    have hIEE : I ⊆ Sₗ.toMatroid.E ∪ Sᵣ.toMatroid.E
    · simpa [hXXX, hYYY, Set.union_comm, Set.union_left_comm] using hIS
    have hB : S.B = (Matrix.fromBlocks Sₗ.B 0 0 Sᵣ.B).toMatrixElemElem hXXX hYYY
    · aesop
    simp_rw [hIEE]
    simp [show I ⊆ S.X ∪ S.Y from hIS]
    convert
      standardReprSum1_eq_disjointSum_aux Sₗ.hXY Sᵣ.hXY hS.left.left hS.left.right hXY hYX hXXX hYYY
        Sₗ.B Sᵣ.B hIS _ _


-- @@ L208-212 verbatim
/-- The 1-sum of matroids is a disjoint sum of those matroids. -/
theorem Matroid.IsSum1of.eq_disjointSum {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum1of Mₗ Mᵣ) :
    M = hMMM.disjoint_E.matroidSum := by
  obtain ⟨S, _, _, _, _, hS, rfl, rfl, rfl⟩ := hMMM
  exact standardReprSum1_eq_disjointSum hS


-- @@ L214-231 expanded
lemma standardReprSum1_hasTuSigning {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Disjoint Sₗ.X Sᵣ.Y}
    {hYX : Disjoint Sₗ.Y Sᵣ.X} (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning)
    (hS : standardReprSum1 hXY hYX = some S) : S.B.HasTuSigning :=
  by
  have ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  have ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  have hSX : S.X = Sₗ.X ∪ Sᵣ.X := standardReprSum1_X_eq hS
  have hSY : S.Y = Sₗ.Y ∪ Sᵣ.Y := standardReprSum1_Y_eq hS
  have hSB : S.B = (matrixSum1 Sₗ.B Sᵣ.B).toMatrixElemElem hSX hSY
  · simp_rw [standardReprSum1, Option.ite_none_right_eq_some] at hS
    aesop
  use (matrixSum1 Bₗ Bᵣ).toMatrixElemElem hSX hSY,
    (Matrix.fromBlocks_isTotallyUnimodular hBₗ hBᵣ).toMatrixElemElem hSX hSY
  rw [hSB]
  intro i j
  simp only [Matrix.toMatrixElemElem_apply]
  exact
    (hSX ▸ i).toSum.casesOn (fun iₗ : Sₗ.X => (hSY ▸ j).toSum.casesOn (hBBₗ iₗ) (fun _ => abs_zero))
      (fun iᵣ : Sᵣ.X => (hSY ▸ j).toSum.casesOn (fun _ => abs_zero) (hBBᵣ iᵣ))


-- @@ L233-243 verbatim
/-- Any 1-sum of regular matroids is a regular matroid.
    This is part one (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsSum1of.isRegular {M Mₗ Mᵣ : Matroid α}
    (hMMM : M.IsSum1of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨S, Sₗ, Sᵣ, _, _, hSSS, rfl, rfl, rfl⟩ := hMMM
  have hX : Finite S.X := S.finite_X_of_toMatroid_rankFinite hM
  obtain ⟨hXₗ, hXᵣ⟩ : Finite Sₗ.X ∧ Finite Sᵣ.X
  · simpa [standardReprSum1_X_eq hSSS, Set.finite_coe_iff] using hX
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum1_hasTuSigning hMₗ hMᵣ hSSS
