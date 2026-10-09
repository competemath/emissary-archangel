import OAI.RepresentationTheory.Saxl.PathContraction


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped TensorProduct


-- @@ L9-10 verbatim
namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/

-- @@ L11-13 verbatim
@[reducible] def Cells : List ℕ → Type
  | [] => Empty
  | r :: rs => Fin r ⊕ Cells rs


-- @@ L15-17 verbatim
instance cellsFintype : (rs : List ℕ) → Fintype (Cells rs)
  | [] => inferInstanceAs (Fintype Empty)
  | r :: rs => @instFintypeSum (Fin r) (Cells rs) inferInstance (cellsFintype rs)


-- @@ L19-21 verbatim
instance cellsDecEq : (rs : List ℕ) → DecidableEq (Cells rs)
  | [] => inferInstanceAs (DecidableEq Empty)
  | r :: rs => @instDecidableEqSum (Fin r) (Cells rs) inferInstance (cellsDecEq rs)


-- @@ L23-25 verbatim
def row : {rs : List ℕ} → Cells rs → ℕ
  | _ :: _, .inl i => i.val
  | _ :: _, .inr c => row c


-- @@ L27-29 verbatim
def col : {rs : List ℕ} → Cells rs → ℕ
  | _ :: _, .inl _ => 0
  | _ :: _, .inr c => col c + 1


-- @@ L31-33 verbatim
def enumerate : (rs : List ℕ) → Fin rs.sum ≃ Cells rs
  | [] => (Equiv.equivOfIsEmpty (Fin 0) Empty)
  | r :: rs => finSumFinEquiv.symm.trans ((Equiv.refl (Fin r)).sumCongr (enumerate rs))


-- @@ L35-38 verbatim
@[simp] lemma enumerate_left (r : ℕ) (rs : List ℕ) (i : Fin r) :
    enumerate (r :: rs) (Fin.castAdd rs.sum i) = Sum.inl i := by
  exact congrArg ((Equiv.refl (Fin r)).sumCongr (enumerate rs))
    (finSumFinEquiv_symm_apply_castAdd i)


-- @@ L40-43 verbatim
@[simp] lemma enumerate_right (r : ℕ) (rs : List ℕ) (i : Fin rs.sum) :
    enumerate (r :: rs) (Fin.natAdd r i) = Sum.inr (enumerate rs i) := by
  exact congrArg ((Equiv.refl (Fin r)).sumCongr (enumerate rs))
    (finSumFinEquiv_symm_apply_natAdd i)


-- @@ L45-47 verbatim
@[reducible] def Perms : List ℕ → Type
  | [] => Unit
  | r :: rs => Equiv.Perm (Fin r) × Perms rs


-- @@ L49-51 verbatim
instance permsFintype : (rs : List ℕ) → Fintype (Perms rs)
  | [] => inferInstanceAs (Fintype Unit)
  | r :: rs => @instFintypeProd (Equiv.Perm (Fin r)) (Perms rs) inferInstance (permsFintype rs)


-- @@ L53-55 verbatim
def perm : {rs : List ℕ} → Perms rs → Equiv.Perm (Cells rs)
  | [], _ => Equiv.refl _
  | _ :: _, (π, σ) => Equiv.sumCongr π (perm σ)


-- @@ L57-59 verbatim
def sg : {rs : List ℕ} → Perms rs → ℂ
  | [], _ => 1
  | _ :: _, (π, σ) => (((Equiv.Perm.sign π : ℤ) : ℂ)) * sg σ


-- @@ L61-69 verbatim
lemma sign_perm {rs : List ℕ} (π : Perms rs) :
    (((Equiv.Perm.sign (perm π) : ℤ) : ℂ)) = sg π := by
  induction rs with
  | nil => simp [perm, sg]
  | cons r rs ih =>
    obtain ⟨π, σ⟩ := π
    have hh := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ))
      (Equiv.Perm.sign_sumCongr π (perm σ))
    exact hh.trans (by simp only [Units.val_mul, Int.cast_mul, ih]; rfl)


-- @@ L71-78 verbatim
lemma perm_col {rs : List ℕ} (π : Perms rs) (c : Cells rs) : col (perm π c) = col c := by
  induction rs with
  | nil => exact isEmptyElim c
  | cons r rs ih =>
    obtain ⟨π, σ⟩ := π
    cases c with
    | inl i => rfl
    | inr c => exact congrArg (· + 1) (ih σ c)


-- @@ L80-100 verbatim
lemma coords_injective (rs : List ℕ) :
    Function.Injective (fun c : Cells rs => (row c, col c)) := by
  induction rs with
  | nil => exact Function.injective_of_subsingleton _
  | cons r rs ih =>
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext (congrArg Prod.fst h))
      | inr b => have := congrArg Prod.snd h; simp [col] at this
    | inr a =>
      cases b with
      | inl b => have := congrArg Prod.snd h; simp [col] at this
      | inr b =>
        apply congrArg Sum.inr
        apply ih
        dsimp only [row, col] at h
        have hr := congrArg Prod.fst h
        have hc := congrArg Prod.snd h
        exact Prod.ext hr (Nat.add_right_cancel hc)


-- @@ L102-129 verbatim
lemma coords_range (rs : List ℕ) (i j : ℕ) :
    (∃ c : Cells rs, row c = i ∧ col c = j) ↔ ∃ h : j < rs.length, i < rs[j] := by
  induction rs generalizing j with
  | nil => simp [Cells]
  | cons r rs ih =>
    cases j with
    | zero =>
      constructor
      · rintro ⟨c, hr, hc⟩
        cases c with
        | inl a => exact ⟨by simp, by simpa [row] using hr ▸ a.isLt⟩
        | inr a => simp [col] at hc
      · rintro ⟨h, hi⟩
        exact ⟨Sum.inl ⟨i, hi⟩, rfl, rfl⟩
    | succ j =>
      constructor
      · rintro ⟨c, hr, hc⟩
        cases c with
        | inl a => simp [col] at hc
        | inr a =>
          have hj : col a = j := Nat.add_right_cancel hc
          obtain ⟨hj, hi⟩ := (ih j).mp ⟨a, hr, hj⟩
          exact ⟨Nat.succ_lt_succ hj, hi⟩
      · rintro ⟨h, hi⟩
        obtain ⟨a, ha, hc⟩ := (ih j).mpr ⟨Nat.lt_of_succ_lt_succ h, hi⟩
        exact ⟨Sum.inr a, ha, congrArg (· + 1) hc⟩

/- The matrix product indexed by the actual consecutive position order. -/

-- @@ L130-131 verbatim
def chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) (π : Perms rs) : Band.Mat :=
  (List.ofFn fun q : Fin rs.sum => Band.D (p + q.val) (N (row (perm π (enumerate rs q))))).prod


-- @@ L133-152 verbatim
lemma chain_cons (r : ℕ) (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat)
    (π : Equiv.Perm (Fin r)) (σ : Perms rs) :
    chain (r :: rs) p N (π, σ) =
      (List.ofFn fun j : Fin r => Band.D (p + j.val) (N (π j).val)).prod *
      chain rs (p + r) N σ := by
  unfold chain
  erw [List.ofFn_add, List.prod_append]
  congr 2
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + j.val) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.castAdd rs.sum j))))) = _
    rw [enumerate_left]
    rfl
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + (r + j.val)) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.natAdd r j))))) = _
    erw [enumerate_right r rs (show Fin rs.sum from j)]
    simp only [perm, Equiv.sumCongr_apply, Sum.map_inr, row, Nat.add_assoc]

/- Ordered product of independent alternating column segments. -/

-- @@ L153-160 verbatim
def segments : ℕ → List ℕ → (ℕ → Band.Mat) → Band.Mat
  | _, [], _ => 1
  | p, r :: rs, N =>
      (∑ π : Equiv.Perm (Fin r), (((Equiv.Perm.sign π : ℤ) : ℂ)) •
        (List.ofFn fun i : Fin r => Band.D (p + i.val) (N (π i).val)).prod) *
      segments (p+r) rs N

/- Factorization over independent column permutations, without commuting factors. -/

-- @@ L161-167 verbatim
lemma sum_chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) :
    (∑ π : Perms rs, sg π • chain rs p N π) = segments p rs N := by
  induction rs generalizing p with
  | nil => simp [Perms, chain, sg, segments]
  | cons r rs ih =>
    simp only [Perms, Fintype.sum_prod_type, sg, chain_cons, segments]
    simp_rw [← smul_mul_smul_comm, ← Finset.mul_sum, ← Finset.sum_mul, ih]


-- @@ L169-181 verbatim
lemma perm_injective (rs : List ℕ) : Function.Injective (@perm rs) := by
  induction rs with
  | nil => exact Function.injective_of_subsingleton _
  | cons r rs ih =>
    rintro ⟨π, σ⟩ ⟨π', σ'⟩ h
    apply Prod.ext
    · apply Equiv.ext
      intro i
      exact Sum.inl.inj (Equiv.congr_fun h (Sum.inl i))
    · apply ih
      apply Equiv.ext
      intro c
      exact Sum.inr.inj (Equiv.congr_fun h (Sum.inr c))


-- @@ L183-203 verbatim
lemma perm_surjective (rs : List ℕ) (g : Equiv.Perm (Cells rs))
    (hg : ∀ c, col (g c) = col c) : ∃ π : Perms rs, perm π = g := by
  induction rs with
  | nil => exact ⟨(), Subsingleton.elim _ _⟩
  | cons r rs ih =>
    have hm : Set.MapsTo g (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro c ⟨i, rfl⟩
      have hh := hg (Sum.inl i)
      cases h : g (Sum.inl i) with
      | inl j => exact ⟨j, rfl⟩
      | inr c => simp [h, col] at hh
    obtain ⟨⟨π, σ⟩, he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm
    have hs : ∀ c : Cells rs, col (σ c) = col c := by
      intro c
      have hh := hg (Sum.inr c)
      rw [← he] at hh
      exact Nat.add_right_cancel hh
    obtain ⟨τ, hτ⟩ := ih σ hs
    exact ⟨(π, τ), by simp only [perm, hτ]; exact he⟩

/- The column-recursive coordinates enumerate the actual Ferrers cells. -/

-- @@ L204-218 verbatim
def toYoung (μ : YoungDiagram) : Cells μ.transpose.rowLens ≃ μ.cells := by
  let f : Cells μ.transpose.rowLens → μ.cells := fun c =>
    ⟨(row c, col c), by
      obtain ⟨hj, hi⟩ := (coords_range μ.transpose.rowLens (row c) (col c)).mp ⟨c, rfl, rfl⟩
      simpa only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen,
        YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose] using hi⟩
  exact Equiv.ofBijective f ⟨fun _ _ h => coords_injective _ (congrArg Subtype.val h), by
    intro c
    have hmem : c.val.1 < μ.colLen c.val.2 := YoungDiagram.mem_iff_lt_colLen.mp c.property
    have hj : c.val.2 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
      (μ.up_left_mem (Nat.zero_le _) le_rfl c.property)
    have hj' : c.val.2 < μ.transpose.rowLens.length := by simpa using hj
    obtain ⟨a, ha, hb⟩ := (coords_range μ.transpose.rowLens c.val.1 c.val.2).mpr
      ⟨hj', by simpa using hmem⟩
    exact ⟨a, Subtype.ext (Prod.ext ha hb)⟩⟩


-- @@ L220-221 verbatim
@[simp] lemma toYoung_val (μ : YoungDiagram) (c : Cells μ.transpose.rowLens) :
    (toYoung μ c).val = (row c, col c) := rfl


-- @@ L223-225 verbatim
lemma row_lt (μ : YoungDiagram) (c : Cells μ.transpose.rowLens) : row c < μ.colLen 0 :=
  YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (Nat.zero_le _) (toYoung μ c).property)



-- @@ L228-229 verbatim
def columnTableau (μ : YoungDiagram) : Tableau μ.transpose.rowLens.sum μ :=
  (enumerate μ.transpose.rowLens).trans (toYoung μ)


-- @@ L231-233 verbatim
@[simp] lemma columnTableau_val (μ : YoungDiagram) (i : Fin μ.transpose.rowLens.sum) :
    (columnTableau μ i).val = (row (enumerate μ.transpose.rowLens i),
      col (enumerate μ.transpose.rowLens i)) := rfl


-- @@ L235-241 verbatim
def columnPerm (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    columnGroup (columnTableau μ) :=
  ⟨(enumerate μ.transpose.rowLens).symm.permCongr (perm π), by
    intro i
    simp only [columnTableau_val, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
    exact perm_col π _⟩


-- @@ L243-261 verbatim
lemma columnPerm_bijective (μ : YoungDiagram) : Function.Bijective (columnPerm μ) := by
  constructor
  · intro π σ h
    apply perm_injective μ.transpose.rowLens
    apply (enumerate μ.transpose.rowLens).symm.permCongr.injective
    exact congrArg Subtype.val h
  · intro g
    let e := enumerate μ.transpose.rowLens
    obtain ⟨π, hπ⟩ := perm_surjective μ.transpose.rowLens (e.permCongr g.val) (by
      intro c
      have hh := g.property (e.symm c)
      simpa only [columnTableau_val, Equiv.permCongr_apply, e, Equiv.apply_symm_apply] using hh)
    refine ⟨π, ?_⟩
    apply Subtype.ext
    change e.symm.permCongr (perm π) = g.val
    rw [hπ]
    apply Equiv.ext
    intro i
    simp [Equiv.permCongr_apply]


-- @@ L263-264 verbatim
def columnEquiv (μ : YoungDiagram) : Perms μ.transpose.rowLens ≃ columnGroup (columnTableau μ) :=
  Equiv.ofBijective (columnPerm μ) (columnPerm_bijective μ)


-- @@ L266-270 verbatim
lemma columnPerm_sign (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    signC (columnPerm μ π).val = sg π := by
  change (((Equiv.Perm.sign ((enumerate μ.transpose.rowLens).symm.permCongr (perm π)) : ℤ) : ℂ)) = sg π
  rw [Equiv.Perm.sign_permCongr]
  exact sign_perm π


-- @@ L272-304 verbatim
lemma mapped_columnTableau (μ : YoungDiagram) (N : ℕ → Band.Mat) :
    wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
      N i.val (Path.parts a).1 (Path.parts a).2) (polytabloid (columnTableau μ)) =
    ∑ π : Perms μ.transpose.rowLens, sg π • Path.pureWord
      (fun q => N (row (perm π (enumerate μ.transpose.rowLens q)))) := by
  classical
  let := Fintype.ofFinite (columnGroup (columnTableau μ))
  unfold polytabloid
  rw [map_sum]
  let e : Perms μ.transpose.rowLens ≃ columnGroup (columnTableau μ) :=
    (columnEquiv μ).trans (Equiv.inv _)
  symm
  apply Fintype.sum_equiv e
  intro π
  rw [map_smul, wordRep_single]
  have hs : signC (e π).val = sg π := by
    change signC (columnPerm μ π).val⁻¹ = sg π
    rw [signC_inv, columnPerm_sign]
  change sg π • _ = signC (e π).val • _
  rw [hs]
  congr 1
  funext w
  rw [wordMap_single]
  unfold Path.pureWord
  apply Finset.prod_congr rfl
  intro q hq
  have hr : row (perm π (enumerate μ.transpose.rowLens q)) =
      ((columnTableau μ) ((e π).val⁻¹ q)).val.1 := by
    change _ = ((columnTableau μ) (((columnPerm μ π).val⁻¹)⁻¹ q)).val.1
    rw [inv_inv, columnTableau_val]
    dsimp only [columnPerm, Equiv.permCongr_apply]
    rw [Equiv.apply_symm_apply, Equiv.symm_symm]
  exact congrArg (fun j => N j (Path.parts (w q)).1 (Path.parts (w q)).2) hr


-- @@ L306-306 verbatim
end Saxl.Columns


-- @@ L308-308 verbatim
end


-- @@ L310-310 verbatim
end OAI
