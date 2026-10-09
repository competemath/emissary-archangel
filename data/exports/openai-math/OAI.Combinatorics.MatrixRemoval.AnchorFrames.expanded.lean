import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-8 verbatim
/-!
Full row and column orders extending the variable order.
The raw carrier is the anchor / variable / dummy sum.
-/


-- @@ L10-10 verbatim
universe uM uV uO


-- @@ L12-12 verbatim
namespace Problem348.AnchorFrames


-- @@ L14-14 verbatim
abbrev Raw (M : Type uM) (V : Type uV) (O : Type uO) := (M × Fin 64 × O) ⊕ (V ⊕ O)

-- @@ L15-15 verbatim
abbrev AnchorOrder (M : Type uM) (O : Type uO) := M ×ₗ Fin 64 ×ₗ O

-- @@ L16-16 verbatim
abbrev RowOrder (M : Type uM) (V : Type uV) (O : Type uO) := AnchorOrder M O ⊕ₗ (V ⊕ₗ O)

-- @@ L17-17 verbatim
abbrev ColOrder (M : Type uM) (V : Type uV) (O : Type uO) := AnchorOrder M O ⊕ₗ (O ⊕ₗ V)


-- @@ L19-23 verbatim
/-- Coordinates for the row order: anchors, variables, dummy. -/
def rowKey {M : Type uM} {V : Type uV} {O : Type uO} : Raw M V O → RowOrder M V O
  | .inl (t, u, x) => .inlₗ (toLex (t, toLex (u, x)))
  | .inr (.inl v) => .inrₗ (.inlₗ v)
  | .inr (.inr x) => .inrₗ (.inrₗ x)


-- @@ L25-29 verbatim
/-- Coordinates for the column order: anchors, dummy, variables. -/
def colKey {M : Type uM} {V : Type uV} {O : Type uO} : Raw M V O → ColOrder M V O
  | .inl (t, u, x) => .inlₗ (toLex (t, toLex (u, x)))
  | .inr (.inl v) => .inrₗ (.inrₗ v)
  | .inr (.inr x) => .inrₗ (.inlₗ x)


-- @@ L31-37 verbatim
def rowEquiv (M : Type uM) (V : Type uV) (O : Type uO) : Raw M V O ≃ RowOrder M V O where
  toFun := rowKey
  invFun x := match ofLex x with
    | .inl a => .inl ((ofLex a).1, (ofLex (ofLex a).2).1, (ofLex (ofLex a).2).2)
    | .inr b => .inr (ofLex b)
  left_inv := by rintro (⟨t,u,x⟩ | (v | x)) <;> rfl
  right_inv := by rintro (⟨t,u,x⟩ | (v | x)) <;> rfl


-- @@ L39-47 verbatim
def colEquiv (M : Type uM) (V : Type uV) (O : Type uO) : Raw M V O ≃ ColOrder M V O where
  toFun := colKey
  invFun x := match ofLex x with
    | .inl a => .inl ((ofLex a).1, (ofLex (ofLex a).2).1, (ofLex (ofLex a).2).2)
    | .inr b => match ofLex b with
      | .inl x => .inr (.inr x)
      | .inr v => .inr (.inl v)
  left_inv := by rintro (⟨t,u,x⟩ | (v | x)) <;> rfl
  right_inv := by rintro (⟨t,u,x⟩ | (x | v)) <;> rfl


-- @@ L49-49 verbatim
section Orders

-- @@ L50-50 verbatim
variable {M : Type uM} {V : Type uV} {O : Type uO} [LinearOrder M] [LinearOrder V] [LinearOrder O]


-- @@ L52-53 verbatim
/-- The full raw row order, suitable for local instance installation. -/
abbrev rowOrder : LinearOrder (Raw M V O) := LinearOrder.lift' rowKey (rowEquiv M V O).injective


-- @@ L55-56 verbatim
/-- The full raw column order, suitable for local instance installation. -/
abbrev colOrder : LinearOrder (Raw M V O) := LinearOrder.lift' colKey (colEquiv M V O).injective


-- @@ L58-65 verbatim
/-- Arbitrary offsets in successive groups give increasing selected anchors. -/
theorem row_anchor_strictMono (t : M) (a : Fin 64 → O) :
    StrictMono (fun u => rowKey (M := M) (V := V) (.inl (t, u, a u))) := by
  intro u v huv
  change Sum.Lex _ _ _ _
  apply Sum.Lex.inl
  apply Prod.Lex.right
  exact Prod.Lex.left _ _ huv


-- @@ L67-73 verbatim
theorem col_anchor_strictMono (t : M) (a : Fin 64 → O) :
    StrictMono (fun u => colKey (M := M) (V := V) (.inl (t, u, a u))) := by
  intro u v huv
  change Sum.Lex _ _ _ _
  apply Sum.Lex.inl
  apply Prod.Lex.right
  exact Prod.Lex.left _ _ huv


-- @@ L75-77 verbatim
theorem row_anchor_lt_nonanchor (t : M) (u : Fin 64) (a : O) (x : V ⊕ O) :
    rowKey (.inl (t,u,a)) < rowKey (.inr x) := by
  cases x <;> exact Sum.Lex.sep _ _


-- @@ L79-81 verbatim
theorem col_anchor_lt_nonanchor (t : M) (u : Fin 64) (a : O) (x : V ⊕ O) :
    colKey (.inl (t,u,a)) < colKey (.inr x) := by
  cases x <;> exact Sum.Lex.sep _ _


-- @@ L83-85 verbatim
theorem row_variable_lt_dummy (v : V) (x : O) :
    rowKey (M := M) (.inr (.inl v)) < rowKey (.inr (.inr x)) :=
  Sum.Lex.inr (Sum.Lex.sep _ _)


-- @@ L87-89 verbatim
theorem col_dummy_lt_variable (v : V) (x : O) :
    colKey (M := M) (.inr (.inr x)) < colKey (.inr (.inl v)) :=
  Sum.Lex.inr (Sum.Lex.sep _ _)


-- @@ L91-93 verbatim
@[simp] theorem row_variable_lt_variable (v w : V) :
    rowKey (M := M) (O := O) (.inr (.inl v)) < rowKey (.inr (.inl w)) ↔ v < w := by
  simp [rowKey]


-- @@ L95-97 verbatim
@[simp] theorem col_variable_lt_variable (v w : V) :
    colKey (M := M) (O := O) (.inr (.inl v)) < colKey (.inr (.inl w)) ↔ v < w := by
  simp [colKey]


-- @@ L99-102 verbatim
/-- The anchor region is an initial segment of the complete row axis. -/
theorem row_not_nonanchor_lt_anchor (t : M) (u : Fin 64) (a : O) (x : V ⊕ O) :
    ¬ rowKey (.inr x) < rowKey (.inl (t,u,a)) :=
  not_lt_of_gt (row_anchor_lt_nonanchor t u a x)


-- @@ L104-107 verbatim
/-- The anchor region is also an initial segment of the complete column axis. -/
theorem col_not_nonanchor_lt_anchor (t : M) (u : Fin 64) (a : O) (x : V ⊕ O) :
    ¬ colKey (.inr x) < colKey (.inl (t,u,a)) :=
  not_lt_of_gt (col_anchor_lt_nonanchor t u a x)


-- @@ L109-114 verbatim
/-- Within one mode, increasing selected anchors have nondecreasing group labels. -/
theorem row_group_le_of_lt (t : M) (u v : Fin 64) (a b : O)
    (hab : rowKey (V := V) (.inl (t,u,a)) < rowKey (.inl (t,v,b))) : u ≤ v := by
  have h : toLex (u,a) < toLex (v,b) := by
    simpa [rowKey, Prod.Lex.lt_iff] using hab
  exact (Prod.Lex.monotone_fst_ofLex h.le)


-- @@ L116-120 verbatim
theorem col_group_le_of_lt (t : M) (u v : Fin 64) (a b : O)
    (hab : colKey (V := V) (.inl (t,u,a)) < colKey (.inl (t,v,b))) : u ≤ v := by
  have h : toLex (u,a) < toLex (v,b) := by
    simpa [colKey, Prod.Lex.lt_iff] using hab
  exact (Prod.Lex.monotone_fst_ofLex h.le)


-- @@ L122-125 verbatim
/-- Selected anchor rows after the full axis has been enumerated by `Fin n`. -/
def selectedRows {n : ℕ} (e : Fin n ≃o RowOrder M V O)
    (t : M) (a : Fin 64 → O) : Fin 64 → Fin n :=
  fun u => e.symm (rowKey (.inl (t, u, a u)))


-- @@ L127-130 verbatim
/-- Selected anchor columns after the full axis has been enumerated by `Fin n`. -/
def selectedCols {n : ℕ} (e : Fin n ≃o ColOrder M V O)
    (t : M) (a : Fin 64 → O) : Fin 64 → Fin n :=
  fun u => e.symm (colKey (.inl (t, u, a u)))


-- @@ L132-134 verbatim
theorem selectedRows_strictMono {n : ℕ} (e : Fin n ≃o RowOrder M V O)
    (t : M) (a : Fin 64 → O) : StrictMono (selectedRows e t a) :=
  e.symm.strictMono.comp (row_anchor_strictMono t a)


-- @@ L136-138 verbatim
theorem selectedCols_strictMono {n : ℕ} (e : Fin n ≃o ColOrder M V O)
    (t : M) (a : Fin 64 → O) : StrictMono (selectedCols e t a) :=
  e.symm.strictMono.comp (col_anchor_strictMono t a)


-- @@ L140-143 verbatim
theorem selectedRows_lt_nonanchor {n : ℕ} (e : Fin n ≃o RowOrder M V O)
    (t : M) (a : Fin 64 → O) (u : Fin 64) (x : V ⊕ O) :
    selectedRows e t a u < e.symm (rowKey (.inr x)) :=
  e.symm.strictMono (row_anchor_lt_nonanchor t u (a u) x)


-- @@ L145-148 verbatim
theorem selectedCols_lt_nonanchor {n : ℕ} (e : Fin n ≃o ColOrder M V O)
    (t : M) (a : Fin 64 → O) (u : Fin 64) (x : V ⊕ O) :
    selectedCols e t a u < e.symm (colKey (.inr x)) :=
  e.symm.strictMono (col_anchor_lt_nonanchor t u (a u) x)


-- @@ L150-150 verbatim
end Orders

-- @@ L151-151 verbatim
end Problem348.AnchorFrames


-- @@ L153-153 verbatim
end OAI
