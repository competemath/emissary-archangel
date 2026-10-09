import OAI.Combinatorics.MatrixRemoval.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Problem348


-- @@ L7-14 verbatim
/-- The anchor is off-diagonal one outside its modified bit rectangle. -/
theorem anchor64_eq_decide_ne (u v : Fin 64)
    (h : u.val < 32 ∨ v.val < 59) :
    anchor64 u v = decide (u.val ≠ v.val) := by
  unfold anchor64
  split_ifs with hmod
  · rcases h with h | h <;> omega
  · rfl


-- @@ L16-20 verbatim
/-- In the dense prefix, every column has at most one zero. -/
theorem anchor64_first32_zero_iff (u v : Fin 64) (hu : u.val < 32) :
    anchor64 u v = false ↔ u = v := by
  rw [anchor64_eq_decide_ne u v (Or.inl hu)]
  simp [Fin.ext_iff]


-- @@ L22-26 verbatim
/-- In the dense prefix, every row has at most one zero. -/
theorem anchor64_first32_column_zero_iff (u v : Fin 64) (hv : v.val < 32) :
    anchor64 u v = false ↔ u = v := by
  rw [anchor64_eq_decide_ne u v (Or.inr (by omega))]
  simp [Fin.ext_iff]


-- @@ L28-31 verbatim
/-- Every anchor row contains at least 58 ones. -/
theorem anchor64_row_ones : ∀ u : Fin 64,
    58 ≤ (Finset.univ.filter (fun v => anchor64 u v = true)).card := by
  decide


-- @@ L33-36 verbatim
/-- Every anchor column contains at least 48 ones. -/
theorem anchor64_column_ones : ∀ v : Fin 64,
    48 ≤ (Finset.univ.filter (fun u => anchor64 u v = true)).card := by
  decide


-- @@ L38-39 verbatim
/-- The five bit-coordinate columns of the anchor. -/
def anchorLastCol (b : Fin 5) : Fin 64 := ⟨b.val + 59, by omega⟩


-- @@ L41-60 verbatim
/-- Distinct rows have distinct complete anchor words. -/
theorem anchor64_rows_injective : Function.Injective anchor64 := by
  intro u v huv
  by_cases hu : u.val < 59
  · have h := congrFun huv u
    rw [anchor64_eq_decide_ne u u (Or.inr hu),
      anchor64_eq_decide_ne v u (Or.inr hu)] at h
    apply Fin.ext
    have hvu : v.val = u.val := by simpa using h
    exact hvu.symm
  by_cases hv : v.val < 59
  · have h := congrFun huv v
    rw [anchor64_eq_decide_ne u v (Or.inr hv),
      anchor64_eq_decide_ne v v (Or.inr hv)] at h
    simpa [Fin.ext_iff] using h
  have hlast : ∀ a b : Fin 64, 59 ≤ a.val → 59 ≤ b.val →
      (∀ j : Fin 5, anchor64 a (anchorLastCol j) =
        anchor64 b (anchorLastCol j)) → a = b := by
    decide
  exact hlast u v (by omega) (by omega) (fun j => congrFun huv _)


-- @@ L62-65 verbatim
/-- Distinct columns have distinct complete anchor words. -/
theorem anchor64_columns_injective :
    Function.Injective (fun v : Fin 64 => fun u : Fin 64 => anchor64 u v) := by
  decide


-- @@ L67-69 verbatim
/-- All five-bit words, in the order used by the replacement rectangle. -/
def anchorWord (a : Fin 32) (b : Fin 5) : Bool :=
  anchor64 ⟨a.val + 32, by omega⟩ ⟨b.val + 59, by omega⟩


-- @@ L71-73 verbatim
/-- The 32 lower anchor rows realize all binary words on the last five columns. -/
theorem anchorWord_bijective : Function.Bijective anchorWord := by
  decide


-- @@ L75-76 verbatim
/-- Inclusion of the dense 32-position prefix. -/
def anchorFirst32 (i : Fin 32) : Fin 64 := ⟨i.val, by omega⟩


-- @@ L78-82 verbatim
/-- First-prefix column density, used to exclude variable columns. -/
theorem anchor64_first32_column_ones : ∀ v : Fin 64,
    31 ≤ (Finset.univ.filter (fun u : Fin 32 =>
      anchor64 (anchorFirst32 u) v = true)).card := by
  decide


-- @@ L84-88 verbatim
/-- First-prefix row density, used to exclude variable rows. -/
theorem anchor64_first32_row_ones : ∀ u : Fin 64,
    31 ≤ (Finset.univ.filter (fun v : Fin 32 =>
      anchor64 u (anchorFirst32 v) = true)).card := by
  decide


-- @@ L90-100 verbatim
/-- Any two columns share a one in the first 32 rows. -/
theorem anchor64_columns_common_one : ∀ v w : Fin 64,
    ∃ u : Fin 32, anchor64 (anchorFirst32 u) v = true ∧
      anchor64 (anchorFirst32 u) w = true := by
  intro v w
  by_cases h0 : v.val ≠ 0 ∧ w.val ≠ 0
  · exact ⟨0, by simpa [anchorFirst32, anchor64, ne_comm] using h0⟩
  by_cases h1 : v.val ≠ 1 ∧ w.val ≠ 1
  · exact ⟨1, by simpa [anchorFirst32, anchor64, ne_comm] using h1⟩
  have h2 : v.val ≠ 2 ∧ w.val ≠ 2 := by omega
  exact ⟨2, by simpa [anchorFirst32, anchor64, ne_comm] using h2⟩


-- @@ L102-112 verbatim
/-- Any two rows share a one in the first 32 columns. -/
theorem anchor64_rows_common_one : ∀ u w : Fin 64,
    ∃ v : Fin 32, anchor64 u (anchorFirst32 v) = true ∧
      anchor64 w (anchorFirst32 v) = true := by
  intro u w
  by_cases h0 : u.val ≠ 0 ∧ w.val ≠ 0
  · exact ⟨0, by simpa [anchorFirst32, anchor64] using h0⟩
  by_cases h1 : u.val ≠ 1 ∧ w.val ≠ 1
  · exact ⟨1, by simpa [anchorFirst32, anchor64] using h1⟩
  have h2 : u.val ≠ 2 ∧ w.val ≠ 2 := by omega
  exact ⟨2, by simp [anchorFirst32, anchor64, h2.1, h2.2]⟩


-- @@ L114-114 verbatim
end Problem348


-- @@ L116-116 verbatim
end OAI
