import OAI.Combinatorics.MatrixRemoval.Host


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Exact level-based entry formulas for the canonical flat-class host. -/

-- @@ L6-6 verbatim
namespace Problem348.Construction


-- @@ L8-15 verbatim
theorem variableEntry_same_plus {h i : ℕ} {r c : VariablePosition h}
    (hr : AtLevel i true r) (hc : AtLevel i true c) :
    variableEntry r c = decide (node r ≤ node c) := by
  by_cases hi : i = h
  · simp [variableEntry, hr.1, hc.1, hi]
  · have hpr := hr.2.resolve_left hi
    have hpc := hc.2.resolve_left hi
    simp [variableEntry, hr.1, hc.1, hi, hpr, hpc]


-- @@ L17-25 verbatim
theorem variableEntry_same_minus {h i : ℕ} {r c : VariablePosition h}
    (hr : AtLevel i false r) (hc : AtLevel i false c) :
    variableEntry r c =
      if i = h then decide (node r ≤ node c) else decide (node r < node c) := by
  by_cases hi : i = h
  · simp [variableEntry, hr.1, hc.1, hi]
  · have hpr := hr.2.resolve_left hi
    have hpc := hc.2.resolve_left hi
    simp [variableEntry, hr.1, hc.1, hi, hpr, hpc]


-- @@ L27-32 verbatim
theorem variableEntry_child_parent_plus {h i : ℕ} {r c : VariablePosition h}
    (hr : AtLevel (i + 1) true r) (hc : AtLevel i true c) :
    variableEntry r c = decide (node r / 2 ≤ node c) := by
  have hi : i < h := by have := depth_le r; have hrd := hr.1; omega
  have hpc := hc.2.resolve_left (Nat.ne_of_lt hi)
  simp [variableEntry, hr.1, hc.1, hi, hpc, hr.2]


-- @@ L34-39 verbatim
theorem variableEntry_child_parent_minus {h i : ℕ} {r c : VariablePosition h}
    (hr : AtLevel (i + 1) false r) (hc : AtLevel i false c) :
    variableEntry r c = decide (node r / 2 < node c) := by
  have hi : i < h := by have := depth_le r; have hrd := hr.1; omega
  have hpc := hc.2.resolve_left (Nat.ne_of_lt hi)
  simp [variableEntry, hr.1, hc.1, hi, hpc, hr.2]


-- @@ L41-48 verbatim
/-- Maximal depth is exactly the shared leaf class. -/
theorem class_eq_leaf_of_depth_eq {h : ℕ} {v : VariablePosition h}
    (hv : depth v = h) : v.1 = Fin.last (2 * h) := by
  apply Fin.ext
  have := v.1.isLt
  simp only [Fin.val_last]
  unfold depth at hv
  omega


-- @@ L50-53 verbatim
/-- At leaf depth a node labels a unique position, since its block has size one. -/
theorem node_eq_index_of_depth_eq {h : ℕ} {v : VariablePosition h}
    (hv : depth v = h) : node v = v.2.val := by
  simp [node, hv]


-- @@ L55-57 verbatim
theorem eq_leaf_of_depth_eq {h : ℕ} {v : VariablePosition h}
    (hv : depth v = h) : v = (Fin.last (2 * h), v.2) := by
  exact Prod.ext (class_eq_leaf_of_depth_eq hv) rfl


-- @@ L59-59 verbatim
end Problem348.Construction


-- @@ L61-61 verbatim
end OAI
