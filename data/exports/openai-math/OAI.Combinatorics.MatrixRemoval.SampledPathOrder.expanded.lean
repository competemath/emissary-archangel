import OAI.Combinatorics.MatrixRemoval.HostSampledPath
import OAI.Combinatorics.MatrixRemoval.TreePositions


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
/-! The four sampled body orders, including the shared-leaf edge. -/

-- @@ L7-7 verbatim
universe uR uC


-- @@ L9-9 verbatim
namespace Problem348.HostSampledPath


-- @@ L11-11 verbatim
open SampledPath

 
-- @@ L13-19 verbatim
theorem sample_plus_eq (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    sample h i hi true z u = TreePositions.plusPos i hi (mixFin h i hi z u) := by
  apply Prod.ext
  · apply Fin.ext
    simp [sample, classAt, TreePositions.plusPos]
    omega
  · rfl

 
-- @@ L21-23 verbatim
theorem sample_minus_eq (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    sample h i hi false z u = TreePositions.minusPos i hi (mixFin h i hi z u) := by
  simp [sample, classAt, TreePositions.minusPos]


-- @@ L25-27 verbatim
@[simp] theorem treeNode_mixFin (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    TreePositions.node i (mixFin h i hi z u) = z.val / blockSize h i :=
  mixFin_node h i hi z u

 
-- @@ L29-36 verbatim
theorem row_plus_sample_child_lt_parent {h : ℕ} (i : Fin h)
    (z u v : Fin (2 ^ h)) :
    TreePositions.rowKey h (sample h (i.val + 1) (by omega) true z u) <
      TreePositions.rowKey h (sample h i.val (by omega) true z v) := by
  rw [sample_plus_eq, sample_plus_eq,
    TreePositions.row_plus_child_lt_parent i.isLt]
  simp only [treeNode_mixFin]
  rw [ancestor_parent h i.val z.val (by omega)]

 
-- @@ L38-45 verbatim
theorem row_minus_sample_parent_lt_child {h : ℕ} (i : Fin h)
    (z u v : Fin (2 ^ h)) :
    TreePositions.rowKey h (sample h i.val (by omega) false z v) <
      TreePositions.rowKey h (sample h (i.val + 1) (by omega) false z u) := by
  rw [sample_minus_eq, sample_minus_eq,
    TreePositions.row_minus_parent_lt_child i.isLt]
  simp only [treeNode_mixFin]
  rw [ancestor_parent h i.val z.val (by omega)]

 
-- @@ L47-54 verbatim
theorem column_plus_sample_parent_lt_child {h : ℕ} (i : Fin h)
    (z u v : Fin (2 ^ h)) :
    TreePositions.columnKey h (sample h i.val (by omega) true z v) <
      TreePositions.columnKey h (sample h (i.val + 1) (by omega) true z u) := by
  rw [sample_plus_eq, sample_plus_eq,
    TreePositions.column_plus_parent_lt_child i.isLt]
  simp only [treeNode_mixFin]
  rw [ancestor_parent h i.val z.val (by omega)]

 
-- @@ L56-63 verbatim
theorem column_minus_sample_child_lt_parent {h : ℕ} (i : Fin h)
    (z u v : Fin (2 ^ h)) :
    TreePositions.columnKey h (sample h (i.val + 1) (by omega) false z u) <
      TreePositions.columnKey h (sample h i.val (by omega) false z v) := by
  rw [sample_minus_eq, sample_minus_eq,
    TreePositions.column_minus_child_lt_parent i.isLt]
  simp only [treeNode_mixFin]
  rw [ancestor_parent h i.val z.val (by omega)]


-- @@ L65-74 verbatim
/-- Consequence after transporting the canonical row key into any ordered axis. -/
theorem row_plus_sample_order {h : ℕ} {R : Type uR} [Preorder R]
    (r : Construction.Position h → R)
    (hr : ∀ p q : Construction.VariablePosition h,
      TreePositions.rowKey h p < TreePositions.rowKey h q →
        r (Sum.inr (Sum.inl p)) < r (Sum.inr (Sum.inl q)))
    (i : Fin h) (z u v : Fin (2 ^ h)) :
    r (position h (i.val + 1) (by omega) true z u) <
      r (position h i.val (by omega) true z v) :=
  hr _ _ (row_plus_sample_child_lt_parent i z u v)

 
-- @@ L76-84 verbatim
theorem row_minus_sample_order {h : ℕ} {R : Type uR} [Preorder R]
    (r : Construction.Position h → R)
    (hr : ∀ p q : Construction.VariablePosition h,
      TreePositions.rowKey h p < TreePositions.rowKey h q →
        r (Sum.inr (Sum.inl p)) < r (Sum.inr (Sum.inl q)))
    (i : Fin h) (z u v : Fin (2 ^ h)) :
    r (position h i.val (by omega) false z v) <
      r (position h (i.val + 1) (by omega) false z u) :=
  hr _ _ (row_minus_sample_parent_lt_child i z u v)

 
-- @@ L86-94 verbatim
theorem column_plus_sample_order {h : ℕ} {C : Type uC} [Preorder C]
    (c : Construction.Position h → C)
    (hc : ∀ p q : Construction.VariablePosition h,
      TreePositions.columnKey h p < TreePositions.columnKey h q →
        c (Sum.inr (Sum.inl p)) < c (Sum.inr (Sum.inl q)))
    (i : Fin h) (z u v : Fin (2 ^ h)) :
    c (position h i.val (by omega) true z v) <
      c (position h (i.val + 1) (by omega) true z u) :=
  hc _ _ (column_plus_sample_parent_lt_child i z u v)

 
-- @@ L96-104 verbatim
theorem column_minus_sample_order {h : ℕ} {C : Type uC} [Preorder C]
    (c : Construction.Position h → C)
    (hc : ∀ p q : Construction.VariablePosition h,
      TreePositions.columnKey h p < TreePositions.columnKey h q →
        c (Sum.inr (Sum.inl p)) < c (Sum.inr (Sum.inl q)))
    (i : Fin h) (z u v : Fin (2 ^ h)) :
    c (position h (i.val + 1) (by omega) false z u) <
      c (position h i.val (by omega) false z v) :=
  hc _ _ (column_minus_sample_child_lt_parent i z u v)


-- @@ L106-106 verbatim
end Problem348.HostSampledPath


-- @@ L108-108 verbatim
end OAI
