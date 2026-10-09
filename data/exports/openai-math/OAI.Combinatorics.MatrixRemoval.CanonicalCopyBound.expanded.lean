import OAI.Combinatorics.MatrixRemoval.OrderedAnchorRigidity
import OAI.Combinatorics.MatrixRemoval.OrderedHostCopy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-11 verbatim
/-!
# Unconditional copy bound for the canonical host

Concrete anchor rigidity and six-mode body localization imply the integer
copy bound and its normalized form.
-/


-- @@ L13-13 verbatim
namespace Problem348.OrderedHost


-- @@ L15-15 verbatim
open Construction


-- @@ L17-19 verbatim
theorem anchor64Pinned (h : ℕ) :
    Anchor64Pinned (rowIndex h) (columnIndex h) :=
  HostAnchorRigidity.representatives_of_indices


-- @@ L21-26 verbatim
theorem matching_copy_leaf (h : ℕ) (r c : Fin 66 → Position h)
    (hr : StrictMono (fun i => rowIndex h (r i)))
    (hc : StrictMono (fun j => columnIndex h (c j)))
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j) :
    ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z :=
  matching_copy_leaf_of_pinning h (anchor64Pinned h) r c hr hc hmatch


-- @@ L28-31 verbatim
theorem canonical_copyCount_le (h : ℕ) :
    copyCount fixedH (hostMatrix (rowIndex h) (columnIndex h)) ≤
      2 ^ h * (size h) ^ 130 :=
  copyCount_le_of_pinning h (anchor64Pinned h)


-- @@ L33-37 verbatim
theorem canonical_copyDensity_le (h : ℕ) :
    (copyCount fixedH (hostMatrix (rowIndex h) (columnIndex h)) : ℝ) /
        ((size h : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) :=
  copyDensity_le_of_pinning h (anchor64Pinned h)


-- @@ L39-39 verbatim
end Problem348.OrderedHost


-- @@ L41-41 verbatim
end OAI
