module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.GroupWithZero.Hom


-- @@ L7-7 verbatim
public section


-- @@ L9-9 verbatim
open scoped Indicator


-- @@ L11-11 verbatim
variable {F α β M₀ N₀ : Type*}


-- @@ L13-13 verbatim
namespace Set

-- @@ L14-14 verbatim
variable [MonoidWithZero M₀] [MonoidWithZero N₀] {s : Set α}


-- @@ L16-17 expanded
lemma indicator_one_inter_apply (s t : Set α) (x : α) :
    (Set.indicator (s ∩ t) fun _ ↦ (1 : M₀)) x =
      (Set.indicator s fun _ ↦ (1 : _)) x * (Set.indicator t fun _ ↦ (1 : _)) x :=
  by classical simp [indicator_apply, ← ite_and, and_comm]


-- @@ L19-20 expanded
lemma indicator_one_inter (s t : Set α) :
    (Set.indicator (s ∩ t) fun _ ↦ (1 : M₀)) =
      (Set.indicator s fun _ ↦ (1 : _)) * Set.indicator t fun _ ↦ (1 : _) :=
  funext <| indicator_one_inter_apply _ _


-- @@ L22-23 expanded
lemma map_indicator_one [FunLike F M₀ N₀] [MonoidWithZeroHomClass F M₀ N₀] (f : F) (s : Set α)
    (x : α) : f ((Set.indicator s fun _ ↦ (1 : _)) x) = (Set.indicator s fun _ ↦ (1 : _)) x := by
  classical exact MonoidWithZeroHom.map_ite_one_zero ..


-- @@ L25-27 expanded
variable (M₀) in
@[simp]
lemma indicator_one_image (e : α ≃ β) (s : Set α) (b : β) :
    (Set.indicator (e '' s) fun _ ↦ (1 : M₀)) b = (Set.indicator s fun _ ↦ (1 : _)) (e.symm b) := by
  classical simp [indicator_apply, ← e.eq_symm_apply]


-- @@ L29-29 verbatim
variable [Nontrivial M₀] {a : α}


-- @@ L31-32 expanded
@[simp high]
lemma indicator_one_apply_eq_zero : (Set.indicator s fun _ ↦ (1 : M₀)) a = 0 ↔ a ∉ s := by
  classical exact one_ne_zero.ite_eq_right_iff


-- @@ L34-35 expanded
lemma indicator_one_apply_ne_zero : (Set.indicator s fun _ ↦ (1 : M₀)) a ≠ 0 ↔ a ∈ s := by
  classical exact one_ne_zero.ite_ne_right_iff


-- @@ L37-38 expanded
@[simp high]
lemma indicator_one_eq_zero : (Set.indicator s fun _ ↦ (1 : M₀)) = 0 ↔ s = ∅ := by
  simp [funext_iff, eq_empty_iff_forall_notMem]


-- @@ L40-40 expanded
lemma indicator_one_ne_zero : (Set.indicator s fun _ ↦ (1 : M₀)) ≠ 0 ↔ s.Nonempty := by
  simp [nonempty_iff_ne_empty]


-- @@ L42-44 expanded
variable (M₀) in
@[simp high]
lemma support_indicator_one : (Set.indicator s fun _ ↦ (1 : M₀)).support = s := by ext;
  exact indicator_one_apply_ne_zero


-- @@ L46-46 verbatim
end Set
