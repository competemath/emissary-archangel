/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.AugmentedForm
public import LeanPool.MisereGames.Form.Misere.Outcome
public import LeanPool.MisereGames.Form.Adjoint


-- @@ L12-14 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L16-16 verbatim
namespace MisereGames


-- @@ L18-18 verbatim
universe u


-- @@ L20-20 verbatim
open Form

-- @@ L21-21 verbatim
open Form.Misere.Outcome


-- @@ L23-23 verbatim
namespace AugmentedForm


-- @@ L25-25 verbatim
public section


-- @@ L27-33 expanded
/-- Lift an augmented form to the next universe level. -/
noncomputable def liftSucc (g : AugmentedForm.{u}) : AugmentedForm.{u + 1} :=
  ofSetsWithTombs (fun p => Set.range (fun y : moves p g => liftSucc y.val))
    (fun p => g.hasTombstone p)
termination_by g
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L35-40 verbatim
@[simp]
theorem moves_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    moves p (liftSucc g) = liftSucc '' moves p g := by
  rw [liftSucc, moves_ofSetsWithTombs]
  ext x
  simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_image]


-- @@ L42-45 verbatim
@[simp]
theorem hasTombstone_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    (liftSucc g).hasTombstone p ↔ g.hasTombstone p := by
  rw [liftSucc, hasTombstone_ofSetsWithTombs]


-- @@ L47-62 verbatim
theorem liftSucc_injective : Function.Injective liftSucc := by
  intro a b hab
  induction a using AugmentedForm.moveRecOn generalizing b with
  | mk a ha =>
    induction b using AugmentedForm.moveRecOn with
    | mk b hb =>
      ext p x
      · replace hab := congr_arg (fun g => moves p g) hab
        simp at hab
        constructor <;> intro hx
        · obtain ⟨y, hy, hy'⟩ := hab.subset ⟨x, hx, rfl⟩
          exact Set.mem_of_eq_of_mem (ha p x hx (Eq.symm hy')) hy
        · obtain ⟨y, hy, hy'⟩ := hab.symm.subset ⟨x, hx, rfl⟩
          exact Set.mem_of_eq_of_mem (Eq.symm (ha p y hy hy')) hy
      · replace hab := congr_arg (fun g => hasTombstone p g) hab
        simpa only [hasTombstone_liftSucc, eq_iff_iff] using hab


-- @@ L64-67 verbatim
@[simp]
theorem isEnd_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    IsEnd p (liftSucc g) ↔ IsEnd p g := by
  rw [isEnd_def, isEnd_def, moves_liftSucc, Set.image_eq_empty]


-- @@ L69-72 verbatim
@[simp]
theorem isEndLike_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    IsEndLike p (liftSucc g) ↔ IsEndLike p g := by
  rw [IsEndLike_iff, IsEndLike_iff, hasTombstone_liftSucc, isEnd_liftSucc]


-- @@ L74-85 verbatim
@[simp]
theorem liftSucc_add (a b : AugmentedForm.{u}) :
    liftSucc (a + b) = liftSucc a + liftSucc b := by
  induction a using AugmentedForm.moveRecOn generalizing b with
  | mk a ha =>
    induction b using AugmentedForm.moveRecOn with
    | mk b hb =>
      ext p
      · simp only [moves_liftSucc, moves_add, Set.image_union, Set.image_image, Set.mem_union,
                   Set.mem_image]
        grind only
      · simp [hasTombstone_add, hasTombstone_liftSucc, isEndLike_liftSucc]


-- @@ L87-94 verbatim
@[simp]
theorem winsGoingFirst_liftSucc (p : Player) (g : AugmentedForm.{u}) :
    WinsGoingFirst p (liftSucc g) ↔ WinsGoingFirst p g := by
  induction g using AugmentedForm.moveRecOn generalizing p with
  | mk g hg =>
    rw [winsGoingFirst_iff, winsGoingFirst_iff]
    simp only [isEndLike_liftSucc, moves_liftSucc, Set.mem_image, exists_exists_and_eq_and]
    grind only


-- @@ L96-100 verbatim
@[simp]
theorem misereOutcome_liftSucc (g : AugmentedForm.{u}) :
    MisereOutcome (liftSucc g) = MisereOutcome g := by
  unfold MisereOutcome MiserePlayerOutcome
  rw [winsGoingFirst_liftSucc, winsGoingFirst_liftSucc]


-- @@ L102-108 verbatim
@[simp]
theorem liftSucc_zero : liftSucc (0 : AugmentedForm.{u}) = 0 := by
  ext p x
  · simp only [moves_liftSucc, moves_zero, Set.image_empty, Set.mem_empty_iff_false]
  · rw [<-AugmentedForm.hasTombstone_liftSucc p 0, <-AugmentedForm.ofGameForm_zero]
    simp only [hasTombstone_liftSucc, not_hasTombstone_ofGameForm, false_iff]
    exact not_hasTombstone_zero' p


-- @@ L110-113 expanded
@[simp]
theorem not_hasTombstone_adjoint {p : Player} {g : AugmentedForm.{u}} :
    ¬hasTombstone p (adjoint g) := by
  rw [adjoint_def]
  split_ifs <;> simp


-- @@ L115-128 expanded
@[simp]
theorem liftSucc_adjoint (g : AugmentedForm.{u}) : liftSucc (adjoint g) = adjoint (liftSucc g) := by
  induction g using moveRecOn with
  | mk g ih =>
    apply AugmentedForm.ext
    · intro p
      rw [moves_liftSucc, Adjoint.moves p g, Adjoint.moves, isEnd_liftSucc, moves_liftSucc]
      by_cases h : IsEnd (-p) g
      · simp only [h, ite_true, Set.image_singleton, liftSucc_zero]
      · rw [ite_eq_right h, ite_eq_right h, ← Set.image_comp, ← Set.image_comp]
        apply Set.image_congr
        intro y hy
        simpa only [Function.comp_apply] using ih (-p) y hy
    · simp only [hasTombstone_liftSucc, not_hasTombstone_adjoint, implies_true]


-- @@ L130-130 verbatim
end


-- @@ L132-132 verbatim
end AugmentedForm


-- @@ L134-134 verbatim
end MisereGames
