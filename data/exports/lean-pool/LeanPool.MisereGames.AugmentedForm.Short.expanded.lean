/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.AugmentedForm
public import LeanPool.MisereGames.Form.Short


-- @@ L11-13 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L15-15 verbatim
namespace MisereGames


-- @@ L17-17 verbatim
universe u


-- @@ L19-19 verbatim
open Form


-- @@ L21-21 verbatim
public section


-- @@ L23-29 verbatim
/--
A concrete encoding of the data of a short augmented form: a finite list of
Left options, a finite list of Right options, and two tombstone bits. As an
inductive type in `Type 0`, it is `Small.{u}` for every `u`.
-/
inductive ShortTree : Type
  | mk (L R : List ShortTree) (tL tR : Bool) : ShortTree


-- @@ L31-31 verbatim
namespace ShortTree


-- @@ L33-48 verbatim
/--
Interpret a `ShortTree` as an augmented form.
-/
noncomputable def toForm : ShortTree → AugmentedForm.{u}
  | .mk L R tL tR =>
      AugmentedForm.ofSetsWithTombs
        (fun p => Set.range (fun i : Fin (p.cases L R).length =>
            ShortTree.toForm ((p.cases L R).get i)))
        (fun p => p.cases tL tR)
  decreasing_by
    cases p
    all_goals
      simp only [Player.cases, ShortTree.mk.sizeOf_spec]
      have h := List.sizeOf_get _ i
      simp only [Player.cases] at h
      omega


-- @@ L50-61 verbatim
@[simp]
theorem moves_toForm (p : Player) (L R : List ShortTree) (tL tR : Bool) :
    moves p (toForm (.mk L R tL tR)) = toForm '' {y | y ∈ p.cases L R} := by
  rw [toForm, AugmentedForm.moves_ofSetsWithTombs]
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, List.get_mem _ _, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hy
    exact ⟨i, rfl⟩


-- @@ L63-66 verbatim
@[simp]
theorem hasTombstone_toForm (p : Player) (L R : List ShortTree) (tL tR : Bool) :
    (toForm (.mk L R tL tR)).hasTombstone p = p.cases tL tR := by
  rw [toForm, AugmentedForm.hasTombstone_ofSetsWithTombs]


-- @@ L68-78 verbatim
/--
Any finite set of augmented forms, each of which is in the range of `toForm`,
is the image under `toForm` of (the set of members of) some list.
-/
theorem exists_list_image (S : Set AugmentedForm.{u}) (hfin : S.Finite)
    (h_ext : ∀ y ∈ S, ∃ t : ShortTree, toForm t = y) :
    ∃ L : List ShortTree, toForm '' {y | y ∈ L} = S := by
  choose f hf using h_ext
  refine ⟨hfin.toFinset.attach.toList.map (fun y => f y.val (hfin.mem_toFinset.mp y.prop)), ?_⟩
  ext y
  simp_all


-- @@ L80-97 verbatim
/--
Every short augmented form is in the range of `toForm`.
-/
theorem isShort_mem_range_toForm {x : AugmentedForm.{u}} (h_isShort : IsShort x) :
    ∃ t : ShortTree, toForm t = x := by
  induction x using AugmentedForm.moveRecOn with
  | mk x ih =>
    classical
    obtain ⟨L, hL⟩ := exists_list_image (moves .left x) (Short.finite_moves .left h_isShort)
      (fun y hy => ih .left y hy (Short.of_mem_moves h_isShort hy))
    obtain ⟨R, hR⟩ := exists_list_image (moves .right x) (Short.finite_moves .right h_isShort)
      (fun y hy => ih .right y hy (Short.of_mem_moves h_isShort hy))
    refine ⟨.mk L R (decide (x.hasTombstone .left)) (decide (x.hasTombstone .right)), ?_⟩
    refine AugmentedForm.ext (fun p => ?_) (fun p => ?_)
    · rw [moves_toForm]
      cases p <;> assumption
    · rw [hasTombstone_toForm]
      cases p <;> simp only [Player.cases, decide_eq_true_eq]


-- @@ L99-101 verbatim
end ShortTree

-- TODO: There MUST be a simpler way to get this instance


-- @@ L103-110 verbatim
/--
The set of all short augmented forms definable in `u` is `u`-small.
-/
instance smallSetOfIsShort : Small.{u} {x : AugmentedForm.{u} | IsShort x} := by
  apply small_subset (s := Set.range ShortTree.toForm)
  intro x hx
  obtain ⟨t, ht⟩ := ShortTree.isShort_mem_range_toForm hx
  exact ⟨t, ht⟩


-- @@ L112-112 verbatim
end


-- @@ L114-114 verbatim
end MisereGames
