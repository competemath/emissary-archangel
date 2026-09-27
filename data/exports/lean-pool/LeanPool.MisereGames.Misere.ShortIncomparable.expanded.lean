/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

import LeanPool.MisereGames.AugmentedForm.Short
public import LeanPool.MisereGames.AugmentedForm
public import LeanPool.MisereGames.Form.Adjoint
public import LeanPool.MisereGames.Form.Misere.Outcome
public import LeanPool.MisereGames.Misere.Universe
import LeanPool.MisereGames.Misere.Comparison


-- @@ L15-17 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L19-19 verbatim
namespace MisereGames


-- @@ L21-34 verbatim
/-!

# Short Sets and Comparison

This is a mirror of `CombinatorialGames.Misere.LiftIncomparable` module with
the difference that if we are in a short universe then we do not need to
increase the universe level.

The main results are
- `g_misereEQ_h_short`
- `g_misereEQ_h_shortUniverse`
- `g_h_incomparable`
- `g_h_incomparable_longUniverse`
-/


-- @@ L36-36 verbatim
universe u


-- @@ L38-38 verbatim
open Form

-- @@ L39-39 verbatim
open Form.Misere.Outcome

-- @@ L40-40 verbatim
open Form.Misere.Adjoint


-- @@ L42-42 verbatim
namespace AugmentedForm.Short


-- @@ L44-44 verbatim
public section


-- @@ L46-51 expanded
/-- The set of all adjoints $J^\circ$ (lifted to $u + 1$) for all short $J$ in
universe $u$.
-/
noncomputable def adjointsOfShort : Set AugmentedForm.{u} :=
  Set.range (fun J : {x : AugmentedForm.{u} | IsShort x} => adjoint (J : AugmentedForm.{u}))


-- @@ L53-55 verbatim
instance smallShortAdjoints : Small.{u} (adjointsOfShort.{u}) := by
  unfold adjointsOfShort
  exact small_range _


-- @@ L57-60 expanded
/-- $G = \{ J^\circ \mid J^\circ \}$ for all short $J$ in universe $u$.
-/
noncomputable def g : AugmentedForm.{u} :=
  OfSets.ofSets (Player.cases adjointsOfShort adjointsOfShort)
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L62-63 verbatim
instance smallInsertG : Small.{u} (insert g adjointsOfShort : Set AugmentedForm.{u}) := by
  infer_instance


-- @@ L65-69 expanded
/-- $H = \{ G, J^\circ \mid G, J^\circ \}$ for all short $J$ in universe $u$.
-/
noncomputable def h : AugmentedForm.{u} :=
  OfSets.ofSets (Player.cases (insert g adjointsOfShort) (insert g adjointsOfShort))
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L71-73 expanded
theorem adjoint_mem_adjointsOfShort {X : AugmentedForm.{u}} (hX : IsShort X) :
    adjoint X ∈ adjointsOfShort :=
  ⟨⟨X, hX⟩, rfl⟩


-- @@ L75-77 verbatim
@[simp]
theorem moves_g (p : Player) : moves p g = adjointsOfShort := by
  cases p <;> simp [g]


-- @@ L79-82 verbatim
@[simp]
theorem moves_h (p : Player) :
    moves p h = insert g adjointsOfShort := by
  cases p <;> simp [h]


-- @@ L84-90 verbatim
theorem bigG_not_isEndLike (p : Player) : ¬ IsEndLike p g := by
  rw [AugmentedForm.IsEndLike_iff]
  cases p <;> simp +decide only [isEnd_def, moves_g, not_or]
  · exact ⟨by unfold g; simp +decide [hasTombstone_ofSets],
      Set.Nonempty.ne_empty ⟨_, adjoint_mem_adjointsOfShort Short.zero⟩⟩
  · refine ⟨?_, Set.Nonempty.ne_empty ⟨_, adjoint_mem_adjointsOfShort Short.zero⟩⟩
    unfold g; simp +decide [AugmentedForm.hasTombstone_ofSets]


-- @@ L92-96 verbatim
theorem bigH_not_isEndLike (p : Player) : ¬ IsEndLike p h := by
  rw [AugmentedForm.IsEndLike_iff]
  cases p <;> simp +decide only [isEnd_def, moves_h, not_or]
  all_goals exact ⟨by unfold h; simp +decide [hasTombstone_ofSets],
    Set.Nonempty.ne_empty ⟨_, Set.mem_insert _ _⟩⟩


-- @@ L98-111 expanded
theorem misereOutcome_g_add_short {x : AugmentedForm.{u}} (h_isShort : IsShort x) :
    MisereOutcome (g + x) = Outcome.N :=
  by
  rw [misereOutcome_N_iff_winsGoingFirst, add_comm]
  constructor <;> apply winsGoingFirst_of_moves
  · use x + adjoint x
    constructor
    · apply add_left_mem_moves_add
      exact moves_g Player.left ▸ adjoint_mem_adjointsOfShort h_isShort
    · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P x)
  · use x + adjoint x
    constructor
    · apply add_left_mem_moves_add
      exact moves_g Player.right ▸ adjoint_mem_adjointsOfShort h_isShort
    · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P x)


-- @@ L113-126 expanded
theorem misereOutcome_h_add_short {x : AugmentedForm.{u}} (h_isShort : IsShort x) :
    MisereOutcome (h + x) = Outcome.N :=
  by
  rw [misereOutcome_N_iff_winsGoingFirst, add_comm]
  constructor <;> apply winsGoingFirst_of_moves
  · use x + adjoint x
    constructor
    · apply add_left_mem_moves_add
      exact moves_h Player.left ▸ Set.mem_insert_of_mem _ (adjoint_mem_adjointsOfShort h_isShort)
    · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P x)
  · use x + adjoint x
    constructor
    · apply add_left_mem_moves_add
      exact moves_h Player.right ▸ Set.mem_insert_of_mem _ (adjoint_mem_adjointsOfShort h_isShort)
    · exact not_winsGoingFirst_of_misereOutcome_P (misereOutcome_add_adjoint_eq_P x)


-- @@ L128-135 verbatim
theorem g_not_isEndLike (p : Player) : ¬ IsEndLike p g := by
  rw [AugmentedForm.IsEndLike_iff, not_or]
  constructor
  · simp only [g, hasTombstone_ofSets, not_false_eq_true]
  · cases p <;> simp only [g, adjointsOfShort, Set.coe_ofPred,
                           isEnd_def, leftMoves_ofSets, rightMoves_ofSets, Set.range_eq_empty_iff,
                           nonempty_subtype, not_isEmpty_of_nonempty, not_false_eq_true,
                           Exists.intro 0 Short.zero, ]


-- @@ L137-159 expanded
private theorem not_winsGoingFirst_g_add_g {p : Player} : ¬WinsGoingFirst p (g + g) :=
  by
  rw [not_winsGoingFirst_iff]
  · constructor
    · simp [g_not_isEndLike]
    · intro g' h_g'_mem
      simp only [moves_add, moves_g, Set.mem_union, Set.mem_image] at h_g'_mem
      obtain (⟨x, ⟨⟨y, h_y_isShort⟩, rfl⟩, rfl⟩ | ⟨x, ⟨⟨y, h_y_isShort⟩, rfl⟩, rfl⟩) := h_g'_mem
      · apply winsGoingFirst_of_moves
        use (adjoint y) + (adjoint (adjoint y))
        constructor
        · apply add_left_mem_moves_add
          exact moves_g _ ▸ adjoint_mem_adjointsOfShort (Adjoint.short_adjoint h_y_isShort)
        · apply not_winsGoingFirst_of_misereOutcome_P
          exact misereOutcome_add_adjoint_eq_P (adjoint y)
      · rw [add_comm]
        apply winsGoingFirst_of_moves
        use (adjoint y) + (adjoint (adjoint y))
        constructor
        · apply add_left_mem_moves_add
          exact moves_g _ ▸ adjoint_mem_adjointsOfShort (Adjoint.short_adjoint h_y_isShort)
        · apply not_winsGoingFirst_of_misereOutcome_P
          exact misereOutcome_add_adjoint_eq_P (adjoint y)


-- @@ L161-162 verbatim
theorem misereOutcome_g_add_g : MisereOutcome (g + g) = Outcome.P := by
  simp [misereOutcome_P_iff_winsGoingFirst, not_winsGoingFirst_g_add_g]


-- @@ L164-174 verbatim
theorem misereOutcome_h_add_g : MisereOutcome (h + g) = Outcome.N := by
  rw [misereOutcome_N_iff_winsGoingFirst]
  constructor <;> apply winsGoingFirst_of_moves
  · use g + g
    constructor
    · simp_all
    · exact not_winsGoingFirst_of_misereOutcome_P misereOutcome_g_add_g
  · use g + g
    constructor
    · simp_all
    · exact not_winsGoingFirst_of_misereOutcome_P misereOutcome_g_add_g


-- @@ L176-179 expanded
theorem g_misereEQ_h_short (A : AugmentedForm.{u} → Prop) (h_short : ∀ x, A x → IsShort x) :
    MisereEQ A g h := by
  intro x hx
  rw [misereOutcome_g_add_short (h_short x hx), misereOutcome_h_add_short (h_short x hx)]


-- @@ L181-183 verbatim
theorem g_misereEQ_h_shortUniverse (U : AugmentedForm.{u} → Prop) [ShortUniverse U] :
    MisereEQ U g h :=
  g_misereEQ_h_short U (fun _ hx => Universe.isAmbient_of_mem hx)


-- @@ L185-191 expanded
theorem g_h_incomparable {A : AugmentedForm.{u} → Prop} (h_Ag : A g) :
    ¬(MisereGE A g h) ∧ ¬(MisereGE A h g) :=
  by
  constructor
  all_goals
    · intro h
      have := h _ h_Ag
      simp +decide only [misereOutcome_g_add_g, misereOutcome_h_add_g, ge_iff_le] at this


-- @@ L193-205 verbatim
/--
$G$ is in any universe $\mathcal{U}$ in $u$.
-/
theorem g_mem_longUniverse (U : AugmentedForm.{u} → Prop) [LongUniverse U] :
     U g := by
  have h_ambient : Ambient (IsLong : AugmentedForm.{u} → Prop) := inferInstance
  have h_mem : ∀ b ∈ adjointsOfShort.{u}, U b := by
    rintro b ⟨⟨J, h_j⟩, rfl⟩
    exact Form.rootedAdjoint_mem_of_isAmbient (r := 0)
      (Universe.zero_mem IsLong) (fun _ _ => isLong _) (isLong _)
  have h_notempty : (adjointsOfShort.{u}).Nonempty := ⟨_,  adjoint_mem_adjointsOfShort Short.zero⟩
  exact ClosedUnderDicotic.closed_dicotic (IsAmbient := IsLong)
    adjointsOfShort adjointsOfShort h_mem h_mem h_notempty h_notempty (isLong _)


-- @@ L207-209 expanded
theorem g_h_incomparable_longUniverse (U : AugmentedForm.{u} → Prop) [LongUniverse U] :
    ¬(MisereGE U g h) ∧ ¬(MisereGE U h g) :=
  g_h_incomparable (g_mem_longUniverse U)


-- @@ L211-211 verbatim
end


-- @@ L213-213 verbatim
end AugmentedForm.Short


-- @@ L215-215 verbatim
end MisereGames
