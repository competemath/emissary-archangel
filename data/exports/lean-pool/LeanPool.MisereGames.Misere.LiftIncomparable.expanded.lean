/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.AugmentedForm.Lift
public import LeanPool.MisereGames.Misere.Universe
import LeanPool.MisereGames.Misere.Comparison


-- @@ L12-14 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L16-16 verbatim
namespace MisereGames


-- @@ L18-26 verbatim
/-!

# Lifting Sets and Comparison

The main results are
- `g_misereEQ_h_lift`
- `g_h_incomparable`
- `g_h_incomparable_longUniverse`
-/


-- @@ L28-28 verbatim
universe u


-- @@ L30-30 verbatim
open Form

-- @@ L31-31 verbatim
open Form.Misere.Outcome

-- @@ L32-32 verbatim
open Form.Misere.Adjoint


-- @@ L34-34 verbatim
namespace AugmentedForm


-- @@ L36-36 verbatim
public section


-- @@ L38-43 expanded
/-- The set of all adjoints $J^\circ$ (lifted to $u + 1$) for all $J$ in universe
$u$.
-/
noncomputable def adjointsOfSmall : Set AugmentedForm.{u + 1} :=
  Set.range (fun J : AugmentedForm.{u} => liftSucc (adjoint J))


-- @@ L45-47 verbatim
instance smallAdjointsOfSmall : Small.{u + 1} (adjointsOfSmall.{u}) := by
  unfold adjointsOfSmall
  exact small_range _


-- @@ L49-52 expanded
/-- $G = \{ J^\circ \mid J^\circ \}$ for all $J$ in universe $u$.
-/
noncomputable def g : AugmentedForm.{u + 1} :=
  OfSets.ofSets (Player.cases adjointsOfSmall adjointsOfSmall)
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L54-55 verbatim
instance smallInsertG : Small.{u+1} (insert g adjointsOfSmall : Set AugmentedForm.{u+1}) := by
  exact small_insert g adjointsOfSmall


-- @@ L57-61 expanded
/-- $H = \{ G, J^\circ \mid G, J^\circ \}$ for all $J$ in universe $u$.
-/
noncomputable def h : AugmentedForm.{u + 1} :=
  OfSets.ofSets (Player.cases (insert g adjointsOfSmall) (insert g adjointsOfSmall))
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L63-65 verbatim
@[simp]
theorem moves_g (p : Player) : moves p g = adjointsOfSmall.{u} := by
  cases p <;> simp [g]


-- @@ L67-70 verbatim
@[simp]
theorem moves_h (p : Player) :
    moves p h = insert g adjointsOfSmall.{u} := by
  cases p <;> simp [h]


-- @@ L72-74 expanded
theorem liftAdjoint_mem_adjointsOfSmall (x : AugmentedForm.{u}) :
    liftSucc (adjoint x) ∈ adjointsOfSmall.{u} :=
  ⟨x, rfl⟩


-- @@ L76-81 verbatim
theorem g_not_isEndLike (p : Player) : ¬ IsEndLike p g := by
  rw [AugmentedForm.IsEndLike_iff, not_or]
  constructor
  · simp only [g, hasTombstone_ofSets, not_false_eq_true]
  · cases p <;> simp only [g, adjointsOfSmall, isEnd_def, leftMoves_ofSets, rightMoves_ofSets,
                           Set.range_eq_empty_iff, not_isEmpty_of_nonempty, not_false_eq_true]


-- @@ L83-89 expanded
/-- The sum of a (lifted) adjoint and its base game is a $\mathscr{P}$-position.
-/
theorem misereOutcome_add_liftSucc_adjoint_eq_P (x : AugmentedForm.{u}) :
    MisereOutcome (liftSucc x + liftSucc (adjoint x)) = Outcome.P :=
  by
  rw [← liftSucc_add, misereOutcome_liftSucc]
  exact misereOutcome_add_adjoint_eq_P x


-- @@ L91-110 expanded
/-- For all games in universe $u$ and $G$ in $u + 1$, $\operatorname{o}(G + X) =
\mathscr{N}$.
-/
theorem misereOutcome_g_add_lift (x : AugmentedForm.{u}) :
    MisereOutcome (g + liftSucc x) = Outcome.N :=
  by
  rw [add_comm, misereOutcome_N_iff_winsGoingFirst]
  constructor <;> apply winsGoingFirst_of_moves
  · use liftSucc x + liftSucc (adjoint x)
    constructor
    · apply add_left_mem_moves_add
      exact moves_g Player.left ▸ liftAdjoint_mem_adjointsOfSmall x
    · apply not_winsGoingFirst_of_misereOutcome_P
      exact misereOutcome_add_liftSucc_adjoint_eq_P x
  · use liftSucc x + liftSucc (adjoint x)
    constructor
    · apply add_left_mem_moves_add
      exact moves_g Player.right ▸ liftAdjoint_mem_adjointsOfSmall x
    · apply not_winsGoingFirst_of_misereOutcome_P
      exact misereOutcome_add_liftSucc_adjoint_eq_P x


-- @@ L112-131 expanded
/-- For all games in universe $u$ and $H$ in $u + 1$, $\operatorname{o}(G + X) =
\mathscr{N}$.
-/
theorem misereOutcome_h_add_lift (x : AugmentedForm.{u}) :
    MisereOutcome (h + liftSucc x) = Outcome.N :=
  by
  rw [add_comm, misereOutcome_N_iff_winsGoingFirst]
  constructor <;> apply winsGoingFirst_of_moves
  · use liftSucc x + liftSucc (adjoint x)
    constructor
    · apply add_left_mem_moves_add
      exact moves_h Player.left ▸ Set.mem_insert_of_mem _ (liftAdjoint_mem_adjointsOfSmall x)
    · apply not_winsGoingFirst_of_misereOutcome_P
      exact misereOutcome_add_liftSucc_adjoint_eq_P x
  · use liftSucc x + liftSucc (adjoint x)
    constructor
    · apply add_left_mem_moves_add
      exact moves_h Player.right ▸ Set.mem_insert_of_mem _ (liftAdjoint_mem_adjointsOfSmall x)
    · apply not_winsGoingFirst_of_misereOutcome_P
      exact misereOutcome_add_liftSucc_adjoint_eq_P x


-- @@ L133-138 verbatim
/--
Lift a set on `AugmentedForm.{u}` to one on `AugmentedForm.{u + 1}` via the
range of `AugmentedForm.liftSucc`.
-/
def liftSet (A : AugmentedForm.{u} → Prop) : AugmentedForm.{u + 1} → Prop :=
  fun x => ∃ y, A y ∧ liftSucc y = x


-- @@ L140-148 expanded
/-- If $G, H$ are in universe $u$ then there are indistinguishable modulo set
$\mathcal{A}$ lifted to $u + 1$.
-/
theorem g_misereEQ_h_lift (A : AugmentedForm.{u} → Prop) : MisereEQ (liftSet A) g h :=
  by
  intro x ⟨y, h_Uy, h_eq⟩
  subst h_eq
  rw [misereOutcome_g_add_lift, misereOutcome_h_add_lift]


-- @@ L150-172 expanded
private theorem not_winsGoingFirst_g_add_g {p : Player} : ¬WinsGoingFirst p (g + g) :=
  by
  rw [not_winsGoingFirst_iff]
  · constructor
    · simp [g_not_isEndLike]
    · intro g' h_g'_mem
      simp only [moves_add, moves_g, Set.mem_union, Set.mem_image] at h_g'_mem
      obtain (⟨x, ⟨y, rfl⟩, rfl⟩ | ⟨x, ⟨y, rfl⟩, rfl⟩) := h_g'_mem
      · apply winsGoingFirst_of_moves
        use liftSucc (adjoint y) + liftSucc (adjoint (adjoint y))
        constructor
        · apply add_left_mem_moves_add
          exact moves_g _ ▸ liftAdjoint_mem_adjointsOfSmall (adjoint y)
        · apply not_winsGoingFirst_of_misereOutcome_P
          exact misereOutcome_add_liftSucc_adjoint_eq_P (adjoint y)
      · rw [add_comm]
        apply winsGoingFirst_of_moves
        use liftSucc (adjoint y) + liftSucc (adjoint (adjoint y))
        constructor
        · apply add_left_mem_moves_add
          exact moves_g _ ▸ liftAdjoint_mem_adjointsOfSmall (adjoint y)
        · apply not_winsGoingFirst_of_misereOutcome_P
          exact misereOutcome_add_liftSucc_adjoint_eq_P (adjoint y)


-- @@ L174-178 verbatim
/--
$o(G + G) = \mathscr{P}$
-/
theorem misereOutcome_g_add_g : MisereOutcome (g + g) = Outcome.P := by
  simp [misereOutcome_P_iff_winsGoingFirst, not_winsGoingFirst_g_add_g]


-- @@ L180-193 verbatim
/--
$\operatorname{o}(H + G) = \mathscr{N}$.
-/
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


-- @@ L195-204 expanded
/-- $G$ and $H$ are incomparable modulo any set $\mathcal{A}$ in $u + 1$.
-/
theorem g_h_incomparable {A : AugmentedForm.{u + 1} → Prop} (h_Ag : A g) :
    ¬(MisereGE A g h) ∧ ¬(MisereGE A h g) :=
  by
  constructor
  all_goals
    · intro h
      have := h _ h_Ag
      simp +decide only [misereOutcome_g_add_g, misereOutcome_h_add_g, ge_iff_le] at this


-- @@ L206-221 expanded
/-- $G$ is in any universe $\mathcal{U}$ in $u + 1$.
-/
theorem g_mem_longUniverse (U : AugmentedForm.{u + 1} → Prop) [LongUniverse U] : U g :=
  by
  have h_ambient : Ambient (IsLong : AugmentedForm.{u + 1} → Prop) := inferInstance
  have h_mem : ∀ b ∈ adjointsOfSmall.{u}, U b :=
    by
    rintro b ⟨J, rfl⟩
    simp only [liftSucc_adjoint]
    exact
      Form.rootedAdjoint_mem_of_isAmbient (IsAmbient := IsLong) (A := U) (r := 0)
        (Universe.zero_mem IsLong) (fun _ _ => isLong _) (isLong _)
  have h_notempty : (adjointsOfSmall.{u}).Nonempty := ⟨_, liftAdjoint_mem_adjointsOfSmall 0⟩
  change
    U
      (OfSets.ofSets (Player.cases adjointsOfSmall adjointsOfSmall)
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid"))
  exact
    ClosedUnderDicotic.closed_dicotic (IsAmbient := IsLong) adjointsOfSmall adjointsOfSmall h_mem
      h_mem h_notempty h_notempty (isLong _)


-- @@ L223-228 expanded
/-- $G$ and $H$ are incomparable modulo any universe $\mathcal{U}$ in $u + 1$.
-/
theorem g_h_incomparable_longUniverse (U : AugmentedForm.{u + 1} → Prop) [LongUniverse U] :
    ¬(MisereGE U g h) ∧ ¬(MisereGE U h g) :=
  g_h_incomparable (g_mem_longUniverse U)


-- @@ L230-230 verbatim
end


-- @@ L232-232 verbatim
end AugmentedForm


-- @@ L234-234 verbatim
end MisereGames
