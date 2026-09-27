/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Junyan Xu
-/
module

public import LeanPool.MisereGames.Form


-- @@ L10-12 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L14-14 verbatim
namespace MisereGames


-- @@ L16-34 verbatim
/-!
# Combinatorial games from a type of states

In the literature, games are often described in terms of their *game graphs*,
which can be thought of as (not necessarily properly) 2-edge-coloured rooted
arborescences. Or more informally as a set of states with move relations for
Left and Right (the two players).

We define a structure `GameGraph` that facilitates this viewpoint, bundling the
Left and Right option set functions along with the type, as well as
`GameGraph.toForm`, which turns the graph into the relevant type of game form.

## Design notes

When working with any "specific" game (Nim, Domineering, Hackenbush, et
cetera), one can use `GameGraph` to set up the basic theorems and definitions,
but the intent is that one need not work with `GameGraph` directly most of the
time.
-/


-- @@ L36-36 verbatim
universe u v


-- @@ L38-38 verbatim
public noncomputable section


-- @@ L40-40 verbatim
open Form Set


-- @@ L42-42 verbatim
variable {α : Type v}


-- @@ L44-53 verbatim
/--
A game graph is a type of states endowed with option sets for Left and Right.

Use `GameGraph.toForm` to turn this structure into the appropriate game type.
-/
structure GameGraph (α : Type v) : Type v where
  /--
  The sets of options for the players.
  -/
  moves : Player → α → Set α


-- @@ L55-55 verbatim
namespace GameGraph


-- @@ L57-57 verbatim
variable {g : GameGraph.{v} α}


-- @@ L59-59 verbatim
variable [Hl : ∀ a, Small.{u} (g.moves .left a)] [Hr : ∀ a, Small.{u} (g.moves .right a)]


-- @@ L61-63 verbatim
/-!
### Well-founded games
-/


-- @@ L65-72 verbatim
/--
A game graph is well-founded if from every position there is no infinite
sequence of (not necessarily alternating) Left and Right moves. In the
literature, such a game is called *loopfree* (see [Siegel, Definition 4.1 on p.
34][siegel:CombinatorialGameTheory:2013]).
-/
protected class IsWellFounded (c : GameGraph α) where
  wf (c) : WellFounded fun a b => ∃ p, a ∈ c.moves p b


-- @@ L74-78 verbatim
omit Hl Hr in
theorem IsWellFounded.of_subrelation (r : α → α → Prop) [WellFounded r]
    (hr : ∀ a b p, a ∈ g.moves p b → r a b) : g.IsWellFounded := by
  refine ⟨Subrelation.isWellFounded (r := r) ?_⟩
  simpa only [Subrelation, forall_exists_index]


-- @@ L80-80 verbatim
variable [g.IsWellFounded]


-- @@ L82-90 verbatim
/--
**Conway induction**: build data for a game by recursively building it on its
Left and Right sets.
-/
@[elab_as_elim]
def moveRecOn {motive : α → Sort*} (x)
    (ind : Π x : α, (∀ p, Π y ∈ g.moves p x, motive y) → motive x) :
    motive x :=
  (IsWellFounded.wf g).fix (fun x IH ↦ ind x fun _ _ h ↦ IH _ ⟨_, h⟩) x


-- @@ L92-97 verbatim
omit Hl Hr in
theorem moveRecOn_eq {motive : α → Sort*} (x)
    (ind : Π x : α, (∀ p, Π y ∈ g.moves p x, motive y) → motive x) :
    g.moveRecOn x ind = ind x fun _ y _ ↦ g.moveRecOn y ind := by
  rw [moveRecOn, WellFounded.fix_eq]
  rfl


-- @@ L99-99 verbatim
variable {G : Type (u + 1)} [Form G]


-- @@ L101-105 expanded
/-- Turns a state of a `GameGraph` into a `Form`.
-/
def toForm (a : α) : G :=
  g.moveRecOn a fun x IH ↦
    OfSets.ofSets (fun p ↦ .range fun b : g.moves p x ↦ IH p b b.2)
      (by
        first
        | done
        | trivial
        | assumption
        | aesop
        |
          fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
            where `h` is a proof that sets are valid")


-- @@ L107-109 expanded
theorem toForm_def' (a : α) :
    g.toForm a =
      (OfSets.ofSets (fun p ↦ g.toForm '' g.moves p a)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") :
        G) :=
  by rw [toForm, moveRecOn_eq]; simp only [toForm, image_eq_range]


-- @@ L111-113 expanded
theorem toForm_def (a : α) :
    g.toForm a =
      (OfSets.ofSets (Player.cases (g.toForm '' g.moves .left a) (g.toForm '' g.moves .right a))
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") :
        G) :=
  by rw [toForm_def', ofSets_eq_ofSets_cases]


-- @@ L115-118 verbatim
@[simp]
theorem moves_toForm (p : Player) (a : α) :
    Form.moves p (g.toForm a) = g.toForm (G := G) '' g.moves p a := by
  rw [toForm_def']; simp


-- @@ L120-123 verbatim
theorem mem_moves_toForm_of_mem (p : Player) {a b : α} (hab : b ∈ g.moves p a) :
    g.toForm b ∈ Form.moves p (g.toForm (G := G) a) := by
  rw [moves_toForm]
  exact ⟨b, hab, rfl⟩


-- @@ L125-125 verbatim
end GameGraph

-- @@ L126-126 verbatim
end


-- @@ L128-128 verbatim
end MisereGames
