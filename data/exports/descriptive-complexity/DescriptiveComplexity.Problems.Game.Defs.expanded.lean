/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Vocabulary
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Problems.Reachability


-- @@ L10-46 verbatim
/-!
# GAME: alternating reachability

The natural PTIME-complete problem the catalog was missing. An **AND/OR graph**
is a directed graph whose nodes are split between two players, together with a
set of nodes that win outright; a node is *winning* when

* it wins outright, or
* it belongs to the existential player and **some** successor is winning, or
* it belongs to the universal player, it **has** a successor, and **every**
  successor is winning.

`DescriptiveComplexity.GAME` asks whether some marked source is winning. Reading
the three clauses with the universal player removed gives
`DescriptiveComplexity.REACH` back, so this is alternating reachability in the
same sense that `DescriptiveComplexity.PSPACE` is `DescriptiveComplexity.NL`
with alternation: one operator more, one class up.

## The stuck-universal convention

A universal node with no successor **loses**. The other convention – vacuous
universal quantification, so that a stuck universal node wins – is equally
standard; this one is chosen because it is the convention
`DescriptiveComplexity.ATMData.AltWin` already uses, and matching them is what
lets the alternating machine's configuration graph be read as an instance of
this problem with nothing to adjust. A node that *should* win vacuously is
marked as winning outright instead, which is what the reduction from HORN-SAT
does with a clause that has no body.

## Winning as an inductive predicate

`DescriptiveComplexity.WinsOn` is an inductive predicate, i.e., the least fixed
point of the game operator, so an infinite play is a loss for the existential
player. That is also the presentation the FO(LFP) membership proof mirrors
clause by clause – with one twist, since a Horn rule cannot carry a universally
quantified body atom; see `DescriptiveComplexity.Problems.Game.Membership`.
-/


-- @@ L48-48 verbatim
namespace FirstOrder


-- @@ L50-50 verbatim
namespace Language


-- @@ L52-63 verbatim
/-- The relational vocabulary of AND/OR graphs: a move relation, a mark for the
nodes of the universal player, a mark for the starting positions and a mark for
the positions that win outright. -/
fo_language andOrGraph with ag where
  /-- `move a b`: the player to move at `a` may move to `b`. -/
  move : 2
  /-- `univ a`: the node `a` belongs to the universal player. -/
  univ : 1
  /-- `start a`: the node `a` is a marked starting position. -/
  start : 1
  /-- `won a`: the node `a` wins outright. -/
  won : 1


-- @@ L65-66 verbatim
/-- The move symbol in the ordered expansion. -/
abbrev agMoveO : (Language.andOrGraph.sum Language.order).Relations 2 := Sum.inl agMove


-- @@ L68-69 verbatim
/-- The universal-player symbol in the ordered expansion. -/
abbrev agUnivO : (Language.andOrGraph.sum Language.order).Relations 1 := Sum.inl agUniv


-- @@ L71-72 verbatim
/-- The marked-start symbol in the ordered expansion. -/
abbrev agStartO : (Language.andOrGraph.sum Language.order).Relations 1 := Sum.inl agStart


-- @@ L74-75 verbatim
/-- The won-outright symbol in the ordered expansion. -/
abbrev agWonO : (Language.andOrGraph.sum Language.order).Relations 1 := Sum.inl agWon


-- @@ L77-77 verbatim
end Language


-- @@ L79-79 verbatim
end FirstOrder


-- @@ L81-81 verbatim
namespace DescriptiveComplexity


-- @@ L83-83 verbatim
open FirstOrder


-- @@ L85-85 verbatim
open Language Structure


-- @@ L87-87 verbatim
/-! ### The semantics -/


-- @@ L89-89 verbatim
section Defs


-- @@ L91-91 verbatim
variable {A : Type} [Language.andOrGraph.Structure A]


-- @@ L93-93 verbatim
fo_predicates Language.andOrGraph ag


-- @@ L95-106 verbatim
variable (A) in
/-- **The winning positions of an AND/OR graph**, as a least fixed point: a
position that wins outright, an existential position with a winning successor,
or a universal position that has a successor and all of whose successors
win. -/
inductive WinsOn : A → Prop
  /-- A position that wins outright. -/
  | won {a : A} : AGWon a → WinsOn a
  /-- An existential position with a winning successor. -/
  | ex {a b : A} : ¬AGUniv a → AGMove a b → WinsOn b → WinsOn a
  /-- A universal position with a successor, all of whose successors win. -/
  | all {a : A} : AGUniv a → (∃ b, AGMove a b) → (∀ b, AGMove a b → WinsOn b) → WinsOn a


-- @@ L108-110 verbatim
variable (A) in
/-- Some marked starting position is winning. -/
def GameWon : Prop := ∃ s : A, AGStart s ∧ WinsOn A s


-- @@ L112-112 verbatim
end Defs


-- @@ L114-114 verbatim
/-! ### Without the universal player, the game is reachability -/


-- @@ L116-116 verbatim
section Collapse


-- @@ L118-118 verbatim
variable {A : Type} [Language.andOrGraph.Structure A]


-- @@ L120-120 verbatim
end Collapse


-- @@ L122-122 verbatim
/-! ### Isomorphism-invariance -/


-- @@ L124-124 verbatim
section Iso


-- @@ L126-126 verbatim
variable {A B : Type} [Language.andOrGraph.Structure A] [Language.andOrGraph.Structure B]


-- @@ L128-130 verbatim
private theorem agMove_map (e : A ≃[Language.andOrGraph] B) (a b : A) :
    AGMove a b ↔ AGMove (e a) (e b) :=
  relMap_equiv₂ e agMove a b


-- @@ L132-144 verbatim
private theorem winsOn_of_iso (e : A ≃[Language.andOrGraph] B) {a : A} (h : WinsOn A a) :
    WinsOn B (e a) := by
  induction h with
  | won hw => exact .won ((relMap_equiv₁ e agWon _).mp hw)
  | @ex a b hu hm _ ih =>
    exact .ex (fun hc => hu ((relMap_equiv₁ e agUniv a).mpr hc)) ((agMove_map e a b).mp hm) ih
  | @all a hu hex _ ih =>
    refine .all ((relMap_equiv₁ e agUniv a).mp hu) ?_ ?_
    · obtain ⟨b, hb⟩ := hex
      exact ⟨e b, (agMove_map e a b).mp hb⟩
    · intro b hb
      obtain ⟨b₀, rfl⟩ : ∃ b₀ : A, e b₀ = b := ⟨e.symm b, e.toEquiv.apply_symm_apply b⟩
      exact ih b₀ ((agMove_map e a b₀).mpr hb)


-- @@ L146-148 verbatim
private theorem gameWon_of_iso (e : A ≃[Language.andOrGraph] B) (h : GameWon A) : GameWon B := by
  obtain ⟨s, hs, hw⟩ := h
  exact ⟨e s, (relMap_equiv₁ e agStart s).mp hs, winsOn_of_iso e hw⟩


-- @@ L150-152 verbatim
/-- Being won is isomorphism-invariant. -/
theorem gameWon_iso (e : A ≃[Language.andOrGraph] B) : GameWon A ↔ GameWon B :=
  ⟨gameWon_of_iso e, gameWon_of_iso e.symm⟩


-- @@ L154-154 verbatim
end Iso


-- @@ L156-160 verbatim
/-- **GAME**, alternating reachability: is some marked starting position of the
AND/OR graph winning? -/
def GAME : DecisionProblem Language.andOrGraph where
  Holds := fun A inst => @GameWon A inst
  iso_invariant := fun e => gameWon_iso e


-- @@ L162-165 verbatim
@[simp]
theorem game_holds_iff (A : Type) [Language.andOrGraph.Structure A] :
    GAME A ↔ GameWon A :=
  Iff.rfl


-- @@ L167-167 verbatim
end DescriptiveComplexity
