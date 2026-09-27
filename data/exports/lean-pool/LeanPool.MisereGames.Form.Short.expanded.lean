/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski, Kim Morrison, Violeta Hernández Palacios
-/
module

public import LeanPool.MisereGames.Form.Classes
import Mathlib.Data.Fintype.Order
public import LeanPool.MisereGames.Form.Birthday
public import LeanPool.MisereGames.GameForm
import LeanPool.MisereGames.GameForm.Birthday
import Mathlib.Order.Lattice.Nat


-- @@ L15-17 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L19-19 verbatim
namespace MisereGames


-- @@ L21-27 verbatim
/-!
# Short games

A combinatorial game is `Short` if it is finite and loopfree: it has only
finite many distinct subpositions, and every run has finite length. See
[Siegel, Definition 4.1 on p. 34][siegel:CombinatorialGameTheory:2013].
-/


-- @@ L29-29 verbatim
universe u


-- @@ L31-31 verbatim
public section


-- @@ L33-33 verbatim
namespace Form


-- @@ L35-35 verbatim
open Form

-- @@ L36-36 verbatim
open GameForm


-- @@ L38-38 verbatim
variable {G : Type (u + 1)} [Form G]


-- @@ L40-44 expanded
/-- Short forms have finitely many options, all of which are short. -/
def IsShort (x : G) : Prop :=
  ∀ p, (Moves.moves p x).Finite ∧ ∀ y ∈ Moves.moves p x, IsShort y
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L46-48 verbatim
theorem short_def {x : G}
    : IsShort x ↔ ∀ p, (Moves.moves p x).Finite ∧ ∀ y ∈ Moves.moves p x, IsShort y := by
  rw [IsShort]


-- @@ L50-50 verbatim
alias ⟨_, Short.mk⟩ := short_def


-- @@ L52-52 verbatim
namespace Short


-- @@ L54-55 verbatim
theorem finite_moves (p : Player) {x : G} (hx : IsShort x) : (Moves.moves p x).Finite :=
  (short_def.mp hx p).left


-- @@ L57-58 verbatim
theorem finite_moves' (p : Player) {x : G} (hx : IsShort x) : Finite ↑(moves p x) :=
  finite_moves p hx


-- @@ L60-62 verbatim
theorem finite_setOf_isOption {x : G} (hx : IsShort x) : {y | Moves.IsOption y x}.Finite := by
  simp_rw [Moves.IsOption.iff_mem_union]
  exact (finite_moves _ hx).union (finite_moves _ hx)


-- @@ L64-66 verbatim
protected theorem of_mem_moves {x y : G} (hx : IsShort x) {p} (hy : y ∈ Moves.moves p x) :
    IsShort y :=
  (short_def.mp hx p).right y hy


-- @@ L68-72 verbatim
protected theorem isOption {x y : G} (hx : IsShort x) (h : Moves.IsOption y x) : IsShort y := by
  rw [Moves.IsOption.iff_mem_union] at h
  cases h with
  | inl h => exact Short.of_mem_moves hx h
  | inr h => exact Short.of_mem_moves hx h


-- @@ L74-74 verbatim
alias _root_.Moves.IsOption.short := Short.isOption


-- @@ L76-81 expanded
protected theorem subposition {x y : G} (hx : IsShort x) (h : Subposition y x) : IsShort y := by
  cases h with
  | single h => exact Short.isOption hx h
  | tail IH h => have hx' := Short.isOption hx h; exact Short.subposition hx' IH
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L83-83 verbatim
alias _root_.Moves.IsOption.subposition := Short.subposition


-- @@ L85-95 expanded
theorem finite_setOf_subposition {x : G} (hx : IsShort x) : {y | Moves.Subposition y x}.Finite :=
  by
  have :
    {y | Moves.Subposition y x} =
      {y | Moves.IsOption y x} ∪ ⋃ y ∈ {y | Moves.IsOption y x}, {z | Moves.Subposition z y} :=
    by
    ext
    rw [Set.mem_ofPred_eq, Moves.Subposition, Relation.transGen_iff]
    simp [and_comm]
  rw [this]
  refine (finite_setOf_isOption hx).union <| (finite_setOf_isOption hx).biUnion fun y hy ↦ ?_
  exact finite_setOf_subposition (Short.isOption hx hy)
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L97-104 expanded
theorem _root_.Moves.short_iff_finite_setOf_subposition {x : G} :
    IsShort x ↔ {y | Moves.Subposition y x}.Finite :=
  by
  refine ⟨@finite_setOf_subposition _ _ x, fun h ↦ mk fun p ↦ ⟨?_, ?_⟩⟩
  on_goal 1 => refine h.subset fun y hy ↦ ?_
  on_goal 2 => refine fun y hy ↦ short_iff_finite_setOf_subposition.2 <| h.subset fun z hz ↦ ?_
  all_goals
    all_goals
      solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left,
        PSigma.Lex.right, Subposition.of_mem_moves, Subposition.trans, Subtype.prop]
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L106-115 expanded
protected theorem add {x y : G} (hx : IsShort x) (hy : IsShort y) : IsShort (x + y) :=
  by
  refine Short.mk fun p ↦ ⟨?_, ?_⟩
  · rw [moves_add]
    simpa using ⟨(Short.finite_moves _ hx).image _, (Short.finite_moves _ hy).image _⟩
  · intro z hz; change z ∈ moves p (x + y) at hz; rw [moves_add] at hz
    cases hz with
    | inl h => obtain ⟨a, ha, rfl⟩ := h; exact Short.add (Short.of_mem_moves hx ha) hy
    | inr h => obtain ⟨b, hb, rfl⟩ := h; exact Short.add hx (Short.of_mem_moves hy hb)
termination_by (x, y)
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L117-125 expanded
protected theorem neg {x : G} (hx : IsShort x) : IsShort (-x) :=
  by
  rw [short_def]; intro p; constructor
  · rw [moves_neg]
    simpa [← Set.image_neg_eq_neg] using (Short.finite_moves _ hx).image _
  · intro y hy; change y ∈ moves p (-x) at hy; rw [moves_neg] at hy
    have h_neg_y : -y ∈ moves (-p) x := by rwa [Set.mem_neg] at hy
    simpa using Short.neg (Short.of_mem_moves hx h_neg_y)
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L127-128 verbatim
instance : ClosedUnderNeg (IsShort (G := G)) where
  neg_of := Short.neg


-- @@ L130-131 verbatim
instance : Hereditary IsShort (G := G) where
  has_option := Moves.IsOption.short


-- @@ L133-133 verbatim
protected theorem neg_iff {x : G} : IsShort (-x) ↔ IsShort x := ClosedUnderNeg.neg_iff


-- @@ L135-139 verbatim
theorem short_iff_finite_setOf_subposition {x : G} :
    IsShort x ↔ {y | Subposition y x}.Finite := by
  constructor <;> intro h1
  · apply finite_setOf_subposition h1
  · exact Moves.short_iff_finite_setOf_subposition.mpr h1


-- @@ L141-144 verbatim
@[simp]
protected theorem zero : IsShort (0 : G) := by
  rw [Form.short_def]
  simp


-- @@ L146-147 verbatim
instance : HasZero IsShort (G := G) where
  has_zero := Short.zero


-- @@ L149-157 expanded
protected theorem ofSets {s t : Set G} [Small s] [Small t] (hs_fin : s.Finite)
    (hs_short : ∀ g ∈ s, IsShort g) (ht_fin : t.Finite) (ht_short : ∀ g ∈ t, IsShort g) :
    IsShort
      (OfSets.ofSets (Player.cases s t)
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid")) :=
  by
  rw [short_def]
  intro p
  cases p
  · exact ⟨by simpa using hs_fin, by simpa using hs_short⟩
  · exact ⟨by simpa using ht_fin, by simpa using ht_short⟩


-- @@ L159-165 expanded
@[simp]
protected theorem star :
    IsShort
      (OfSets.ofSets (Player.cases {0} {0})
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
  by
  apply Short.ofSets
  · exact Set.finite_singleton 0
  · simp_all
  · exact Set.finite_singleton 0
  · simp_all


-- @@ L167-170 verbatim
@[simp]
protected theorem one : IsShort (1 : G) := by
  rw [one_def, Form.short_def]
  simp_all


-- @@ L172-173 verbatim
protected theorem sub {x y : GameForm} (hx : IsShort x) (hy : IsShort y) : IsShort (x - y) :=
  Short.add hx (Short.neg hy)


-- @@ L175-178 verbatim
@[simp]
protected theorem natCast : ∀ n : ℕ, IsShort (n : G)
  | 0 =>  Short.zero
  | n + 1 => Short.add (Short.natCast n) Short.one


-- @@ L180-182 verbatim
@[simp]
protected theorem ofNat (n : ℕ) [n.AtLeastTwo] : IsShort (ofNat(n) : G) :=
  Short.natCast n


-- @@ L184-187 verbatim
@[simp]
protected theorem intCast : ∀ n : ℤ, IsShort (n : G)
  | .ofNat n => Short.natCast n
  | .negSucc n => Short.neg (Short.natCast (n + 1))


-- @@ L189-189 verbatim
end Short

-- @@ L190-190 verbatim
end Form


-- @@ L192-192 verbatim
namespace GameForm


-- @@ L194-194 verbatim
open Form


-- @@ L196-214 expanded
theorem short_iff_birthday_finite {g : GameForm} :
    IsShort g ↔ birthday g < NatOrdinal.of Ordinal.omega0 :=
  by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have (y : { y // IsOption y g }) : ∃ n : ℕ, birthday y.val = n :=
      by
      rw [← NatOrdinal.lt_omega0, ← short_iff_birthday_finite]
      exact Short.isOption h y.prop
    choose f hf using this
    have : Finite { y // IsOption y g } := (Short.finite_setOf_isOption h).to_subtype
    obtain ⟨n, hn⟩ := (Set.finite_range f).exists_le
    apply lt_of_le_of_lt _ (NatOrdinal.nat_lt_omega0 (n + 1))
    rw [birthday_le_iff', Nat.cast_add_one]
    simp only [Order.lt_add_one_iff]
    aesop
  · rw [NatOrdinal.lt_omega0, Form.Short.short_iff_finite_setOf_subposition]
    intro ⟨n, hn⟩
    apply (birthdayFinset n).finite_toSet.subset fun y hy ↦ ?_
    exact (mem_birthdayFinset (x := y) (n := n)).2 ((birthday_lt_of_subposition hy).le.trans_eq hn)
termination_by g
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L216-218 verbatim
theorem short_iff_birthday_nat {x : GameForm} :
    IsShort x ↔ (∃ (n : ℕ), birthday x = n) := by
  rw [short_iff_birthday_finite, NatOrdinal.lt_omega0]


-- @@ L220-220 verbatim
end GameForm


-- @@ L222-222 verbatim
end


-- @@ L224-224 verbatim
end MisereGames
