/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Form


-- @@ L10-12 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L14-14 verbatim
namespace MisereGames


-- @@ L16-16 verbatim
universe u


-- @@ L18-18 verbatim
public section


-- @@ L20-20 verbatim
namespace Form


-- @@ L22-22 verbatim
variable {G : Type (u + 1)} [Form G]


-- @@ L24-28 verbatim
/--
The ambient space of all games, imposing no restriction. This is the
counterpart of `IsShort`.
-/
@[expose] def IsLong (x : G) : Prop := x = x


-- @@ L30-31 verbatim
omit [Form G] in
theorem isLong (g : G) : IsLong g := rfl


-- @@ L33-35 verbatim
/-- A set of forms containing zero. -/
class HasZero (A : G → Prop) where
  has_zero : A (0 : G)


-- @@ L37-39 verbatim
/-- A set of forms containing all natural-number games. -/
class HasNat (A : G → Prop) where
  has_nat (n : ℕ) : A (n : G)


-- @@ L41-43 verbatim
/-- A set of forms containing all integer games. -/
class HasInt (A : G → Prop) where
  has_int (n : ℤ) : A (n : G)


-- @@ L45-46 verbatim
instance {A : G → Prop} [HasNat A] : HasZero A where
  has_zero := by exact_mod_cast HasNat.has_nat (A := A) 0


-- @@ L48-49 verbatim
instance {A : G → Prop} [HasInt A] : HasNat A where
  has_nat n := HasInt.has_int n


-- @@ L51-52 verbatim
instance : HasInt (IsLong : G → Prop) where
  has_int _ := isLong _


-- @@ L54-56 verbatim
theorem HasInt.has_neg_int {A : G → Prop} [HasInt A] (n : ℕ) : A (-(n : G)) := by
  have hi := HasInt.has_int (A := A) (-(n : ℤ))
  rwa [Form.intCast_neg, Form.intCast_nat] at hi


-- @@ L58-60 verbatim
theorem HasNat.zero {A : G → Prop} [HasNat A] : A 0 := by
  rw [<-Nat.cast_zero]
  exact HasNat.has_nat 0


-- @@ L62-64 verbatim
theorem HasNat.one {A : G → Prop} [HasNat A] : A 1 := by
  rw [<-Nat.cast_one]
  exact HasNat.has_nat 1


-- @@ L66-68 verbatim
/-- A set of forms closed under adding natural-number games on the right. -/
class ClosedUnderAddNat {G : Type (u + 1)} [Form G] (A : G → Prop) where
  has_add {g : G} (h1 : A g) (n : ℕ) : A (g + n)


-- @@ L70-71 verbatim
instance : ClosedUnderAddNat (IsLong : G → Prop) where
  has_add _ _ := isLong _


-- @@ L73-75 verbatim
/-- A set of forms closed under addition. -/
class ClosedUnderAdd (A : G → Prop) where
  has_add (g h : G) (h_g : A g) (h_h : A h) : A (g + h)


-- @@ L77-78 verbatim
instance : ClosedUnderAdd (IsLong : G → Prop) where
  has_add _ _ _ _ := isLong _


-- @@ L80-80 verbatim
variable {A : G → Prop}


-- @@ L82-84 verbatim
/-- A set of forms closed under passing to options. -/
class Hereditary (A : G → Prop) where
  has_option {g g' : G} (h1 : A g) (h2 : Moves.IsOption g' g) : A g'


-- @@ L86-88 verbatim
theorem Hereditary.of_mem_moves {A : G → Prop} [Hereditary A]
  {p : Player} {g g' : G} (hA : A g) (h_mem : g' ∈ moves p g) : A g' :=
  Hereditary.has_option hA (IsOption.of_mem_moves h_mem)


-- @@ L90-91 verbatim
instance : Hereditary (IsLong : G → Prop) where
  has_option _ _ := isLong _


-- @@ L93-102 expanded
private theorem exists_isZeroLike_of_mem [Hereditary A] {g : G} (hg : A g) :
    ∃ z, A z ∧ IsZeroLike z := by
  by_cases hz : IsZeroLike g
  · exact ⟨g, hg, hz⟩
  · simp only [IsZeroLike, not_forall] at hz
    obtain ⟨p, hp⟩ := hz
    obtain ⟨gp, hgp⟩ := not_isEnd_exists_move hp
    exact exists_isZeroLike_of_mem (Hereditary.of_mem_moves hg hgp)
termination_by g
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L104-109 verbatim
/--
A nonempty hereditary set of forms contains a zero-like form.
-/
theorem exists_isZeroLike [Hereditary A] (h : ∃ g, A g) : ∃ z, A z ∧ IsZeroLike z :=
  let ⟨_, hg⟩ := h
  exists_isZeroLike_of_mem hg


-- @@ L111-113 verbatim
/-- A set of forms closed under conjugation. -/
class ClosedUnderNeg (A : G → Prop) where
  neg_of {g : G} (h1 : A g) : A (-g)


-- @@ L115-116 verbatim
instance : ClosedUnderNeg (IsLong : G → Prop) where
  neg_of _ := isLong _


-- @@ L118-124 verbatim
theorem ClosedUnderNeg.neg_iff {A : G → Prop} [ClosedUnderNeg A] {g : G}
    : A (-g) ↔ A g := by
  constructor
  · intro h1
    have h2 := ClosedUnderNeg.neg_of h1
    rwa [neg_neg (G := G)] at h2
  · exact ClosedUnderNeg.neg_of


-- @@ L126-130 verbatim
theorem HasInt.of_hasNat {A : G → Prop} [HasNat A] [ClosedUnderNeg A] : HasInt A where
  has_int n := by
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
    · simpa using HasNat.has_nat (A := A) k
    · simpa using ClosedUnderNeg.neg_of (HasNat.has_nat (A := A) k)


-- @@ L132-137 verbatim
theorem ClosedUnderAddNat.has_add_neg {A : G → Prop} [ClosedUnderAddNat A] [ClosedUnderNeg A]
    {g : G} (hAg : A g) (n : ℕ) :
    A (g + (-n)) := by
  have := ClosedUnderNeg.neg_of (ClosedUnderAddNat.has_add (ClosedUnderNeg.neg_of hAg) n)
  simp only [neg_add_rev, neg_neg] at this
  rwa [add_comm] at this


-- @@ L139-153 verbatim
theorem ClosedUnderAddNat.has_add_int {A :
    G → Prop} [ClosedUnderAddNat A] [ClosedUnderNeg A]
    {g : G} (hAg : A g) (n : ℤ) :
    A (g + n) := by
  match n with
  | .ofNat k =>
    simp only [Int.ofNat_eq_natCast, Form.intCast_nat]
    exact ClosedUnderAddNat.has_add hAg k
  | .negSucc k =>
    simp only [Form.intCast_negSucc, neg_add_rev]
    rw [<-Form.intCast_one, <-add_assoc, <-sub_eq_add_neg g, Form.intCast_ofNat, sub_eq_add_neg]
    have := ClosedUnderNeg.neg_of (ClosedUnderAddNat.has_add (ClosedUnderNeg.neg_of hAg) 1)
    simp only [neg_add_rev, neg_neg] at this
    rw [add_comm] at this
    exact ClosedUnderAddNat.has_add_neg this k


-- @@ L155-161 verbatim
theorem ClosedUnderAddNat.has_add_int_neg {A :
    G → Prop} [ClosedUnderAddNat A] [ClosedUnderNeg A]
    {g : G} (hAg : A g) (n : ℤ) :
    A (g + (-n)) := by
  have := ClosedUnderNeg.neg_of (ClosedUnderAddNat.has_add_int (ClosedUnderNeg.neg_of hAg) n)
  simp only [neg_add_rev, neg_neg] at this
  rwa [add_comm] at this


-- @@ L163-163 verbatim
end Form


-- @@ L165-165 verbatim
end


-- @@ L167-167 verbatim
end MisereGames
