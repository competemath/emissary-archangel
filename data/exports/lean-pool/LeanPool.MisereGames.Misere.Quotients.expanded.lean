/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import LeanPool.MisereGames.Form.Misere.Outcome
import Mathlib.Tactic.Bound.Init


-- @@ L12-14 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L16-16 verbatim
namespace MisereGames


-- @@ L18-18 verbatim
universe u


-- @@ L20-20 verbatim
variable {G : Type (u + 1)} [Form G]


-- @@ L22-22 verbatim
open Form

-- @@ L23-23 verbatim
open Form.Misere.Outcome


-- @@ L25-25 verbatim
public noncomputable section


-- @@ L27-33 expanded
/-- Restricted misère equality modulo `A`, as a setoid on `A`'s games.
-/
@[expose]
def MisereSetoid (A : G → Prop) : Setoid { g : G // A g }
    where
  r g h := MisereEQ A (g : G) (h : G)
  iseqv := ⟨fun _ _ _ => rfl, MisereEQ.symm, MisereEQ.trans⟩


-- @@ L35-40 verbatim
/--
The games in `A` taken up to misère equality modulo `A`.
-/
@[expose]
def MisereQuotient (A : G → Prop) : Type (u + 1) :=
  Quotient (MisereSetoid A)


-- @@ L42-43 verbatim
instance instSetoidSubtypeLeanPool (A : G → Prop) : Setoid {g : G // A g} :=
  MisereSetoid A


-- @@ L45-45 verbatim
namespace Form.MisereQuotient


-- @@ L47-47 verbatim
variable {A : G → Prop}


-- @@ L49-54 verbatim
/--
The class of a game in the misère quotient.
-/
@[expose]
def mk (g : {g : G // A g}) : MisereQuotient A :=
  Quotient.mk (MisereSetoid A) g


-- @@ L56-60 verbatim
/--
A chosen representative of a misère-quotient class.
-/
def out (x : MisereQuotient A) : {g : G // A g} :=
  Quotient.out x


-- @@ L62-63 expanded
theorem mk_eq_mk {g h : { g : G // A g }} : mk g = mk h ↔ MisereEQ A (g : G) (h : G) :=
  Quotient.eq


-- @@ L65-66 verbatim
theorem sound {g h : {g : G // A g}} (hgh : MisereEQ A (g : G) (h : G)) : mk g = mk h :=
  Quotient.sound hgh


-- @@ L68-69 expanded
theorem exact {g h : { g : G // A g }} (hgh : mk g = mk h) : MisereEQ A (g : G) (h : G) :=
  Quotient.exact hgh


-- @@ L71-73 verbatim
@[simp]
theorem mk_out (x : MisereQuotient A) : mk x.out = x :=
  Quotient.out_eq x


-- @@ L75-76 expanded
theorem out_equiv_self (g : { g : G // A g }) : MisereEQ A ((mk g).out : G) (g : G) :=
  Quotient.mk_out (s := MisereSetoid A) g


-- @@ L78-91 expanded
theorem add_misereEQ_add [ClosedUnderAdd A] {g g' h h' : G} (hh : A h) (hg' : A g')
    (hg : MisereEQ A g g') (hh' : MisereEQ A h h') : MisereEQ A (g + h) (g' + h') :=
  by
  intro x hx
  have hhx : A (h + x) := ClosedUnderAdd.has_add _ _ hh hx
  have hgx : A (g' + x) := ClosedUnderAdd.has_add _ _ hg' hx
  calc
    MisereOutcome ((g + h) + x) = MisereOutcome (g + (h + x)) := by rw [add_assoc]
    _ = MisereOutcome (g' + (h + x)) := (hg _ hhx)
    _ = MisereOutcome (h + (g' + x)) := by simp only [add_left_comm]
    _ = MisereOutcome (h' + (g' + x)) := (hh' _ hgx)
    _ = MisereOutcome ((g' + h') + x) := by simp only [add_comm, add_left_comm]


-- @@ L93-97 expanded
theorem add_misereGE_add_right [ClosedUnderAdd A] {k : G} (hk : A k) {g h : G}
    (hgh : MisereGE A g h) : MisereGE A (g + k) (h + k) :=
  by
  intro x hx
  have hkx : A (k + x) := ClosedUnderAdd.has_add _ _ hk hx
  simpa only [add_assoc, add_comm, add_left_comm] using hgh (k + x) hkx


-- @@ L99-103 verbatim
instance instAdd [ClosedUnderAdd A] : Add (MisereQuotient A) where
  add x y :=
    Quotient.liftOn₂ x y
      (fun g h => mk ⟨(g : G) + (h : G), ClosedUnderAdd.has_add _ _ g.2 h.2⟩)
      fun _ b a' _ hg hh => sound (add_misereEQ_add b.2 a'.2 hg hh)


-- @@ L105-108 verbatim
@[simp]
theorem mk_add_mk [ClosedUnderAdd A] (g h : {g : G // A g}) :
    mk g + mk h = mk ⟨(g : G) + (h : G), ClosedUnderAdd.has_add _ _ g.2 h.2⟩ :=
  rfl


-- @@ L110-123 verbatim
instance instAddCommSemigroup [ClosedUnderAdd A] : AddCommSemigroup (MisereQuotient A) where
  add_assoc x y z := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    induction z using Quotient.inductionOn
    apply sound
    intro t ht
    simp only [add_assoc]
  add_comm x y := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    apply sound
    intro t ht
    simp only [add_comm]


-- @@ L125-126 verbatim
instance instZero [HasZero A] : Zero (MisereQuotient A) where
  zero := mk ⟨0, HasZero.has_zero⟩


-- @@ L128-130 verbatim
@[simp]
theorem mk_zero [HasZero A] : mk (A := A) ⟨0, HasZero.has_zero⟩ = (0 : MisereQuotient A) :=
  rfl


-- @@ L132-146 verbatim
instance instAddCommMonoid [HasZero A] [ClosedUnderAdd A] :
    AddCommMonoid (MisereQuotient A) where
  add_zero x := by
    induction x using Quotient.inductionOn
    apply sound
    intro t ht
    simp only [add_zero]
  zero_add x := by
    induction x using Quotient.inductionOn
    apply sound
    intro t ht
    simp only [zero_add]
  add_comm := add_comm
  add_assoc := add_assoc
  nsmul := nsmulRec


-- @@ L148-161 expanded
/-- The order on the quotient: `mk g ≤ mk h` exactly when `h ≥m A g`.
-/
instance instLE : LE (MisereQuotient A) where
  le x
    y :=
    Quotient.liftOn₂ x y (fun g h => MisereGE A (h : G) (g : G)) fun g h g' h' hg hh =>
      by
      change MisereEQ A (g : G) (g' : G) at hg
      change MisereEQ A (h : G) (h' : G) at hh
      apply propext
      constructor
      · intro hge
        exact misereGE_rw_left hh (misereGE_rw_right (MisereEQ.symm hg) hge)
      · intro hge
        exact misereGE_rw_left (MisereEQ.symm hh) (misereGE_rw_right hg hge)


-- @@ L163-164 expanded
theorem mk_le_mk (g h : { g : G // A g }) : mk g ≤ mk h ↔ MisereGE A (h : G) (g : G) :=
  Iff.rfl


-- @@ L166-179 verbatim
instance instPartialOrder : PartialOrder (MisereQuotient A) where
  le := (· ≤ ·)
  le_refl x := by
    induction x using Quotient.inductionOn
    exact MisereGE.refl _
  le_trans x y z hxy hyz := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    induction z using Quotient.inductionOn
    exact MisereGE.trans hyz hxy
  le_antisymm x y hxy hyx := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    exact sound (MisereEq.of_antisymm hyx hxy)


-- @@ L181-184 expanded
theorem out_le_out {a b : MisereQuotient A} : a ≤ b ↔ (MisereGE A (b.out : G) (a.out : G)) :=
  by
  conv_lhs => rw [← mk_out a, ← mk_out b]
  exact mk_le_mk _ _


-- @@ L186-193 verbatim
instance instIsOrderedAddMonoid [HasZero A] [ClosedUnderAdd A] :
    IsOrderedAddMonoid (MisereQuotient A) where
  add_le_add_left x y hxy z := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    induction z using Quotient.inductionOn with | h z =>
    change MisereGE A (_ + _) (_ + _)
    exact add_misereGE_add_right z.2 hxy


-- @@ L195-195 verbatim
end Form.MisereQuotient


-- @@ L197-197 verbatim
end


-- @@ L199-199 verbatim
end MisereGames
