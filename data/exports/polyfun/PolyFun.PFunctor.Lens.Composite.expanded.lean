/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Basic


-- @@ L10-36 verbatim
/-!
# Lenses into composites, and the composition-power of a lens

Two pieces of Spivak–Niu Ch. 6 machinery for the composition product `◃`.

## Destructor triple (Example 6.40)

A lens `φ : p ⇆ q ◃ r` is exactly a triple `(φ^q, φ^r, φ♯)`:

* `φ^q : (i : p.A) → q.A` — the `q`-position policy;
* `φ^r : (i : p.A) → q.B (φ^q i) → r.A` — the `r`-position policy, given a
  `q`-direction; and
* `φ♯ : (i : p.A) → (Σ u : q.B (φ^q i), r.B (φ^r i u)) → p.B i` — the joint pullback
  of directions.

These are not a second representation: they are the components already stored by
the lens. The accessors `Lens.compOuter`, `Lens.compInner`, and
`Lens.compPullback` expose the three views directly, without conversion or an
auxiliary wrapper type.

## Composition power of a lens (§6.1.4)

`Lens.compNthMap l n : Lens (compNth p n) (compNth q n)` lifts a lens `l : p ⇆ q`
through the `n`-fold composition power `p^{◃n}` (Spivak–Niu's `φ^{◁n}`, the
"`n` steps of the interface" map). It is the interface-lift underneath multi-step
dynamical systems.
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
universe uA uB


-- @@ L42-42 verbatim
namespace PFunctor


-- @@ L44-44 verbatim
namespace Lens


-- @@ L46-46 verbatim
variable {p q r : PFunctor.{uA, uB}}


-- @@ L48-48 verbatim
/-! ## Components of a lens into `q ◃ r` -/


-- @@ L50-53 verbatim
/-- The outer `q`-position selected by a lens into `q ◃ r` at each source
position (Spivak–Niu Example 6.40). -/
def compOuter (l : Lens p (q ◃ r)) (i : p.A) : q.A :=
  (l.toFunA i).1


-- @@ L55-58 verbatim
/-- The inner `r`-position selected by a lens into `q ◃ r` after receiving
an outer `q`-direction. -/
def compInner (l : Lens p (q ◃ r)) (i : p.A) (u : q.B (l.compOuter i)) : r.A :=
  (l.toFunA i).2 u


-- @@ L60-64 verbatim
/-- The joint pullback of the outer and inner directions of a lens into
`q ◃ r`. -/
def compPullback (l : Lens p (q ◃ r)) (i : p.A) :
    (Σ u : q.B (l.compOuter i), r.B (l.compInner i u)) → p.B i :=
  l.toFunB i


-- @@ L66-66 verbatim
/-! ## The composition power of a lens -/


-- @@ L68-72 verbatim
/-- The `n`-fold composition power of a lens: `l^{◃n} : compNth p n ⇆ compNth q n`
(Spivak–Niu §6.1.4). Built by iterating `compMap` (`◃ₗ`). -/
def compNthMap (l : Lens p q) : (n : ℕ) → Lens (compNth p n) (compNth q n)
  | 0 => Lens.id y
  | n + 1 => l ◃ₗ compNthMap l n


-- @@ L74-74 verbatim
@[simp] theorem compNthMap_zero (l : Lens p q) : compNthMap l 0 = Lens.id y := rfl


-- @@ L76-77 verbatim
@[simp] theorem compNthMap_succ (l : Lens p q) (n : ℕ) :
    compNthMap l (n + 1) = l ◃ₗ compNthMap l n := rfl


-- @@ L79-83 verbatim
@[simp] theorem compNthMap_id (P : PFunctor.{uA, uB}) (n : ℕ) :
    compNthMap (Lens.id P) n = Lens.id (compNth P n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [compNthMap, ih, compMap_id]


-- @@ L85-91 verbatim
/-- Composition powers preserve lens composition: taking `n` copies of a
composite is the composite of the two `n`-fold maps. -/
@[simp] theorem compNthMap_comp (l₁ : Lens q r) (l₂ : Lens p q) (n : ℕ) :
    compNthMap (l₁ ∘ₗ l₂) n = compNthMap l₁ n ∘ₗ compNthMap l₂ n := by
  induction n with
  | zero => simp [compNthMap]
  | succ n ih => simp [compNthMap_succ, ih, compMap_comp]


-- @@ L93-93 verbatim
end Lens


-- @@ L95-95 verbatim
end PFunctor
