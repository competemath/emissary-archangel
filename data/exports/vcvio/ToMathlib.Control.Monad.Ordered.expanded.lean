/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Control.Monad.Cont
public import Mathlib.CategoryTheory.Monad.Basic
public import PolyFun.Control.Monad.Algebra
public import ToMathlib.Control.Monad.Relation
public import ToMathlib.Control.Monad.Transformer
public import Mathlib.Order.Monotone.Basic


-- @@ L15-29 verbatim
/-!
# Ordered monads

This file collects all definitions and basic theorems about adding ordering to monads.

## Main definitions

- `OrderedMonad`
- `OrderedMonadAlgebra`
- `OrderedMonadLift`
- `MonadIdeal`
- `OrderedMonadTransformer`
- Left / right Kan extension of ordered monads

-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
universe u v w


-- @@ L35-40 verbatim
/-- An ordered monad `m` is a monad equipped with a preorder on each type `m α`, such that the bind
    operation preserves the order. -/
class OrderedMonad (m : Type u → Type v) extends Monad m where
  [monadOrder {α : Type u} : Preorder (m α)]
  bind_mono {α β : Type u} {ma ma' : m α} {f f' : α → m β} (ha : ma ≤ ma') (hf : ∀ a, f a ≤ f' a) :
    ma >>= f ≤ ma' >>= f'


-- @@ L42-42 verbatim
export OrderedMonad (monadOrder bind_mono)


-- @@ L44-44 verbatim
instance {m} [OrderedMonad m] {α : Type u} : Preorder (m α) := monadOrder


-- @@ L46-46 verbatim
attribute [simp] bind_mono


-- @@ L48-52 verbatim
/-- Unbundled version of `OrderedMonad`. -/
class Monad.IsOrdered (m : Type u → Type v) [Monad m] where
  [monadOrder {α : Type u} : Preorder (m α)]
  bind_mono {α β : Type u} {ma ma' : m α} {f f' : α → m β} (ha : ma ≤ ma') (hf : ∀ a, f a ≤ f' a) :
    ma >>= f ≤ ma' >>= f'


-- @@ L54-56 verbatim
instance {m} [Monad m] [Monad.IsOrdered m] : OrderedMonad m where
  monadOrder := Monad.IsOrdered.monadOrder
  bind_mono := Monad.IsOrdered.bind_mono


-- @@ L58-58 verbatim
namespace OrderedMonad


-- @@ L60-62 verbatim
/-- The less-than-or-equal relation on an ordered monad `m`. -/
@[reducible] def monadLE {m} [OrderedMonad m] : {α : Type u} → m α → m α → Prop :=
  monadOrder.le


-- @@ L64-66 verbatim
/-- The less-than relation on an ordered monad `m`. -/
@[reducible] def monadLT {m} [OrderedMonad m] : {α : Type u} → m α → m α → Prop :=
  monadOrder.lt


-- @@ L68-68 verbatim
@[inherit_doc] scoped infix:50 " ≤ₘ " => OrderedMonad.monadLE

-- @@ L69-69 verbatim
@[inherit_doc] scoped infix:50 " <ₘ " => OrderedMonad.monadLT


-- @@ L71-71 expanded
macro_rules
  | `(OrderedMonad.monadLE $x $y) => `(binrel% OrderedMonad.monadLE $x $y)


-- @@ L72-72 expanded
macro_rules
  | `(OrderedMonad.monadLT $x $y) => `(binrel% OrderedMonad.monadLT $x $y)


-- @@ L74-74 verbatim
namespace Discrete


-- @@ L76-91 verbatim
/-- Any monad can be given the discrete preorder, where `a ≤ b` if and only if `a = b`.

This is put into the `Discrete` scope in order to avoid conflicts with other instances. This
instance should only be used as a last resort. -/
scoped instance (priority := low) instDiscreteMonad (m) [Monad m] : OrderedMonad m where
  monadOrder := {
    le := (· = ·)
    le_refl _ := rfl
    le_trans _ _ _ hab hbc := hab.trans hbc
  }
  bind_mono h hf := by
    subst h
    rename_i f g
    have hfg : f = g := funext hf
    subst hfg
    rfl


-- @@ L93-93 verbatim
end Discrete


-- @@ L95-95 verbatim
end OrderedMonad


-- @@ L97-97 verbatim
export OrderedMonad (monadLE monadLT)


-- @@ L99-104 verbatim
open OrderedMonad

-- class OrderedAlgebra (m : Type u → Type u) [Monad m] [MonadAlgebra m] where
--   [carrierOrder {α : Type u} : Preorder α]
--   monadAlg_mono {α β : Type u} {f f' : α → β} {ma ma' : m α} (hf : ∀ a, (f a) ≤ (f' a))
--     (hm : ma ≤ ma') : (monadAlg (f <$> ma)) ≤ (monadAlg (f' <$> ma'))


-- @@ L106-109 expanded
class OrderedMonadAlgebra (m : Type u → Type v) [OrderedMonad m] [MonadAlgebra m] where
  [carrierOrder {α : Type u} : Preorder α]
  monadAlg_mono {α β : Type u} {f f' : α → β} {ma ma' : m α} (hf : ∀ a, (f a) ≤ (f' a))
    (hm : OrderedMonad.monadLE ma ma') : (monadAlg (f <$> ma)) ≤ (monadAlg (f' <$> ma'))


-- @@ L111-111 verbatim
export OrderedMonadAlgebra (monadAlg_mono)


-- @@ L113-113 verbatim
attribute [simp] monadAlg_mono


-- @@ L115-115 verbatim
section MonadLift


-- @@ L117-120 expanded
/-- A class that express an ordering for monad lifts. -/
class MonadLift.LE (m : Type u → Type v) (n : Type u → Type w) [Monad m] [OrderedMonad n]
    [φ : MonadLift m n] [ψ : MonadLift m n] where
  monadLift_le {α} (a : m α) : OrderedMonad.monadLE (φ.monadLift a) (ψ.monadLift a)


-- @@ L122-129 expanded
/-- If the target monad `n` is ordered, then we have a preorder on the monad lifts from `m`
to `n`. -/
instance {m n} [Monad m] [OrderedMonad n] : Preorder (MonadLift m n)
    where
  le := fun φ ψ => ∀ {α : Type u} (a : m α), OrderedMonad.monadLE (φ.monadLift a) (ψ.monadLift a)
  le_refl _ := by intro α a; simp only [ge_iff_le, le_refl]
  le_trans _ _ _ h1
    h2 := by
    intro α a
    exact (h1 a).trans (h2 a)


-- @@ L131-133 verbatim
class OrderedMonadLift (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [OrderedMonad m] [OrderedMonad n] extends MonadLift m n where
  monadLift_mono {α} : Monotone (@monadLift α)


-- @@ L135-137 verbatim
class OrderedMonadLiftT (m : Type u → Type v) (n : Type u → Type w)
    [OrderedMonad m] [OrderedMonad n] extends MonadLiftT m n where
  monadLift_mono {α} : Monotone (@monadLift α)


-- @@ L139-139 verbatim
export OrderedMonadLiftT (monadLift_mono)


-- @@ L141-141 verbatim
attribute [simp] monadLift_mono


-- @@ L143-145 expanded
@[simp]
theorem monadLift_mono' {m n} [OrderedMonad m] [OrderedMonad n] [OrderedMonadLiftT m n] {α}
    {a b : m α} (h : OrderedMonad.monadLE a b) :
    OrderedMonad.monadLE (monadLift a) (monadLift b : n α) :=
  (monadLift_mono (m := m) (n := n) (α := α)) h


-- @@ L147-153 verbatim
instance {m} [OrderedMonad m] : OrderedMonadLiftT m m where
  monadLift_mono h := by simp only [monadLift_self, h]

-- TODO: fix synthesization order
-- instance (m n o) [Monad m] [Monad n] [Monad o] [OrderedMonadLift n o]
--     [OrderedMonadLiftT m n] : OrderedMonadLiftT m o where
--   monadLift_mono h := by simp


-- @@ L155-165 verbatim
open OrderedMonad Discrete in
/--
Given the (default) discrete preorder on the beginning monad `m`, we can have a preorder on the
monad lifts from `m` to `n`.

This is stated as a definition and not an instance, since oftentimes we want to have another
instance on the monad lift.
-/
@[reducible] def instDiscreteMonadLift {m n} [Monad m] [h : OrderedMonad n] [MonadLift m n] :
    OrderedMonadLift m n where
  monadLift_mono h := by rename_i a b; have : a = b := h; simp only [this, le_refl]


-- @@ L167-167 verbatim
end MonadLift


-- @@ L169-169 verbatim
namespace MonadRelation


-- @@ L171-173 expanded
class IsUpperClosed (m : Type u → Type v) (n : Type u → Type w) [Monad m] [OrderedMonad n]
    [MonadRelation m n] where
  monadRel_upper_closed {α} {ma : m α} {na na' : n α} (hr : ma ∼ₘ na)
    (hn : OrderedMonad.monadLE na na') : ma ∼ₘ na'


-- @@ L175-176 expanded
instance {m n} [Monad m] [OrderedMonad n] [MonadLiftT m n] : MonadRelation m n where
  monadRel := fun a b => OrderedMonad.monadLE (monadLift a) b


-- @@ L178-185 verbatim
instance {m n} [Monad m] [OrderedMonad n] [MonadLiftT m n] [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftT m n] : LawfulMonadRelation m n where
  monadRel_pure := by
    simp only [monadRel, liftM_pure, ge_iff_le, le_refl, implies_true]
  monadRel_bind ha hb := by
    simp_all only [monadRel, ge_iff_le, liftM_bind, implies_true, bind_mono]

-- TODO: monad morphism also defines a monad ideal


-- @@ L187-187 verbatim
end MonadRelation


-- @@ L189-193 verbatim
class OrderedMonadTransformer (t : (Type u → Type v) → Type u → Type w)
    extends MonadTransformer t where
  mapOrderedMonad {m} [OrderedMonad m] : OrderedMonad (t m)
  liftOf_mono {m n} [OrderedMonad m] [OrderedMonad n] [OrderedMonadLiftT m n] :
    OrderedMonadLiftT (t m) (t n)


-- @@ L195-200 verbatim
class AssertAssume (α : Type u) [Preorder α] where
  assert : Prop → α → α
  assume : Prop → α → α
  assert_strengthen : ∀ p x, assert p x ≤ x
  assume_weaken : ∀ p x, x ≤ assume p x
  assert_assume_iff : ∀ p x y, assert p x ≤ y ↔ x ≤ assume p y


-- @@ L202-203 verbatim
class Monad.AssertAssume (m : Type u → Type v) [∀ α, Preorder (m α)] where
  assert_assume {α} : _root_.AssertAssume (m α)


-- @@ L205-205 verbatim
section KanExtension

-- @@ L206-206 verbatim
variable {w : Type u → Type v} [OrderedMonad w]


-- @@ L208-209 expanded
def leftKanExtension {α β : Type u} (f : w β) (p : w α) :=
  { ext : α → w β //
    OrderedMonad.monadLE (p >>= ext) f ∧
      (∀ w', OrderedMonad.monadLE (p >>= w') f → ∀ b, OrderedMonad.monadLE (w' b) (ext b)) }


-- @@ L211-212 expanded
def rightKanExtension {α β : Type u} (f : w β) (p : w α) :=
  { ext : β → w α //
    OrderedMonad.monadLE (f >>= ext) p ∧
      (∀ w', OrderedMonad.monadLE (f >>= w') p → ∀ a, OrderedMonad.monadLE (w' a) (ext a)) }


-- @@ L214-214 verbatim
end KanExtension
