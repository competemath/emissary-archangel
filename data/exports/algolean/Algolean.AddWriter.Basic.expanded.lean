/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai, Eric Wieser
-/

module

public import Mathlib.Algebra.Group.Defs


-- @@ L11-31 verbatim
/-!

# AddWriter: Additive Writer Monad
`AddWriter T α` represents a computation that produces a value of type `α` and tracks its cost.

`T` can be instantiated with AddCommMonoid types to count costs in types of varying complexity.

## Notation
- **`✓`** : A call to tell, see `tell`.
- **`⟪tm⟫`** : Extract the pure value from an `AddWriter` computation (notation for `tm.ret`).

## Notes on Authorship and Terminology
This file was authored by Sorrachai Yingchareonthawornchai in the CSLib repository.
It was named the Time monad `TimeM`. The standard name for this concept is the Writer Monad.
Since Lean/Mathlib makes a distinction between additive and multiplicative algebraic structures,
and Mathlib already contains a Writer monad, we call this structure `AddWriter`.

## References
1. [Elementary explanation of writer monads](https://williamyaoh.com/posts/2020-07-26-deriving-writer-monad.html)
2. [Danielsson2008] on lightweight monadic verification of time complexity.
-/



-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
namespace Algolean


-- @@ L38-46 verbatim
/-- A monad for tracking log complexity of computations.
`AddWriter T α` represents a computation that returns a value of type `α`
and accumulates a log cost (represented as a type `T`, typically `ℕ`). -/
@[ext]
structure AddWriter (w : Type*) (α : Type*) where
  /-- The return value of the computation -/
  ret : α
  /-- The accumulated tell cost of the computation -/
  tell : w


-- @@ L48-48 verbatim
namespace AddWriter


-- @@ L50-54 verbatim
/-- Lifts a pure value into a `AddWriter` computation with zero tell cost.

Prefer to use `pure` instead of `AddWriter.pure`. -/
protected def pure [Zero T] {α} (a : α) : AddWriter T α :=
  ⟨a, 0⟩


-- @@ L56-57 verbatim
instance [Zero T] : Pure (AddWriter T) where
  pure := AddWriter.pure


-- @@ L59-64 verbatim
/-- Sequentially composes two `AddWriter` computations, summing their log costs.

Prefer to use the `>>=` notation. -/
protected def bind {α β} [Add T] (m : AddWriter T α) (f : α → AddWriter T β) : AddWriter T β :=
  let r := f m.ret
  ⟨r.ret, m.tell + r.tell⟩


-- @@ L66-67 verbatim
instance [Add T] : Bind (AddWriter T) where
  bind := AddWriter.bind


-- @@ L69-70 verbatim
instance : Functor (AddWriter T) where
  map f x := ⟨f x.ret, x.tell⟩


-- @@ L72-73 verbatim
instance [Add T] : Seq (AddWriter T) where
  seq f x := ⟨f.ret (x ()).ret, f.tell + (x ()).tell⟩


-- @@ L75-76 verbatim
instance [Add T] : SeqLeft (AddWriter T) where
  seqLeft x y := ⟨x.ret, x.tell + (y ()).tell⟩


-- @@ L78-79 verbatim
instance [Add T] : SeqRight (AddWriter T) where
  seqRight x y := ⟨(y ()).ret, x.tell + (y ()).tell⟩


-- @@ L81-87 verbatim
instance [AddZero T] : Monad (AddWriter T) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight


-- @@ L89-89 verbatim
@[simp, grind =] theorem ret_pure {α} [Zero T] (a : α) : (pure a : AddWriter T α).ret = a := rfl


-- @@ L91-92 verbatim
@[simp, grind =] theorem ret_bind {α β} [Add T] (m : AddWriter T α) (f : α → AddWriter T β) :
    (m >>= f).ret = (f m.ret).ret := rfl


-- @@ L94-95 verbatim
@[simp, grind =] theorem ret_map {α β} (f : α → β) (x : AddWriter T α) : (f <$> x).ret = f x.ret :=
  rfl


-- @@ L97-98 verbatim
@[simp] theorem ret_seqRight {α} (x : AddWriter T α) (y : Unit → AddWriter T β) [Add T] :
    (SeqRight.seqRight x y).ret = (y ()).ret := rfl


-- @@ L100-101 verbatim
@[simp] theorem ret_seqLeft {α} [Add T] (x : AddWriter T α) (y : Unit → AddWriter T β) :
    (SeqLeft.seqLeft x y).ret = x.ret := rfl


-- @@ L103-104 verbatim
@[simp] theorem ret_seq {α β} [Add T] (f : AddWriter T (α → β)) (x : Unit → AddWriter T α) :
    (Seq.seq f x).ret = f.ret (x ()).ret := rfl


-- @@ L106-107 verbatim
@[simp, grind =] theorem tell_bind {α β} [Add T] (m : AddWriter T α) (f : α → AddWriter T β) :
    (m >>= f).tell = m.tell + (f m.ret).tell := rfl


-- @@ L109-109 verbatim
@[simp, grind =] theorem tell_pure {α} [Zero T] (a : α) : (pure a : AddWriter T α).tell = 0 := rfl


-- @@ L111-112 verbatim
@[simp, grind =] theorem tell_map {α β} (f : α → β) (x : AddWriter T α) : (f <$> x).tell = x.tell :=
  rfl

-- @@ L113-114 verbatim
@[simp] theorem tell_seqRight {α} [Add T] (x : AddWriter T α) (y : Unit → AddWriter T β) :
    (SeqRight.seqRight x y).tell = x.tell + (y ()).tell := rfl


-- @@ L116-117 verbatim
@[simp] theorem tell_seqLeft {α} [Add T] (x : AddWriter T α) (y : Unit → AddWriter T β) :
    (SeqLeft.seqLeft x y).tell = x.tell + (y ()).tell := rfl


-- @@ L119-120 verbatim
@[simp] theorem tell_seq {α β} [Add T] (f : AddWriter T (α → β)) (x : Unit → AddWriter T α) :
    (Seq.seq f x).tell = f.tell + (x ()).tell := rfl


-- @@ L122-128 verbatim
/-- `AddWriter` is lawful so long as addition in the cost is associative and absorbs zero. -/
instance [AddMonoid T] : LawfulMonad (AddWriter T) := .mk'
  (id_map := fun x => rfl)
  (pure_bind := fun _ _ => by ext <;> simp)
  (bind_assoc := fun _ _ _ => by ext <;> simp [add_assoc])
  (seqLeft_eq := fun _ _ => by ext <;> simp)
  (bind_pure_comp := fun _ _ => by ext <;> simp)


-- @@ L130-131 verbatim
/-- Creates a `AddWriter` computation with a tell cost. -/
def tick (c : T) : AddWriter T PUnit := ⟨.unit, c⟩


-- @@ L133-133 verbatim
@[simp, grind =] theorem ret_tick (c : T) : (tick c).ret = () := rfl


-- @@ L135-135 verbatim
@[simp, grind =] theorem tell_tick (c : T) : (tick c).tell = c := rfl


-- @@ L137-138 verbatim
/-- `✓[c] x` adds `c` ticks, then executes `x`. -/
macro "✓[" c:term "]" body:doElem : doElem => `(doElem| do tick $c; $body:doElem)


-- @@ L140-141 verbatim
/-- `✓ x` is a shorthand for `✓[1] x`, which adds one tick and executes `x`. -/
macro "✓" body:doElem : doElem => `(doElem| do tick 1 $body:doElem)


-- @@ L143-144 verbatim
/-- Notation for extracting the return value from a `AddWriter` computation: `⟪tm⟫` -/
scoped notation:max "⟪" tm "⟫" => (AddWriter.ret tm)


-- @@ L146-146 verbatim
end AddWriter

-- @@ L147-147 verbatim
end Algolean
