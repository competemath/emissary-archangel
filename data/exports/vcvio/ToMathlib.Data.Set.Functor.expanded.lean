/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.Set.Functor


-- @@ L11-17 verbatim
/-!
# Equations for the set monad wrapper

This file exposes the `pure`, `bind`, and `map` equations for `SetM` through
`SetM.run`. Keeping these equations at the wrapper boundary lets clients reason
about the monad without relying on reduction through its bundled instance.
-/


-- @@ L19-19 verbatim
public section


-- @@ L21-21 verbatim
universe u


-- @@ L23-23 verbatim
namespace SetM


-- @@ L25-26 verbatim
/-- Regard a set as a computation in the `SetM` wrapper. -/
@[expose] protected def ofSet {α : Type u} (s : Set α) : SetM α := s


-- @@ L28-29 verbatim
@[simp]
lemma run_ofSet {α : Type u} (s : Set α) : SetM.run (SetM.ofSet s) = s := rfl


-- @@ L31-33 verbatim
@[simp]
lemma liftM_self {α : Type u} (s : SetM α) : (liftM s : SetM α) = s :=
  monadLift_self s


-- @@ L35-37 verbatim
@[simp]
lemma run_pure {α : Type u} (x : α) : SetM.run (pure x : SetM α) = {x} :=
  Set.pure_def x


-- @@ L39-42 verbatim
@[simp]
lemma run_bind {α β : Type u} (s : SetM α) (f : α → SetM β) :
    SetM.run (s >>= f) = ⋃ x ∈ SetM.run s, SetM.run (f x) :=
  Set.bind_def


-- @@ L44-47 verbatim
@[simp]
lemma run_map {α β : Type u} (f : α → β) (s : SetM α) :
    SetM.run (f <$> s) = f '' SetM.run s :=
  Set.fmap_eq_image f


-- @@ L49-49 verbatim
end SetM
