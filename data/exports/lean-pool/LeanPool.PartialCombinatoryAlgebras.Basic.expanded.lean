/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
module

public import Mathlib.Data.Part


-- @@ L10-16 verbatim
/-!
# Notation and core classes for partial combinatory algebras

A notation for totality of a partial element, a generic class for a
left-associative binary application operator, and the class for a partial
binary operation on a type.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace LeanPool.PartialCombinatoryAlgebras


-- @@ L22-23 verbatim
/-- A notation for totality of a partial element (we find writing `x.Dom` a bit silly). -/
notation:50 u:max " ⇓" => Part.Dom u


-- @@ L25-28 verbatim
/-- A generic notation for a left-associative binary operation. -/
class HasDot (A : Type*) where
  /-- (possibly partial) binary application -/
  dot : A → A → A


-- @@ L30-31 verbatim
@[inherit_doc]
infixl:70 " ⬝ " => HasDot.dot


-- @@ L33-36 verbatim
/-- A partial binary operation on a set. -/
class PartialApplication (A : Type*) where
  /-- Partial application -/
  app : Part A → Part A → Part A


-- @@ L38-38 verbatim
namespace PartialApplication


-- @@ L40-41 verbatim
instance hasDot {A : Type*} [PartialApplication A] : HasDot (Part A) where
  dot := app


-- @@ L43-43 verbatim
end PartialApplication


-- @@ L45-45 verbatim
end LeanPool.PartialCombinatoryAlgebras
