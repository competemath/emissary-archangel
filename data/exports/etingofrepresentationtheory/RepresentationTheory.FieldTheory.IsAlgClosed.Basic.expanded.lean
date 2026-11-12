/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import RepresentationTheory.Alignment.Attribute


-- @@ L11-11 verbatim
/-! # Algebraically closed fields -/


-- @@ L13-13 verbatim
namespace RepresentationTheory.FieldTheory.IsAlgClosed.Basic


-- @@ L15-15 verbatim
open Polynomial


-- @@ L17-26 verbatim
/-- A field is algebraically closed exactly when every polynomial of nonzero degree has a root. -/
@[source_ref "Chapter2/Discussion_2.2_intro" (role := primary)]
theorem isAlgClosed_iff_nonconstant_root (k : Type*) [Field k] :
    IsAlgClosed k ↔ ∀ p : k[X], p.degree ≠ 0 → ∃ x : k, p.IsRoot x := by
  constructor
  · intro _ p hp
    exact IsAlgClosed.exists_root p hp
  · intro h
    exact IsAlgClosed.of_exists_root k fun p _ hp ↦
      h p (degree_pos_of_irreducible hp).ne'


-- @@ L28-30 verbatim
/-- The complex numbers form an algebraically closed field. -/
@[source_ref "Chapter2/Discussion_2.2_intro" (role := primary)]
theorem Complex.isAlgClosed : IsAlgClosed ℂ := inferInstance


-- @@ L32-34 verbatim
/-- A primality witness equips integers modulo that number with a field structure. -/
@[source_ref "Chapter2/Discussion_2.2_intro" (role := supporting)]
noncomputable abbrev ZMod.fieldOfPrime (p : ℕ) [Fact p.Prime] : Field (ZMod p) := inferInstance


-- @@ L36-38 verbatim
/-- The finite type cardinality of integers modulo a prime equals that prime. -/
@[source_ref "Chapter2/Discussion_2.2_intro" (role := supporting)]
theorem ZMod.card_eq_prime (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p) = p := ZMod.card p


-- @@ L40-43 verbatim
/-- The algebraic closure of integers modulo a prime is algebraically closed. -/
@[source_ref "Chapter2/Discussion_2.2_intro" (role := supporting)]
theorem AlgebraicClosure.zmod_isAlgClosed (p : ℕ) [Fact p.Prime] :
    IsAlgClosed (AlgebraicClosure (ZMod p)) := inferInstance


-- @@ L45-48 verbatim
/-- The algebraic closure of integers modulo a prime has the corresponding characteristic. -/
@[source_ref "Chapter2/Discussion_2.2_intro" (role := supporting)]
theorem AlgebraicClosure.zmod_charP (p : ℕ) [Fact p.Prime] :
    CharP (AlgebraicClosure (ZMod p)) p := inferInstance


-- @@ L50-50 verbatim
end RepresentationTheory.FieldTheory.IsAlgClosed.Basic
