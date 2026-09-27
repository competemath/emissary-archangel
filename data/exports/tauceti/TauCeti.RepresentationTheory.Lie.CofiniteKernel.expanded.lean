/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations


-- @@ L12-34 verbatim
/-!
# Cofinite kernels of finite-dimensional Lie representations

A Lie algebra map `f : L →ₗ⁅K⁆ A` into an associative algebra extends along the universal property
to an algebra homomorphism `UniversalEnvelopingAlgebra.lift K f`.  The motivating case is a
representation `ρ : L →ₗ⁅K⁆ Module.End K V`, but nothing below uses the endomorphism structure, so
the results are stated for an arbitrary associative target.  When `A` is finite-dimensional, the
kernel of this extension is cofinite: its quotient embeds linearly in `A`.  As a ring-homomorphism
kernel it is automatically a two-sided ideal in Mathlib's ideal API.

The same kernel records nilpotence of the original map.  For `x : L`, the element `f x` is
nilpotent exactly when some power of the canonical generator `ι x` belongs to the kernel.  This is
the form needed when a finite-dimensional representation is replaced by a smaller ideal while
preserving nilpotence of selected operators.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.finiteDimensional_quotient_ker_lift`: its quotient is
  finite-dimensional.
* `TauCeti.UniversalEnvelopingAlgebra.isNilpotent_iff_exists_pow_ι_mem_ker_lift`: nilpotence of
  the image of an element is equivalent to membership of a power of its enveloping generator in
  the kernel.
-/


-- @@ L36-36 verbatim
public section


-- @@ L38-38 verbatim
namespace TauCeti


-- @@ L40-40 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L42-42 verbatim
namespace UniversalEnvelopingAlgebra


-- @@ L44-44 verbatim
universe u v w


-- @@ L46-46 verbatim
variable (R : Type u) (L : Type v) [LieRing L]


-- @@ L48-48 verbatim
local notation "U" => _root_.UniversalEnvelopingAlgebra R L


-- @@ L50-50 verbatim
section FiniteDimensional


-- @@ L52-52 verbatim
variable [Field R] [LieAlgebra R L]

-- @@ L53-53 verbatim
variable {A : Type w} [Ring A] [Algebra R A]


-- @@ L55-61 verbatim
/-- The quotient by the kernel of the enveloping-algebra extension of a Lie algebra map into a
finite-dimensional associative algebra is finite-dimensional. -/
theorem finiteDimensional_quotient_ker_lift [FiniteDimensional R A] (f : L →ₗ⁅R⁆ A) :
    FiniteDimensional R
      (U ⧸ RingHom.ker (_root_.UniversalEnvelopingAlgebra.lift R f)) :=
  Module.Finite.equiv
    (Ideal.quotientKerEquivRange (_root_.UniversalEnvelopingAlgebra.lift R f)).symm.toLinearEquiv


-- @@ L63-63 verbatim
end FiniteDimensional


-- @@ L65-65 verbatim
section Nilpotence


-- @@ L67-67 verbatim
variable [CommRing R] [LieAlgebra R L]

-- @@ L68-68 verbatim
variable {A : Type w} [Ring A] [Algebra R A]


-- @@ L70-76 verbatim
/-- A power of the canonical enveloping generator belongs to the kernel of the extended map
exactly when the corresponding power of the image vanishes. -/
theorem pow_ι_mem_ker_lift_iff (f : L →ₗ⁅R⁆ A) (x : L) (n : ℕ) :
    (_root_.UniversalEnvelopingAlgebra.ι R x) ^ n ∈
        RingHom.ker (_root_.UniversalEnvelopingAlgebra.lift R f) ↔
      (f x) ^ n = 0 := by
  rw [RingHom.mem_ker, map_pow, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]


-- @@ L78-84 verbatim
/-- The image of an element is nilpotent exactly when some power of its canonical
enveloping-algebra generator belongs to the kernel of the extended map. -/
theorem isNilpotent_iff_exists_pow_ι_mem_ker_lift (f : L →ₗ⁅R⁆ A) (x : L) :
    IsNilpotent (f x) ↔
      ∃ n : ℕ, (_root_.UniversalEnvelopingAlgebra.ι R x) ^ n ∈
        RingHom.ker (_root_.UniversalEnvelopingAlgebra.lift R f) := by
  simp only [IsNilpotent, pow_ι_mem_ker_lift_iff]


-- @@ L86-86 verbatim
end Nilpotence


-- @@ L88-88 verbatim
end UniversalEnvelopingAlgebra


-- @@ L90-90 verbatim
end TauCeti
