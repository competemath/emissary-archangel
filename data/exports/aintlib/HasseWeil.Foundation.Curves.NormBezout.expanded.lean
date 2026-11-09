/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Curves.FiniteOverKx
import Mathlib.RingTheory.Norm.Basic


-- @@ L9-30 verbatim
/-!
# Algebra norm on the function field

For a smooth plane curve `C/F`, the function field `K(C)` is a finite
extension of `Frac F[X]` (Silverman III.3.1.1, via our `FiniteOverKx`).
The algebra norm

```
N : K(C) → Frac(F[X])
```

is a multiplicative map sending each element to the determinant of its
multiplication-by endomorphism. This is the foundational tool for the
Bezout-counting argument used in ticket T-II-1-004 (finite zeros/poles).

This closes ticket T-II-INFRA-D-003 of the Stream-A infrastructure plan.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.1.2 (proof sketch);
  the norm approach is standard — see e.g. Hartshorne II.6.10.
-/


-- @@ L32-32 verbatim
namespace HasseWeil.Curves


-- @@ L34-34 verbatim
namespace SmoothPlaneCurve


-- @@ L36-36 verbatim
variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)


-- @@ L38-42 verbatim
/-- The **algebra norm** `N : K(C) → Frac(F[X])` for the finite extension
`K(C) / Frac(F[X])`. Sends `f ∈ K(C)` to `det` of multiplication by `f`.
Reference: Silverman II.1.2 proof (via Hartshorne II.6.10). -/
noncomputable def fieldNorm (f : C.FunctionField) : FractionRing (Polynomial F) :=
  Algebra.norm (FractionRing (Polynomial F)) f


-- @@ L44-44 verbatim
@[simp] theorem fieldNorm_one : C.fieldNorm 1 = 1 := map_one _


-- @@ L46-48 verbatim
@[simp] theorem fieldNorm_mul (f g : C.FunctionField) :
    C.fieldNorm (f * g) = C.fieldNorm f * C.fieldNorm g :=
  map_mul _ f g


-- @@ L50-51 verbatim
theorem fieldNorm_pow (f : C.FunctionField) (n : ℕ) :
    C.fieldNorm (f ^ n) = C.fieldNorm f ^ n := map_pow _ f n


-- @@ L53-57 verbatim
/-- The norm is zero iff the input is zero (uses integral-domain / free
module structure). -/
theorem fieldNorm_eq_zero_iff (f : C.FunctionField) :
    C.fieldNorm f = 0 ↔ f = 0 :=
  Algebra.norm_eq_zero_iff


-- @@ L59-60 verbatim
theorem fieldNorm_ne_zero_iff (f : C.FunctionField) :
    C.fieldNorm f ≠ 0 ↔ f ≠ 0 := not_iff_not.mpr (fieldNorm_eq_zero_iff C f)


-- @@ L62-63 verbatim
@[simp] theorem fieldNorm_zero : C.fieldNorm 0 = 0 :=
  (fieldNorm_eq_zero_iff C 0).mpr rfl


-- @@ L65-72 verbatim
/-- The norm of a scalar from the base field, applied via `algebraMap`.
For `r ∈ Frac(F[X])`, `N(r) = r^2` (degree of the extension). -/
theorem fieldNorm_algebraMap (r : FractionRing (Polynomial F)) :
    C.fieldNorm (algebraMap (FractionRing (Polynomial F)) C.FunctionField r) = r ^ 2 := by
  have h : C.fieldNorm (algebraMap (FractionRing (Polynomial F)) C.FunctionField r) =
      r ^ Module.finrank (FractionRing (Polynomial F)) C.FunctionField :=
    Algebra.norm_algebraMap r
  rw [h, finrank_functionField_over_fracPolynomialX]


-- @@ L74-76 verbatim
/-- A nonzero function has nonzero norm. -/
theorem fieldNorm_ne_zero {f : C.FunctionField} (hf : f ≠ 0) :
    C.fieldNorm f ≠ 0 := (fieldNorm_ne_zero_iff C f).mpr hf


-- @@ L78-78 verbatim
end SmoothPlaneCurve


-- @@ L80-80 verbatim
end HasseWeil.Curves
