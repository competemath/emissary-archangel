/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LutzNagell.DivisionPolynomialDegree
import LutzNagell.ZSMul
import LutzNagell.LutzNagellTheorem.EvalBridge
import LutzNagell.LutzNagellTheorem.GeneralCurve
import LutzNagell.LutzNagellTheorem.GeneralPrimeOrder
import LutzNagell.LutzNagellTheorem.PIDIntegralMultiple
import Mathlib.RingTheory.Localization.Rat
import Mathlib.RingTheory.Polynomial.RationalRoot


-- @@ L15-29 verbatim
/-!
# Integral multiple implies integral point (general Weierstrass curves)

If `n • P` has integral affine coordinates on a general Weierstrass curve
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` over `ℚ` with `aᵢ ∈ ℤ`,
then `P` already has integral affine coordinates.

The maximally general form of every result here — over an arbitrary UFD `R` with fraction
field `K`, with integrality expressed as `IsLocalization.IsInteger R` — lives in
`LutzNagell.LutzNagellTheorem.PIDIntegralMultiple` (the `LutzNagell.PID` namespace). The `ℤ/ℚ`
statements below are the `R = ℤ`, `K = ℚ` specialisations of those general lemmas, with
`IsLocalization.IsInteger ℤ x` unfolded to the concrete `∃ x₀ : ℤ, (x₀ : ℚ) = x` used by the
downstream `GeneralMain`/`GeneralDiscriminant` consumers. `curveQ W` is definitionally
`PID.curveK ℤ ℚ W`, so the specialisation is immediate.
-/


-- @@ L31-31 verbatim
namespace LutzNagell

-- @@ L32-32 verbatim
namespace LutzNagellTheorem


-- @@ L34-34 verbatim
open WeierstrassCurve Polynomial


-- @@ L36-36 verbatim
variable (W : WeierstrassCurve ℤ)


-- @@ L38-41 verbatim
/-- `IsLocalization.IsInteger ℤ x` is the concrete predicate `∃ x₀ : ℤ, (x₀ : ℚ) = x`. -/
theorem isInteger_int_iff {x : ℚ} :
    IsLocalization.IsInteger ℤ x ↔ ∃ x₀ : ℤ, (x₀ : ℚ) = x := by
  simp only [IsLocalization.IsInteger, RingHom.mem_rangeS, algebraMap_int_eq, eq_intCast]


-- @@ L43-43 verbatim
/-! ### The x-coordinate formula -/


-- @@ L45-54 verbatim
/-- The x-coordinate of `n • P` satisfies `x' · ΨSq_n(x) = Φ_n(x)`.

`ℤ/ℚ` specialisation of `LutzNagell.PID.x_coord_nsmul_eq`. -/
theorem x_coord_nsmul_eq_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0)
    {x' y' : ℚ} (hns' : (curveQ W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns') :
    x' * ((curveQ W).ΨSq n).eval x = ((curveQ W).Φ n).eval x :=
  PID.x_coord_nsmul_eq (curveQ W) hns hn hns' hnP


-- @@ L56-56 verbatim
/-! ### Monic polynomial from the coordinate formula -/


-- @@ L58-64 verbatim
/-- `Φ_n - C c * ΨSq_n` is monic over `ℤ` for any `c : ℤ` and `n ≠ 0`.

`ℤ` specialisation of `LutzNagell.PID.monic_Φ_sub_smul_ΨSq`. -/
theorem monic_Φ_sub_smul_ΨSq_general
    {n : ℤ} (hn : n ≠ 0) (c : ℤ) :
    (W.Φ n - C c * W.ΨSq n).Monic :=
  PID.monic_Φ_sub_smul_ΨSq W (by exact_mod_cast hn) c


-- @@ L66-66 verbatim
/-! ### x integral from the coordinate formula + monic polynomial -/


-- @@ L68-79 verbatim
/-- If `n • P` has integral x-coordinate, then `P` has integral x-coordinate.

`ℤ/ℚ` specialisation of `LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger`. -/
theorem x_integral_of_nsmul_x_integral_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0)
    {x' y' : ℚ} (hns' : (curveQ W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    {c : ℤ} (hc : (c : ℚ) = x') :
    ∃ x₀ : ℤ, (x₀ : ℚ) = x :=
  isInteger_int_iff.mp <| PID.x_isInteger_of_nsmul_x_isInteger W hns hn (by exact_mod_cast hn)
    hns' hnP (by simpa only [algebraMap_int_eq, Int.coe_castRingHom, eq_intCast] using hc)


-- @@ L81-81 verbatim
/-! ### Main theorem -/


-- @@ L83-96 verbatim
/-- If `n • P` has integral coordinates on a general integral Weierstrass curve,
then `P` has integral coordinates.

`ℤ/ℚ` specialisation of `LutzNagell.PID.isInteger_of_nsmul_isInteger`. -/
theorem integral_of_nsmul_integral_general
    {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0)
    {x' y' : ℚ} (hns' : (curveQ W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    (hx' : ∃ x₀ : ℤ, (x₀ : ℚ) = x') (hy' : ∃ y₀ : ℤ, (y₀ : ℚ) = y') :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y := by
  obtain ⟨hxi, hyi⟩ := PID.isInteger_of_nsmul_isInteger W hns hn (by exact_mod_cast hn) hns' hnP
    (isInteger_int_iff.mpr hx') (isInteger_int_iff.mpr hy')
  exact ⟨isInteger_int_iff.mp hxi, isInteger_int_iff.mp hyi⟩


-- @@ L98-98 verbatim
end LutzNagellTheorem

-- @@ L99-99 verbatim
end LutzNagell
