/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import LutzNagell.Universal
import LutzNagell.EllipticDivisibilitySequence


-- @@ L9-17 verbatim
/-!
# Division polynomials of Weierstrass curves

This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
name conflicts (both define `normEDS`, `complEDS`, etc.).

See the original file for full documentation.
-/


-- @@ L19-19 verbatim
open Polynomial

-- @@ L20-20 verbatim
open scoped Polynomial.Bivariate


-- @@ L22-23 verbatim
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])


-- @@ L25-25 verbatim
universe r s u v


-- @@ L27-27 verbatim
namespace WeierstrassCurve


-- @@ L29-29 verbatim
variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (W : WeierstrassCurve R)


-- @@ L31-31 verbatim
section Ψ₂Sq


-- @@ L33-33 verbatim
/-! ### The univariate polynomial `Ψ₂Sq` -/


-- @@ L35-37 verbatim
/-- The `2`-division polynomial `ψ₂ = Ψ₂`. -/
noncomputable def ψ₂ : R[X][Y] :=
  W.toAffine.polynomialY


-- @@ L39-41 verbatim
/-- The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`. -/
noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆


-- @@ L43-46 expanded
lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial :=
  by
  rw [Ψ₂Sq, ψ₂, b₂, b₄, b₆, Affine.polynomialY, Affine.polynomial]
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  ring1


-- @@ L48-49 verbatim
lemma ψ₂_sq : W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial := by
  simp [C_Ψ₂Sq]


-- @@ L51-54 verbatim
lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) := by
  simp [C_Ψ₂Sq]

-- TODO: remove `twoTorsionPolynomial` in favour of `Ψ₂Sq`

-- @@ L55-56 verbatim
lemma Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly :=
  rfl


-- @@ L58-58 verbatim
end Ψ₂Sq


-- @@ L60-60 verbatim
section preΨ'


-- @@ L62-62 verbatim
/-! ### The univariate polynomials `preΨₙ` for `n ∈ ℕ` -/


-- @@ L64-66 verbatim
/-- The `3`-division polynomial `ψ₃ = Ψ₃`. -/
noncomputable def Ψ₃ : R[X] :=
  3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈


-- @@ L68-72 verbatim
/-- The univariate polynomial `preΨ₄`, which is auxiliary to the 4-division polynomial
`ψ₄ = Ψ₄ = preΨ₄ψ₂`. -/
noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)


-- @@ L74-77 verbatim
/-- The univariate polynomials `preΨₙ` for `n ∈ ℕ`, which are auxiliary to the bivariate polynomials
`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. -/
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n


-- @@ L79-81 verbatim
@[simp]
lemma preΨ'_zero : W.preΨ' 0 = 0 :=
  preNormEDS'_zero ..


-- @@ L83-85 verbatim
@[simp]
lemma preΨ'_one : W.preΨ' 1 = 1 :=
  preNormEDS'_one ..


-- @@ L87-89 verbatim
@[simp]
lemma preΨ'_two : W.preΨ' 2 = 1 :=
  preNormEDS'_two ..


-- @@ L91-93 verbatim
@[simp]
lemma preΨ'_three : W.preΨ' 3 = W.Ψ₃ :=
  preNormEDS'_three ..


-- @@ L95-97 verbatim
@[simp]
lemma preΨ'_four : W.preΨ' 4 = W.preΨ₄ :=
  preNormEDS'_four ..


-- @@ L99-102 verbatim
lemma preΨ'_even (m : ℕ) : W.preΨ' (2 * (m + 3)) =
    W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2 :=
  preNormEDS'_even ..


-- @@ L104-107 verbatim
lemma preΨ'_odd (m : ℕ) : W.preΨ' (2 * (m + 2) + 1) =
    W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS'_odd ..


-- @@ L109-109 verbatim
end preΨ'


-- @@ L111-111 verbatim
section preΨ


-- @@ L113-113 verbatim
/-! ### The univariate polynomials `preΨₙ` for `n ∈ ℤ` -/


-- @@ L115-118 verbatim
/-- The univariate polynomials `preΨₙ` for `n ∈ ℤ`, which are auxiliary to the bivariate polynomials
`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. -/
noncomputable def preΨ (n : ℤ) : R[X] :=
  preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n


-- @@ L120-122 verbatim
@[simp]
lemma preΨ_ofNat (n : ℕ) : W.preΨ n = W.preΨ' n :=
  preNormEDS_ofNat ..


-- @@ L124-126 verbatim
@[simp]
lemma preΨ_zero : W.preΨ 0 = 0 :=
  preNormEDS_zero ..


-- @@ L128-130 verbatim
@[simp]
lemma preΨ_one : W.preΨ 1 = 1 :=
  preNormEDS_one ..


-- @@ L132-134 verbatim
@[simp]
lemma preΨ_two : W.preΨ 2 = 1 :=
  preNormEDS_two ..


-- @@ L136-138 verbatim
@[simp]
lemma preΨ_three : W.preΨ 3 = W.Ψ₃ :=
  preNormEDS_three ..


-- @@ L140-142 verbatim
@[simp]
lemma preΨ_four : W.preΨ 4 = W.preΨ₄ :=
  preNormEDS_four ..


-- @@ L144-146 verbatim
@[simp]
lemma preΨ_neg (n : ℤ) : W.preΨ (-n) = -W.preΨ n :=
  preNormEDS_neg ..


-- @@ L148-151 verbatim
lemma preΨ_even (m : ℤ) : W.preΨ (2 * m) =
    W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 :=
  preNormEDS_even ..


-- @@ L153-156 verbatim
lemma preΨ_odd (m : ℤ) : W.preΨ (2 * m + 1) =
    W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS_odd ..


-- @@ L158-158 verbatim
end preΨ


-- @@ L160-160 verbatim
section ΨSq


-- @@ L162-162 verbatim
/-! ### The univariate polynomials `ΨSqₙ` -/


-- @@ L164-166 verbatim
/-- The univariate polynomials `ΨSqₙ` congruent to `ψₙ²`. -/
noncomputable def ΨSq (n : ℤ) : R[X] :=
  W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1


-- @@ L168-170 verbatim
@[simp]
lemma ΨSq_ofNat (n : ℕ) : W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1 := by
  simp [ΨSq]


-- @@ L172-174 verbatim
@[simp]
lemma ΨSq_zero : W.ΨSq 0 = 0 := by
  simp [ΨSq]


-- @@ L176-178 verbatim
@[simp]
lemma ΨSq_one : W.ΨSq 1 = 1 := by
  simp [ΨSq]


-- @@ L180-182 verbatim
@[simp]
lemma ΨSq_two : W.ΨSq 2 = W.Ψ₂Sq := by
  simp [ΨSq]


-- @@ L184-186 verbatim
@[simp]
lemma ΨSq_three : W.ΨSq 3 = W.Ψ₃ ^ 2 := by
  simp [ΨSq, show ¬Even (3 : ℤ) by decide]


-- @@ L188-190 verbatim
@[simp]
lemma ΨSq_four : W.ΨSq 4 = W.preΨ₄ ^ 2 * W.Ψ₂Sq := by
  simp [ΨSq, show ¬Odd (4 : ℤ) by decide]


-- @@ L192-194 verbatim
@[simp]
lemma ΨSq_neg (n : ℤ) : W.ΨSq (-n) = W.ΨSq n := by
  simp [ΨSq]


-- @@ L196-199 verbatim
lemma ΨSq_even (m : ℤ) : W.ΨSq (2 * m) =
    (W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2) ^ 2 * W.Ψ₂Sq := by
  rw [ΨSq, preΨ_even, if_pos <| even_two_mul m]


-- @@ L201-204 verbatim
lemma ΨSq_odd (m : ℤ) : W.ΨSq (2 * m + 1) =
    (W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2)) ^ 2 := by
  rw [ΨSq, preΨ_odd, if_neg m.not_even_two_mul_add_one, mul_one]


-- @@ L206-206 verbatim
end ΨSq


-- @@ L208-208 verbatim
section Ψ


-- @@ L210-210 verbatim
/-! ### The bivariate polynomials `Ψₙ` -/


-- @@ L212-214 verbatim
/-- The bivariate polynomials `Ψₙ` congruent to the `n`-division polynomials `ψₙ`. -/
protected noncomputable def Ψ (n : ℤ) : R[X][Y] :=
  C (W.preΨ n) * if Even n then W.ψ₂ else 1


-- @@ L216-216 verbatim
open WeierstrassCurve (Ψ)


-- @@ L218-220 verbatim
@[simp]
lemma Ψ_ofNat (n : ℕ) : W.Ψ n = C (W.preΨ' n) * if Even n then W.ψ₂ else 1 := by
  simp [Ψ]


-- @@ L222-224 verbatim
@[simp]
lemma Ψ_zero : W.Ψ 0 = 0 := by
  simp [Ψ]


-- @@ L226-228 verbatim
@[simp]
lemma Ψ_one : W.Ψ 1 = 1 := by
  simp [Ψ]


-- @@ L230-232 verbatim
@[simp]
lemma Ψ_two : W.Ψ 2 = W.ψ₂ := by
  simp [Ψ]


-- @@ L234-236 verbatim
@[simp]
lemma Ψ_three : W.Ψ 3 = C W.Ψ₃ := by
  simp [Ψ, show ¬Even (3 : ℤ) by decide]


-- @@ L238-240 verbatim
@[simp]
lemma Ψ_four : W.Ψ 4 = C W.preΨ₄ * W.ψ₂ := by
  simp [Ψ, show ¬Odd (4 : ℤ) by decide]


-- @@ L242-244 verbatim
@[simp]
lemma Ψ_neg (n : ℤ) : W.Ψ (-n) = -W.Ψ n := by
  simp_rw [Ψ, preΨ_neg, C_neg, neg_mul, even_neg]


-- @@ L246-250 expanded
lemma Ψ_even (m : ℤ) :
    W.Ψ (2 * m) * W.ψ₂ =
      W.Ψ (m - 1) ^ 2 * W.Ψ m * W.Ψ (m + 2) - W.Ψ (m - 2) * W.Ψ m * W.Ψ (m + 1) ^ 2 :=
  by
  simp_rw [Ψ, preΨ_even, if_pos <| even_two_mul m, Int.even_add, Int.even_sub, even_two, iff_true,
    Int.not_even_one, iff_false]
  split_ifs <;> simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow] <;> ring1


-- @@ L252-259 expanded
lemma Ψ_odd (m : ℤ) :
    W.Ψ (2 * m + 1) =
      W.Ψ (m + 2) * W.Ψ m ^ 3 - W.Ψ (m - 1) * W.Ψ (m + 1) ^ 3 +
        W.toAffine.polynomial * (16 * W.toAffine.polynomial - 8 * W.ψ₂ ^ 2) *
          C
            (if Even m then W.preΨ (m + 2) * W.preΨ m ^ 3
            else -W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3) :=
  by
  simp_rw [Ψ, preΨ_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub, even_two,
    iff_true, Int.not_even_one, iff_false]
  split_ifs <;> simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow] <;>
      rw [C_Ψ₂Sq] <;>
    ring1


-- @@ L261-263 verbatim
lemma Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) := by
  simp_rw [Ψ, ΨSq, map_mul, apply_ite C, apply_ite <| mk W, mul_pow, ite_pow, mk_ψ₂_sq, map_one,
    one_pow, map_pow]


-- @@ L265-265 verbatim
end Ψ


-- @@ L267-267 verbatim
section Φ


-- @@ L269-269 verbatim
/-! ### The univariate polynomials `Φₙ` -/


-- @@ L271-273 verbatim
/-- The univariate polynomials `Φₙ` congruent to `φₙ`. -/
protected noncomputable def Φ (n : ℤ) : R[X] :=
  X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq


-- @@ L275-275 verbatim
open WeierstrassCurve (Φ)


-- @@ L277-283 verbatim
@[simp]
lemma Φ_ofNat (n : ℕ) : W.Φ (n + 1) =
    X * W.preΨ' (n + 1) ^ 2 * (if Even n then 1 else W.Ψ₂Sq) -
      W.preΨ' (n + 2) * W.preΨ' n * (if Even n then W.Ψ₂Sq else 1) := by
  rw [Φ, add_sub_cancel_right]
  norm_cast
  simp_rw [ΨSq_ofNat, Nat.even_add_one, ite_not, ← mul_assoc, preΨ_ofNat]


-- @@ L285-287 verbatim
@[simp]
lemma Φ_zero : W.Φ 0 = 1 := by
  simp [Φ]


-- @@ L289-291 verbatim
@[simp]
lemma Φ_one : W.Φ 1 = X := by
  simp [Φ]


-- @@ L293-298 expanded
@[simp]
lemma Φ_two : W.Φ 2 = X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈ :=
  by
  rw [show 2 = ((1 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_two, if_neg Nat.not_even_one, Ψ₂Sq,
    preΨ'_three, preΨ'_one, if_neg Nat.not_even_one, Ψ₃]
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  ring1


-- @@ L300-303 verbatim
@[simp]
lemma Φ_three : W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq := by
  rw [show 3 = ((2 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_three, if_pos <| by decide, mul_one,
    preΨ'_four, preΨ'_two, mul_one, if_pos even_two]


-- @@ L305-310 verbatim
@[simp]
lemma Φ_four : W.Φ 4 = X * W.preΨ₄ ^ 2 * W.Ψ₂Sq - W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) := by
  rw [show 4 = ((3 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_four, if_neg <| by decide,
    show 3 + 2 = 2 * 2 + 1 by rfl, preΨ'_odd, preΨ'_four, preΨ'_two, if_pos Even.zero, preΨ'_one,
    preΨ'_three, if_pos Even.zero, if_neg <| by decide]
  ring1


-- @@ L312-315 verbatim
@[simp]
lemma Φ_neg (n : ℤ) : W.Φ (-n) = W.Φ n := by
  simp_rw [Φ, ΨSq_neg, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', preΨ_neg,
    neg_mul_neg, mul_comm <| W.preΨ <| n - 1, even_neg]


-- @@ L317-317 verbatim
end Φ


-- @@ L319-319 verbatim
section ψ


-- @@ L321-321 verbatim
/-! ### The bivariate polynomials `ψₙ` -/


-- @@ L323-325 verbatim
/-- The bivariate `n`-division polynomials `ψₙ`. -/
protected noncomputable def ψ : ℤ → R[X][Y] :=
  normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)


-- @@ L327-327 verbatim
open WeierstrassCurve (Ψ ψ)


-- @@ L329-331 verbatim
@[simp]
lemma ψ_zero : W.ψ 0 = 0 :=
  normEDS_zero ..


-- @@ L333-335 verbatim
@[simp]
lemma ψ_one : W.ψ 1 = 1 :=
  normEDS_one ..


-- @@ L337-339 verbatim
@[simp]
lemma ψ_two : W.ψ 2 = W.ψ₂ :=
  normEDS_two ..


-- @@ L341-343 verbatim
@[simp]
lemma ψ_three : W.ψ 3 = C W.Ψ₃ :=
  normEDS_three ..


-- @@ L345-347 verbatim
@[simp]
lemma ψ_four : W.ψ 4 = C W.preΨ₄ * W.ψ₂ :=
  normEDS_four ..


-- @@ L349-351 verbatim
@[simp]
lemma ψ_neg (n : ℤ) : W.ψ (-n) = -W.ψ n :=
  normEDS_neg ..


-- @@ L353-355 verbatim
lemma ψ_even (m : ℤ) : W.ψ (2 * m) * W.ψ₂ =
    W.ψ (m - 1) ^ 2 * W.ψ m * W.ψ (m + 2) - W.ψ (m - 2) * W.ψ m * W.ψ (m + 1) ^ 2 :=
  normEDS_even ..


-- @@ L357-359 verbatim
lemma ψ_odd (m : ℤ) : W.ψ (2 * m + 1) =
    W.ψ (m + 2) * W.ψ m ^ 3 - W.ψ (m - 1) * W.ψ (m + 1) ^ 3 :=
  normEDS_odd ..


-- @@ L361-362 verbatim
lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) := by
  simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]


-- @@ L364-364 verbatim
end ψ


-- @@ L366-366 verbatim
section φ


-- @@ L368-368 verbatim
/-! ### The bivariate polynomials `φₙ` -/


-- @@ L370-372 verbatim
/-- The bivariate polynomials `φₙ`. -/
protected noncomputable def φ (n : ℤ) : R[X][Y] :=
  C X * (W.ψ n) ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)


-- @@ L374-374 verbatim
open WeierstrassCurve (Ψ Φ φ)


-- @@ L376-378 verbatim
@[simp]
lemma φ_zero : W.φ 0 = 1 := by
  simp [φ]


-- @@ L380-382 verbatim
@[simp]
lemma φ_one : W.φ 1 = C X := by
  simp [φ]


-- @@ L384-386 verbatim
@[simp]
lemma φ_two : W.φ 2 = C X * W.ψ₂ ^ 2 - C W.Ψ₃ := by
  simp [φ]


-- @@ L388-390 verbatim
@[simp]
lemma φ_three : W.φ 3 = C X * C W.Ψ₃ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 2 := by
  simp [φ, mul_assoc, sq]


-- @@ L392-398 verbatim
@[simp]
lemma φ_four :
    W.φ 4 = C X * C W.preΨ₄ ^ 2 * W.ψ₂ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 4 * C W.Ψ₃ + C W.Ψ₃ ^ 4 := by
  rw [φ, ψ_four, show (4 + 1 : ℤ) = 2 * 2 + 1 by rfl, ψ_odd, two_add_two_eq_four, ψ_four,
    show (2 - 1 : ℤ) = 1 by rfl, ψ_two, ψ_one, two_add_one_eq_three, show (4 - 1 : ℤ) = 3 by rfl,
    ψ_three]
  ring1


-- @@ L400-403 verbatim
@[simp]
lemma φ_neg (n : ℤ) : W.φ (-n) = W.φ n := by
  simp_rw [φ, ψ_neg, neg_sq, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', ψ_neg,
    neg_mul_neg, mul_comm <| W.ψ <| n - 1]


-- @@ L405-408 verbatim
lemma Affine.CoordinateRing.mk_φ (n : ℤ) : mk W (W.φ n) = mk W (C <| W.Φ n) := by
  simp_rw [φ, Φ, map_sub, map_mul, map_pow, mk_ψ, mk_Ψ_sq, Ψ, map_mul,
    mul_mul_mul_comm _ <| mk W <| ite .., Int.even_add_one, Int.even_sub_one, ite_not, ← sq,
    apply_ite C, apply_ite <| mk W, ite_pow, map_one, one_pow, mk_ψ₂_sq]


-- @@ L410-410 verbatim
end φ


-- @@ L412-412 verbatim
section Map


-- @@ L414-414 verbatim
/-! ### Maps across ring homomorphisms -/


-- @@ L416-416 verbatim
open WeierstrassCurve (Ψ Φ ψ φ)


-- @@ L418-418 verbatim
variable (f : R →+* S)


-- @@ L420-422 verbatim
@[simp]
lemma map_ψ₂ : (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f) := by
  simp_rw [ψ₂, Affine.map_polynomialY]


-- @@ L424-426 verbatim
@[simp]
lemma map_Ψ₂Sq : (W.map f).Ψ₂Sq = W.Ψ₂Sq.map f := by
  simp [Ψ₂Sq, map_ofNat]


-- @@ L428-430 verbatim
@[simp]
lemma map_Ψ₃ : (W.map f).Ψ₃ = W.Ψ₃.map f := by
  simp [Ψ₃]


-- @@ L432-434 verbatim
@[simp]
lemma map_preΨ₄ : (W.map f).preΨ₄ = W.preΨ₄.map f := by
  simp [preΨ₄]


-- @@ L436-438 verbatim
@[simp]
lemma map_preΨ' (n : ℕ) : (W.map f).preΨ' n = (W.preΨ' n).map f := by
  simp [preΨ', map_preNormEDS', ← coe_mapRingHom]


-- @@ L440-442 verbatim
@[simp]
lemma map_preΨ (n : ℤ) : (W.map f).preΨ n = (W.preΨ n).map f := by
  simp [preΨ, map_preNormEDS, ← coe_mapRingHom]


-- @@ L444-446 verbatim
@[simp]
lemma map_ΨSq (n : ℤ) : (W.map f).ΨSq n = (W.ΨSq n).map f := by
  simp [ΨSq, ← coe_mapRingHom, apply_ite <| mapRingHom f]


-- @@ L448-451 verbatim
@[simp]
lemma map_Ψ (n : ℤ) : (W.map f).Ψ n = (W.Ψ n).map (mapRingHom f) := by
  rw [← coe_mapRingHom]
  simp [Ψ, apply_ite <| mapRingHom _]


-- @@ L453-456 verbatim
@[simp]
lemma map_Φ (n : ℤ) : (W.map f).Φ n = (W.Φ n).map f := by
  rw [← coe_mapRingHom]
  simp [Φ, map_sub, apply_ite <| mapRingHom f]


-- @@ L458-461 verbatim
@[simp]
lemma map_ψ (n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f) := by
  rw [← coe_mapRingHom]
  simp [ψ, map_normEDS]


-- @@ L463-465 verbatim
@[simp]
lemma map_φ (n : ℤ) : (W.map f).φ n = (W.φ n).map (mapRingHom f) := by
  simp [φ]


-- @@ L467-467 verbatim
end Map


-- @@ L469-469 verbatim
section BaseChange


-- @@ L471-471 verbatim
/-! ### Base changes across algebra homomorphisms -/


-- @@ L473-474 verbatim
variable [Algebra R S] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)


-- @@ L476-477 verbatim
lemma baseChange_ψ₂ : (W.baseChange B).ψ₂ = (W.baseChange A).ψ₂.map (mapRingHom f) := by
  rw [← map_ψ₂, map_baseChange]


-- @@ L479-480 verbatim
lemma baseChange_Ψ₂Sq : (W.baseChange B).Ψ₂Sq = (W.baseChange A).Ψ₂Sq.map f := by
  rw [← map_Ψ₂Sq, map_baseChange]


-- @@ L482-483 verbatim
lemma baseChange_Ψ₃ : (W.baseChange B).Ψ₃ = (W.baseChange A).Ψ₃.map f := by
  rw [← map_Ψ₃, map_baseChange]


-- @@ L485-486 verbatim
lemma baseChange_preΨ₄ : (W.baseChange B).preΨ₄ = (W.baseChange A).preΨ₄.map f := by
  rw [← map_preΨ₄, map_baseChange]


-- @@ L488-489 verbatim
lemma baseChange_preΨ' (n : ℕ) : (W.baseChange B).preΨ' n = ((W.baseChange A).preΨ' n).map f := by
  rw [← map_preΨ', map_baseChange]


-- @@ L491-492 verbatim
lemma baseChange_preΨ (n : ℤ) : (W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f := by
  rw [← map_preΨ, map_baseChange]


-- @@ L494-495 verbatim
lemma baseChange_ΨSq (n : ℤ) : (W.baseChange B).ΨSq n = ((W.baseChange A).ΨSq n).map f := by
  rw [← map_ΨSq, map_baseChange]


-- @@ L497-498 verbatim
lemma baseChange_Ψ (n : ℤ) : (W.baseChange B).Ψ n = ((W.baseChange A).Ψ n).map (mapRingHom f) := by
  rw [← map_Ψ, map_baseChange]


-- @@ L500-501 verbatim
lemma baseChange_Φ (n : ℤ) : (W.baseChange B).Φ n = ((W.baseChange A).Φ n).map f := by
  rw [← map_Φ, map_baseChange]


-- @@ L503-504 verbatim
lemma baseChange_ψ (n : ℤ) : (W.baseChange B).ψ n = ((W.baseChange A).ψ n).map (mapRingHom f) := by
  rw [← map_ψ, map_baseChange]


-- @@ L506-507 verbatim
lemma baseChange_φ (n : ℤ) : (W.baseChange B).φ n = ((W.baseChange A).φ n).map (mapRingHom f) := by
  rw [← map_φ, map_baseChange]


-- @@ L509-509 verbatim
end BaseChange


-- @@ L511-511 verbatim
end WeierstrassCurve
