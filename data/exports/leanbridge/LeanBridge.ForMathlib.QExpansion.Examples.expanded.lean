import LeanBridge.ForMathlib.QExpansion.DeltaBridge


-- @@ L3-20 verbatim
/-!
# Examples: certifying q-expansion coefficients for several level-1 modular forms

This file demonstrates the generic framework on several level-1 modular forms beyond `Δ`:

* `E₄` itself (weight 4), polynomial encoding `[(1, 0, 1)]`.
* `E₆` itself (weight 6), polynomial encoding `[(0, 1, 1)]`.
* `E₄² = E₈` (weight 8, since `dim M₈ = 1`), polynomial encoding `[(2, 0, 1)]`.
* `E₄ · E₆ = E₁₀` (weight 10, since `dim M₁₀ = 1`), polynomial encoding `[(1, 1, 1)]`.
* `Δ` (weight 12), polynomial encoding `[(3, 0, 1/1728), (0, 2, -1/1728)]`.

For each form we define:
* `<form>_polyData : List (ℕ × ℕ × ℚ)` — the polynomial in `E₄, E₆`.
* `<form>_qExpansion_eq_evalEisPS` — the bridge lemma.
* `<form>_qExpansion_coeff` — the coefficient corollary, derived via `qexp_coeff_via_E4E6`.

A single unified `qexp_certify` macro handles all forms uniformly.
-/


-- @@ L22-22 verbatim
namespace LeanBridge.QExpansion


-- @@ L24-24 verbatim
open ModularForm EisensteinSeries PowerSeries UpperHalfPlane

-- @@ L25-25 verbatim
open scoped MatrixGroups


-- @@ L27-35 verbatim
/-! ## Unified `qexp_certify` macro

Bundles the rewrite + `decide +kernel` + cast pattern for any form expressible as a
polynomial in `E₄`, `E₆`. The user supplies:

* `thm` — the per-form coefficient theorem (built from `qexp_coeff_via_E4E6`),
* `poly` — the polynomial encoding,
* `precision` / `idx` / `value` — as before.
-/


-- @@ L37-38 verbatim
/-- Positional syntax: `qexp_certify <thm> <poly> <precision> <idx> <value>`. -/
syntax "qexp_certify" term:max term:max num num term:max : tactic


-- @@ L40-45 verbatim
macro_rules
  | `(tactic| qexp_certify $thm:term $poly:term $N:num $n:num $v:term) =>
    `(tactic|
        (rw [$thm $N $n (by decide),
             show (evalEisList $poly $N).getD $n 0 = ($v : ℚ) from by decide +kernel]
         push_cast; rfl))


-- @@ L47-47 verbatim
/-! ## E₄ -/


-- @@ L49-50 verbatim
/-- E₄ as a polynomial in `(E₄, E₆)`: just `1 · E₄¹ · E₆⁰`. -/
def E4_polyData : List (ℕ × ℕ × ℚ) := [(1, 0, 1)]


-- @@ L52-55 verbatim
lemma E4_qExpansion_eq_evalEisPS :
    qExpansion 1 (↑E₄ : ℍ → ℂ) = evalEisPS E4_polyData := by
  unfold evalEisPS E4_polyData monomialEisPS
  simp


-- @@ L57-60 verbatim
theorem E4_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (↑E₄ : ℍ → ℂ))
      = ((evalEisList E4_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 E4_polyData _ E4_qExpansion_eq_evalEisPS N n hn


-- @@ L62-65 expanded
/-- E₄ q-expansion: `1 + 240q + 2160q² + 6720q³ + 17520q⁴ + 30240q⁵`. -/
example : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (↑E₄ : ℍ → ℂ)) = 1 := by
  ( rw [E4_qExpansion_coeff 6 0 (by decide),
      show (evalEisList E4_polyData 6).getD 0 0 = ((1) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L67-69 expanded
example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (↑E₄ : ℍ → ℂ)) = 240 := by
  ( rw [E4_qExpansion_coeff 6 1 (by decide),
      show (evalEisList E4_polyData 6).getD 1 0 = ((240) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L71-73 expanded
example : (PowerSeries.coeff (R := ℂ) 2) (qExpansion 1 (↑E₄ : ℍ → ℂ)) = 2160 := by
  ( rw [E4_qExpansion_coeff 6 2 (by decide),
      show (evalEisList E4_polyData 6).getD 2 0 = ((2160) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L75-77 expanded
example : (PowerSeries.coeff (R := ℂ) 5) (qExpansion 1 (↑E₄ : ℍ → ℂ)) = 30240 := by
  ( rw [E4_qExpansion_coeff 6 5 (by decide),
      show (evalEisList E4_polyData 6).getD 5 0 = ((30240) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L79-79 verbatim
/-! ## E₆ -/


-- @@ L81-82 verbatim
/-- E₆ as a polynomial in `(E₄, E₆)`: just `1 · E₄⁰ · E₆¹`. -/
def E6_polyData : List (ℕ × ℕ × ℚ) := [(0, 1, 1)]


-- @@ L84-87 verbatim
lemma E6_qExpansion_eq_evalEisPS :
    qExpansion 1 (↑E₆ : ℍ → ℂ) = evalEisPS E6_polyData := by
  unfold evalEisPS E6_polyData monomialEisPS
  simp


-- @@ L89-92 verbatim
theorem E6_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (↑E₆ : ℍ → ℂ))
      = ((evalEisList E6_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 E6_polyData _ E6_qExpansion_eq_evalEisPS N n hn


-- @@ L94-97 expanded
/-- E₆ q-expansion: `1 - 504q - 16632q² - 122976q³ - 532728q⁴ - 1575504q⁵`. -/
example : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (↑E₆ : ℍ → ℂ)) = 1 := by
  ( rw [E6_qExpansion_coeff 6 0 (by decide),
      show (evalEisList E6_polyData 6).getD 0 0 = ((1) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L99-101 expanded
example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (↑E₆ : ℍ → ℂ)) = -504 := by
  ( rw [E6_qExpansion_coeff 6 1 (by decide),
      show (evalEisList E6_polyData 6).getD 1 0 = ((-504) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L103-105 expanded
example : (PowerSeries.coeff (R := ℂ) 5) (qExpansion 1 (↑E₆ : ℍ → ℂ)) = -1575504 := by
  ( rw [E6_qExpansion_coeff 6 5 (by decide),
      show (evalEisList E6_polyData 6).getD 5 0 = ((-1575504) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L107-107 verbatim
/-! ## E₄² (a weight-8 form, equal to E₈) -/


-- @@ L109-110 verbatim
/-- The level-1 modular form `E₄²` of weight 8. Up to normalization this is `E₈`. -/
noncomputable def E4Sq : ModularForm 𝒮ℒ 8 := ModularForm.mcast (by decide) (E₄.pow 2)


-- @@ L112-114 verbatim
lemma E4Sq_apply (z : ℍ) : E4Sq z = E₄ z ^ 2 := by
  change ⇑(E₄.pow 2) z = _
  rw [coe_pow]; rfl


-- @@ L116-117 verbatim
/-- E₄² as a polynomial in `(E₄, E₆)`: just `1 · E₄² · E₆⁰`. -/
def E4Sq_polyData : List (ℕ × ℕ × ℚ) := [(2, 0, 1)]


-- @@ L119-125 verbatim
lemma E4Sq_qExpansion_eq_evalEisPS :
    qExpansion 1 (E4Sq : ℍ → ℂ) = evalEisPS E4Sq_polyData := by
  show qExpansion 1 ⇑(ModularForm.mcast (by decide) (E₄.pow 2)) = _
  change qExpansion 1 ⇑(E₄.pow 2) = _
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 2]
  unfold evalEisPS E4Sq_polyData monomialEisPS
  simp


-- @@ L127-130 verbatim
theorem E4Sq_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (E4Sq : ℍ → ℂ))
      = ((evalEisList E4Sq_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 E4Sq_polyData _ E4Sq_qExpansion_eq_evalEisPS N n hn


-- @@ L132-136 expanded
/-- E₄² q-expansion: `1 + 480q + 61920q² + 1050240q³ + …`.
Compare to `E₈ = 1 + 480 σ₇(n) q^n`: c₂ = `480 · σ₇(2) = 480 · 129 = 61920`. -/
example : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (E4Sq : ℍ → ℂ)) = 1 := by
  ( rw [E4Sq_qExpansion_coeff 5 0 (by decide),
      show (evalEisList E4Sq_polyData 5).getD 0 0 = ((1) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L138-140 expanded
example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (E4Sq : ℍ → ℂ)) = 480 := by
  ( rw [E4Sq_qExpansion_coeff 5 1 (by decide),
      show (evalEisList E4Sq_polyData 5).getD 1 0 = ((480) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L142-144 expanded
example : (PowerSeries.coeff (R := ℂ) 2) (qExpansion 1 (E4Sq : ℍ → ℂ)) = 61920 := by
  ( rw [E4Sq_qExpansion_coeff 5 2 (by decide),
      show (evalEisList E4Sq_polyData 5).getD 2 0 = ((61920) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L146-148 expanded
example : (PowerSeries.coeff (R := ℂ) 3) (qExpansion 1 (E4Sq : ℍ → ℂ)) = 1050240 := by
  ( rw [E4Sq_qExpansion_coeff 5 3 (by decide),
      show (evalEisList E4Sq_polyData 5).getD 3 0 = ((1050240) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L150-150 verbatim
/-! ## E₄ · E₆ (a weight-10 form, equal to E₁₀) -/


-- @@ L152-153 verbatim
/-- The level-1 modular form `E₄ · E₆` of weight 10. Up to normalization this is `E₁₀`. -/
noncomputable def E4MulE6 : ModularForm 𝒮ℒ 10 := ModularForm.mcast (by decide) (E₄.mul E₆)


-- @@ L155-157 verbatim
lemma E4MulE6_apply (z : ℍ) : E4MulE6 z = E₄ z * E₆ z := by
  change ⇑(E₄.mul E₆) z = _
  rfl


-- @@ L159-160 verbatim
/-- E₄ · E₆ as a polynomial in `(E₄, E₆)`: `1 · E₄¹ · E₆¹`. -/
def E4MulE6_polyData : List (ℕ × ℕ × ℚ) := [(1, 1, 1)]


-- @@ L162-168 verbatim
lemma E4MulE6_qExpansion_eq_evalEisPS :
    qExpansion 1 (E4MulE6 : ℍ → ℂ) = evalEisPS E4MulE6_polyData := by
  show qExpansion 1 ⇑(ModularForm.mcast (by decide) (E₄.mul E₆)) = _
  change qExpansion 1 ⇑(E₄.mul E₆) = _
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL E₄ E₆]
  unfold evalEisPS E4MulE6_polyData monomialEisPS
  simp


-- @@ L170-173 verbatim
theorem E4MulE6_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (E4MulE6 : ℍ → ℂ))
      = ((evalEisList E4MulE6_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 E4MulE6_polyData _ E4MulE6_qExpansion_eq_evalEisPS N n hn


-- @@ L175-179 expanded
/-- E₄ · E₆ q-expansion: `1 - 264q - 135432q² - 5196576q³ - …`.
Compare to `E₁₀ = 1 - 264 σ₉(n) q^n`: c₂ = `-264 · σ₉(2) = -264 · 513 = -135432`. -/
example : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (E4MulE6 : ℍ → ℂ)) = 1 := by
  ( rw [E4MulE6_qExpansion_coeff 5 0 (by decide),
      show (evalEisList E4MulE6_polyData 5).getD 0 0 = ((1) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L181-183 expanded
example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (E4MulE6 : ℍ → ℂ)) = -264 := by
  ( rw [E4MulE6_qExpansion_coeff 5 1 (by decide),
      show (evalEisList E4MulE6_polyData 5).getD 1 0 = ((-264) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L185-187 expanded
example : (PowerSeries.coeff (R := ℂ) 2) (qExpansion 1 (E4MulE6 : ℍ → ℂ)) = -135432 := by
  ( rw [E4MulE6_qExpansion_coeff 5 2 (by decide),
      show (evalEisList E4MulE6_polyData 5).getD 2 0 = ((-135432) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L189-191 expanded
example : (PowerSeries.coeff (R := ℂ) 3) (qExpansion 1 (E4MulE6 : ℍ → ℂ)) = -5196576 := by
  ( rw [E4MulE6_qExpansion_coeff 5 3 (by decide),
      show (evalEisList E4MulE6_polyData 5).getD 3 0 = ((-5196576) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L193-193 verbatim
/-! ## Δ — same unified macro -/


-- @@ L195-199 expanded
/-- Same as `discriminant_qExpansion_coeff_via_generic` but going through the unified macro. -/
example : (PowerSeries.coeff (R := ℂ) 5) (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 4830 :=
  by
  ( rw [discriminant_qExpansion_coeff_via_generic 12 5 (by decide),
      show (evalEisList Delta_polyData 12).getD 5 0 = ((4830) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L201-204 expanded
example :
    (PowerSeries.coeff (R := ℂ) 11) (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) = 534612 := by
  ( rw [discriminant_qExpansion_coeff_via_generic 12 11 (by decide),
      show (evalEisList Delta_polyData 12).getD 11 0 = ((534612) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L206-206 verbatim
end LeanBridge.QExpansion
