import LeanBridge.ForMathlib.QExpansion.Generic
import LeanBridge.ForMathlib.QExpansion.Examples  -- for `qexp_certify` macro


-- @@ L4-15 verbatim
/-!
# LMFDB level-1 modular form `1.12.a.a`

The unique normalized cusp form of weight 12 (the modular discriminant Δ).

Polynomial in `(E₄, E₆)`, computed by Sage:
  `(1/1728) · E₄³ · E₆⁰ + (-1/1728) · E₄⁰ · E₆²`

Sturm bound for weight 12: `⌊12/12⌋ + 1 = 2`. Verifying agreement on the first 2
q-coefficients with the LMFDB-published expansion would, by Sturm + injectivity of
`evalE₄E₆`, identify this form as THE LMFDB form `1.12.a.a`.
-/


-- @@ L17-17 verbatim
namespace LeanBridge.QExpansion


-- @@ L19-19 verbatim
open ModularForm EisensteinSeries PowerSeries UpperHalfPlane

-- @@ L20-20 verbatim
open scoped MatrixGroups


-- @@ L22-24 verbatim
/-- Polynomial encoding of `1.12.a.a` in `(E₄, E₆)`. -/
def lmfdb_1_12_a_a_polyData : List (ℕ × ℕ × ℚ) :=
  [(3, 0, 1 / 1728), (0, 2, -(1 / 1728))]


-- @@ L26-29 verbatim
/-- The level-1 modular form `1.12.a.a`, defined as the polynomial in `E₄, E₆`. -/
noncomputable def lmfdb_1_12_a_a : ModularForm 𝒮ℒ 12 :=
  (1 / 1728 : ℂ) • mkMonomForm 3 0 12 (by decide) +
  (-(1 / 1728) : ℂ) • mkMonomForm 0 2 12 (by decide)


-- @@ L31-43 verbatim
lemma lmfdb_1_12_a_a_qExpansion_eq_evalEisPS :
    qExpansion 1 (lmfdb_1_12_a_a : ℍ → ℂ) = evalEisPS lmfdb_1_12_a_a_polyData := by
  unfold lmfdb_1_12_a_a
  rw [ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
    ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    qExpansion_mkMonomForm, qExpansion_mkMonomForm]
  unfold evalEisPS lmfdb_1_12_a_a_polyData monomialEisPS
  simp only [List.foldr_cons, List.foldr_nil, add_zero]
  push_cast
  module


-- @@ L45-49 verbatim
theorem lmfdb_1_12_a_a_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (lmfdb_1_12_a_a : ℍ → ℂ))
      = ((evalEisList lmfdb_1_12_a_a_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 lmfdb_1_12_a_a_polyData _
    lmfdb_1_12_a_a_qExpansion_eq_evalEisPS N n hn


-- @@ L51-54 verbatim
/-! ## Sturm-bound certificates

Sturm bound for weight 12 is 2. The first 2 q-coefficients of the LMFDB form `1.12.a.a` are
`[0, 1]` (the form is normalized so that `q¹` coefficient is 1, and constant term is 0). -/


-- @@ L56-59 expanded
/-- Constant term: 0 (cusp form). -/
example : (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (lmfdb_1_12_a_a : ℍ → ℂ)) = 0 := by
  ( rw [lmfdb_1_12_a_a_qExpansion_coeff 2 0 (by decide),
      show (evalEisList lmfdb_1_12_a_a_polyData 2).getD 0 0 = ((0) : ℚ) from by decide +kernel]
    push_cast; rfl)


-- @@ L61-67 expanded
/-- First Hecke eigenvalue: 1 (normalized form). -/
example : (PowerSeries.coeff (R := ℂ) 1) (qExpansion 1 (lmfdb_1_12_a_a : ℍ → ℂ)) = 1 := by
  ( rw [lmfdb_1_12_a_a_qExpansion_coeff 2 1 (by decide),
      show
        (evalEisList lmfdb_1_12_a_a_polyData 2).getD 1 0 =
          ((1)
              /- By the Sturm bound (and injectivity of `evalE₄E₆` from PR #38813), `lmfdb_1_12_a_a`
              above equals the LMFDB form labelled `1.12.a.a` (the modular discriminant Δ). -/
               :
            ℚ)
        from by decide +kernel]
    push_cast; rfl)


-- @@ L69-69 verbatim
end LeanBridge.QExpansion
