import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import IdealArithmetic.DedekindProject.Polynomial.BrillhartIrreducibilityTest


-- @@ L5-5 verbatim
open Polynomial


-- @@ L7-7 verbatim
local notation "T" => (X^5 - X^4 + 3*X^2 + 21*X + 4 : ℤ[X])


-- @@ L9-9 verbatim
local notation "l" => [4, 21, 3, 0, -1, 1]


-- @@ L11-11 verbatim
unseal Rat.add Rat.mul Rat.inv


-- @@ L13-13 expanded
lemma T_ofList' : (X ^ 5 - X ^ 4 + 3 * X ^ 2 + 21 * X + 4 : ℤ[X]) = ofList [4, 21, 3, 0, -1, 1] :=
  by norm_num; ring


-- @@ L15-30 expanded
noncomputable def C :
    CertificateIrreducibleIntOfPrime (X ^ 5 - X ^ 4 + 3 * X ^ 2 + 21 * X + 4 : ℤ[X])
      [4, 21, 3, 0, -1, 1]
    where
  hpol := T_ofList'
  hdeg := by decide
  hprim := by decide
  hlz := by decide
  s := 2
  P := 3359
  M := 6
  r := 11 / 4
  ρ := 20017 / 5324
  hPPrime := by norm_num
  hrpos := by norm_num
  hrhoeq := by decide
  hrho := by decide
  hs := by norm_num
  heval := by norm_num


-- @@ L32-32 expanded
theorem irreducible_T : Irreducible (X ^ 5 - X ^ 4 + 3 * X ^ 2 + 21 * X + 4 : ℤ[X]) :=
  irreducible_of_CertificateIrreducibleIntOfPrime _ _ C

