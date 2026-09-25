import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import IdealArithmetic.DedekindProject.Polynomial.BrillhartIrreducibilityTest


-- @@ L5-5 verbatim
open Polynomial


-- @@ L7-7 verbatim
local notation "T" => (X^6 - 5*X^4 - 50*X^2 + 125 : ℤ[X])


-- @@ L9-9 verbatim
local notation "l" => [125, 0, -50, 0, -5, 0, 1]


-- @@ L11-11 verbatim
unseal Rat.add Rat.mul Rat.inv


-- @@ L13-13 expanded
lemma T_ofList' :
    (X ^ 6 - 5 * X ^ 4 - 50 * X ^ 2 + 125 : ℤ[X]) = ofList [125, 0, -50, 0, -5, 0, 1] := by
  norm_num; ring


-- @@ L14-29 expanded
noncomputable def C :
    CertificateIrreducibleIntOfPrime (X ^ 6 - 5 * X ^ 4 - 50 * X ^ 2 + 125 : ℤ[X])
      [125, 0, -50, 0, -5, 0, 1]
    where
  hpol := T_ofList'
  hdeg := by decide
  hprim := by decide
  hlz := by decide
  s := 1
  P := 38501
  M := 6
  r := 13 / 4
  ρ := 249 / 52
  hPPrime := by norm_num
  hrpos := by norm_num
  hrhoeq := by decide
  hrho := by decide
  hs := by norm_num
  heval := by norm_num


-- @@ L31-31 expanded
theorem irreducible_T : Irreducible (X ^ 6 - 5 * X ^ 4 - 50 * X ^ 2 + 125 : ℤ[X]) :=
  irreducible_of_CertificateIrreducibleIntOfPrime _ _ C

