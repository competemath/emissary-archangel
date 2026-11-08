import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest


-- @@ L5-5 verbatim
open Polynomial


-- @@ L7-7 verbatim
local notation "T" => (X^4 + 5*X^2 + 7 : ℤ[X])


-- @@ L9-9 verbatim
local notation "l" => [7, 0, 5, 0, 1]


-- @@ L11-11 expanded
lemma T_ofList' : (X ^ 4 + 5 * X ^ 2 + 7 : ℤ[X]) = ofList [7, 0, 5, 0, 1] := by norm_num; ring


-- @@ L13-28 expanded
noncomputable def C :
    CertificateIrreducibleIntOfPrime (X ^ 4 + 5 * X ^ 2 + 7 : ℤ[X]) [7, 0, 5, 0, 1]
    where
  hpol := T_ofList'
  hdeg := by decide
  hprim := by decide
  hlz := by decide
  s := 1
  P := 1483
  M := 6
  r := 2
  ρ := 9 / 2
  hPPrime := by norm_num
  hrpos := by norm_num
  hrhoeq := by decide +kernel
  hrho := by decide +kernel
  hs := by norm_num
  heval := by norm_num


-- @@ L30-30 expanded
theorem irreducible_T : Irreducible (X ^ 4 + 5 * X ^ 2 + 7 : ℤ[X]) :=
  irreducible_of_CertificateIrreducibleIntOfPrime _ _ C

