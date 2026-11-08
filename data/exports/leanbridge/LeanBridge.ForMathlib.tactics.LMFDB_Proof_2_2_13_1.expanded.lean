import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest


-- @@ L5-5 verbatim
open Polynomial


-- @@ L7-7 verbatim
local notation "T" => (X^2 - X - 3 : ℤ[X])


-- @@ L9-9 verbatim
local notation "l" => [-3, -1, 1]


-- @@ L11-11 expanded
lemma T_ofList' : (X ^ 2 - X - 3 : ℤ[X]) = ofList [-3, -1, 1] := by norm_num; ring


-- @@ L13-28 expanded
noncomputable def C : CertificateIrreducibleIntOfPrime (X ^ 2 - X - 3 : ℤ[X]) [-3, -1, 1]
    where
  hpol := T_ofList'
  hdeg := by decide
  hprim := by decide
  hlz := by decide
  s := 3
  P := 13
  M := 7
  r := 3 / 2
  ρ := 7 / 2
  hPPrime := by norm_num
  hrpos := by norm_num
  hrhoeq := by decide +kernel
  hrho := by decide +kernel
  hs := by norm_num
  heval := by norm_num


-- @@ L30-30 expanded
theorem irreducible_T : Irreducible (X ^ 2 - X - 3 : ℤ[X]) :=
  irreducible_of_CertificateIrreducibleIntOfPrime _ _ C

