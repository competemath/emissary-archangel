import Mathlib
import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest


-- @@ L6-6 verbatim
namespace LMFDB_2_0_55_1


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open NumberField Polynomial


-- @@ L12-12 verbatim
abbrev min_poly_2_0_55_1 : Polynomial ℚ := (1) * Polynomial.X ^ 2 + (-1) * Polynomial.X + (14)


-- @@ L14-14 verbatim
abbrev K_2_0_55_1 := AdjoinRoot min_poly_2_0_55_1




-- @@ L18-18 verbatim
open Polynomial


-- @@ L20-20 verbatim
local notation "T" => (X^2 - X + 14 : ℤ[X])


-- @@ L22-22 verbatim
local notation "l" => [14, -1, 1]


-- @@ L24-24 verbatim
lemma T_ofList' : T = ofList l := by norm_num ; ring
    

-- @@ L26-41 verbatim
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 14
 P := 59
 M := -28
 r := 7/2
 ρ := 15/2
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num


-- @@ L43-43 verbatim
theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 




-- @@ L47-47 verbatim
abbrev K_gen_2_0_55_1 : K_2_0_55_1 := AdjoinRoot.root min_poly_2_0_55_1


-- @@ L49-60 verbatim
lemma irreducible_poly : Irreducible min_poly_2_0_55_1 := by
  have := irreducible_T
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast] at this
  · convert this
    simp
    ring
  · refine Polynomial.Monic.isPrimitive ?_
    refine Polynomial.Monic.def.mpr ?_
    rw [T_ofList', ofList_leadingCoeff]
    · simp
    · apply List.cons_ne_nil _ _
    · rfl


-- @@ L62-62 verbatim
instance : Fact (Irreducible min_poly_2_0_55_1) := ⟨irreducible_poly⟩




-- @@ L66-66 verbatim
axiom LMFDB_NF_2_0_55_1_discr : NumberField.discr K_2_0_55_1 = -55


-- @@ L68-68 verbatim
axiom LMFDB_NF_2_0_55_1_isGalois : IsGalois ℚ K_2_0_55_1


-- @@ L70-70 verbatim
axiom LMFDB_NF_2_0_55_1_classNumber : NumberField.classNumber K_2_0_55_1 = 4


-- @@ L72-72 verbatim
axiom LMFDB_NF_2_0_55_1_totallyComplex : IsTotallyComplex K_2_0_55_1


-- @@ L74-74 verbatim
instance LMFDB_NF_2_0_55_1_totallyComplexInstance : IsTotallyComplex K_2_0_55_1 := LMFDB_NF_2_0_55_1_totallyComplex


-- @@ L76-76 verbatim
axiom LMFDB_NF_2_0_55_1_isCM : NumberField.IsCMField K_2_0_55_1


-- @@ L78-78 verbatim
end
