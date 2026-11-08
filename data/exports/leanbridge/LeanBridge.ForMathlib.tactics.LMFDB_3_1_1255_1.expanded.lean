import Mathlib
import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest


-- @@ L6-6 verbatim
namespace LMFDB_3_1_1255_1


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open NumberField Polynomial


-- @@ L12-12 verbatim
abbrev min_poly_3_1_1255_1 : Polynomial ℚ := (1) * Polynomial.X ^ 3 + (-1) * Polynomial.X ^ 2 + (4) * Polynomial.X + (5)


-- @@ L14-14 verbatim
abbrev K_3_1_1255_1 := AdjoinRoot min_poly_3_1_1255_1




-- @@ L18-18 verbatim
open Polynomial


-- @@ L20-20 verbatim
local notation "T" => (X^3 - X^2 + 4*X + 5 : ℤ[X])


-- @@ L22-22 verbatim
local notation "l" => [5, 4, -1, 1]


-- @@ L24-24 verbatim
lemma T_ofList' : T = ofList l := by norm_num ; ring
    

-- @@ L26-41 verbatim
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 5
 P := 227
 M := -10
 r := 2
 ρ := 4
 hPPrime := by norm_num
 hrpos := by norm_num
 hrhoeq := by decide +kernel
 hrho := by decide +kernel
 hs := by norm_num
 heval := by norm_num


-- @@ L43-45 verbatim
theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C 

-- Fundamental Units




-- @@ L49-49 verbatim
abbrev K_gen_3_1_1255_1 : K_3_1_1255_1 := AdjoinRoot.root min_poly_3_1_1255_1


-- @@ L51-62 verbatim
lemma irreducible_poly : Irreducible min_poly_3_1_1255_1 := by
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


-- @@ L64-64 verbatim
instance : Fact (Irreducible min_poly_3_1_1255_1) := ⟨irreducible_poly⟩


-- @@ L66-67 verbatim
lemma K_int_3_1_1255_1 : IsIntegral ℤ K_gen_3_1_1255_1 := by
  sorry


-- @@ L69-69 verbatim
def K_gen_int_3_1_1255_1 : 𝓞 K_3_1_1255_1 := ⟨K_gen_3_1_1255_1, K_int_3_1_1255_1⟩


-- @@ L71-75 verbatim
def fundamental_unit_3_1_1255_1_1 : (𝓞 K_3_1_1255_1)ˣ where
  val := -K_gen_int_3_1_1255_1 - 1
  inv := -K_gen_int_3_1_1255_1^2 + 2 * K_gen_int_3_1_1255_1 - 6
  val_inv := by sorry
  inv_val := by sorry




-- @@ L79-79 verbatim
axiom LMFDB_NF_3_1_1255_1_discr : NumberField.discr K_3_1_1255_1 = -1255


-- @@ L81-81 verbatim
axiom LMFDB_NF_3_1_1255_1_isGalois : ¬ IsGalois ℚ K_3_1_1255_1


-- @@ L83-83 verbatim
axiom LMFDB_NF_3_1_1255_1_classNumber : NumberField.classNumber K_3_1_1255_1 = 2



-- @@ L86-86 verbatim
end
