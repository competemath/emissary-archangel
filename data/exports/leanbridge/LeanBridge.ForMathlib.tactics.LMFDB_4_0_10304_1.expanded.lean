import Mathlib
import LeanBridge.ForMathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.ForMathlib.Irreduciblepolys.BrillhartIrreducibilityTest


-- @@ L6-6 verbatim
namespace LMFDB_4_0_10304_1


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open NumberField Polynomial


-- @@ L12-12 verbatim
abbrev min_poly_4_0_10304_1 : Polynomial ℚ := (1) * Polynomial.X ^ 4 + (-2) * Polynomial.X ^ 3 + (7) * Polynomial.X ^ 2 + (-4) * Polynomial.X + (14)


-- @@ L14-14 verbatim
abbrev K_4_0_10304_1 := AdjoinRoot min_poly_4_0_10304_1




-- @@ L18-18 verbatim
open Polynomial


-- @@ L20-20 verbatim
local notation "T" => (X^4 - 2*X^3 + 7*X^2 - 4*X + 14 : ℤ[X])


-- @@ L22-22 verbatim
local notation "l" => [14, -4, 7, -2, 1]


-- @@ L24-24 verbatim
lemma T_ofList' : T = ofList l := by norm_num ; ring
    

-- @@ L26-41 verbatim
noncomputable def C : CertificateIrreducibleIntOfPrime T l where
 hpol := T_ofList'
 hdeg := by decide
 hprim := by decide
 hlz := by decide
 s := 2
 P := 4337
 M := 10
 r := 5/2
 ρ := 53/10
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
abbrev K_gen_4_0_10304_1 : K_4_0_10304_1 := AdjoinRoot.root min_poly_4_0_10304_1


-- @@ L51-62 verbatim
lemma irreducible_poly : Irreducible min_poly_4_0_10304_1 := by
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
instance : Fact (Irreducible min_poly_4_0_10304_1) := ⟨irreducible_poly⟩


-- @@ L66-67 verbatim
lemma K_int_4_0_10304_1 : IsIntegral ℤ K_gen_4_0_10304_1 := by
  sorry


-- @@ L69-69 verbatim
def K_gen_int_4_0_10304_1 : 𝓞 K_4_0_10304_1 := ⟨K_gen_4_0_10304_1, K_int_4_0_10304_1⟩


-- @@ L71-80 verbatim
def fundamental_unit_4_0_10304_1_1 : (𝓞 K_4_0_10304_1)ˣ where
  -- The unit's coordinates in the power basis are rational, so the value must be built in the
  -- field `K` (which has division) and then coerced into `𝓞 K`; the ring of integers itself has
  -- no `Div`. Integrality holds (it is a unit) but is left as `sorry`, matching this file's WIP state.
  val := ⟨(((1) / (4)) * K_gen_4_0_10304_1 ^ 3 - ((1) / (4)) * K_gen_4_0_10304_1 ^ 2
            + ((1) / (2)) * K_gen_4_0_10304_1 + ((3) / (2)) : K_4_0_10304_1), by sorry⟩
  inv := ⟨(((1) / (4)) * K_gen_4_0_10304_1 ^ 3 - ((1) / (4)) * K_gen_4_0_10304_1 ^ 2
            + ((1) / (2)) * K_gen_4_0_10304_1 - ((1) / (2)) : K_4_0_10304_1), by sorry⟩
  val_inv := by sorry
  inv_val := by sorry




-- @@ L84-84 verbatim
axiom LMFDB_NF_4_0_10304_1_discr : NumberField.discr K_4_0_10304_1 = 10304


-- @@ L86-86 verbatim
axiom LMFDB_NF_4_0_10304_1_isGalois : ¬ IsGalois ℚ K_4_0_10304_1


-- @@ L88-88 verbatim
axiom LMFDB_NF_4_0_10304_1_classNumber : NumberField.classNumber K_4_0_10304_1 = 4


-- @@ L90-90 verbatim
axiom LMFDB_NF_4_0_10304_1_totallyComplex : IsTotallyComplex K_4_0_10304_1


-- @@ L92-92 verbatim
instance LMFDB_NF_4_0_10304_1_totallyComplexInstance : IsTotallyComplex K_4_0_10304_1 := LMFDB_NF_4_0_10304_1_totallyComplex


-- @@ L94-94 verbatim
axiom LMFDB_NF_4_0_10304_1_isCM : NumberField.IsCMField K_4_0_10304_1


-- @@ L96-96 verbatim
end
