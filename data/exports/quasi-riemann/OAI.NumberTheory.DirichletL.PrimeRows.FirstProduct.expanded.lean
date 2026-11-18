import OAI.NumberTheory.DirichletL.PrimeRows.FirstTail


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L8-8 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler

-- @@ L9-9 verbatim
open CanonicalRowCompletion CompletedGauss

-- @@ L10-10 verbatim
local notation "O" => HeckeFamily.O


-- @@ L12-29 verbatim
theorem unramifiedFactor_first_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0<eps)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤firstPrimeDefectBound eps P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using firstPrimeDefectBound_nonneg eps P
  · apply unramifiedClosed_first_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact heps
    · exact hx
    · exact hz
    · exact hw
    · exact hxw


-- @@ L31-38 verbatim
theorem unramifiedProduct_first_defect (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw) hS.half hS.small


-- @@ L40-55 verbatim
theorem unramifiedProduct_first_multipliable (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))


-- @@ L57-57 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
end OAI
