import OAI.NumberTheory.DirichletL.PrimeRows.Ramified


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


-- @@ L12-13 verbatim
def unramifiedFactor (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∣Ideal.span {u.val} then 1 else idealUnramifiedCorrection η u P x w z


-- @@ L15-16 verbatim
def unramifiedProduct (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},unramifiedFactor η u P.val x w z


-- @@ L18-32 verbatim
theorem unramifiedFactor_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedFactor η u P x w z-1‖≤globalPrimeDefectBound P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using globalPrimeDefectBound_nonneg P
  · apply unramifiedClosed_open_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact hx
    · exact hw
    · exact hz


-- @@ L34-40 verbatim
theorem unramifiedProduct_defect (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small


-- @@ L42-55 verbatim
theorem unramifiedProduct_multipliable (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S} =>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S} => unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S} => globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))


-- @@ L57-74 verbatim
theorem unramifiedProduct_analytic_x (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>unramifiedProduct S η u x w z) {x : ℂ | 7/8<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply unramifiedClosed_analytic_x
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hz
  · intro P x hx
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half


-- @@ L76-94 verbatim
theorem unramifiedProduct_analytic_w (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x z : ℂ) (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w =>unramifiedProduct S η u x w z) {w : ℂ | 9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply unramifiedClosed_analytic_w
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
      · exact hz
  · intro P w hw
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half


-- @@ L96-115 verbatim
theorem unramifiedProduct_analytic_z (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) :
    AnalyticOnNhd ℂ (fun z =>unramifiedProduct S η u x w z) {z : ℂ | 4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ => if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [ite_eq_right h]
      apply unramifiedClosed_analytic_z
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
  · intro P z hz
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


-- @@ L117-117 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L119-119 verbatim
end


-- @@ L121-121 verbatim
end OAI
