import OAI.NumberTheory.DirichletL.PrimeRows.SelectedAgreement


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical Topology

-- @@ L7-7 verbatim
open Filter

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L9-9 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler

-- @@ L10-10 verbatim
open CanonicalQuadraticSieve CompletedGauss

-- @@ L11-11 verbatim
local notation "O" => HeckeFamily.O


-- @@ L13-18 verbatim
theorem continuedMarkedLocal_eq_quotient (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hV : 1-coordV P.val.absNorm z≠0) :
    continuedMarkedLocal η u P hs x w z=(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z) := by
  rw [ramifiedCorrection_eq_marked]
  field_simp
  ring


-- @@ L20-25 verbatim
theorem selected_V_ne_zero (P : PrimeIdeal) (hQ : (4:ℝ)≤P.val.absNorm) (z : ℂ)
    (hz : (4/25:ℝ)≤z.re) : 1-coordV P.val.absNorm z≠0 := by
  apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
  rw [coordV_norm _ (by linarith : (0:ℝ)<P.val.absNorm)]
  apply rpow_le_half _ _ hQ
  linarith


-- @@ L27-35 verbatim
theorem continuedMarkedLocal_analyticAt_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)<x.re) (hz : (4/25:ℝ)≤z.re) :
    AnalyticAt ℂ (fun x=>continuedMarkedLocal η u P hs x w z) x := by
  have he : (fun x=>continuedMarkedLocal η u P hs x w z)=
      (fun x=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun x=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact (((ramifiedCorrection_analytic_x η u P hs hQ w z hz) x hx).sub analyticAt_const).div_const


-- @@ L37-45 verbatim
theorem continuedMarkedLocal_differentiable_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedMarkedLocal η u P hs x w z) := by
  have he : (fun w=>continuedMarkedLocal η u P hs x w z)=
      (fun w=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun w=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact ((ramifiedCorrection_analytic_w η u P hs hQ x z hx hz).sub_const 1).div_const _


-- @@ L47-57 verbatim
theorem continuedMarkedLocal_analyticAt_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)<z.re) :
    AnalyticAt ℂ (fun z=>continuedMarkedLocal η u P hs x w z) z := by
  have hcv := (coordV_differentiable (P.val.absNorm:ℝ) (by linarith)).analyticAt z
  have ha : AnalyticAt ℂ (fun t=>(ramifiedCorrection η u P hs x w t-1)/(1-coordV P.val.absNorm t)) z :=
    (((ramifiedCorrection_analytic_z η u P hs hQ x w hx) z hz).sub analyticAt_const).div
    (analyticAt_const.sub hcv) (selected_V_ne_zero P hQ z hz.le)
  apply ha.congr
  filter_upwards [(Complex.isOpen_re_gt (4/25)).mem_nhds hz] with t ht
  exact (continuedMarkedLocal_eq_quotient η u P hs x w t (selected_V_ne_zero P hQ t ht.le)).symm


-- @@ L59-59 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
end OAI
