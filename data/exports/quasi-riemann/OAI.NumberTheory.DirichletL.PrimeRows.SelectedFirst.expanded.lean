import OAI.NumberTheory.DirichletL.PrimeRows.SelectedHolomorphic
import OAI.NumberTheory.DirichletL.PrimeRows.FirstContinuation


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical Topology

-- @@ L8-8 verbatim
open Filter

-- @@ L9-9 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L10-10 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler

-- @@ L11-11 verbatim
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L12-12 verbatim
local notation "O" => HeckeFamily.O


-- @@ L14-22 verbatim
theorem continuedMarkedLocal_first_analyticAt_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)<x.re) (hz : (1/3:ℝ)≤z.re) :
    AnalyticAt ℂ (fun x=>continuedMarkedLocal η u P hs x w z) x := by
  have he : (fun x=>continuedMarkedLocal η u P hs x w z)=
      (fun x=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun x=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z (by linarith)))
  rw [he]
  exact (((ramifiedCorrection_first_analytic_x η u P hs hQ w z hz) x hx).sub analyticAt_const).div_const


-- @@ L24-32 verbatim
theorem continuedMarkedLocal_first_differentiable_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedMarkedLocal η u P hs x w z) := by
  have he : (fun w=>continuedMarkedLocal η u P hs x w z)=
      (fun w=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun w=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z (by linarith)))
  rw [he]
  exact ((ramifiedCorrection_first_analytic_w η u P hs hQ x z hx hz).sub_const 1).div_const _


-- @@ L34-44 verbatim
theorem continuedMarkedLocal_first_analyticAt_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)<z.re) :
    AnalyticAt ℂ (fun z=>continuedMarkedLocal η u P hs x w z) z := by
  have hcv := (coordV_differentiable (P.val.absNorm:ℝ) (by linarith)).analyticAt z
  have ha : AnalyticAt ℂ (fun t=>(ramifiedCorrection η u P hs x w t-1)/(1-coordV P.val.absNorm t)) z :=
    (((ramifiedCorrection_first_analytic_z η u P hs hQ x w hx) z hz).sub analyticAt_const).div
    (analyticAt_const.sub hcv) (selected_V_ne_zero P hQ z (by linarith))
  apply ha.congr
  filter_upwards [(Complex.isOpen_re_gt (1/3)).mem_nhds hz] with t ht
  exact (continuedMarkedLocal_eq_quotient η u P hs x w t (selected_V_ne_zero P hQ t (by linarith))).symm


-- @@ L46-61 verbatim
theorem continuedCompensatedLocal_first_differentiableAt_x (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)<x.re) (hz : (1/3:ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) x := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := (continuedMarkedLocal_first_analyticAt_x η u P hs hQ x w z hx hz).differentiableAt
  have hD := coordD_differentiable (P.val.absNorm:ℝ) hQ0 (idealCoeff η P.val) (idealRowHom u.val P.val)
  have hB : Differentiable ℂ (fun x:ℂ=>star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) :=
    (differentiable_id.const_cpow (Or.inl hQc)).const_mul _
  have hd := (first_open_region_denominators (P.val.absNorm:ℝ) 0 (idealCoeff η P.val)
    (idealRowHom u.val P.val) x z hQ (by simp) (idealCoeff_norm_le_one η _)
    (idealRowHom_norm u.val _) hx.le hz).2.2
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop (disch := first | assumption | exact Or.inl hQc)


-- @@ L63-75 verbatim
theorem continuedCompensatedLocal_first_differentiable_w (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := continuedMarkedLocal_first_differentiable_w η u P hs hQ x z hx hz
  have hW := coordW_differentiable (P.val.absNorm:ℝ) hQ0 (idealRowHom u.val P.val)
  have hq : Differentiable ℂ (fun w:ℂ=>(P.val.absNorm:ℂ)^(-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hQc)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop


-- @@ L77-86 verbatim
theorem continuedCompensatedLocal_first_differentiableAt_z (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)<z.re) :
    DifferentiableAt ℂ (fun z=>continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) z := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hM := (continuedMarkedLocal_first_analyticAt_z η u P hs hQ x w z hx hz).differentiableAt
  have hV := coordV_differentiable (P.val.absNorm:ℝ) hQ0
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop


-- @@ L88-88 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L90-90 verbatim
end


-- @@ L92-92 verbatim
end OAI
