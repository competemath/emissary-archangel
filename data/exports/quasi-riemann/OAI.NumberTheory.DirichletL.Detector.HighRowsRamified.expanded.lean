import OAI.NumberTheory.DirichletL.Detector.HighRowsFiniteBounds


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
namespace SevenEighths.ProbeEuler

-- @@ L7-7 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower

-- @@ L8-8 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L9-10 verbatim
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)


-- @@ L12-15 verbatim
def ramifiedClosed (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  1+(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j


-- @@ L17-32 verbatim
include hc in
theorem ramifiedClosed_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (19/20:ℝ)≤w.re) (hz : (33/200:ℝ)≤z.re) (j : ℕ) :
    ‖ramifiedClosed p hp hg eta a rho x w z j‖≤193 := by
  have hb := rowClosedMarked_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j
  have hv := second_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  simp only [norm_one] at hs
  unfold ramifiedClosed
  apply (norm_add_le _ _).trans
  rw [norm_one,norm_mul]
  have hm := mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
  linarith


-- @@ L34-47 verbatim
include hc in

theorem sourceRowSeries_ramified (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1)
    (j : ℕ) (hj0 : j≠0) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)=
      ramifiedClosed p hp hg eta a rho x w z j := by
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hR hW j hj,ite_eq_right hj0,add_zero]
  unfold ramifiedClosed
  have hn := one_sub_ne_zero_of_norm_lt_one _ hV
  field_simp


-- @@ L49-49 verbatim
end SevenEighths.ProbeEuler

-- @@ L50-50 verbatim
end


-- @@ L52-52 verbatim
end OAI
