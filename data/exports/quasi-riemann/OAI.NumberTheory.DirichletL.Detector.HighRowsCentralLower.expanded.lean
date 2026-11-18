import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralDefect


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Topology

-- @@ L7-7 verbatim
open Filter

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeEuler

-- @@ L9-9 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-21 verbatim
theorem central_correction_threshold (eps : ℝ) (heps : 0<eps) :
    ∃Q0 : ℝ,480≤Q0 ∧ ∀Q : ℝ,Q0≤Q→198*Q^(-10*eps)≤1/2 := by
  have hh : Tendsto (fun Q : ℝ=>198*Q^(-10*eps)) atTop (nhds 0) := by
    simpa only [mul_zero,neg_mul] using
      (tendsto_rpow_neg_atTop (show 0<10*eps by positivity)).const_mul (198:ℝ)
  have he := hh.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  obtain ⟨Q0,hQ0⟩ := Filter.eventually_atTop.mp he
  refine ⟨max 480 Q0,le_max_left _ _,?_⟩
  intro Q hQ
  exact (hQ0 Q ((le_max_right _ _).trans hQ)).le


-- @@ L23-24 verbatim
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

-- @@ L25-39 verbatim
include hc in
theorem ramifiedClosed_central_lower (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    1/2≤‖ramifiedClosed p hp hg eta a rho x w z j‖ := by
  have hd := ramifiedClosed_central_defect p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hh := norm_add_le (1-ramifiedClosed p hp hg eta a rho x w z j)
    (ramifiedClosed p hp hg eta a rho x w z j)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at hh
  linarith

-- @@ L40-40 verbatim
end SevenEighths.ProbeEuler

-- @@ L41-41 verbatim
end


-- @@ L43-43 verbatim
end OAI
