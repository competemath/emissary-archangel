import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralStrict


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


-- @@ L12-23 verbatim
include hc in
lemma sourceRowTerm_central_strict_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j<6) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (3/2) (1-x.re-w.re)
  · have hb := squarefree_base_strict_norm p hp hg hc j hj
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) by linarith)
  · norm_num ; linarith


-- @@ L25-37 verbatim
include hc in
lemma sourceRowTerm_central_boundary_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j≤1) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (1/2) (-x.re-w.re)
  · have hb := squarefree_base_boundary_norm p hp hg hc j hj
    rw [Real.sqrt_eq_rpow] at hb
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) by linarith)
  · norm_num

-- @@ L38-38 verbatim
end SevenEighths.ProbeEuler

-- @@ L39-39 verbatim
end


-- @@ L41-41 verbatim
end OAI
