import OAI.NumberTheory.DirichletL.Detector.HighRowsUnramified
import OAI.NumberTheory.DirichletL.Detector.HighEulerRational


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L9-9 verbatim
open ProbeEuler ProbeRow ConcretePrimeRowBridge ProbePrimePower

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-37 verbatim
lemma row_initial_geometric (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    ‖coordV Q z‖<1 ∧ ‖coordR Q ((actualACube η p)^2) x z‖<1 ∧
      ‖coordW Q rho w‖<1 ∧ ‖coordD Q (targetMonoid η p) rho x‖<1 := by
  dsimp only
  have hP : Prime (Ideal.span {p}:Ideal O) := (Ideal.prime_span_singleton_iff).mpr hp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hn : ‖actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)‖≤1 :=
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p b hg hc hb) (by decide)).le
  refine ⟨?_,?_,?_,?_⟩
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordW_norm_le _ hQ0 _ w hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordD_norm_le _ hQ0 _ _ x (targetMonoid_norm_le_one η p) hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)


-- @@ L39-57 verbatim
theorem idealRowHighLocalFactor_unramified (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    idealRowHighLocalFactor η b (Ideal.span {p}) x w z=
      (1-coordD Q (targetMonoid η p) rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (actualAPhase η p) (targetMonoid η p) rho x w z := by
  have hd := row_initial_geometric η p hp hg hc b hb x w z hx hw hz
  dsimp only at hd ⊢
  have he := idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb 0 x w z
  simp only [pow_zero,mul_one] at he
  rw [he]
  simpa only [actualACube_sq,sourceRowSeries] using
    sourceRowSeries_unramified_euler p hp hg hc (targetMonoid η p) (actualACube η p)
      _ x w z (actualSextic_unit_six p b hg hc hb) hd.1 hd.2.1 hd.2.2.1
      (one_sub_ne_zero_of_norm_lt_one _ hd.2.2.2)


-- @@ L59-59 verbatim
end SevenEighths.ProbePhysical

-- @@ L60-60 verbatim
end


-- @@ L62-62 verbatim
end OAI
