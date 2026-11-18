import OAI.NumberTheory.DirichletL.Detector.HighRowsClosed


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower ProbeEuler

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeRow CubicEisenstein

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-19 verbatim
theorem actualSextic_unit_six (p b : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hb : IsCoprime b p) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^6=1 := by
  have h := congrArg (fun χ : MulChar (O ⧸ Ideal.span {p}) ℂ =>
    χ (Ideal.Quotient.mk _ b)) (actualSextic_six _ hg hc)
  simpa only [MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),
    MulChar.one_apply ((isUnit_quotient_span_iff p b).mpr hb.symm)] using h


-- @@ L21-44 verbatim
theorem idealRowHighLocalFactor_eq_closed (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (j : ℕ) (hj : j<6) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) j := by
  rw [idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb j x w z]
  exact sourceRowSeries_eq_closed p hp hg hc _ _ _ x w z
    (actualSextic_unit_six p b hg hc hb) hV hR hW j hj


-- @@ L46-46 verbatim
end SevenEighths.ProbePhysical

-- @@ L47-47 verbatim
end


-- @@ L49-49 verbatim
end OAI
