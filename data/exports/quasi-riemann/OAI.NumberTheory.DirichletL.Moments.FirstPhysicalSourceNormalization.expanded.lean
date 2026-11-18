import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePool


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalSource

-- @@ L9-9 verbatim
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge

-- @@ L10-10 verbatim
open CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily

-- @@ L11-11 verbatim
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive

-- @@ L12-12 verbatim
open CenteredMomentFirstReduced

-- @@ L13-13 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L15-33 verbatim
theorem scalar_norm (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀:ℝ)(hK:0<K)(_hA₀:0<A₀)(_hB₀:0<B₀):
    ‖scalar C D hC E K A₀ B₀‖=
      ‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖*Real.sqrt A₀*Real.sqrt B₀):=by
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero
      (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hk:0<K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos he)
  unfold scalar
  rw [norm_mul,norm_div,norm_mul,
    norm_canonicalNormalizedGauss (activePrime C D) (activeCoprime C D) (activeGood C D hC)
      (fun P=>common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=>netExponent_lt_six _ _)]
  simp only [mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hk,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _)]
  ring


-- @@ L35-35 verbatim
end SevenEighths.CenteredMomentFirstPhysicalSource


-- @@ L37-37 verbatim
end


-- @@ L39-39 verbatim
end OAI
