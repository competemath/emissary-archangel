import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowCanonical
import OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff

-- @@ L8-8 verbatim
open MeasureTheory


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalSource

-- @@ L11-11 verbatim
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve

-- @@ L12-12 verbatim
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors

-- @@ L13-13 verbatim
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow

-- @@ L14-14 verbatim
open CenteredMomentHeckeWindowEnergy CenteredMomentSmoothedWindowEnergy

-- @@ L15-15 verbatim
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow IdealMobiusDivisorSum

-- @@ L16-16 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L17-17 verbatim
variable {ι:Type*}[Fintype ι]

-- @@ L18-18 verbatim
local instance firstWindowEnergyDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L20-25 verbatim
def commonEnergy (s:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)
    (t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):ℂ:=
  let Q:=residualPool C hC.1 s.columns
  gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then s.beta (C*I) else 0)*heightCoeff τ t I) U K


-- @@ L27-38 verbatim
lemma column_unwindowed_common (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I) z=
      commonGauss s C hC τ t L z:=by
  rw [columns_gauss_polynomial_filter Q C hC s.columns
    (fun I=>(if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I) z]
  unfold commonGauss
  congr 1
  funext I
  rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]


-- @@ L40-49 verbatim
theorem column_unwindowed_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I) U K=
      commonEnergy s C hC τ t L U K:=by
  unfold gaussEnergy commonEnergy
  apply tsum_congr
  intro z
  rw [column_unwindowed_common s Q C hQ hC hQC τ t L z]
  rfl


-- @@ L51-71 verbatim
theorem column_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2:=by
  have hh:=smoothed_window_energy_from_height V hVc hVs J Finset.univ
    (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
    (fun I:columns Q C hC.1 s.columns=>if L∣(I:Ideal O) then s.beta (C*I) else 0)
    τ t θ X hX U K hK hU E hE (fun v=>by
      simp only [element_span]
      rw [column_unwindowed_energy s Q C hQ hC hQC]
      exact henergy v)
  simpa only [ha,element_span,element_norm] using hh


-- @@ L73-90 verbatim
theorem column_star_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) U K).re≤
      (E*heightCost t (-θ)^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity (fun x=>star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) w‖)^2:=by
  simp only [star_columnPhase]
  exact column_window_energy s Q C hQ hC hQC τ t (-θ) X hX
    (fun x=>star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs)
    L a ha U K hK hU J E hE henergy


-- @@ L92-92 verbatim
end SevenEighths.CenteredMomentFirstPhysicalSource


-- @@ L94-94 verbatim
end


-- @@ L96-96 verbatim
end OAI
