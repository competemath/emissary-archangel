import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowEnergy
import OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalSource

-- @@ L10-10 verbatim
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve

-- @@ L11-11 verbatim
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice

-- @@ L12-12 verbatim
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow

-- @@ L13-13 verbatim
open CenteredMomentLogDyadic CenteredMomentSecondWindowSource CenteredMomentSecondWindowBudget

-- @@ L14-14 verbatim
open IdealMobiusDivisorSum

-- @@ L15-15 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L16-16 verbatim
variable {ι:Type*}[Fintype ι]


-- @@ L18-32 verbatim
theorem column_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  exact (column_window_energy s Q C hQ hC hQC τ t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth L a ha U K hK hU J E hE henergy).trans
      (shifted_window_budget J t θ E hE)


-- @@ L34-47 verbatim
theorem column_star_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  simpa only [star_logAnnulus_column,norm_neg] using
    column_dyadic_window_energy s Q C hQ hC hQC τ t (-θ) X hX L a ha U K hK hU J E hE henergy


-- @@ L49-49 verbatim
end SevenEighths.CenteredMomentFirstPhysicalSource


-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
end OAI
