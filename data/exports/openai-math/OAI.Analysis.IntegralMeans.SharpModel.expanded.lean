import OAI.Analysis.IntegralMeans.Model
import OAI.Analysis.IntegralMeans.Koebe


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open Set MeasureTheory

-- @@ L8-8 verbatim
open scoped ENNReal

-- @@ L9-9 verbatim
namespace Brennan.Sharp


-- @@ L11-11 verbatim
def koebeDomain : Set ℂ := koebeMap '' disk


-- @@ L13-13 verbatim
def koebeInverse : ℂ → ℂ := Function.invFunOn koebeMap disk


-- @@ L15-16 verbatim
def areaMoment (f : ℂ → ℂ) (U : Set ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ t) ∂volume


-- @@ L18-23 verbatim
def SharpEndpointStatement : Prop :=
  Schlicht koebeMap ∧
  areaMoment koebeMap disk (-2) = ⊤ ∧
  areaMoment koebeMap disk (2 / 3) = ⊤ ∧
  ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 : ℝ)) koebeDomain volume ∧
  ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 / 3 : ℝ)) koebeDomain volume


-- @@ L25-25 verbatim
end Brennan.Sharp


-- @@ L27-27 verbatim
end


-- @@ L29-29 verbatim
end OAI
