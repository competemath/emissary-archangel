import OAI.Analysis.IntegralMeans.Main
import OAI.Analysis.IntegralMeans.InverseMoment
import OAI.Analysis.IntegralMeans.KoebeDivergence


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open Set MeasureTheory

-- @@ L9-9 verbatim
open scoped ENNReal

-- @@ L10-10 verbatim
namespace Brennan.Sharp


-- @@ L12-15 verbatim
lemma koebe_inverse_four_area : areaMoment koebeInverse koebeDomain 4 = ⊤ := by
  rw [koebe_inverse_areaMoment]
  norm_num
  exact koebe_negative_endpoint_area


-- @@ L17-21 verbatim
lemma koebe_inverse_four_thirds_area :
    areaMoment koebeInverse koebeDomain (4 / 3) = ⊤ := by
  rw [koebe_inverse_areaMoment]
  norm_num
  exact koebe_positive_endpoint_area


-- @@ L23-27 verbatim
theorem sharp_endpoints : SharpEndpointStatement := by
  refine ⟨koebeMap_schlicht, koebe_negative_endpoint_area,
    koebe_positive_endpoint_area, ?_, ?_⟩
  · exact not_integrable_of_areaMoment_top koebe_inverse_four_area
  · exact not_integrable_of_areaMoment_top koebe_inverse_four_thirds_area


-- @@ L29-29 verbatim
end Brennan.Sharp


-- @@ L31-31 verbatim
end


-- @@ L33-33 verbatim
end OAI
