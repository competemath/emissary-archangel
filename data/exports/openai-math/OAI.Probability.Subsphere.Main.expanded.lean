import Mathlib
import OAI.Probability.Subsphere.Estimates.Weighted
import OAI.Probability.Subsphere.Estimates.HalfPrecision
import OAI.Probability.Subsphere.Estimates.AffinePrecision
import OAI.Probability.Subsphere.Estimates.FixedPrecision
import OAI.Probability.Subsphere.Mixture.Domination


-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-10 verbatim
section

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
universe u v w

-- @@ L13-13 verbatim
namespace SubsphereCurrent


-- @@ L15-18 verbatim
theorem full_current_main_scope : CurrentMainScope.{u,v,w} := by
  exact ⟨explicit_precision, Weighted.radius_weighted_full_estimate,
    half_precision, Affine.all_affine_full_estimate, Fixed.dimension_estimate,
    Mixture.mixture_estimate⟩


-- @@ L20-20 verbatim
end SubsphereCurrent

-- @@ L21-21 verbatim
end

-- @@ L22-22 verbatim
end


-- @@ L24-24 verbatim
end OAI
