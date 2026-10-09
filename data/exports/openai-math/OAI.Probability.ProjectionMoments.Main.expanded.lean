import OAI.Probability.ProjectionMoments.SphereWeights


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section


-- @@ L7-7 verbatim
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace

-- @@ L8-8 verbatim
open NoiselessRegression NoiselessRegression.FiniteKernelLearner

-- @@ L9-9 verbatim
open scoped ENNReal NNReal RealInnerProductSpace Topology

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
universe u

-- @@ L12-12 verbatim
namespace ProjectionMoments


-- @@ L14-26 verbatim
theorem main : MainStatement.{u} := by
  refine ⟨integrated_frame_moment, normalized_unitBall_moment, all_radii_sphere_moment,
    positive_family_cap_domination, riesz_deterministic_offsets, one_block_all_radii,
    NoiselessRegression.FiniteKernelLearner.haar_success,
    NoiselessRegression.FiniteKernelLearner.riesz_success,
    NoiselessRegression.FiniteKernelLearner.cap_fixed_stop,
    NoiselessRegression.FiniteKernelLearner.cap_total_success,
    NoiselessRegression.FiniteKernelLearner.cap_fixed_stop_asymptotic,
    NoiselessRegression.FiniteKernelLearner.cap_total_success_asymptotic, ?_,
    NoiselessRegression.FiniteKernelLearner.subquadratic_memory_with_pointwise,
    NoiselessRegression.FiniteKernelLearner.fixed_quadratic_memory⟩
  intro d M T hd K hK
  exact K.exists_equivalent_tape hK hd


-- @@ L28-28 verbatim
end ProjectionMoments


-- @@ L30-30 verbatim
end


-- @@ L32-32 verbatim
end


-- @@ L34-34 verbatim
end OAI
