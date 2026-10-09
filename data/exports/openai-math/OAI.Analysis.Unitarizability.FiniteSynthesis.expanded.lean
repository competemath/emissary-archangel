import OAI.Analysis.Unitarizability.KernelEnergy
import Mathlib.Analysis.InnerProductSpace.Adjoint


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
/-! Finite synthesis maps and their adjoints, with bounds for all small subfamilies. -/

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace Dixmier

-- @@ L9-9 verbatim
namespace FiniteSynthesis

-- @@ L10-10 verbatim
open scoped ComplexConjugate

-- @@ L11-11 verbatim
variable {I K : Type*} [Fintype K]

-- @@ L12-12 verbatim
local instance : DecidableEq I := Classical.decEq I


-- @@ L14-16 verbatim
def synthesis (v : I → EuclideanSpace ℂ K) (J : Finset I) :
    EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ K :=
  ∑ i : J, InnerProductSpace.rankOne ℂ (v i) (EuclideanSpace.basisFun J ℂ i)


-- @@ L18-20 verbatim
@[simp] theorem synthesis_apply (v : I → EuclideanSpace ℂ K) (J : Finset I)
    (z : EuclideanSpace ℂ J) : synthesis v J z = ∑ i : J, z i • v i := by
  simp only [synthesis, _root_.sum_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.basisFun_inner]


-- @@ L22-27 verbatim
@[simp] theorem synthesis_adjoint_apply (v : I → EuclideanSpace ℂ K) (J : Finset I)
    (x : EuclideanSpace ℂ K) (i : J) : (synthesis v J).adjoint x i = inner ℂ (v i) x := by
  rw [← EuclideanSpace.basisFun_inner, ContinuousLinearMap.adjoint_inner_right]
  have h : synthesis v J (EuclideanSpace.basisFun J ℂ i) = v i := by
    simp [synthesis_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  rw [h]


-- @@ L29-32 verbatim
/-- The synthesis operator bound on subfamily coordinate spaces,
including the empty subfamily. -/
def FrameBound (v : I → EuclideanSpace ℂ K) (p : ℕ) (b : ℝ) : Prop :=
  ∀ J : Finset I, J.card ≤ p → ‖synthesis v J‖ ≤ b


-- @@ L34-40 verbatim
theorem synthesis_sq_le (v : I → EuclideanSpace ℂ K) (J : Finset I) {b : ℝ}
    (_hb : 0 ≤ b) (hJ : ‖synthesis v J‖ ≤ b) (z : J → ℂ) :
    ‖∑ i : J, z i • v i‖^2 ≤ b^2 * ∑ i : J, ‖z i‖^2 := by
  let z' : EuclideanSpace ℂ J := WithLp.toLp 2 z
  have h := (synthesis v J).le_of_opNorm_le hJ z'
  have hpow := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [synthesis_apply, mul_pow, EuclideanSpace.norm_sq_eq] using hpow


-- @@ L42-48 verbatim
theorem analysis_sq_le (v : I → EuclideanSpace ℂ K) (J : Finset I) {b : ℝ}
    (_hb : 0 ≤ b) (hJ : ‖synthesis v J‖ ≤ b) (x : EuclideanSpace ℂ K) :
    ∑ i : J, ‖inner ℂ (v i) x‖^2 ≤ b^2 * ‖x‖^2 := by
  have hj : ‖(synthesis v J).adjoint‖ ≤ b := by simpa using hJ
  have h := (synthesis v J).adjoint.le_of_opNorm_le hj x
  have hpow := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [EuclideanSpace.norm_sq_eq, synthesis_adjoint_apply, mul_pow] using hpow


-- @@ L50-50 verbatim
end FiniteSynthesis

-- @@ L51-51 verbatim
end Dixmier


-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
end OAI
