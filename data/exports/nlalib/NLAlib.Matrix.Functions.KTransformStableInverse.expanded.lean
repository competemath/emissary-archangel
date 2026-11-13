import NLAlib.Matrix.Functions.KTransformLocalRealBranch
import NLAlib.Matrix.Functions.KTransformGlobalInjectivity
import Mathlib.Data.Set.Function


-- @@ L5-11 verbatim
/-! # The actual inverse on the stable K-transform image

Mathlib's inverse-on-a-set construction is applied to the actual stable
domain. Genuine global uniqueness identifies it with each local analytic
branch, so its restriction to every Hermitian affine target path has the
actual native derivative equation.
-/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
set_option autoImplicit false

-- @@ L15-15 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L16-16 verbatim
open Matrix MeasureTheory Set Filter

-- @@ L17-17 verbatim
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology

-- @@ L18-18 verbatim
namespace NLAlib

-- @@ L19-19 verbatim
variable {n : Type*} [Fintype n] [DecidableEq n]

-- @@ L20-20 verbatim
local notation "M" => Matrix n n ℂ


-- @@ L22-25 verbatim
/-- The inverse-on-a-set of the actual K transform on its original stable
domain. Its meaningful values are on that map's actual image. -/
def matrixKStableInverse (ν : Measure (selfAdjoint M)) (α : ℝ) : M → M :=
  Function.invFunOn (matrixKTransform ν α) (matrixKStableDomain ν α)


-- @@ L27-34 verbatim
/-- The actual stable inverse lies in the original domain and solves the
native K equation at every target in the actual stable image. -/
theorem matrixKStableInverse_mem_and_transform_eq
    (ν : Measure (selfAdjoint M)) (α : ℝ) {U : M}
    (hU : U ∈ (matrixKTransform ν α) '' matrixKStableDomain ν α) :
    matrixKStableInverse ν α U ∈ matrixKStableDomain ν α ∧
      matrixKTransform ν α (matrixKStableInverse ν α U) = U :=
  Function.invFunOn_pos hU


-- @@ L36-36 verbatim
variable [Nonempty n]


-- @@ L38-45 verbatim
/-- Global native derivative stability proves injectivity of the actual
K map on its original stable domain. -/
theorem injOn_matrixKTransform_stableDomain
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) : InjOn (matrixKTransform ν α) (matrixKStableDomain ν α) := by
  intro S hS Q hQ hK
  exact (matrixKTransform_eq_iff_eq_of_quadratic_pos ν hν α hα S Q
    hS.1 hQ.1 hS.2.1 hQ.2.1 hS.2.2 hQ.2.2).mp hK


-- @@ L47-53 verbatim
/-- The constructed inverse recovers every original stable matrix, using
the genuine global uniqueness theorem. -/
theorem matrixKStableInverse_matrixKTransform
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (S : M) (hS : S ∈ matrixKStableDomain ν α) :
    matrixKStableInverse ν α (matrixKTransform ν α S) = S :=
  (injOn_matrixKTransform_stableDomain ν hν α hα).leftInvOn_invFunOn hS


-- @@ L55-96 verbatim
/-- The actual stable inverse has a Hermitian derivative along every
Hermitian affine target path through its actual image. The derivative
solves the genuine native K derivative equation. No inverse-path
regularity or derivative identity is assumed.
Source: Montanari--Saeed (2026), stable inverse branch.
atlas: block-wishart-log-potential (partial) -/
theorem exists_hasDerivAt_matrixKStableInverse_affine
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (U H : M) (hH : H.IsHermitian) (t : ℝ)
    (hU : U + t • H ∈ (matrixKTransform ν α) '' matrixKStableDomain ν α) :
    ∃ B : M, B.IsHermitian ∧
      HasDerivAt (fun r : ℝ => matrixKStableInverse ν α (U + r • H)) B t ∧
      matrixKTransformDeriv ν α (matrixKStableInverse ν α (U + t • H)) B = H := by
  let S := matrixKStableInverse ν α (U + t • H)
  obtain ⟨hS, hKS⟩ := matrixKStableInverse_mem_and_transform_eq ν α hU
  obtain ⟨G, B, _hGa, _hG0, _hGd, hGR, hBH, hDB, hGeq, hstable⟩ :=
    exists_analytic_real_matrixKTransform_affine_branch ν hν α hα S hS H hH
  have hshift : Tendsto (fun r : ℝ => r - t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => r - t) := by fun_prop
    simpa only [sub_self] using hc.tendsto t
  have hshiftC : Tendsto (fun r : ℝ => ((r - t : ℝ) : ℂ)) (𝓝 t) (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hshift
  have hevent : (fun r : ℝ => matrixKStableInverse ν α (U + r • H)) =ᶠ[𝓝 t]
      (fun r : ℝ => G ((r - t : ℝ) : ℂ)) := by
    filter_upwards [hshift.eventually hstable, hshiftC.eventually hGeq] with r hr hsolve
    have hsm : ((r - t : ℝ) : ℂ) • H = (r - t) • H :=
      IsScalarTower.algebraMap_smul ℂ (r - t) H
    have hK : matrixKTransform ν α (G ((r - t : ℝ) : ℂ)) = U + r • H := by
      calc
        _ = matrixKTransform ν α S + ((r - t : ℝ) : ℂ) • H := hsolve.2
        _ = U + t • H + (r - t) • H := by rw [hKS, hsm]
        _ = U + r • H := by module
    rw [← hK]
    exact matrixKStableInverse_matrixKTransform ν hν α hα _ hr
  have hGR0 : HasDerivAt (fun v : ℝ => G v) B (t - t) := by
    simpa only [sub_self] using hGR
  have hGshift : HasDerivAt (fun r : ℝ => G ((r - t : ℝ) : ℂ)) B t := by
    have hd : HasDerivAt (fun r : ℝ => r - t) 1 t := by
      simpa only [id_eq] using (hasDerivAt_id t).sub_const t
    convert! hGR0.hasFDerivAt.comp_hasDerivAt t (f := fun r : ℝ => r - t) hd using 1; simp
  exact ⟨B, hBH, hGshift.congr_of_eventuallyEq hevent, hDB⟩


-- @@ L98-98 verbatim
end NLAlib
