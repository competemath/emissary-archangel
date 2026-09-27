/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPathMap
public import LeanPool.NavierStokesAndEuler.Euler.TransverseSourceCoefficientPath


-- @@ L11-17 verbatim
/-!
# Source deformation data for the concrete transverse packet provider

Only the prescribed deformation, its inverse, and their actual time identity
are inputs. The transverse frame, normal, both coercivity constants, and all
geometry needed by the forward solve are derived below.
-/


-- @@ L19-19 verbatim
section


-- @@ L21-27 verbatim
/-!
# Source geometry for the bounded frame and normal

The literal fields Q=F R⊥ and m=F⁻ᵀm₀ satisfy the tangency, range, strain,
and quantitative normal lower bounds used by the actual transverse solver.
Only the original deformation and its genuine pointwise inverse are inputs.
-/


-- @@ L29-29 verbatim
section


-- @@ L31-38 verbatim
/-!
# The literal source frame as a uniformly smooth bounded coefficient path

The reference-plane restriction is a fixed linear contraction. The actual
source fields F and F_t therefore construct the full bounded frame fields,
with their genuine jets and time derivative. A pointwise bound on F⁻¹ proves
the uniform frame coercivity used by the constructed Gram inverse.
-/


-- @@ L40-40 verbatim
@[expose] public section


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
namespace EulerTransverseBoundedFrame


-- @@ L46-48 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseFrameCoordinates EulerTransverseSourceFrame EulerTransverseSourceCoefficientPath
  EulerVolterraConvolution

-- @@ L49-49 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L51-52 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m₀ : Space) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)


-- @@ L54-61 verbatim
/-- Restricting a matrix to the orthonormal reference plane is a contraction. -/
theorem restriction_norm : ‖referenceRestriction m₀ R‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  change ‖A.comp (referenceEmbedding m₀ R)‖ ≤ 1*‖A‖
  exact (opNorm_comp_le A (referenceEmbedding m₀ R)).trans
    (by simpa only [mul_one,one_mul] using
      mul_le_mul_of_nonneg_left (referenceEmbedding_norm m₀ R) (norm_nonneg A))


-- @@ L63-63 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L65-68 verbatim
/-- The actual source F R⊥, including all its uniformly continuous spatial jets. -/
def coefficient (F : SmoothCoefficientPath K (Space →L[ℝ] Space)) :
    SmoothCoefficientPath K (U →L[ℝ] Space) :=
  SmoothCoefficientPath.map (referenceRestriction m₀ R) F


-- @@ L70-72 verbatim
@[simp] theorem coefficient_apply (F : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (t : K) (x : Space) (v : U) : (coefficient m₀ R F).field t x v = F.field t x (R v : Space) :=
        rfl


-- @@ L74-81 verbatim
/-- The original pointwise source coefficient derivative bound survives without loss. -/
theorem coefficient_derivative_bound (F : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (n : ℕ) (C : ℝ)
    (hF : ∀ t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n ((coefficient m₀ R F).field t : Space → U →L[ℝ] Space) x‖ ≤ C :=
  SmoothCoefficientPath.map_derivative_bound (referenceRestriction m₀ R) (restriction_norm m₀ R) F
      n C hF t x


-- @@ L83-99 verbatim
/-- The uniform inverse-frame bound gives the precise squared lower frame bound. -/
theorem coefficient_lower (F : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (FInv : K → Space → Space →L[ℝ] Space) (B : ℝ) (hB : 0 < B)
    (hInv : ∀ t x v, FInv t x (F.field t x v) = v)
    (hNorm : ∀ t x, ‖FInv t x‖ ≤ B) (t : K) (x : Space) (v : U) :
    (B⁻¹)^2*‖v‖^2 ≤ ‖(coefficient m₀ R F).field t x v‖^2 := by
  have hn : ‖v‖ ≤ B*‖(coefficient m₀ R F).field t x v‖ := by
    calc
      ‖v‖ = ‖(R v : Space)‖ := (R.norm_map v).symm
      _ = ‖FInv t x (F.field t x (R v : Space))‖ := congrArg norm (hInv t x (R v : Space)).symm
      _ ≤ ‖FInv t x‖*‖F.field t x (R v : Space)‖ := (FInv t x).le_opNorm _
      _ ≤ B*‖(coefficient m₀ R F).field t x v‖ :=
        mul_le_mul_of_nonneg_right (hNorm t x) (norm_nonneg _)
  have hdiv : ‖v‖/B ≤ ‖(coefficient m₀ R F).field t x v‖ :=
    (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hn)
  have hs := (sq_le_sq₀ (div_nonneg (norm_nonneg v) hB.le) (norm_nonneg _)).2 hdiv
  simpa only [div_eq_mul_inv,mul_pow,mul_comm] using hs


-- @@ L101-101 verbatim
section Time


-- @@ L103-104 verbatim
variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))


-- @@ L106-115 verbatim
/-- The actual source time derivative also commutes with the reference restriction. -/
theorem coefficient_hasDerivWithinAt
    (hF : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath T hT F.field s x)
        (extendPath T hT F₁.field t x) (Icc (0 : ℝ) T) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun s => extendPath T hT (coefficient m₀ R F).field s x)
      (extendPath T hT (coefficient m₀ R F₁).field t x) (Icc (0 : ℝ) T) t := by
  have hd := (referenceRestriction m₀ R).hasFDerivAt.comp_hasDerivWithinAt t (hF t ht x)
  exact hd


-- @@ L117-117 verbatim
end Time


-- @@ L119-119 verbatim
end EulerTransverseBoundedFrame


-- @@ L121-121 verbatim
end

-- @@ L122-122 verbatim
end


-- @@ L124-124 verbatim
end


-- @@ L126-126 verbatim
@[expose] public section


-- @@ L128-128 verbatim
noncomputable section


-- @@ L130-130 verbatim
namespace EulerTransverseBoundedFrame


-- @@ L132-133 verbatim
open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseFrameCoordinates

-- @@ L134-134 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L136-136 verbatim
variable (m₀ : Space)


-- @@ L138-142 verbatim
/-- The fixed linear operation sending F⁻¹ to F⁻ᵀm₀. -/
def normalMap : (Space →L[ℝ] Space) →L[ℝ] Space :=
  (ContinuousLinearMap.apply ℝ Space m₀).comp
    (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap :
      (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space))


-- @@ L144-144 verbatim
@[simp] theorem normalMap_apply (A : Space →L[ℝ] Space) : normalMap m₀ A = A.adjoint m₀ := rfl


-- @@ L146-152 verbatim
theorem normalMap_norm (hm₀ : ‖m₀‖ = 1) : ‖normalMap m₀‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  change ‖A.adjoint m₀‖ ≤ 1*‖A‖
  have h := A.adjoint.le_opNorm m₀
  simpa only [hm₀,mul_one,one_mul,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.norm_map] using h


-- @@ L154-154 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L156-158 verbatim
/-- The normal has the genuine spatial jets inherited from the inverse deformation. -/
def normalCoefficient (FInv : SmoothCoefficientPath K (Space →L[ℝ] Space)) :
    SmoothCoefficientPath K Space := SmoothCoefficientPath.map (normalMap m₀) FInv


-- @@ L160-161 verbatim
@[simp] theorem normalCoefficient_apply (FInv : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (t : K) (x : Space) : (normalCoefficient m₀ FInv).field t x = (FInv.field t x).adjoint m₀ := rfl


-- @@ L163-168 verbatim
theorem normalCoefficient_derivative_bound (FInv : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (hm₀ : ‖m₀‖ = 1) (n : ℕ) (C : ℝ)
    (hF : ∀ t x, ‖iteratedFDeriv ℝ n (FInv.field t : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n ((normalCoefficient m₀ FInv).field t : Space → Space) x‖ ≤ C :=
  SmoothCoefficientPath.map_derivative_bound (normalMap m₀) (normalMap_norm m₀ hm₀) FInv n C hF t x


-- @@ L170-172 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
  (F FInv : SmoothCoefficientPath K (Space →L[ℝ] Space))


-- @@ L174-179 verbatim
theorem coefficient_tangent
    (hInv : ∀ t x v, FInv.field t x (F.field t x v) = v) (t : K) (x : Space) (v : U) :
    ⟪(normalCoefficient m₀ FInv).field t x,(coefficient m₀ R F).field t x v⟫_ℝ = 0 := by
  rw [normalCoefficient_apply,coefficient_apply,adjoint_inner_left,hInv]
  have h := (R v).property
  rwa [Submodule.mem_orthogonal_singleton_iff_inner_right] at h


-- @@ L181-191 verbatim
theorem coefficient_range
    (hInv : ∀ t x v, F.field t x (FInv.field t x v) = v)
    (t : K) (x η : Space) (hη : ⟪(normalCoefficient m₀ FInv).field t x, η⟫_ℝ = 0) :
    ∃ v, (coefficient m₀ R F).field t x v = η := by
  have hmem : FInv.field t x η ∈ referencePlane m₀ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simpa only [normalCoefficient_apply,adjoint_inner_left] using hη
  let z : referencePlane m₀ := ⟨FInv.field t x η,hmem⟩
  refine ⟨R.symm z,?_⟩
  rw [coefficient_apply,R.apply_symm_apply]
  exact hInv t x η


-- @@ L193-198 verbatim
theorem coefficient_strain (F₁ M : SmoothCoefficientPath K (Space →L[ℝ] Space))
    (hFlow : ∀ t x v, F₁.field t x v = M.field t x (F.field t x v)) (t : K) (x : Space) :
    (coefficient m₀ R F₁).field t x = (M.field t x).comp ((coefficient m₀ R F).field t x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact hFlow t x (R v : Space)


-- @@ L200-222 verbatim
/-- The source inverse identity also prevents degeneration of the normal. -/
theorem normalCoefficient_lower (hm₀ : ‖m₀‖ = 1)
    (hInv : ∀ t x v, FInv.field t x (F.field t x v) = v)
    (B : ℝ) (hB : 0 < B) (hFnorm : ∀ t x, ‖F.field t x‖ ≤ B) (t : K) (x : Space) :
    (B⁻¹)^2 ≤ ‖(normalCoefficient m₀ FInv).field t x‖^2 := by
  have he : (F.field t x).adjoint ((normalCoefficient m₀ FInv).field t x) = m₀ := by
    apply ext_inner_right ℝ
    intro v
    rw [adjoint_inner_left,normalCoefficient_apply,adjoint_inner_left,hInv]
  have hnorm : ‖(F.field t x).adjoint‖ = ‖F.field t x‖ :=
    ContinuousLinearMap.adjoint.norm_map (F.field t x)
  have hn : 1 ≤ B*‖(normalCoefficient m₀ FInv).field t x‖ := by
    calc
      1 = ‖(F.field t x).adjoint ((normalCoefficient m₀ FInv).field t x)‖ := by rw [he,hm₀]
      _ ≤ ‖(F.field t x).adjoint‖*‖(normalCoefficient m₀ FInv).field t x‖ :=
        (F.field t x).adjoint.le_opNorm _
      _ ≤ B*‖(normalCoefficient m₀ FInv).field t x‖ := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_right (hFnorm t x) (norm_nonneg _)
  have hd : B⁻¹ ≤ ‖(normalCoefficient m₀ FInv).field t x‖ := by
    rw [← one_div]
    exact (div_le_iff₀ hB).2 (by simpa only [mul_comm] using hn)
  exact (sq_le_sq₀ (inv_nonneg.mpr hB.le) (norm_nonneg _)).2 hd


-- @@ L224-224 verbatim
end EulerTransverseBoundedFrame


-- @@ L226-226 verbatim
end

-- @@ L227-227 verbatim
end


-- @@ L229-229 verbatim
end


-- @@ L231-231 verbatim
@[expose] public section


-- @@ L233-233 verbatim
noncomputable section


-- @@ L235-235 verbatim
namespace EulerTransversePacketProvider


-- @@ L237-238 verbatim
open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseFrameCoordinates EulerTransverseBoundedFrame EulerVolterraConvolution

-- @@ L239-239 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L241-268 verbatim
/-- Data, collecting `T`, `T_pos`, `support`, `support_compact`, `m₀`, `m₀_unit` and their
compatibility conditions. -/
structure Data (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] where
  /-- Time horizon of `Data`, of type `ℝ`. -/
  T : ℝ
  T_pos : 0 < T
  /-- Support set of `Data`, of type `Set Space`. -/
  support : Set Space
  support_compact : IsCompact support
  /-- M₀ of `Data`, of type `Space`. -/
  m₀ : Space
  m₀_unit : ‖m₀‖ = 1
  /-- Radius parameter of `Data`, of type `U ≃ₗᵢ[ℝ] referencePlane m₀`. -/
  R : U ≃ₗᵢ[ℝ] referencePlane m₀
  /-- F of `Data`, of type `SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)`. -/
  F : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  /-- F₁ of `Data`, of type `SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)`. -/
  F₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  /-- F inv of `Data`, of type `SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)`. -/
  FInv : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  /-- M of `Data`, of type `SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)`. -/
  M : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)
  inverse_left : ∀ t x v, FInv.field t x (F.field t x v) = v
  inverse_right : ∀ t x v, F.field t x (FInv.field t x v) = v
  frame_time : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath T T_pos.le F.field s x)
      (extendPath T T_pos.le F₁.field t x) (Icc (0 : ℝ) T) t
  strain_equation : ∀ t x v, F₁.field t x v = M.field t x (F.field t x v)


-- @@ L270-270 verbatim
namespace Data


-- @@ L272-272 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)


-- @@ L274-275 verbatim
theorem support_measurable : MeasurableSet D.support :=
  D.support_compact.isClosed.measurableSet


-- @@ L277-278 verbatim
/-- Frame: an abbreviation for `coefficient D.m₀ D.R D.F`. -/
abbrev frame := coefficient D.m₀ D.R D.F

-- @@ L279-280 verbatim
/-- Frame derivative: an abbreviation for `coefficient D.m₀ D.R D.F₁`. -/
abbrev frameDerivative := coefficient D.m₀ D.R D.F₁

-- @@ L281-282 verbatim
/-- Normal: an abbreviation for `normalCoefficient D.m₀ D.FInv`. -/
abbrev normal := normalCoefficient D.m₀ D.FInv


-- @@ L284-285 verbatim
/-- Inverse bound, given by `1+‖D.FInv.field‖`. -/
def inverseBound : ℝ := 1+‖D.FInv.field‖

-- @@ L286-287 verbatim
/-- Frame bound, given by `1+‖D.F.field‖`. -/
def frameBound : ℝ := 1+‖D.F.field‖

-- @@ L288-289 verbatim
/-- Frame lower, given by `D.inverseBound⁻¹^2`. -/
def frameLower : ℝ := D.inverseBound⁻¹^2

-- @@ L290-291 verbatim
/-- Normal lower, given by `D.frameBound⁻¹^2`. -/
def normalLower : ℝ := D.frameBound⁻¹^2


-- @@ L293-295 verbatim
theorem inverseBound_pos : 0 < D.inverseBound := by
  unfold inverseBound
  positivity


-- @@ L297-299 verbatim
theorem frameBound_pos : 0 < D.frameBound := by
  unfold frameBound
  positivity


-- @@ L301-302 verbatim
theorem frameLower_pos : 0 < D.frameLower :=
  pow_pos (inv_pos.mpr D.inverseBound_pos) 2


-- @@ L304-305 verbatim
theorem normalLower_pos : 0 < D.normalLower :=
  pow_pos (inv_pos.mpr D.frameBound_pos) 2


-- @@ L307-310 verbatim
theorem inverse_norm (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖D.FInv.field t x‖ ≤ D.inverseBound := by
  exact ((D.FInv.field t).norm_coe_le_norm x).trans
    ((D.FInv.field.norm_coe_le_norm t).trans (by unfold inverseBound; linarith))


-- @@ L312-315 verbatim
theorem frame_norm (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖D.F.field t x‖ ≤ D.frameBound := by
  exact ((D.F.field t).norm_coe_le_norm x).trans
    ((D.F.field.norm_coe_le_norm t).trans (by unfold frameBound; linarith))


-- @@ L317-321 verbatim
/-- Uniform coercivity follows from the actual inverse deformation. -/
theorem frame_lower (t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    D.frameLower*‖v‖^2 ≤ ‖D.frame.field t x v‖^2 :=
  coefficient_lower D.m₀ D.R D.F (fun t x => D.FInv.field t x)
    D.inverseBound D.inverseBound_pos D.inverse_left D.inverse_norm t x v


-- @@ L323-327 verbatim
/-- The scalar pressure inverse is nondegenerate by the same source identity. -/
theorem normal_lower (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.normalLower ≤ ‖D.normal.field t x‖^2 :=
  normalCoefficient_lower D.m₀ D.F D.FInv D.m₀_unit D.inverse_left
    D.frameBound D.frameBound_pos D.frame_norm t x


-- @@ L329-331 verbatim
theorem frame_tangent (t : Icc (0 : ℝ) D.T) (x : Space) (v : U) :
    ⟪D.normal.field t x,D.frame.field t x v⟫_ℝ = 0 :=
  coefficient_tangent D.m₀ D.R D.F D.FInv D.inverse_left t x v


-- @@ L333-335 verbatim
theorem frame_range (t : Icc (0 : ℝ) D.T) (x η : Space)
    (hη : ⟪D.normal.field t x, η⟫_ℝ = 0) : ∃ v, D.frame.field t x v = η :=
  coefficient_range D.m₀ D.R D.F D.FInv D.inverse_right t x η hη


-- @@ L337-339 verbatim
theorem frame_strain (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.frameDerivative.field t x = (D.M.field t x).comp (D.frame.field t x) :=
  coefficient_strain D.m₀ D.R D.F D.F₁ D.M D.strain_equation t x


-- @@ L341-344 verbatim
theorem frame_derivative (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le D.frame.field s x)
      (extendPath D.T D.T_pos.le D.frameDerivative.field t x) (Icc (0 : ℝ) D.T) t :=
  coefficient_hasDerivWithinAt D.m₀ D.R D.T D.T_pos.le D.F D.F₁ D.frame_time t ht x


-- @@ L346-346 verbatim
end Data


-- @@ L348-348 verbatim
end EulerTransversePacketProvider
