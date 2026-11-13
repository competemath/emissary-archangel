import Submission.StandardSaddleCobordism
import Submission.TubeFrameClass


-- @@ L4-12 verbatim
/-!
# The explicit frame of the standard Cassini saddle

This file begins the local frame calculation for the literal saddle from
`StandardSaddleCobordism`.  It extracts the spatial differential at every
Cassini level, identifies the gradient rows, and proves that the planar normal
never vanishes on either endpoint level.  The resulting tangent/normal pair is
the common input for the two incoming ovals and the outgoing loop.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
set_option maxHeartbeats 1600000


-- @@ L18-18 verbatim
namespace Submission

-- @@ L19-19 verbatim
namespace StandardSaddle


-- @@ L21-21 verbatim
open Set Function InnerProductSpace

-- @@ L22-22 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval


-- @@ L24-24 verbatim
variable (m : ℕ)


-- @@ L26-26 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L27-27 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L29-29 verbatim
/-! ## Spatial differential and gradient rows -/


-- @@ L31-49 verbatim
theorem fderiv_levelMap_apply_castSucc (a : ℝ) (x h : E)
    (j : Fin (m + 1)) :
    fderiv ℝ (levelMap m a) x h j.castSucc = h j.castSucc.castSucc := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj j.castSucc
  let inProj : E →L[ℝ] ℝ := EuclideanSpace.proj j.castSucc.castSucc
  have hG : HasFDerivAt (levelMap m a) (fderiv ℝ (levelMap m a) x) x :=
    ((contDiff_levelMap m a).differentiable infty_ne_zero x).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => levelMap m a w j.castSucc)
      (outProj.comp (fderiv ℝ (levelMap m a) x)) x := by
    exact (PiLp.hasFDerivAt_apply 2 (levelMap m a x) j.castSucc).comp x hG
  have hcoord : HasFDerivAt (fun w : E => w j.castSucc.castSucc) inProj x :=
    inProj.hasFDerivAt
  have hfun : (fun w => levelMap m a w j.castSucc) =
      fun w : E => w j.castSucc.castSucc := by
    funext w
    simp [levelMap]
  have hmaps : outProj.comp (fderiv ℝ (levelMap m a) x) = inProj := by
    rw [← hcomp.fderiv, hfun, hcoord.fderiv]
  exact congrArg (fun A : E →L[ℝ] ℝ => A h) hmaps


-- @@ L51-82 verbatim
theorem fderiv_levelMap_apply_last (a : ℝ) (x h : E) :
    fderiv ℝ (levelMap m a) x h (Fin.last (m + 1)) =
      4 * x (planeFirst m) * (radiusSq m x - 1) * h (planeFirst m) +
        4 * x (planeSecond m) * (radiusSq m x + 1) * h (planeSecond m) := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last (m + 1))
  have hG : HasFDerivAt (levelMap m a) (fderiv ℝ (levelMap m a) x) x :=
    ((contDiff_levelMap m a).differentiable infty_ne_zero x).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => levelMap m a w (Fin.last (m + 1)))
      (outProj.comp (fderiv ℝ (levelMap m a) x)) x := by
    exact (PiLp.hasFDerivAt_apply 2 (levelMap m a x)
      (Fin.last (m + 1))).comp x hG
  let pA : E →L[ℝ] ℝ := EuclideanSpace.proj (planeFirst m)
  let pB : E →L[ℝ] ℝ := EuclideanSpace.proj (planeSecond m)
  have hA := (pA.hasFDerivAt : HasFDerivAt pA pA x)
  have hB := (pB.hasFDerivAt : HasFDerivAt pB pB x)
  have hq :=
    ((((hA.sub_const 1).pow 2).add (hB.pow 2)).mul
      (((hA.add_const 1).pow 2).add (hB.pow 2))).sub_const 1
  change HasFDerivAt
    (fun w : E =>
      ((pA w - 1) ^ 2 + pB w ^ 2) *
        ((pA w + 1) ^ 2 + pB w ^ 2) - 1) _ x at hq
  have hdirect := hq.sub_const a
  have hfun : (fun w => levelMap m a w (Fin.last (m + 1))) = fun w : E =>
      (((pA w - 1) ^ 2 + (pB w) ^ 2) *
        ((pA w + 1) ^ 2 + (pB w) ^ 2) - 1) - a := by
    funext w
    simp [levelMap, cassiniQ, pA, pB]
  have happ := congrArg (fun A : E →L[ℝ] ℝ => A h) hcomp.fderiv.symm
  rw [hfun, hdirect.fderiv] at happ
  simp [outProj, pA, pB, radiusSq] at happ
  convert happ using 1 <;> simp [radiusSq] <;> ring


-- @@ L84-86 verbatim
/-- First coefficient of the planar gradient of the Cassini equation. -/
def normalFirst (x : E) : ℝ :=
  4 * x (planeFirst m) * (radiusSq m x - 1)


-- @@ L88-90 verbatim
/-- Second coefficient of the planar gradient of the Cassini equation. -/
def normalSecond (x : E) : ℝ :=
  4 * x (planeSecond m) * (radiusSq m x + 1)


-- @@ L92-95 verbatim
/-- The last gradient row, supported in the Cassini plane. -/
def planarNormal (x : E) : E :=
  normalFirst m x • EuclideanSpace.single (planeFirst m) 1 +
    normalSecond m x • EuclideanSpace.single (planeSecond m) 1


-- @@ L97-100 verbatim
/-- The counterclockwise quarter-turn of `planarNormal`. -/
def planarTangent (x : E) : E :=
  (-normalSecond m x) • EuclideanSpace.single (planeFirst m) 1 +
    normalFirst m x • EuclideanSpace.single (planeSecond m) 1


-- @@ L102-113 verbatim
theorem gradVec_levelMap_castSucc (a : ℝ) (x : E) (j : Fin (m + 1)) :
    gradVec (levelMap m a) j.castSucc x =
      EuclideanSpace.single j.castSucc.castSucc 1 := by
  apply ext_inner_right_basis (EuclideanSpace.basisFun (Fin (m + 3)) ℝ).toBasis
  intro k
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change inner ℝ (gradVec (levelMap m a) j.castSucc x)
      (EuclideanSpace.single k 1) =
    inner ℝ (EuclideanSpace.single j.castSucc.castSucc 1)
      (EuclideanSpace.single k 1)
  rw [inner_gradVec, fderiv_levelMap_apply_castSucc]
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply]


-- @@ L115-128 verbatim
theorem gradVec_levelMap_last (a : ℝ) (x : E) :
    gradVec (levelMap m a) (Fin.last (m + 1)) x = planarNormal m x := by
  apply ext_inner_right_basis (EuclideanSpace.basisFun (Fin (m + 3)) ℝ).toBasis
  intro k
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change inner ℝ (gradVec (levelMap m a) (Fin.last (m + 1)) x)
      (EuclideanSpace.single k 1) =
    inner ℝ (planarNormal m x) (EuclideanSpace.single k 1)
  rw [inner_gradVec, fderiv_levelMap_apply_last]
  rw [planarNormal, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left]
  simp [normalFirst, normalSecond, EuclideanSpace.inner_single_left,
    PiLp.single_apply]


-- @@ L130-130 verbatim
/-! ## The endpoint normal is nowhere zero -/


-- @@ L132-136 verbatim
theorem transverse_eq_zero_of_levelMap_eq_zero {a : ℝ} {x : E}
    (hx : levelMap m a x = 0) (j : Fin (m + 1)) :
    x j.castSucc.castSucc = 0 := by
  have h := congrArg (fun q : F => q j.castSucc) hx
  simpa using h


-- @@ L138-142 verbatim
theorem cassiniQ_eq_level_of_levelMap_eq_zero {a : ℝ} {x : E}
    (hx : levelMap m a x = 0) : cassiniQ m x = a := by
  have h := congrArg (fun q : F => q (Fin.last (m + 1))) hx
  simp at h
  linarith


-- @@ L144-178 verbatim
/-- The only critical values of the planar Cassini polynomial are `0` and
`-1`; hence its planar gradient cannot vanish on any other level. -/
theorem normalFirst_ne_zero_or_normalSecond_ne_zero_of_level
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha0 : a ≠ 0) (ha1 : a ≠ -1) :
    normalFirst m x ≠ 0 ∨ normalSecond m x ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨hA, hB⟩
  have hr_nonneg : 0 ≤ radiusSq m x := by
    simp [radiusSq]
    positivity
  have hrp : 0 < radiusSq m x + 1 := by linarith
  have hy0 : x (planeSecond m) = 0 := by
    unfold normalSecond at hB
    rcases mul_eq_zero.mp hB with h4x | hr
    · norm_num at h4x
      exact h4x
    · exact False.elim ((ne_of_gt hrp) hr)
  have hx0_or_r1 : x (planeFirst m) = 0 ∨ radiusSq m x = 1 := by
    unfold normalFirst at hA
    rcases mul_eq_zero.mp hA with h4x | hr
    · norm_num at h4x
      exact Or.inl h4x
    · exact Or.inr (sub_eq_zero.mp hr)
  have hlevel := cassiniQ_eq_level_of_levelMap_eq_zero m hx
  rw [cassiniQ_eq] at hlevel
  rcases hx0_or_r1 with hx0 | hr1
  · apply ha0
    simp [radiusSq, hx0, hy0] at hlevel
    exact hlevel.symm
  · apply ha1
    have hxSq : x (planeFirst m) ^ 2 = 1 := by
      simpa [radiusSq, hy0] using hr1
    nlinarith


-- @@ L180-186 verbatim
theorem endpoint_normal_coefficients_ne_zero
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    normalFirst m x ≠ 0 ∨ normalSecond m x ≠ 0 := by
  apply normalFirst_ne_zero_or_normalSecond_ne_zero_of_level m hx
  · rcases ha with rfl | rfl <;> norm_num
  · rcases ha with rfl | rfl <;> norm_num


-- @@ L188-208 verbatim
theorem planarNormal_ne_zero_of_endpoint
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    planarNormal m x ≠ 0 := by
  obtain hA | hB := endpoint_normal_coefficients_ne_zero m hx ha
  · intro hzero
    have hcoord := congrArg (fun q : E => q (planeFirst m)) hzero
    have hAB : planeFirst m ≠ planeSecond m := by
      intro h
      have := congrArg Fin.val h
      simp [planeFirst, planeSecond] at this
    simp [planarNormal, PiLp.single_apply, hAB] at hcoord
    exact hA hcoord
  · intro hzero
    have hcoord := congrArg (fun q : E => q (planeSecond m)) hzero
    have hBA : planeSecond m ≠ planeFirst m := by
      intro h
      have := congrArg Fin.val h
      simp [planeFirst, planeSecond] at this
    simp [planarNormal, PiLp.single_apply, hBA] at hcoord
    exact hB hcoord


-- @@ L210-230 verbatim
theorem planarTangent_ne_zero_of_endpoint
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    planarTangent m x ≠ 0 := by
  obtain hA | hB := endpoint_normal_coefficients_ne_zero m hx ha
  · intro hzero
    have hcoord := congrArg (fun q : E => q (planeSecond m)) hzero
    have hBA : planeSecond m ≠ planeFirst m := by
      intro h
      have := congrArg Fin.val h
      simp [planeFirst, planeSecond] at this
    simp [planarTangent, PiLp.single_apply, hBA] at hcoord
    exact hA hcoord
  · intro hzero
    have hcoord := congrArg (fun q : E => q (planeFirst m)) hzero
    have hAB : planeFirst m ≠ planeSecond m := by
      intro h
      have := congrArg Fin.val h
      simp [planeFirst, planeSecond] at this
    simp [planarTangent, PiLp.single_apply, hAB] at hcoord
    exact hB hcoord


-- @@ L232-242 verbatim
theorem inner_planarTangent_planarNormal (x : E) :
    inner ℝ (planarTangent m x) (planarNormal m x) = 0 := by
  have hAB : planeFirst m ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  have hBA : planeSecond m ≠ planeFirst m := hAB.symm
  simp [planarTangent, planarNormal, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, hAB, hBA]
  ring


-- @@ L244-250 verbatim
@[simp] theorem planarNormal_apply_planeFirst (x : E) :
    planarNormal m x (planeFirst m) = normalFirst m x := by
  have hAB : planeFirst m ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  simp [planarNormal, hAB]


-- @@ L252-258 verbatim
@[simp] theorem planarNormal_apply_planeSecond (x : E) :
    planarNormal m x (planeSecond m) = normalSecond m x := by
  have hBA : planeSecond m ≠ planeFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  simp [planarNormal, hBA]


-- @@ L260-266 verbatim
@[simp] theorem planarTangent_apply_planeFirst (x : E) :
    planarTangent m x (planeFirst m) = -normalSecond m x := by
  have hAB : planeFirst m ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  simp [planarTangent, hAB]


-- @@ L268-274 verbatim
@[simp] theorem planarTangent_apply_planeSecond (x : E) :
    planarTangent m x (planeSecond m) = normalFirst m x := by
  have hBA : planeSecond m ≠ planeFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  simp [planarTangent, hBA]


-- @@ L276-288 verbatim
@[simp] theorem planarNormal_apply_transverse (x : E) (j : Fin (m + 1)) :
    planarNormal m x j.castSucc.castSucc = 0 := by
  have hjA : j.castSucc.castSucc ≠ planeFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst] at this
    omega
  have hjB : j.castSucc.castSucc ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeSecond] at this
    omega
  simp [planarNormal, hjA, hjB]


-- @@ L290-302 verbatim
@[simp] theorem planarTangent_apply_transverse (x : E) (j : Fin (m + 1)) :
    planarTangent m x j.castSucc.castSucc = 0 := by
  have hjA : j.castSucc.castSucc ≠ planeFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst] at this
    omega
  have hjB : j.castSucc.castSucc ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeSecond] at this
    omega
  simp [planarTangent, hjA, hjB]


-- @@ L304-316 verbatim
theorem inner_planarNormal_self (x : E) :
    inner ℝ (planarNormal m x) (planarNormal m x) =
      normalFirst m x ^ 2 + normalSecond m x ^ 2 := by
  have hAB : planeFirst m ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  have hBA : planeSecond m ≠ planeFirst m := hAB.symm
  simp only [planarNormal, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, if_pos,
    if_neg hAB, if_neg hBA, map_one, mul_one, mul_zero, add_zero, zero_add]
  ring


-- @@ L318-330 verbatim
theorem inner_planarTangent_self (x : E) :
    inner ℝ (planarTangent m x) (planarTangent m x) =
      normalFirst m x ^ 2 + normalSecond m x ^ 2 := by
  have hAB : planeFirst m ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  have hBA : planeSecond m ≠ planeFirst m := hAB.symm
  simp only [planarTangent, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, if_pos,
    if_neg hAB, if_neg hBA, map_one, mul_one, mul_zero, add_zero, zero_add]
  ring


-- @@ L332-336 verbatim
theorem norm_planarTangent_eq_norm_planarNormal (x : E) :
    ‖planarTangent m x‖ = ‖planarNormal m x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_planarTangent_self, inner_planarNormal_self]


-- @@ L338-354 verbatim
/-- The quarter-turned planar normal is exactly in the kernel of every
spatial Cassini level map. -/
theorem fderiv_levelMap_planarTangent (a : ℝ) (x : E) :
    fderiv ℝ (levelMap m a) x (planarTangent m x) = 0 := by
  apply (WithLp.equiv 2 _).injective
  funext i
  induction i using Fin.lastCases with
  | last =>
      change fderiv ℝ (levelMap m a) x (planarTangent m x)
        (Fin.last (m + 1)) = 0
      rw [fderiv_levelMap_apply_last]
      simp [normalFirst, normalSecond]
      ring
  | cast j =>
      change fderiv ℝ (levelMap m a) x (planarTangent m x) j.castSucc = 0
      rw [fderiv_levelMap_apply_castSucc]
      exact planarTangent_apply_transverse m x j


-- @@ L356-358 verbatim
/-- Unit tangent obtained directly from the planar gradient. -/
def unitPlanarTangent (x : E) : E :=
  (‖planarTangent m x‖⁻¹) • planarTangent m x


-- @@ L360-362 verbatim
/-- Unit planar normal obtained directly from the last gradient row. -/
def unitPlanarNormal (x : E) : E :=
  (‖planarNormal m x‖⁻¹) • planarNormal m x


-- @@ L364-370 verbatim
theorem norm_unitPlanarTangent_of_endpoint
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    ‖unitPlanarTangent m x‖ = 1 := by
  rw [unitPlanarTangent, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (planarTangent_ne_zero_of_endpoint m hx ha)


-- @@ L372-378 verbatim
theorem norm_unitPlanarNormal_of_endpoint
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    ‖unitPlanarNormal m x‖ = 1 := by
  rw [unitPlanarNormal, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (planarNormal_ne_zero_of_endpoint m hx ha)


-- @@ L380-382 verbatim
theorem fderiv_levelMap_unitPlanarTangent (a : ℝ) (x : E) :
    fderiv ℝ (levelMap m a) x (unitPlanarTangent m x) = 0 := by
  rw [unitPlanarTangent, map_smul, fderiv_levelMap_planarTangent, smul_zero]


-- @@ L384-387 verbatim
theorem inner_unitPlanarTangent_unitPlanarNormal (x : E) :
    inner ℝ (unitPlanarTangent m x) (unitPlanarNormal m x) = 0 := by
  simp [unitPlanarTangent, unitPlanarNormal, real_inner_smul_left,
    real_inner_smul_right, inner_planarTangent_planarNormal]


-- @@ L389-389 verbatim
/-! ## Identification with the intrinsic oriented tangent -/


-- @@ L391-395 verbatim
/-- Choose the sign of the explicit unit tangent by the same determinant
orientation used in the definition of `tauField`. -/
def tangentOrientationSign (a : ℝ) (x : E) : ℝ :=
  if 0 < crossDet (fun i => gradVec (levelMap m a) i x)
      (unitPlanarTangent m x) then 1 else -1


-- @@ L397-398 verbatim
def orientedUnitPlanarTangent (a : ℝ) (x : E) : E :=
  tangentOrientationSign m a x • unitPlanarTangent m x


-- @@ L400-404 verbatim
theorem tangentOrientationSign_eq_one_or_neg_one (a : ℝ) (x : E) :
    tangentOrientationSign m a x = 1 ∨
      tangentOrientationSign m a x = -1 := by
  unfold tangentOrientationSign
  split_ifs <;> simp


-- @@ L406-409 verbatim
theorem abs_tangentOrientationSign (a : ℝ) (x : E) :
    |tangentOrientationSign m a x| = 1 := by
  rcases tangentOrientationSign_eq_one_or_neg_one m a x with h | h <;>
    rw [h] <;> norm_num


-- @@ L411-417 verbatim
theorem norm_orientedUnitPlanarTangent_of_endpoint
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    ‖orientedUnitPlanarTangent m a x‖ = 1 := by
  rw [orientedUnitPlanarTangent, norm_smul, Real.norm_eq_abs,
    abs_tangentOrientationSign, norm_unitPlanarTangent_of_endpoint m hx ha,
    one_mul]


-- @@ L419-422 verbatim
theorem fderiv_levelMap_orientedUnitPlanarTangent (a : ℝ) (x : E) :
    fderiv ℝ (levelMap m a) x (orientedUnitPlanarTangent m a x) = 0 := by
  rw [orientedUnitPlanarTangent, map_smul,
    fderiv_levelMap_unitPlanarTangent, smul_zero]


-- @@ L424-450 verbatim
theorem crossDet_unitPlanarTangent_ne_zero
    {a : ℝ} {x : E} (hreg : x ∈ regularSet (levelMap m a))
    (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    crossDet (fun i => gradVec (levelMap m a) i x)
        (unitPlanarTangent m x) ≠ 0 := by
  let q := unitPlanarTangent m x
  have hkernel : fderiv ℝ (levelMap m a) x q = 0 :=
    fderiv_levelMap_unitPlanarTangent m a x
  have hmem : q ∈ Submodule.span ℝ {tauField (levelMap m a) x} :=
    (fderiv_eq_zero_iff_mem_span_tauField hreg _).mp hkernel
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hqnorm : ‖q‖ = 1 := norm_unitPlanarTangent_of_endpoint m hx ha
  have hc0 : c ≠ 0 := by
    intro hczero
    rw [hczero, zero_smul] at hc
    have := congrArg norm hc
    simp [hqnorm] at this
  have hdetTau :
      crossDet (fun i => gradVec (levelMap m a) i x)
          (tauField (levelMap m a) x) ≠ 0 :=
    ne_of_gt (crossDet_tauField_pos hreg)
  have hdetEq := congrArg
    (crossDet (fun i => gradVec (levelMap m a) i x)) hc
  rw [crossDet_smul] at hdetEq
  rw [← hdetEq]
  exact mul_ne_zero hc0 hdetTau


-- @@ L452-469 verbatim
theorem crossDet_orientedUnitPlanarTangent_pos
    {a : ℝ} {x : E} (hreg : x ∈ regularSet (levelMap m a))
    (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    0 < crossDet (fun i => gradVec (levelMap m a) i x)
      (orientedUnitPlanarTangent m a x) := by
  let d := crossDet (fun i => gradVec (levelMap m a) i x)
    (unitPlanarTangent m x)
  have hd0 : d ≠ 0 := crossDet_unitPlanarTangent_ne_zero m hreg hx ha
  by_cases hd : 0 < d
  · rw [orientedUnitPlanarTangent, tangentOrientationSign, if_pos hd,
      crossDet_smul]
    simpa [d] using hd
  · have hdneg : d < 0 := lt_of_le_of_ne (not_lt.mp hd) hd0
    have hpos : 0 < -d := neg_pos.mpr hdneg
    rw [orientedUnitPlanarTangent, tangentOrientationSign, if_neg hd,
      crossDet_smul]
    simpa [d] using hpos


-- @@ L471-501 verbatim
/-- A unit kernel vector with positive cross determinant is the canonical
`tauField`.  This is the reusable uniqueness step behind both endpoint
identifications. -/
theorem tauField_eq_of_unit_kernel_crossDet_pos
    {a : ℝ} {x q : E} (hreg : x ∈ regularSet (levelMap m a))
    (hkernel : fderiv ℝ (levelMap m a) x q = 0)
    (hnorm : ‖q‖ = 1)
    (hdet : 0 < crossDet (fun i => gradVec (levelMap m a) i x) q) :
    tauField (levelMap m a) x = q := by
  have hmem : q ∈ Submodule.span ℝ {tauField (levelMap m a) x} :=
    (fderiv_eq_zero_iff_mem_span_tauField hreg _).mp hkernel
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hdetTau : 0 < crossDet (fun i => gradVec (levelMap m a) i x)
      (tauField (levelMap m a) x) := crossDet_tauField_pos hreg
  have hdetEq := congrArg
    (crossDet (fun i => gradVec (levelMap m a) i x)) hc
  rw [crossDet_smul] at hdetEq
  have hprod : 0 < c * crossDet (fun i => gradVec (levelMap m a) i x)
      (tauField (levelMap m a) x) := by
    rw [hdetEq]
    exact hdet
  have hcPos : 0 < c := by
    rcases mul_pos_iff.mp hprod with hp | hn
    · exact hp.1
    · exact False.elim ((not_lt_of_ge (le_of_lt hdetTau)) hn.2)
  have hnormEq := congrArg norm hc
  rw [norm_smul, norm_tauField hreg, mul_one, hnorm,
    Real.norm_eq_abs, abs_of_pos hcPos] at hnormEq
  have hcOne : c = 1 := hnormEq
  rw [hcOne, one_smul] at hc
  exact hc


-- @@ L503-511 verbatim
theorem tauField_levelMap_eq_orientedUnitPlanarTangent
    {a : ℝ} {x : E} (hreg : x ∈ regularSet (levelMap m a))
    (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    tauField (levelMap m a) x = orientedUnitPlanarTangent m a x := by
  apply tauField_eq_of_unit_kernel_crossDet_pos m hreg
  · exact fderiv_levelMap_orientedUnitPlanarTangent m a x
  · exact norm_orientedUnitPlanarTangent_of_endpoint m hx ha
  · exact crossDet_orientedUnitPlanarTangent_pos m hreg hx ha


-- @@ L513-518 verbatim
theorem tauField_source_eq_orientedUnitPlanarTangent
    {x : E} (hx : x ∈ (sourceFLS m).fiber) :
    tauField (sourceFLS m).g x =
      orientedUnitPlanarTangent m (-1 / 2) x := by
  exact tauField_levelMap_eq_orientedUnitPlanarTangent m
    ((sourceFLS m).fiber_subset_regularSet hx) hx (Or.inl rfl)


-- @@ L520-525 verbatim
theorem tauField_target_eq_orientedUnitPlanarTangent
    {x : E} (hx : x ∈ (targetFLS m).fiber) :
    tauField (targetFLS m).g x =
      orientedUnitPlanarTangent m (1 / 2) x := by
  exact tauField_levelMap_eq_orientedUnitPlanarTangent m
    ((targetFLS m).fiber_subset_regularSet hx) hx (Or.inr rfl)


-- @@ L527-527 verbatim
/-! ## The endpoint Gram--Schmidt frame -/


-- @@ L529-533 verbatim
theorem inner_transverse_planarNormal (x : E) (j : Fin (m + 1)) :
    inner ℝ (EuclideanSpace.single j.castSucc.castSucc 1)
      (planarNormal m x) = 0 := by
  rw [EuclideanSpace.inner_single_left]
  simp


-- @@ L535-539 verbatim
theorem inner_transverse_unitPlanarNormal (x : E) (j : Fin (m + 1)) :
    inner ℝ (EuclideanSpace.single j.castSucc.castSucc 1)
      (unitPlanarNormal m x) = 0 := by
  simp [unitPlanarNormal, real_inner_smul_right,
    inner_transverse_planarNormal]


-- @@ L541-545 verbatim
theorem inner_transverse_planarTangent (x : E) (j : Fin (m + 1)) :
    inner ℝ (EuclideanSpace.single j.castSucc.castSucc 1)
      (planarTangent m x) = 0 := by
  rw [EuclideanSpace.inner_single_left]
  simp


-- @@ L547-552 verbatim
theorem inner_transverse_orientedUnitPlanarTangent
    (a : ℝ) (x : E) (j : Fin (m + 1)) :
    inner ℝ (EuclideanSpace.single j.castSucc.castSucc 1)
      (orientedUnitPlanarTangent m a x) = 0 := by
  simp only [orientedUnitPlanarTangent, unitPlanarTangent,
    real_inner_smul_right, inner_transverse_planarTangent, mul_zero]


-- @@ L554-559 verbatim
theorem inner_orientedUnitPlanarTangent_unitPlanarNormal
    (a : ℝ) (x : E) :
    inner ℝ (orientedUnitPlanarTangent m a x)
      (unitPlanarNormal m x) = 0 := by
  simp [orientedUnitPlanarTangent, real_inner_smul_left,
    inner_unitPlanarTangent_unitPlanarNormal]


-- @@ L561-574 verbatim
theorem inner_transverse_transverse (j k : Fin (m + 1)) :
    inner ℝ (EuclideanSpace.single j.castSucc.castSucc (1 : ℝ))
      (EuclideanSpace.single k.castSucc.castSucc 1) =
        if j = k then 1 else 0 := by
  rw [EuclideanSpace.inner_single_left]
  by_cases h : j = k
  · subst k
    simp
  · have hcast : j.castSucc.castSucc ≠ k.castSucc.castSucc := by
      intro heq
      apply h
      apply Fin.ext
      simpa using congrArg (fun z : Fin (m + 3) => z.val) heq
    simp [h, hcast]


-- @@ L576-579 verbatim
/-- Normal rows after their final normalization. -/
def endpointNormalUnit (x : E) : Fin (m + 2) → E :=
  Fin.lastCases (unitPlanarNormal m x)
    (fun j : Fin (m + 1) => EuclideanSpace.single j.castSucc.castSucc 1)


-- @@ L581-583 verbatim
@[simp] theorem endpointNormalUnit_last (x : E) :
    endpointNormalUnit m x (Fin.last (m + 1)) = unitPlanarNormal m x := by
  simp [endpointNormalUnit]


-- @@ L585-588 verbatim
@[simp] theorem endpointNormalUnit_castSucc (x : E) (j : Fin (m + 1)) :
    endpointNormalUnit m x j.castSucc =
      EuclideanSpace.single j.castSucc.castSucc 1 := by
  simp [endpointNormalUnit]


-- @@ L590-616 verbatim
theorem orthonormal_endpointNormalUnit
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    Orthonormal ℝ (endpointNormalUnit m x) := by
  rw [orthonormal_iff_ite]
  intro i j
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last =>
          rw [endpointNormalUnit_last, real_inner_self_eq_norm_sq,
            norm_unitPlanarNormal_of_endpoint m hx ha]
          simp
      | cast j =>
          rw [endpointNormalUnit_last, endpointNormalUnit_castSucc,
            real_inner_comm, inner_transverse_unitPlanarNormal]
          simp [Fin.castSucc_lt_last j |>.ne']
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          rw [endpointNormalUnit_castSucc, endpointNormalUnit_last,
            inner_transverse_unitPlanarNormal]
          simp [Fin.castSucc_lt_last i |>.ne]
      | cast j =>
          rw [endpointNormalUnit_castSucc, endpointNormalUnit_castSucc,
            inner_transverse_transverse]
          simp


-- @@ L618-621 verbatim
/-- The orthonormal endpoint frame: canonical tangent, transverse coordinate
normals, and the normalized Cassini normal. -/
def endpointUnitFrame (a : ℝ) (x : E) : Fin (m + 3) → E :=
  Fin.cons (orientedUnitPlanarTangent m a x) (endpointNormalUnit m x)


-- @@ L623-659 verbatim
theorem orthonormal_endpointUnitFrame
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    Orthonormal ℝ (endpointUnitFrame m a x) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rw [endpointUnitFrame, Fin.cons_zero, real_inner_self_eq_norm_sq,
        norm_orientedUnitPlanarTangent_of_endpoint m hx ha]
      simp
    · induction j using Fin.lastCases with
      | last =>
          rw [endpointUnitFrame, Fin.cons_zero, Fin.cons_succ,
            endpointNormalUnit_last,
            inner_orientedUnitPlanarTangent_unitPlanarNormal]
          simp
      | cast j =>
          rw [endpointUnitFrame, Fin.cons_zero, Fin.cons_succ,
            endpointNormalUnit_castSucc, real_inner_comm,
            inner_transverse_orientedUnitPlanarTangent]
          simp [Ne.symm (Fin.succ_ne_zero j.castSucc)]
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · induction i using Fin.lastCases with
      | last =>
          rw [endpointUnitFrame, Fin.cons_succ, endpointNormalUnit_last,
            Fin.cons_zero, real_inner_comm,
            inner_orientedUnitPlanarTangent_unitPlanarNormal]
          simp
      | cast i =>
          rw [endpointUnitFrame, Fin.cons_succ,
            endpointNormalUnit_castSucc, Fin.cons_zero,
            inner_transverse_orientedUnitPlanarTangent]
          simp
    · rw [endpointUnitFrame, Fin.cons_succ, Fin.cons_succ]
      simpa only [Fin.succ_inj] using
        orthonormal_iff_ite.mp (orthonormal_endpointNormalUnit m hx ha) i j


-- @@ L661-664 verbatim
/-- The unnormalized rows which occur literally in `frameAt`. -/
def endpointRawNormal (x : E) : Fin (m + 2) → E :=
  Fin.lastCases (planarNormal m x)
    (fun j : Fin (m + 1) => EuclideanSpace.single j.castSucc.castSucc 1)


-- @@ L666-667 verbatim
def endpointRawFrame (a : ℝ) (x : E) : Fin (m + 3) → E :=
  Fin.cons (orientedUnitPlanarTangent m a x) (endpointRawNormal m x)


-- @@ L669-676 verbatim
@[simp] theorem endpointRawFrame_last (a : ℝ) (x : E) :
    endpointRawFrame m a x (Fin.last (m + 2)) = planarNormal m x := by
  have hs : (Fin.last (m + 1)).succ =
      (Fin.last (m + 2) : Fin (m + 3)) := by
    apply Fin.ext
    simp
  rw [← hs]
  simp [endpointRawFrame, endpointRawNormal]


-- @@ L678-685 verbatim
@[simp] theorem endpointUnitFrame_last (a : ℝ) (x : E) :
    endpointUnitFrame m a x (Fin.last (m + 2)) = unitPlanarNormal m x := by
  have hs : (Fin.last (m + 1)).succ =
      (Fin.last (m + 2) : Fin (m + 3)) := by
    apply Fin.ext
    simp
  rw [← hs]
  simp [endpointUnitFrame]


-- @@ L687-706 verbatim
theorem levelMap_frame_eq_endpointRawFrame
    {a : ℝ} {x : E} (hreg : x ∈ regularSet (levelMap m a))
    (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    Fin.cons (tauField (levelMap m a) x)
      (fun i => gradVec (levelMap m a) i x) = endpointRawFrame m a x := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rw [Fin.cons_zero, endpointRawFrame, Fin.cons_zero,
      tauField_levelMap_eq_orientedUnitPlanarTangent m hreg hx ha]
  · rw [Fin.cons_succ, endpointRawFrame, Fin.cons_succ]
    induction i using Fin.lastCases with
    | last =>
        rw [endpointRawNormal]
        simp only [Fin.lastCases_last]
        exact gradVec_levelMap_last m a x
    | cast i =>
        rw [endpointRawNormal]
        simp only [Fin.lastCases_castSucc]
        exact gradVec_levelMap_castSucc m a x i


-- @@ L708-713 verbatim
theorem frameAt_source_eq_endpointRawFrame
    {x : E} (hx : x ∈ (sourceFLS m).fiber) :
    frameAt (sourceFLS m) x = endpointRawFrame m (-1 / 2) x := by
  simpa only [frameAt, sourceFLS, Nat.add_assoc] using
    levelMap_frame_eq_endpointRawFrame m
      ((sourceFLS m).fiber_subset_regularSet hx) hx (Or.inl rfl)


-- @@ L715-720 verbatim
theorem frameAt_target_eq_endpointRawFrame
    {x : E} (hx : x ∈ (targetFLS m).fiber) :
    frameAt (targetFLS m) x = endpointRawFrame m (1 / 2) x := by
  simpa only [frameAt, targetFLS, Nat.add_assoc] using
    levelMap_frame_eq_endpointRawFrame m
      ((targetFLS m).fiber_subset_regularSet hx) hx (Or.inr rfl)


-- @@ L722-724 verbatim
/-- Only the final Cassini normal is scaled in the literal derivative frame. -/
def endpointFrameScale (x : E) (i : Fin (m + 3)) : ℝ :=
  if i = Fin.last (m + 2) then ‖planarNormal m x‖ else 1


-- @@ L726-733 verbatim
theorem endpointFrameScale_pos
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ))
    (i : Fin (m + 3)) : 0 < endpointFrameScale m x i := by
  unfold endpointFrameScale
  split_ifs
  · exact norm_pos_iff.mpr (planarNormal_ne_zero_of_endpoint m hx ha)
  · norm_num


-- @@ L735-767 verbatim
theorem endpointRawFrame_eq_smul_endpointUnitFrame
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ))
    (i : Fin (m + 3)) :
    endpointRawFrame m a x i = endpointFrameScale m x i •
      endpointUnitFrame m a x i := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · have h0 : (0 : Fin (m + 3)) ≠ Fin.last (m + 2) := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [endpointRawFrame, endpointUnitFrame, endpointFrameScale, h0]
  · induction i using Fin.lastCases with
    | last =>
        have hs : (Fin.last (m + 1)).succ =
            (Fin.last (m + 2) : Fin (m + 3)) := by
          apply Fin.ext
          simp
        rw [hs]
        rw [endpointRawFrame_last, endpointUnitFrame_last]
        simp only [endpointFrameScale, if_pos]
        rw [unitPlanarNormal, smul_smul]
        have hn : ‖planarNormal m x‖ ≠ 0 :=
          norm_ne_zero_iff.mpr (planarNormal_ne_zero_of_endpoint m hx ha)
        rw [mul_inv_cancel₀ hn, one_smul]
    | cast i =>
        have hil : (i.castSucc.succ : Fin (m + 3)) ≠ Fin.last (m + 2) := by
          intro h
          have hv := congrArg (fun z : Fin (m + 3) => z.val) h
          simp at hv
          omega
        simp [endpointRawFrame, endpointUnitFrame, endpointRawNormal,
          endpointNormalUnit, endpointFrameScale, hil]


-- @@ L769-789 verbatim
theorem gramSchmidtNormed_endpointRawFrame
    {a : ℝ} {x : E} (hx : levelMap m a x = 0)
    (ha : a = (-1 / 2 : ℝ) ∨ a = (1 / 2 : ℝ)) :
    gramSchmidtNormed ℝ (endpointRawFrame m a x) =
      endpointUnitFrame m a x := by
  have hon : Orthonormal ℝ (endpointUnitFrame m a x) :=
    orthonormal_endpointUnitFrame m hx ha
  have horth : Pairwise
      (fun i j => inner ℝ (endpointRawFrame m a x i)
        (endpointRawFrame m a x j) = 0) := by
    intro i j hij
    rw [endpointRawFrame_eq_smul_endpointUnitFrame m hx ha,
      endpointRawFrame_eq_smul_endpointUnitFrame m hx ha,
      real_inner_smul_left, real_inner_smul_right, hon.2 hij,
      mul_zero, mul_zero]
  funext i
  rw [gramSchmidtNormed, gramSchmidt_of_orthogonal ℝ horth,
    endpointRawFrame_eq_smul_endpointUnitFrame m hx ha, norm_smul,
    hon.1 i, mul_one, Real.norm_eq_abs,
    abs_of_pos (endpointFrameScale_pos m hx ha i), smul_smul]
  simp [inv_mul_cancel₀ (endpointFrameScale_pos m hx ha i).ne']


-- @@ L791-796 verbatim
theorem gramSchmidtNormed_frameAt_source
    {x : E} (hx : x ∈ (sourceFLS m).fiber) :
    gramSchmidtNormed ℝ (frameAt (sourceFLS m) x) =
      endpointUnitFrame m (-1 / 2) x := by
  rw [frameAt_source_eq_endpointRawFrame m hx]
  exact gramSchmidtNormed_endpointRawFrame m hx (Or.inl rfl)


-- @@ L798-803 verbatim
theorem gramSchmidtNormed_frameAt_target
    {x : E} (hx : x ∈ (targetFLS m).fiber) :
    gramSchmidtNormed ℝ (frameAt (targetFLS m) x) =
      endpointUnitFrame m (1 / 2) x := by
  rw [frameAt_target_eq_endpointRawFrame m hx]
  exact gramSchmidtNormed_endpointRawFrame m hx (Or.inr rfl)


-- @@ L805-805 verbatim
end StandardSaddle

-- @@ L806-806 verbatim
end Submission
