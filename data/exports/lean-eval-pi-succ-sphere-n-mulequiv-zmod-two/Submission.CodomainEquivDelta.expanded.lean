import Mathlib
import Submission.BackgroundHarmonization
import Submission.RegularSlabEndpointDelta


-- @@ L5-14 verbatim
/-!
# The framed delta under a change of codomain coordinates

This file records the coordinate-change facts needed by background
harmonization.  A positive scalar change is joined to the identity through
positive scalars.  The orientation-reversing part is reduced to changing the
sign of one defining equation; this reverses the intrinsic tangent and that
one normal simultaneously, so the resulting full frame is joined through
`SO(n+1)` and has the same mod-two loop class.
-/


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace Submission


-- @@ L20-20 verbatim
open Set Function Topology Matrix Module InnerProductSpace

-- @@ L21-21 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval BigOperators


-- @@ L23-23 verbatim
variable {n : ℕ}


-- @@ L25-25 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L26-26 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L28-28 verbatim
/-! ## A single coordinate reflection -/


-- @@ L30-34 verbatim
/-- Negate one coordinate of Euclidean space. -/
def coordinateReflection (i : Fin n) : F ≃L[ℝ] F :=
  (LinearIsometryEquiv.piLpCongrRight 2 fun j : Fin n =>
    if j = i then LinearIsometryEquiv.neg ℝ
    else LinearIsometryEquiv.refl ℝ ℝ).toContinuousLinearEquiv


-- @@ L36-38 verbatim
@[simp] theorem coordinateReflection_apply_same (i : Fin n) (x : F) :
    coordinateReflection i x i = -x i := by
  simp [coordinateReflection]


-- @@ L40-42 verbatim
@[simp] theorem coordinateReflection_apply_ne (i j : Fin n) (hji : j ≠ i) (x : F) :
    coordinateReflection i x j = x j := by
  simp [coordinateReflection, hji]


-- @@ L44-49 verbatim
@[simp] theorem coordinateReflection_apply (i j : Fin n) (x : F) :
    coordinateReflection i x j = if j = i then -x j else x j := by
  by_cases h : j = i
  · subst j
    simp
  · simp [h]


-- @@ L51-51 verbatim
namespace FramedLevelSet


-- @@ L53-62 verbatim
theorem fderiv_codomainEquiv (X : FramedLevelSet n)
    (e : F ≃L[ℝ] F) (x : E) :
    fderiv ℝ (X.codomainEquiv e).g x =
      e.toContinuousLinearMap.comp (fderiv ℝ X.g x) := by
  have hX : HasFDerivAt X.g (fderiv ℝ X.g x) x :=
    (X.smooth.differentiable infty_ne_zero x).hasFDerivAt
  have he : HasFDerivAt (e : F → F) e.toContinuousLinearMap (X.g x) :=
    e.toContinuousLinearMap.hasFDerivAt
  change fderiv ℝ ((e : F → F) ∘ X.g) x = _
  exact (he.comp x hX).fderiv


-- @@ L64-75 verbatim
theorem gradVec_coordinateReflection (X : FramedLevelSet n)
    (i j : Fin n) (x : E) :
    gradVec (X.codomainEquiv (coordinateReflection i)).g j x =
      if j = i then -gradVec X.g j x else gradVec X.g j x := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  intro w
  rw [inner_gradVec, X.fderiv_codomainEquiv]
  by_cases h : j = i
  · subst j
    simp [inner_gradVec]
  · simp [h, inner_gradVec]


-- @@ L77-77 verbatim
end FramedLevelSet


-- @@ L79-106 verbatim
/-- Negating one member of an `n`-frame negates its generalized cross
product. -/
theorem crossVec_update_neg (v : Fin n → E) (i : Fin n) :
    crossVec (fun j => if j = i then -v j else v j) = -crossVec v := by
  apply (WithLp.equiv 2 _).injective
  funext k
  change crossDet (fun j => if j = i then -v j else v j)
      (EuclideanSpace.single k 1) =
    -crossDet v (EuclideanSpace.single k 1)
  let A := crossRows v (EuclideanSpace.single k 1)
  have hrows :
      crossRows (fun j => if j = i then -v j else v j)
          (EuclideanSpace.single k 1) =
        A.updateRow i.succ ((-1 : ℝ) • A i.succ) := by
    ext r c
    rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨j, rfl⟩
    · rw [Matrix.updateRow_ne (Fin.succ_ne_zero i).symm]
      rfl
    · by_cases hji : j = i
      · subst j
        simp [A, crossRows]
      · have hs : j.succ ≠ i.succ := fun h => hji (Fin.succ_injective _ h)
        simp [A, crossRows, hji, hs]
  change (crossRows (fun j => if j = i then -v j else v j)
      (EuclideanSpace.single k 1)).det =
    -(crossRows v (EuclideanSpace.single k 1)).det
  rw [hrows, Matrix.det_updateRow_smul]
  simp [A]


-- @@ L108-117 verbatim
theorem FramedLevelSet.kerCross_coordinateReflection
    (X : FramedLevelSet n) (i : Fin n) (x : E) :
    kerCross (X.codomainEquiv (coordinateReflection i)).g x =
      -kerCross X.g x := by
  unfold kerCross
  rw [show (fun j => gradVec (X.codomainEquiv (coordinateReflection i)).g j x) =
      fun j => if j = i then -gradVec X.g j x else gradVec X.g j x by
    funext j
    exact X.gradVec_coordinateReflection i j x]
  exact crossVec_update_neg _ i


-- @@ L119-124 verbatim
theorem FramedLevelSet.tauField_coordinateReflection
    (X : FramedLevelSet n) (i : Fin n) (x : E) :
    tauField (X.codomainEquiv (coordinateReflection i)).g x =
      -tauField X.g x := by
  rw [tauField, X.kerCross_coordinateReflection, norm_neg, tauField]
  exact smul_neg _ _


-- @@ L126-126 verbatim
/-! ## The reversed intrinsic flow -/


-- @@ L128-128 verbatim
namespace TamedField


-- @@ L130-130 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L132-154 verbatim
/-- A one-coordinate reflection reverses the intrinsic unit tangent.  Negating
the old tamed field therefore gives a tamed field for the reflected defining
map. -/
def coordinateReflection (i : Fin n) :
    TamedField (X.codomainEquiv (Submission.coordinateReflection i)) where
  v x := -V.v x
  delta := V.delta
  delta_pos := V.delta_pos
  smooth := V.smooth.neg
  norm_le := fun x => by simpa using V.norm_le x
  eq_tau := by
    intro x hx
    have hx' : x ∈ Metric.cthickening V.delta X.fiber := by
      rwa [← X.fiber_codomainEquiv (Submission.coordinateReflection i)]
    rw [V.eq_tau x hx', X.tauField_coordinateReflection]
  fderiv_zero := by
    intro x
    rw [X.fderiv_codomainEquiv, ContinuousLinearMap.comp_apply, map_neg,
      V.fderiv_zero, neg_zero, map_zero]
  lipschitz := by
    obtain ⟨K, hK⟩ := V.lipschitz
    refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simpa only [dist_neg_neg] using hK.dist_le_mul x y


-- @@ L156-158 verbatim
@[simp] theorem coordinateReflection_v (i : Fin n) (x : E) :
    (V.coordinateReflection i).v x = -V.v x :=
  rfl


-- @@ L160-177 verbatim
/-- The transported flow is the old flow with reversed time. -/
theorem coordinateReflection_flow (i : Fin n) (p : E) (t : ℝ) :
    (V.coordinateReflection i).flow p t = V.flow p (-t) := by
  let W := V.coordinateReflection i
  have htraj : ∀ u : ℝ,
      HasDerivAt (fun z => V.flow p (-z)) (W.v (V.flow p (-u))) u := by
    intro u
    have hneg : HasDerivAt (fun z : ℝ => -z) (-1) u := (hasDerivAt_id u).neg
    have h := (V.hasDerivAt_flow p (-u)).scomp u hneg
    change HasDerivAt (V.flow p ∘ fun z : ℝ => -z)
      (-V.v (V.flow p (-u))) u
    simpa only [neg_one_smul] using h
  have heq : W.flow p = fun u => V.flow p (-u) := by
    apply W.solution_unique (t₀ := 0)
    · exact W.hasDerivAt_flow p
    · exact htraj
    · simp
  exact congrFun heq t


-- @@ L179-189 verbatim
theorem coordinateReflection_orbit (i : Fin n) (p : E) :
    (V.coordinateReflection i).orbit p = V.orbit p := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    rw [V.coordinateReflection_flow]
  · rintro ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    rw [V.coordinateReflection_flow]
    simp only [neg_neg]


-- @@ L191-200 verbatim
theorem periodic_coordinateReflection_iff (i : Fin n) (p : E) (T : ℝ) :
    Function.Periodic ((V.coordinateReflection i).flow p) T ↔
      Function.Periodic (V.flow p) T := by
  constructor
  · intro h
    have hh := h.const_sub 0
    simpa only [zero_sub, V.coordinateReflection_flow, neg_neg] using hh
  · intro h t
    rw [V.coordinateReflection_flow, V.coordinateReflection_flow]
    simpa only [zero_sub] using h.const_sub 0 t


-- @@ L202-216 verbatim
theorem coordinateReflection_fundamentalPeriod (i : Fin n) {p : E}
    (hp : p ∈ X.fiber) :
    (V.coordinateReflection i).fundamentalPeriod
        ((X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mpr hp) =
      V.fundamentalPeriod hp := by
  let W := V.coordinateReflection i
  let hp' : p ∈ (X.codomainEquiv (Submission.coordinateReflection i)).fiber :=
    (X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mpr hp
  apply le_antisymm
  · apply W.fundamentalPeriod_le_period hp' (V.fundamentalPeriod_pos hp)
    exact (V.periodic_coordinateReflection_iff i p _).mpr
      (V.fundamentalPeriod_periodic hp)
  · apply V.fundamentalPeriod_le_period hp (W.fundamentalPeriod_pos hp')
    exact (V.periodic_coordinateReflection_iff i p _).mp
      (W.fundamentalPeriod_periodic hp')


-- @@ L218-218 verbatim
end TamedField


-- @@ L220-220 verbatim
/-! ## The simultaneous tangent/normal sign change lies in `SO` -/


-- @@ L222-225 verbatim
/-- Diagonal coefficient which is negative precisely in the tangent row and
the selected normal row. -/
def doubleSignCoeff (i : Fin n) (j : Fin (n + 1)) : ℝ :=
  if j = 0 ∨ j = i.succ then -1 else 1


-- @@ L227-229 verbatim
def doubleSignMatrix (i : Fin n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (doubleSignCoeff i)


-- @@ L231-233 verbatim
@[simp] theorem doubleSignCoeff_zero (i : Fin n) :
    doubleSignCoeff i 0 = -1 := by
  simp [doubleSignCoeff]


-- @@ L235-237 verbatim
@[simp] theorem doubleSignCoeff_succ_same (i : Fin n) :
    doubleSignCoeff i i.succ = -1 := by
  simp [doubleSignCoeff]


-- @@ L239-249 verbatim
theorem doubleSignCoeff_eq_product (i : Fin n) (j : Fin (n + 1)) :
    doubleSignCoeff i j =
      (if j = 0 then -1 else 1) * (if j = i.succ then -1 else 1) := by
  have hne : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  by_cases h0 : j = 0
  · subst j
    simp [doubleSignCoeff, hne]
  · by_cases hi : j = i.succ
    · subst j
      simp [doubleSignCoeff]
    · simp [doubleSignCoeff, h0, hi]


-- @@ L251-266 verbatim
/-- The two sign changes have determinant `+1`. -/
def doubleSignSO (i : Fin n) : SOGroup (n + 1) := by
  refine ⟨doubleSignMatrix i, ?_⟩
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    rw [doubleSignMatrix, Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    ext r c
    by_cases hrc : r = c
    · subst c
      by_cases h : r = 0 ∨ r = i.succ <;> simp [doubleSignCoeff, h]
    · simp [hrc]
  · rw [doubleSignMatrix, Matrix.det_diagonal]
    simp_rw [doubleSignCoeff_eq_product, Finset.prod_mul_distrib]
    simp


-- @@ L268-271 verbatim
@[simp] theorem doubleSignSO_coe (i : Fin n) :
    ((doubleSignSO i : SOGroup (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = doubleSignMatrix i :=
  rfl


-- @@ L273-273 verbatim
/-! ## Orthonormalizing a continuously moving positive frame -/


-- @@ L275-275 verbatim
section PositiveFrame


-- @@ L277-277 verbatim
variable {m : ℕ}

-- @@ L278-278 verbatim
local notation "Em" => EuclideanSpace ℝ (Fin m)


-- @@ L280-287 verbatim
theorem linearIndependent_rowsMatrix_iff (v : Fin m → Em) :
    LinearIndependent ℝ (rowsMatrix v).row ↔ LinearIndependent ℝ v := by
  have hrow : (rowsMatrix v).row = fun i => WithLp.ofLp (v i) := by
    funext i j
    rfl
  rw [hrow]
  exact (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap.linearIndependent_iff
    (LinearEquiv.ker _)


-- @@ L289-294 verbatim
theorem linearIndependent_of_det_rowsMatrix_ne_zero (v : Fin m → Em)
    (hdet : (rowsMatrix v).det ≠ 0) : LinearIndependent ℝ v := by
  rw [← linearIndependent_rowsMatrix_iff,
    Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact hdet


-- @@ L296-347 verbatim
/-- Gram--Schmidt sends any positively oriented basis to `SO(m)`. -/
def positiveFrameSO (v : Fin m → Em) (hpos : 0 < (rowsMatrix v).det) :
    SOGroup m := by
  let A := rowsMatrix (gramSchmidtNormed ℝ v)
  have hInd : LinearIndependent ℝ v :=
    linearIndependent_of_det_rowsMatrix_ne_zero v (ne_of_gt hpos)
  have horthonormal : Orthonormal ℝ (gramSchmidtNormed ℝ v) :=
    gramSchmidtNormed_orthonormal hInd
  refine ⟨A, ?_⟩
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hinner := orthonormal_iff_ite.mp horthonormal i j
    rw [PiLp.inner_apply] at hinner
    simp only [RCLike.inner_apply, conj_trivial] at hinner
    rw [← hinner]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Matrix.transpose_apply]
      dsimp [A, rowsMatrix]
      rw [mul_comm]
  · have hApos : 0 < A.det := by
      dsimp [A]
      rw [det_rowsMatrix_gramSchmidtNormed]
      apply mul_pos
      · apply Finset.prod_pos
        intro i _
        have hne : gramSchmidt ℝ v i ≠ 0 := gramSchmidt_ne_zero i hInd
        have : 0 < ‖gramSchmidt ℝ v i‖ := norm_pos_iff.mpr hne
        positivity
      · exact hpos
    have hmul : A * Aᵀ = 1 := by
      exact (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mp (by
        rw [Matrix.mem_orthogonalGroup_iff]
        ext i j
        rw [Matrix.mul_apply, Matrix.one_apply]
        have hinner := orthonormal_iff_ite.mp horthonormal i j
        rw [PiLp.inner_apply] at hinner
        simp only [RCLike.inner_apply, conj_trivial] at hinner
        rw [← hinner]
        exact Finset.sum_congr rfl fun k _ => by
          rw [Matrix.transpose_apply]
          dsimp [A, rowsMatrix]
          rw [mul_comm])
    have hdetsq : A.det * A.det = 1 := by
      have h := congrArg Matrix.det hmul
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    rcases mul_self_eq_one_iff.mp hdetsq with h | h
    · exact h
    · rw [h] at hApos
      linarith


-- @@ L349-353 verbatim
@[simp] theorem positiveFrameSO_coe (v : Fin m → Em)
    (hpos : 0 < (rowsMatrix v).det) :
    ((positiveFrameSO v hpos : SOGroup m) : Matrix (Fin m) (Fin m) ℝ) =
      rowsMatrix (gramSchmidtNormed ℝ v) :=
  rfl


-- @@ L355-355 verbatim
end PositiveFrame


-- @@ L357-357 verbatim
/-! ## Row action on full frames -/


-- @@ L359-359 verbatim
section RowAction


-- @@ L361-361 verbatim
variable {m : ℕ}

-- @@ L362-362 verbatim
local notation "Em" => EuclideanSpace ℝ (Fin m)


-- @@ L364-366 verbatim
def frameRowAction (A : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → Em) :
    Fin m → Em :=
  fun i => ∑ j, A i j • v j


-- @@ L368-372 verbatim
@[simp] theorem frameRowAction_diagonal (d : Fin m → ℝ) (v : Fin m → Em)
    (i : Fin m) :
    frameRowAction (Matrix.diagonal d) v i = d i • v i := by
  classical
  simp [frameRowAction, Matrix.diagonal_apply]


-- @@ L374-380 verbatim
theorem rowsMatrix_frameRowAction (A : Matrix (Fin m) (Fin m) ℝ)
    (v : Fin m → Em) :
    rowsMatrix (frameRowAction A v) = A * rowsMatrix v := by
  ext i j
  simp only [rowsMatrix, frameRowAction, Matrix.of_apply, Matrix.mul_apply]
  change (∑ x, A i x • v x) j = ∑ x, A i x * (v x) j
  simp


-- @@ L382-385 verbatim
theorem det_rowsMatrix_frameRowAction (A : Matrix (Fin m) (Fin m) ℝ)
    (v : Fin m → Em) :
    (rowsMatrix (frameRowAction A v)).det = A.det * (rowsMatrix v).det := by
  rw [rowsMatrix_frameRowAction, Matrix.det_mul]


-- @@ L387-392 verbatim
theorem det_rowsMatrix_frameRowAction_pos (A : SOGroup m) (v : Fin m → Em)
    (hpos : 0 < (rowsMatrix v).det) :
    0 < (rowsMatrix (frameRowAction (A : Matrix (Fin m) (Fin m) ℝ) v)).det := by
  rw [det_rowsMatrix_frameRowAction,
    (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).2, one_mul]
  exact hpos


-- @@ L394-399 verbatim
@[simp] theorem frameRowAction_one (v : Fin m → Em) :
    frameRowAction (1 : Matrix (Fin m) (Fin m) ℝ) v = v := by
  classical
  funext i
  rw [← Matrix.diagonal_one]
  simpa using frameRowAction_diagonal (fun _ : Fin m => (1 : ℝ)) v i


-- @@ L401-401 verbatim
end RowAction


-- @@ L403-406 verbatim
/-- A path inside `SO(n+1)` from the identity to the simultaneous sign
change. -/
def doubleSignPath (i : Fin n) : Path (1 : SOGroup (n + 1)) (doubleSignSO i) :=
  PathConnectedSpace.somePath 1 (doubleSignSO i)


-- @@ L408-409 verbatim
@[simp] theorem doubleSignPath_zero (i : Fin n) : doubleSignPath i 0 = 1 :=
  (doubleSignPath i).source


-- @@ L411-413 verbatim
@[simp] theorem doubleSignPath_one (i : Fin n) :
    doubleSignPath i 1 = doubleSignSO i :=
  (doubleSignPath i).target


-- @@ L415-428 verbatim
theorem frameRowAction_doubleSign (X : FramedLevelSet n) (i : Fin n) (x : E) :
    frameRowAction (doubleSignMatrix i) (frameAt X x) =
      frameAt (X.codomainEquiv (coordinateReflection i)) x := by
  funext r
  rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨j, rfl⟩
  · rw [show frameRowAction (doubleSignMatrix i) (frameAt X x) 0 =
        -frameAt X x 0 by
      simp [doubleSignMatrix, doubleSignCoeff]]
    simp [frameAt, X.tauField_coordinateReflection]
  · rw [show frameRowAction (doubleSignMatrix i) (frameAt X x) j.succ =
        (if j = i then -frameAt X x j.succ else frameAt X x j.succ) by
      by_cases h : j = i <;> simp [doubleSignMatrix, doubleSignCoeff, h]]
    simp only [frameAt, Fin.cons_succ]
    exact (X.gradVec_coordinateReflection i j x).symm


-- @@ L430-430 verbatim
/-! ## The frame-loop homotopy for a coordinate reflection -/


-- @@ L432-440 verbatim
/-- The normalized frame along any loop of regular points. -/
def regularFrameLoop (X : FramedLevelSet n) (γ : C(I, E))
    (hreg : ∀ u, γ u ∈ regularSet X.g) : C(I, SOGroup (n + 1)) where
  toFun u := positiveFrameSO (frameAt X (γ u))
    (det_rowsMatrix_frameAt_pos X (hreg u))
  continuous_toFun := by
    apply Continuous.subtype_mk
    simpa only [positiveFrameSO_coe] using
      continuous_frameMatrix_comp X γ.continuous hreg


-- @@ L442-447 verbatim
@[simp] theorem regularFrameLoop_apply_coe (X : FramedLevelSet n) (γ : C(I, E))
    (hreg : ∀ u, γ u ∈ regularSet X.g) (u : I) :
    ((regularFrameLoop X γ hreg u : SOGroup (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
      rowsMatrix (gramSchmidtNormed ℝ (frameAt X (γ u))) :=
  rfl


-- @@ L449-454 verbatim
def coordinateReflectionMovingFrame (X : FramedLevelSet n) (i : Fin n)
    (γ : C(I, E)) (q : I × I) : Fin (n + 1) → E :=
  frameRowAction
    ((doubleSignPath i q.1 : SOGroup (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (frameAt X (γ q.2))


-- @@ L456-461 verbatim
theorem coordinateReflectionMovingFrame_det_pos
    (X : FramedLevelSet n) (i : Fin n) (γ : C(I, E))
    (hreg : ∀ u, γ u ∈ regularSet X.g) (q : I × I) :
    0 < (rowsMatrix (coordinateReflectionMovingFrame X i γ q)).det :=
  det_rowsMatrix_frameRowAction_pos (doubleSignPath i q.1)
    (frameAt X (γ q.2)) (det_rowsMatrix_frameAt_pos X (hreg q.2))


-- @@ L463-478 verbatim
theorem continuous_coordinateReflectionMovingFrame
    (X : FramedLevelSet n) (i : Fin n) (γ : C(I, E))
    (hreg : ∀ u, γ u ∈ regularSet X.g) (r : Fin (n + 1)) :
    Continuous fun q : I × I => coordinateReflectionMovingFrame X i γ q r := by
  unfold coordinateReflectionMovingFrame frameRowAction
  apply continuous_finsetSum
  intro j _
  have hmatrix : Continuous fun q : I × I =>
      (((doubleSignPath i q.1 : SOGroup (n + 1)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) r j) :=
    (continuous_apply j |>.comp (continuous_apply r |>.comp
      (continuous_subtype_val.comp ((doubleSignPath i).continuous.comp continuous_fst))))
  have hframe : Continuous fun q : I × I => frameAt X (γ q.2) j :=
    continuous_frameAt_comp X (γ.continuous.comp continuous_snd)
      (fun q => hreg q.2) j
  exact hmatrix.smul hframe


-- @@ L480-518 verbatim
/-- Changing the sign of one defining equation gives a free homotopy of the
forward-parametrized full frame loops. -/
def coordinateReflectionFrameHomotopy
    (X : FramedLevelSet n) (i : Fin n) (γ : C(I, E))
    (hγ : ∀ u, γ u ∈ X.fiber) :
    ContinuousMap.Homotopy
      (regularFrameLoop X γ (fun u => X.fiber_subset_regularSet (hγ u)))
      (regularFrameLoop (X.codomainEquiv (coordinateReflection i)) γ
        (fun u => (X.codomainEquiv (coordinateReflection i)).fiber_subset_regularSet
          ((X.mem_fiber_codomainEquiv (coordinateReflection i)).mpr (hγ u)))) where
  toFun q := positiveFrameSO (coordinateReflectionMovingFrame X i γ q)
    (coordinateReflectionMovingFrame_det_pos X i γ
      (fun u => X.fiber_subset_regularSet (hγ u)) q)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro r c
    have hInd : ∀ q : I × I,
        LinearIndependent ℝ (coordinateReflectionMovingFrame X i γ q) := fun q =>
      linearIndependent_of_det_rowsMatrix_ne_zero _
        (ne_of_gt (coordinateReflectionMovingFrame_det_pos X i γ
          (fun u => X.fiber_subset_regularSet (hγ u)) q))
    have hgs := continuous_gramSchmidtNormed_family
      (A := coordinateReflectionMovingFrame X i γ)
      (continuous_coordinateReflectionMovingFrame X i γ
        (fun u => X.fiber_subset_regularSet (hγ u))) hInd r
    exact (EuclideanSpace.proj c).continuous.comp hgs
  map_zero_left := by
    intro u
    apply Subtype.ext
    simp only [positiveFrameSO_coe, coordinateReflectionMovingFrame,
      doubleSignPath_zero, OneMemClass.coe_one, frameRowAction_one,
      regularFrameLoop_apply_coe]
  map_one_left := by
    intro u
    apply Subtype.ext
    simp only [positiveFrameSO_coe, coordinateReflectionMovingFrame,
      doubleSignPath_one, doubleSignSO_coe, frameRowAction_doubleSign,
      regularFrameLoop_apply_coe]


-- @@ L520-520 verbatim
/-! ## Fundamental frame classes -/


-- @@ L522-522 verbatim
namespace TamedField


-- @@ L524-524 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L526-530 verbatim
/-- The once-around unit-interval parametrization of the intrinsic orbit. -/
def fundamentalCurve {p : E} (hp : p ∈ X.fiber) : C(I, E) where
  toFun u := V.flow p ((u : ℝ) * V.fundamentalPeriod hp)
  continuous_toFun := (V.continuous_flow p).comp
    (continuous_subtype_val.mul continuous_const)


-- @@ L532-534 verbatim
theorem fundamentalCurve_mem_fiber {p : E} (hp : p ∈ X.fiber) (u : I) :
    V.fundamentalCurve hp u ∈ X.fiber :=
  V.flow_mem_fiber hp _


-- @@ L536-540 verbatim
theorem fundamentalCurve_closed {p : E} (hp : p ∈ X.fiber) :
    V.fundamentalCurve hp 0 = V.fundamentalCurve hp 1 := by
  change V.flow p (0 * V.fundamentalPeriod hp) =
    V.flow p (1 * V.fundamentalPeriod hp)
  simpa using (V.fundamentalPeriod_periodic hp 0).symm


-- @@ L542-549 verbatim
theorem fundamentalFrameLoop_eq_regularFrameLoop {p : E} (hp : p ∈ X.fiber) :
    V.fundamentalFrameLoop hp =
      regularFrameLoop X (V.fundamentalCurve hp)
        (fun u => X.fiber_subset_regularSet (V.fundamentalCurve_mem_fiber hp u)) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rfl


-- @@ L551-551 verbatim
variable (i : Fin n)


-- @@ L553-561 verbatim
/-- The reflected presentation's frame, traversed in the old forward
orientation. -/
def reflectedForwardFrameLoop {p : E} (hp : p ∈ X.fiber) :
    C(I, SOGroup (n + 1)) :=
  regularFrameLoop (X.codomainEquiv (Submission.coordinateReflection i))
    (V.fundamentalCurve hp)
    (fun u => (X.codomainEquiv (Submission.coordinateReflection i)).fiber_subset_regularSet
      ((X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mpr
        (V.fundamentalCurve_mem_fiber hp u)))


-- @@ L563-567 verbatim
theorem reflectedForwardFrameLoop_closed {p : E} (hp : p ∈ X.fiber) :
    V.reflectedForwardFrameLoop i hp 0 = V.reflectedForwardFrameLoop i hp 1 := by
  apply Subtype.ext
  simp only [reflectedForwardFrameLoop, regularFrameLoop_apply_coe]
  rw [V.fundamentalCurve_closed hp]


-- @@ L569-602 verbatim
theorem fundamentalFrameLoop_reflection_freeHomotopy_class {p : E}
    (hp : p ∈ X.fiber) :
    loopClassZ2 (V.fundamentalFrameLoop hp) (V.fundamentalFrameLoop_closed hp) =
      loopClassZ2 (V.reflectedForwardFrameLoop i hp)
        (V.reflectedForwardFrameLoop_closed i hp) := by
  let H := coordinateReflectionFrameHomotopy X i (V.fundamentalCurve hp)
    (V.fundamentalCurve_mem_fiber hp)
  let R₀ := regularFrameLoop X (V.fundamentalCurve hp)
    (fun u => X.fiber_subset_regularSet (V.fundamentalCurve_mem_fiber hp u))
  let R₁ := V.reflectedForwardFrameLoop i hp
  have hR₀ : R₀ 0 = R₀ 1 := by
    apply Subtype.ext
    simp only [R₀, regularFrameLoop_apply_coe]
    rw [V.fundamentalCurve_closed hp]
  have hR₁ : R₁ 0 = R₁ 1 := V.reflectedForwardFrameLoop_closed i hp
  have hH : ∀ s, H (s, 0) = H (s, 1) := by
    intro s
    apply Subtype.ext
    change rowsMatrix (gramSchmidtNormed ℝ
        (coordinateReflectionMovingFrame X i (V.fundamentalCurve hp) (s, 0))) =
      rowsMatrix (gramSchmidtNormed ℝ
        (coordinateReflectionMovingFrame X i (V.fundamentalCurve hp) (s, 1)))
    congr 2
    unfold coordinateReflectionMovingFrame
    rw [V.fundamentalCurve_closed hp]
  calc
    loopClassZ2 (V.fundamentalFrameLoop hp) (V.fundamentalFrameLoop_closed hp) =
        loopClassZ2 R₀ hR₀ :=
      loopClassZ2_congr_fun _ _ (V.fundamentalFrameLoop_eq_regularFrameLoop hp)
    _ = loopClassZ2 R₁ hR₁ := by
      exact loopClassZ2_congr hR₀ hR₁ H hH
    _ = loopClassZ2 (V.reflectedForwardFrameLoop i hp)
          (V.reflectedForwardFrameLoop_closed i hp) := by
      rfl


-- @@ L604-634 verbatim
/-- The actual transported field traverses the reflected forward frame loop in
the opposite direction. -/
theorem coordinateReflection_fundamentalFrameLoop_eq_reverse {p : E}
    (hp : p ∈ X.fiber) :
    (V.coordinateReflection i).fundamentalFrameLoop
        ((X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mpr hp) =
      reverseLoop (V.reflectedForwardFrameLoop i hp) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop (X.codomainEquiv (Submission.coordinateReflection i))
      ((V.coordinateReflection i).flow p)
        ((u : ℝ) * (V.coordinateReflection i).fundamentalPeriod
          ((X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mpr hp)) = _
  rw [V.coordinateReflection_fundamentalPeriod i hp]
  unfold frameLoop
  rw [V.coordinateReflection_flow]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (X.codomainEquiv (Submission.coordinateReflection i))
        (V.flow p (-((u : ℝ) * V.fundamentalPeriod hp))))) =
    rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (X.codomainEquiv (Submission.coordinateReflection i))
        (V.flow p (((unitInterval.symm u : I) : ℝ) * V.fundamentalPeriod hp))))
  have hper := V.fundamentalPeriod_periodic hp
    (-((u : ℝ) * V.fundamentalPeriod hp))
  have harg :
      -((u : ℝ) * V.fundamentalPeriod hp) + V.fundamentalPeriod hp =
        ((unitInterval.symm u : I) : ℝ) * V.fundamentalPeriod hp := by
    simp only [unitInterval.coe_symm_eq]
    ring
  rw [← harg, hper]


-- @@ L636-655 verbatim
theorem coordinateReflection_fundamentalFrameClass {p : E}
    (hp : p ∈ X.fiber) :
    (V.coordinateReflection i).fundamentalFrameClass
        ((X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mpr hp) =
      V.fundamentalFrameClass hp := by
  unfold fundamentalFrameClass
  calc
    loopClassZ2 ((V.coordinateReflection i).fundamentalFrameLoop
        ((X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mpr hp)) _ =
        loopClassZ2 (reverseLoop (V.reflectedForwardFrameLoop i hp))
          (reverseLoop_closed (V.reflectedForwardFrameLoop_closed i hp)) :=
      loopClassZ2_congr_fun _ _
        (V.coordinateReflection_fundamentalFrameLoop_eq_reverse i hp)
    _ =
        loopClassZ2 (V.reflectedForwardFrameLoop i hp)
          (V.reflectedForwardFrameLoop_closed i hp) :=
      loopClassZ2_reverse _ _
    _ = loopClassZ2 (V.fundamentalFrameLoop hp)
          (V.fundamentalFrameLoop_closed hp) :=
      (V.fundamentalFrameLoop_reflection_freeHomotopy_class i hp).symm


-- @@ L657-657 verbatim
/-! ## Component and delta transport -/


-- @@ L659-676 verbatim
/-- Reversing the intrinsic flow does not change the canonical finite set of
orbit subsets. -/
theorem coordinateReflection_orbitFinset :
    (V.coordinateReflection i).orbitFinset = V.orbitFinset := by
  apply Finset.ext
  intro O
  simp only [(V.coordinateReflection i).mem_orbitFinset,
    V.mem_orbitFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p ∈ X.fiber :=
      (X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mp hp
    exact ⟨p, hp', V.coordinateReflection_orbit i p⟩
  · rintro ⟨p, hp, rfl⟩
    have hp' : p ∈ (X.codomainEquiv
        (Submission.coordinateReflection i)).fiber :=
      (X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mpr hp
    exact ⟨p, hp', (V.coordinateReflection_orbit i p).symm⟩


-- @@ L678-689 verbatim
/-- The canonical identification of orbit components under a coordinate
reflection.  Its underlying orbit set is literally unchanged. -/
def coordinateReflectionOrbitEquiv :
    V.OrbitIndex ≃ (V.coordinateReflection i).OrbitIndex where
  toFun O := ⟨O.1, by
    rw [V.coordinateReflection_orbitFinset i]
    exact O.2⟩
  invFun O := ⟨O.1, by
    rw [← V.coordinateReflection_orbitFinset i]
    exact O.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L691-694 verbatim
@[simp] theorem coordinateReflectionOrbitEquiv_coe (O : V.OrbitIndex) :
    ((V.coordinateReflectionOrbitEquiv i O :
      (V.coordinateReflection i).OrbitIndex) : Set E) = O :=
  rfl


-- @@ L696-724 verbatim
/-- Componentwise frame-ledger preservation.  This is the canonical form of
ledger invariance, independent of the arbitrary enumeration used to display a
finite ledger as a list. -/
theorem coordinateReflection_orbitFrameClass (O : V.OrbitIndex) :
    V.orbitFrameClass O =
      (V.coordinateReflection i).orbitFrameClass
        (V.coordinateReflectionOrbitEquiv i O) := by
  let W := V.coordinateReflection i
  let e := V.coordinateReflectionOrbitEquiv i
  let p : E := V.orbitPoint O
  let q : E := W.orbitPoint (e O)
  have hp : p ∈ X.fiber := V.orbitPoint_mem_fiber O
  have hqW : q ∈ (X.codomainEquiv
      (Submission.coordinateReflection i)).fiber :=
    W.orbitPoint_mem_fiber (e O)
  have hq : q ∈ X.fiber :=
    (X.mem_fiber_codomainEquiv (Submission.coordinateReflection i)).mp hqW
  have hsets : (O : Set E) = ((e O : W.OrbitIndex) : Set E) := rfl
  have hqOrbit : q ∈ V.orbit p := by
    have hOp : (O : Set E) = V.orbit p := V.orbitPoint_orbit O
    have hOq : ((e O : W.OrbitIndex) : Set E) = W.orbit q :=
      W.orbitPoint_orbit (e O)
    rw [← hOp, hsets, hOq, V.coordinateReflection_orbit i q]
    exact V.mem_orbit_self q
  have hbase : V.fundamentalFrameClass hq =
      V.fundamentalFrameClass hp :=
    V.fundamentalFrameClass_eq_of_mem_orbit hp hqOrbit
  change V.fundamentalFrameClass hp = W.fundamentalFrameClass hqW
  rw [V.coordinateReflection_fundamentalFrameClass i hq, hbase]


-- @@ L726-731 verbatim
theorem coordinateReflection_orbitContribution (O : V.OrbitIndex) :
    V.orbitContribution O =
      (V.coordinateReflection i).orbitContribution
        (V.coordinateReflectionOrbitEquiv i O) := by
  unfold orbitContribution
  rw [V.coordinateReflection_orbitFrameClass i O]


-- @@ L733-737 verbatim
/-- Coordinate reflection packaged for the finite-sum transport API. -/
def coordinateReflectionDeltaTransport :
    V.DeltaTransport (V.coordinateReflection i) where
  orbitEquiv := V.coordinateReflectionOrbitEquiv i
  contribution_eq := V.coordinateReflection_orbitContribution i


-- @@ L739-739 verbatim
end TamedField


-- @@ L741-741 verbatim
namespace FiberSign


-- @@ L743-743 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L745-759 verbatim
/-- Positive framed delta is invariant under a one-coordinate reflection. -/
theorem positiveFramedDelta_coordinateReflection (V : TamedField X)
    (i : Fin n) :
    S.positiveFramedDelta V =
      (S.codomainEquiv (Submission.coordinateReflection i)).positiveFramedDelta
        (V.coordinateReflection i) := by
  let W := V.coordinateReflection i
  let T := V.coordinateReflectionDeltaTransport i
  apply V.deltaOn_eq_of_transport T
  intro O
  change (O : Set E) ⊆ S.positivePart ↔
    ((T.orbitEquiv O : W.OrbitIndex) : Set E) ⊆
      (S.codomainEquiv (Submission.coordinateReflection i)).positivePart
  rw [S.positivePart_codomainEquiv]
  rfl


-- @@ L761-777 verbatim
/-- The canonical positive delta does not depend on reflecting one defining
equation. -/
theorem positiveDelta_coordinateReflection (i : Fin n) :
    (S.codomainEquiv (Submission.coordinateReflection i)).positiveDelta =
      S.positiveDelta := by
  let V := X.exists_tamedField.some
  let W := V.coordinateReflection i
  calc
    (S.codomainEquiv
        (Submission.coordinateReflection i)).positiveDelta =
        (S.codomainEquiv
          (Submission.coordinateReflection i)).positiveFramedDelta W :=
      (S.codomainEquiv
        (Submission.coordinateReflection i)).positiveDelta_eq W
    _ = S.positiveFramedDelta V :=
      (S.positiveFramedDelta_coordinateReflection V i).symm
    _ = S.positiveDelta := (S.positiveDelta_eq V).symm


-- @@ L779-783 verbatim
/-- Pointwise negation commutes with a change of codomain coordinates. -/
theorem codomainEquiv_neg (e : F ≃L[ℝ] F) :
    (S.codomainEquiv e).neg = S.neg.codomainEquiv e := by
  apply FiberSign.eq_of_toFun_eq
  rfl


-- @@ L785-792 verbatim
/-- The canonical negative delta has the same coordinate-reflection
invariance. -/
theorem negativeDelta_coordinateReflection (i : Fin n) :
    (S.codomainEquiv (Submission.coordinateReflection i)).negativeDelta =
      S.negativeDelta := by
  unfold negativeDelta
  rw [S.codomainEquiv_neg,
    S.neg.positiveDelta_coordinateReflection]


-- @@ L794-794 verbatim
end FiberSign


-- @@ L796-798 verbatim
def isometryMatrix (q : F ≃ₗᵢ[ℝ] F) : Matrix (Fin n) (Fin n) ℝ :=
  q.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis


-- @@ L800-807 verbatim
theorem isometryMatrix_apply (q : F ≃ₗᵢ[ℝ] F) (x : F) (j : Fin n) :
    q x j = ∑ k, isometryMatrix q j k * x k := by
  have h := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis q.toLinearEquiv.toLinearMap x
  have hj := congrFun h j
  simpa [isometryMatrix, Matrix.mulVec, dotProduct,
    EuclideanSpace.basisFun_repr] using hj.symm


-- @@ L809-812 verbatim
def tangentNormalBlock (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons a (fun _ => 0))
    (fun i => Fin.cons 0 (A i)))


-- @@ L814-816 verbatim
@[simp] theorem tangentNormalBlock_zero_zero (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    tangentNormalBlock a A 0 0 = a := rfl


-- @@ L818-820 verbatim
@[simp] theorem tangentNormalBlock_zero_succ (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    tangentNormalBlock a A 0 j.succ = 0 := rfl


-- @@ L822-824 verbatim
@[simp] theorem tangentNormalBlock_succ_zero (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    tangentNormalBlock a A i.succ 0 = 0 := rfl


-- @@ L826-828 verbatim
@[simp] theorem tangentNormalBlock_succ_succ (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    tangentNormalBlock a A i.succ j.succ = A i j := rfl


-- @@ L830-846 verbatim
theorem det_tangentNormalBlock (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (tangentNormalBlock a A).det = a * A.det := by
  have hsub : (tangentNormalBlock a A).submatrix Fin.succ Fin.succ = A := by
    ext i j
    rfl
  have hsucc : (0 : Fin (n + 1)).succAbove = Fin.succ := by
    funext j
    simp
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, tangentNormalBlock_zero_zero,
      one_mul, hsucc, hsub]
  · intro j _ hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact (hj rfl).elim
    · simp [tangentNormalBlock]
  · simp


-- @@ L848-853 verbatim
theorem isometryMatrix_mul_transpose (q : F ≃ₗᵢ[ℝ] F) :
    isometryMatrix q * (isometryMatrix q)ᵀ = 1 := by
  have h := q.toMatrix_mem_unitaryGroup
    (EuclideanSpace.basisFun (Fin n) ℝ)
    (EuclideanSpace.basisFun (Fin n) ℝ)
  exact (Matrix.mem_unitaryGroup_iff.mp h)


-- @@ L855-877 verbatim
def orientationBlockSO (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    SOGroup (n + 1) := by
  refine ⟨tangentNormalBlock ε (isometryMatrix q), ?_⟩
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext r c
    rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨r, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨c, rfl⟩
    · rcases hε with rfl | rfl <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, tangentNormalBlock]
    · rw [Matrix.one_apply]
      simp [Matrix.mul_apply, Fin.sum_univ_succ, tangentNormalBlock,
        (Fin.succ_ne_zero c).symm]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ,
        tangentNormalBlock]
    · have horth := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M r c)
          (isometryMatrix_mul_transpose q)
      simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
        tangentNormalBlock] using horth
  · rw [det_tangentNormalBlock, hdet]
    rcases hε with rfl | rfl <;> norm_num


-- @@ L879-883 verbatim
@[simp] theorem orientationBlockSO_coe (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    ((orientationBlockSO q ε hε hdet : SOGroup (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
      tangentNormalBlock ε (isometryMatrix q) := rfl


-- @@ L885-885 verbatim
namespace FramedLevelSet


-- @@ L887-900 verbatim
theorem gradVec_codomainIsometry (X : FramedLevelSet n)
    (q : F ≃ₗᵢ[ℝ] F) (j : Fin n) (x : E) :
    gradVec (X.codomainEquiv q.toContinuousLinearEquiv).g j x =
      ∑ k, isometryMatrix q j k • gradVec X.g k x := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  intro w
  rw [inner_gradVec, X.fderiv_codomainEquiv,
    ContinuousLinearMap.comp_apply]
  change q (fderiv ℝ X.g x
    ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis w)) j = _
  rw [isometryMatrix_apply]
  rw [sum_inner]
  simp_rw [real_inner_smul_left, inner_gradVec]


-- @@ L902-902 verbatim
end FramedLevelSet


-- @@ L904-906 verbatim
def normalRowAction (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → E) :
    Fin n → E :=
  fun i => ∑ j, A i j • v j


-- @@ L908-916 verbatim
theorem crossRows_frameRowAction_normals (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → E) (w : E) :
    crossRows (normalRowAction A v) w =
      tangentNormalBlock 1 A * crossRows v w := by
  ext r c
  rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨r, rfl⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, tangentNormalBlock, crossRows]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, tangentNormalBlock,
      crossRows, normalRowAction]


-- @@ L918-923 verbatim
theorem crossDet_frameRowAction_normals (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → E) (w : E) :
    crossDet (normalRowAction A v) w = A.det * crossDet v w := by
  unfold crossDet
  rw [crossRows_frameRowAction_normals, Matrix.det_mul,
    det_tangentNormalBlock, one_mul]


-- @@ L925-932 verbatim
theorem crossVec_frameRowAction_normals (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → E) :
    crossVec (normalRowAction A v) = A.det • crossVec v := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  intro w
  rw [inner_crossVec, crossDet_frameRowAction_normals, real_inner_smul_left,
    inner_crossVec]


-- @@ L934-944 verbatim
theorem FramedLevelSet.kerCross_codomainIsometry
    (X : FramedLevelSet n) (q : F ≃ₗᵢ[ℝ] F) (x : E) :
    kerCross (X.codomainEquiv q.toContinuousLinearEquiv).g x =
      (isometryMatrix q).det • kerCross X.g x := by
  unfold kerCross
  rw [show (fun j => gradVec (X.codomainEquiv
      q.toContinuousLinearEquiv).g j x) =
      normalRowAction (isometryMatrix q) (fun j => gradVec X.g j x) by
    funext j
    exact X.gradVec_codomainIsometry q j x]
  exact crossVec_frameRowAction_normals _ _


-- @@ L946-954 verbatim
theorem FramedLevelSet.tauField_codomainIsometry
    (X : FramedLevelSet n) (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) (x : E) :
    tauField (X.codomainEquiv q.toContinuousLinearEquiv).g x =
      ε • tauField X.g x := by
  rw [tauField, X.kerCross_codomainIsometry, hdet, tauField]
  rcases hε with rfl | rfl
  · simp
  · simp


-- @@ L956-956 verbatim
namespace TamedField


-- @@ L958-958 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L960-982 verbatim
def codomainIsometry (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    TamedField (X.codomainEquiv q.toContinuousLinearEquiv) where
  v x := ε • V.v x
  delta := V.delta
  delta_pos := V.delta_pos
  smooth := V.smooth.const_smul ε
  norm_le := by
    intro x
    rcases hε with rfl | rfl <;> simpa using V.norm_le x
  eq_tau := by
    intro x hx
    have hx' : x ∈ Metric.cthickening V.delta X.fiber := by
      rwa [← X.fiber_codomainEquiv q.toContinuousLinearEquiv]
    rw [V.eq_tau x hx', X.tauField_codomainIsometry q ε hε hdet]
  fderiv_zero := by
    intro x
    rw [X.fderiv_codomainEquiv, ContinuousLinearMap.comp_apply, map_smul,
      V.fderiv_zero, smul_zero, map_zero]
  lipschitz := by
    obtain ⟨K, hK⟩ := V.lipschitz
    refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rcases hε with rfl | rfl <;> simpa using hK.dist_le_mul x y


-- @@ L984-987 verbatim
@[simp] theorem codomainIsometry_v (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (x : E) :
    (V.codomainIsometry q ε hε hdet).v x = ε • V.v x := rfl


-- @@ L989-1008 verbatim
theorem codomainIsometry_flow (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (p : E) (t : ℝ) :
    (V.codomainIsometry q ε hε hdet).flow p t = V.flow p (ε * t) := by
  let W := V.codomainIsometry q ε hε hdet
  have htraj : ∀ u : ℝ,
      HasDerivAt (fun z => V.flow p (ε * z)) (W.v (V.flow p (ε * u))) u := by
    intro u
    have hmul : HasDerivAt (fun z : ℝ => ε * z) ε u :=
      by simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul ε
    have h := (V.hasDerivAt_flow p (ε * u)).scomp u hmul
    change HasDerivAt (V.flow p ∘ fun z : ℝ => ε * z)
      (ε • V.v (V.flow p (ε * u))) u
    simpa only [smul_eq_mul] using h
  have heq : W.flow p = fun u => V.flow p (ε * u) := by
    apply W.solution_unique (t₀ := 0)
    · exact W.hasDerivAt_flow p
    · exact htraj
    · simp
  exact congrFun heq t


-- @@ L1010-1021 verbatim
theorem codomainIsometry_orbit (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (p : E) :
    (V.codomainIsometry q ε hε hdet).orbit p = V.orbit p := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨ε * t, (V.codomainIsometry_flow q ε hε hdet p t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨ε * t, ?_⟩
    rw [V.codomainIsometry_flow]
    rcases hε with rfl | rfl <;> simp


-- @@ L1023-1050 verbatim
theorem periodic_codomainIsometry_iff (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (p : E) (T : ℝ) :
    Function.Periodic ((V.codomainIsometry q ε hε hdet).flow p) T ↔
      Function.Periodic (V.flow p) T := by
  constructor
  · intro h
    rcases hε with rfl | rfl
    · intro t
      have hf (s : ℝ) :
          (V.codomainIsometry q 1 (Or.inl rfl) hdet).flow p s = V.flow p s := by
        simpa using V.codomainIsometry_flow q 1 (Or.inl rfl) hdet p s
      rw [← hf (t + T), ← hf t]
      exact h t
    · have hh := h.const_sub 0
      simpa only [zero_sub, V.codomainIsometry_flow, neg_mul, one_mul,
        neg_neg] using hh
  · intro h
    rcases hε with rfl | rfl
    · intro t
      have hf (s : ℝ) :
          (V.codomainIsometry q 1 (Or.inl rfl) hdet).flow p s = V.flow p s := by
        simpa using V.codomainIsometry_flow q 1 (Or.inl rfl) hdet p s
      rw [hf (t + T), hf t]
      exact h t
    · intro t
      rw [V.codomainIsometry_flow, V.codomainIsometry_flow]
      simpa only [neg_mul, one_mul, zero_sub] using h.const_sub 0 t


-- @@ L1052-1068 verbatim
theorem codomainIsometry_fundamentalPeriod
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    {p : E} (hp : p ∈ X.fiber) :
    (V.codomainIsometry q ε hε hdet).fundamentalPeriod
        ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp) =
      V.fundamentalPeriod hp := by
  let W := V.codomainIsometry q ε hε hdet
  let hp' : p ∈ (X.codomainEquiv q.toContinuousLinearEquiv).fiber :=
    (X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp
  apply le_antisymm
  · apply W.fundamentalPeriod_le_period hp' (V.fundamentalPeriod_pos hp)
    exact (V.periodic_codomainIsometry_iff q ε hε hdet p _).mpr
      (V.fundamentalPeriod_periodic hp)
  · apply V.fundamentalPeriod_le_period hp (W.fundamentalPeriod_pos hp')
    exact (V.periodic_codomainIsometry_iff q ε hε hdet p _).mp
      (W.fundamentalPeriod_periodic hp')


-- @@ L1070-1070 verbatim
end TamedField


-- @@ L1072-1084 verbatim
theorem frameRowAction_orientationBlock (X : FramedLevelSet n)
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (x : E) :
    frameRowAction (tangentNormalBlock ε (isometryMatrix q)) (frameAt X x) =
      frameAt (X.codomainEquiv q.toContinuousLinearEquiv) x := by
  funext r
  rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨r, rfl⟩
  · simp [frameRowAction, Fin.sum_univ_succ,
      tangentNormalBlock, frameAt, X.tauField_codomainIsometry q ε hε hdet]
  · simp only [frameAt, Fin.cons_succ, X.gradVec_codomainIsometry]
    simp [frameRowAction, Fin.sum_univ_succ,
      tangentNormalBlock]


-- @@ L1086-1089 verbatim
def orientationBlockPath (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    Path (1 : SOGroup (n + 1)) (orientationBlockSO q ε hε hdet) :=
  PathConnectedSpace.somePath 1 (orientationBlockSO q ε hε hdet)


-- @@ L1091-1094 verbatim
@[simp] theorem orientationBlockPath_zero (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    orientationBlockPath q ε hε hdet 0 = 1 :=
  (orientationBlockPath q ε hε hdet).source


-- @@ L1096-1099 verbatim
@[simp] theorem orientationBlockPath_one (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    orientationBlockPath q ε hε hdet 1 = orientationBlockSO q ε hε hdet :=
  (orientationBlockPath q ε hε hdet).target


-- @@ L1101-1108 verbatim
def codomainIsometryMovingFrame (X : FramedLevelSet n)
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (γ : C(I, E)) (p : I × I) : Fin (n + 1) → E :=
  frameRowAction
    ((orientationBlockPath q ε hε hdet p.1 : SOGroup (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (frameAt X (γ p.2))


-- @@ L1110-1117 verbatim
theorem codomainIsometryMovingFrame_det_pos (X : FramedLevelSet n)
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (γ : C(I, E)) (hreg : ∀ u, γ u ∈ regularSet X.g) (p : I × I) :
    0 < (rowsMatrix
      (codomainIsometryMovingFrame X q ε hε hdet γ p)).det :=
  det_rowsMatrix_frameRowAction_pos (orientationBlockPath q ε hε hdet p.1)
    (frameAt X (γ p.2)) (det_rowsMatrix_frameAt_pos X (hreg p.2))


-- @@ L1119-1137 verbatim
theorem continuous_codomainIsometryMovingFrame (X : FramedLevelSet n)
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (γ : C(I, E)) (hreg : ∀ u, γ u ∈ regularSet X.g)
    (r : Fin (n + 1)) :
    Continuous fun p : I × I => codomainIsometryMovingFrame X q ε hε hdet γ p r := by
  unfold codomainIsometryMovingFrame frameRowAction
  apply continuous_finsetSum
  intro j _
  have hmatrix : Continuous fun p : I × I =>
      (((orientationBlockPath q ε hε hdet p.1 : SOGroup (n + 1)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) r j) :=
    (continuous_apply j |>.comp (continuous_apply r |>.comp
      (continuous_subtype_val.comp
        ((orientationBlockPath q ε hε hdet).continuous.comp continuous_fst))))
  have hframe : Continuous fun p : I × I => frameAt X (γ p.2) j :=
    continuous_frameAt_comp X (γ.continuous.comp continuous_snd)
      (fun p => hreg p.2) j
  exact hmatrix.smul hframe


-- @@ L1139-1177 verbatim
def codomainIsometryFrameHomotopy (X : FramedLevelSet n)
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (γ : C(I, E)) (hγ : ∀ u, γ u ∈ X.fiber) :
    ContinuousMap.Homotopy
      (regularFrameLoop X γ (fun u => X.fiber_subset_regularSet (hγ u)))
      (regularFrameLoop (X.codomainEquiv q.toContinuousLinearEquiv) γ
        (fun u => (X.codomainEquiv q.toContinuousLinearEquiv).fiber_subset_regularSet
          ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr (hγ u)))) where
  toFun p := positiveFrameSO (codomainIsometryMovingFrame X q ε hε hdet γ p)
    (codomainIsometryMovingFrame_det_pos X q ε hε hdet γ
      (fun u => X.fiber_subset_regularSet (hγ u)) p)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro r c
    have hInd : ∀ p : I × I,
        LinearIndependent ℝ (codomainIsometryMovingFrame X q ε hε hdet γ p) :=
      fun p => linearIndependent_of_det_rowsMatrix_ne_zero _
        (ne_of_gt (codomainIsometryMovingFrame_det_pos X q ε hε hdet γ
          (fun u => X.fiber_subset_regularSet (hγ u)) p))
    have hgs := continuous_gramSchmidtNormed_family
      (A := codomainIsometryMovingFrame X q ε hε hdet γ)
      (continuous_codomainIsometryMovingFrame X q ε hε hdet γ
        (fun u => X.fiber_subset_regularSet (hγ u))) hInd r
    exact (EuclideanSpace.proj c).continuous.comp hgs
  map_zero_left := by
    intro u
    apply Subtype.ext
    simp only [positiveFrameSO_coe, codomainIsometryMovingFrame,
      orientationBlockPath_zero, OneMemClass.coe_one, frameRowAction_one,
      regularFrameLoop_apply_coe]
  map_one_left := by
    intro u
    apply Subtype.ext
    simp only [positiveFrameSO_coe, codomainIsometryMovingFrame,
      orientationBlockPath_one, orientationBlockSO_coe,
      regularFrameLoop_apply_coe]
    rw [frameRowAction_orientationBlock X q ε hε hdet (γ u)]


-- @@ L1179-1179 verbatim
namespace TamedField


-- @@ L1181-1181 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L1183-1189 verbatim
def isometryForwardFrameLoop (q : F ≃ₗᵢ[ℝ] F) {p : E}
    (hp : p ∈ X.fiber) : C(I, SOGroup (n + 1)) :=
  regularFrameLoop (X.codomainEquiv q.toContinuousLinearEquiv)
    (V.fundamentalCurve hp)
    (fun u => (X.codomainEquiv q.toContinuousLinearEquiv).fiber_subset_regularSet
      ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr
        (V.fundamentalCurve_mem_fiber hp u)))


-- @@ L1191-1196 verbatim
theorem isometryForwardFrameLoop_closed (q : F ≃ₗᵢ[ℝ] F) {p : E}
    (hp : p ∈ X.fiber) :
    V.isometryForwardFrameLoop q hp 0 = V.isometryForwardFrameLoop q hp 1 := by
  apply Subtype.ext
  simp only [isometryForwardFrameLoop, regularFrameLoop_apply_coe]
  rw [V.fundamentalCurve_closed hp]


-- @@ L1198-1234 verbatim
theorem fundamentalFrameLoop_isometry_freeHomotopy_class
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    {p : E} (hp : p ∈ X.fiber) :
    loopClassZ2 (V.fundamentalFrameLoop hp) (V.fundamentalFrameLoop_closed hp) =
      loopClassZ2 (V.isometryForwardFrameLoop q hp)
        (V.isometryForwardFrameLoop_closed q hp) := by
  let H := codomainIsometryFrameHomotopy X q ε hε hdet
    (V.fundamentalCurve hp) (V.fundamentalCurve_mem_fiber hp)
  let R₀ := regularFrameLoop X (V.fundamentalCurve hp)
    (fun u => X.fiber_subset_regularSet (V.fundamentalCurve_mem_fiber hp u))
  let R₁ := V.isometryForwardFrameLoop q hp
  have hR₀ : R₀ 0 = R₀ 1 := by
    apply Subtype.ext
    simp only [R₀, regularFrameLoop_apply_coe]
    rw [V.fundamentalCurve_closed hp]
  have hR₁ : R₁ 0 = R₁ 1 := V.isometryForwardFrameLoop_closed q hp
  have hH : ∀ s, H (s, 0) = H (s, 1) := by
    intro s
    apply Subtype.ext
    change rowsMatrix (gramSchmidtNormed ℝ
        (codomainIsometryMovingFrame X q ε hε hdet
          (V.fundamentalCurve hp) (s, 0))) =
      rowsMatrix (gramSchmidtNormed ℝ
        (codomainIsometryMovingFrame X q ε hε hdet
          (V.fundamentalCurve hp) (s, 1)))
    congr 2
    unfold codomainIsometryMovingFrame
    rw [V.fundamentalCurve_closed hp]
  calc
    loopClassZ2 (V.fundamentalFrameLoop hp) (V.fundamentalFrameLoop_closed hp) =
        loopClassZ2 R₀ hR₀ :=
      loopClassZ2_congr_fun _ _ (V.fundamentalFrameLoop_eq_regularFrameLoop hp)
    _ = loopClassZ2 R₁ hR₁ := by
      exact loopClassZ2_congr hR₀ hR₁ H hH
    _ = loopClassZ2 (V.isometryForwardFrameLoop q hp)
          (V.isometryForwardFrameLoop_closed q hp) := by rfl


-- @@ L1236-1256 verbatim
theorem codomainIsometry_fundamentalFrameLoop_eq_forward
    (q : F ≃ₗᵢ[ℝ] F) (hdet : (isometryMatrix q).det = 1)
    {p : E} (hp : p ∈ X.fiber) :
    (V.codomainIsometry q 1 (Or.inl rfl) hdet).fundamentalFrameLoop
        ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp) =
      V.isometryForwardFrameLoop q hp := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop (X.codomainEquiv q.toContinuousLinearEquiv)
      ((V.codomainIsometry q 1 (Or.inl rfl) hdet).flow p)
        ((u : ℝ) * (V.codomainIsometry q 1 (Or.inl rfl) hdet).fundamentalPeriod
          ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp)) = _
  rw [V.codomainIsometry_fundamentalPeriod q 1 (Or.inl rfl) hdet hp]
  have hf (t : ℝ) :
      (V.codomainIsometry q 1 (Or.inl rfl) hdet).flow p t = V.flow p t := by
    simpa using V.codomainIsometry_flow q 1 (Or.inl rfl) hdet p t
  have hfun : (V.codomainIsometry q 1 (Or.inl rfl) hdet).flow p =
      V.flow p := funext hf
  rw [hfun]
  rfl


-- @@ L1258-1294 verbatim
theorem codomainIsometry_fundamentalFrameLoop_eq_reverse
    (q : F ≃ₗᵢ[ℝ] F) (hdet : (isometryMatrix q).det = -1)
    {p : E} (hp : p ∈ X.fiber) :
    (V.codomainIsometry q (-1) (Or.inr rfl) hdet).fundamentalFrameLoop
        ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp) =
      reverseLoop (V.isometryForwardFrameLoop q hp) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop (X.codomainEquiv q.toContinuousLinearEquiv)
      ((V.codomainIsometry q (-1) (Or.inr rfl) hdet).flow p)
        ((u : ℝ) * (V.codomainIsometry q (-1) (Or.inr rfl) hdet).fundamentalPeriod
          ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp)) = _
  rw [V.codomainIsometry_fundamentalPeriod q (-1) (Or.inr rfl) hdet hp]
  unfold frameLoop
  rw [V.codomainIsometry_flow]
  simp only [neg_one_mul]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (X.codomainEquiv q.toContinuousLinearEquiv)
        (V.flow p (-((u : ℝ) * V.fundamentalPeriod hp))))) =
    (((V.isometryForwardFrameLoop q hp) (unitInterval.symm u) :
      SOGroup (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  simp only [isometryForwardFrameLoop, regularFrameLoop_apply_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (X.codomainEquiv q.toContinuousLinearEquiv)
        (V.flow p (-((u : ℝ) * V.fundamentalPeriod hp))))) =
    rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (X.codomainEquiv q.toContinuousLinearEquiv)
        (V.flow p (((unitInterval.symm u : I) : ℝ) * V.fundamentalPeriod hp))))
  have hper := V.fundamentalPeriod_periodic hp
    (-((u : ℝ) * V.fundamentalPeriod hp))
  have harg :
      -((u : ℝ) * V.fundamentalPeriod hp) + V.fundamentalPeriod hp =
        ((unitInterval.symm u : I) : ℝ) * V.fundamentalPeriod hp := by
    simp only [unitInterval.coe_symm_eq]
    ring
  rw [← harg, hper]


-- @@ L1296-1330 verbatim
theorem codomainIsometry_fundamentalFrameClass
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    {p : E} (hp : p ∈ X.fiber) :
    (V.codomainIsometry q ε hε hdet).fundamentalFrameClass
        ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp) =
      V.fundamentalFrameClass hp := by
  rcases hε with rfl | rfl
  · unfold fundamentalFrameClass
    calc
      loopClassZ2 ((V.codomainIsometry q 1 (Or.inl rfl) hdet).fundamentalFrameLoop
          ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp)) _ =
          loopClassZ2 (V.isometryForwardFrameLoop q hp)
            (V.isometryForwardFrameLoop_closed q hp) :=
        loopClassZ2_congr_fun _ _
          (V.codomainIsometry_fundamentalFrameLoop_eq_forward q hdet hp)
      _ = loopClassZ2 (V.fundamentalFrameLoop hp)
          (V.fundamentalFrameLoop_closed hp) :=
        (V.fundamentalFrameLoop_isometry_freeHomotopy_class q 1
          (Or.inl rfl) hdet hp).symm
  · unfold fundamentalFrameClass
    calc
      loopClassZ2 ((V.codomainIsometry q (-1) (Or.inr rfl) hdet).fundamentalFrameLoop
          ((X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp)) _ =
          loopClassZ2 (reverseLoop (V.isometryForwardFrameLoop q hp))
            (reverseLoop_closed (V.isometryForwardFrameLoop_closed q hp)) :=
        loopClassZ2_congr_fun _ _
          (V.codomainIsometry_fundamentalFrameLoop_eq_reverse q hdet hp)
      _ = loopClassZ2 (V.isometryForwardFrameLoop q hp)
          (V.isometryForwardFrameLoop_closed q hp) :=
        loopClassZ2_reverse _ _
      _ = loopClassZ2 (V.fundamentalFrameLoop hp)
          (V.fundamentalFrameLoop_closed hp) :=
        (V.fundamentalFrameLoop_isometry_freeHomotopy_class q (-1)
          (Or.inr rfl) hdet hp).symm


-- @@ L1332-1347 verbatim
theorem codomainIsometry_orbitFinset (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    (V.codomainIsometry q ε hε hdet).orbitFinset = V.orbitFinset := by
  apply Finset.ext
  intro O
  simp only [(V.codomainIsometry q ε hε hdet).mem_orbitFinset,
    V.mem_orbitFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p ∈ X.fiber :=
      (X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mp hp
    exact ⟨p, hp', V.codomainIsometry_orbit q ε hε hdet p⟩
  · rintro ⟨p, hp, rfl⟩
    have hp' : p ∈ (X.codomainEquiv q.toContinuousLinearEquiv).fiber :=
      (X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mpr hp
    exact ⟨p, hp', (V.codomainIsometry_orbit q ε hε hdet p).symm⟩


-- @@ L1349-1359 verbatim
def codomainIsometryOrbitEquiv (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    V.OrbitIndex ≃ (V.codomainIsometry q ε hε hdet).OrbitIndex where
  toFun O := ⟨O.1, by
    rw [V.codomainIsometry_orbitFinset q ε hε hdet]
    exact O.2⟩
  invFun O := ⟨O.1, by
    rw [← V.codomainIsometry_orbitFinset q ε hε hdet]
    exact O.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L1361-1366 verbatim
@[simp] theorem codomainIsometryOrbitEquiv_coe
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (O : V.OrbitIndex) :
    ((V.codomainIsometryOrbitEquiv q ε hε hdet O :
      (V.codomainIsometry q ε hε hdet).OrbitIndex) : Set E) = O := rfl


-- @@ L1368-1394 verbatim
theorem codomainIsometry_orbitFrameClass
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (O : V.OrbitIndex) :
    V.orbitFrameClass O =
      (V.codomainIsometry q ε hε hdet).orbitFrameClass
        (V.codomainIsometryOrbitEquiv q ε hε hdet O) := by
  let W := V.codomainIsometry q ε hε hdet
  let e := V.codomainIsometryOrbitEquiv q ε hε hdet
  let p : E := V.orbitPoint O
  let r : E := W.orbitPoint (e O)
  have hp : p ∈ X.fiber := V.orbitPoint_mem_fiber O
  have hrW : r ∈ (X.codomainEquiv q.toContinuousLinearEquiv).fiber :=
    W.orbitPoint_mem_fiber (e O)
  have hr : r ∈ X.fiber :=
    (X.mem_fiber_codomainEquiv q.toContinuousLinearEquiv).mp hrW
  have hsets : (O : Set E) = ((e O : W.OrbitIndex) : Set E) := rfl
  have hrOrbit : r ∈ V.orbit p := by
    have hOp : (O : Set E) = V.orbit p := V.orbitPoint_orbit O
    have hOr : ((e O : W.OrbitIndex) : Set E) = W.orbit r :=
      W.orbitPoint_orbit (e O)
    rw [← hOp, hsets, hOr, V.codomainIsometry_orbit q ε hε hdet r]
    exact V.mem_orbit_self r
  have hbase : V.fundamentalFrameClass hr = V.fundamentalFrameClass hp :=
    V.fundamentalFrameClass_eq_of_mem_orbit hp hrOrbit
  change V.fundamentalFrameClass hp = W.fundamentalFrameClass hrW
  rw [V.codomainIsometry_fundamentalFrameClass q ε hε hdet hr, hbase]


-- @@ L1396-1404 verbatim
theorem codomainIsometry_orbitContribution
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε)
    (O : V.OrbitIndex) :
    V.orbitContribution O =
      (V.codomainIsometry q ε hε hdet).orbitContribution
        (V.codomainIsometryOrbitEquiv q ε hε hdet O) := by
  unfold orbitContribution
  rw [V.codomainIsometry_orbitFrameClass q ε hε hdet O]


-- @@ L1406-1411 verbatim
def codomainIsometryDeltaTransport
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    V.DeltaTransport (V.codomainIsometry q ε hε hdet) where
  orbitEquiv := V.codomainIsometryOrbitEquiv q ε hε hdet
  contribution_eq := V.codomainIsometry_orbitContribution q ε hε hdet


-- @@ L1413-1413 verbatim
end TamedField


-- @@ L1415-1415 verbatim
namespace FiberSign


-- @@ L1417-1417 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L1419-1433 verbatim
theorem positiveFramedDelta_codomainIsometry (V : TamedField X)
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    S.positiveFramedDelta V =
      (S.codomainEquiv q.toContinuousLinearEquiv).positiveFramedDelta
        (V.codomainIsometry q ε hε hdet) := by
  let W := V.codomainIsometry q ε hε hdet
  let T := V.codomainIsometryDeltaTransport q ε hε hdet
  apply V.deltaOn_eq_of_transport T
  intro O
  change (O : Set E) ⊆ S.positivePart ↔
    ((T.orbitEquiv O : W.OrbitIndex) : Set E) ⊆
      (S.codomainEquiv q.toContinuousLinearEquiv).positivePart
  rw [S.positivePart_codomainEquiv]
  rfl


-- @@ L1435-1448 verbatim
theorem positiveDelta_codomainIsometry
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    (S.codomainEquiv q.toContinuousLinearEquiv).positiveDelta =
      S.positiveDelta := by
  let V := X.exists_tamedField.some
  let W := V.codomainIsometry q ε hε hdet
  calc
    (S.codomainEquiv q.toContinuousLinearEquiv).positiveDelta =
        (S.codomainEquiv q.toContinuousLinearEquiv).positiveFramedDelta W :=
      (S.codomainEquiv q.toContinuousLinearEquiv).positiveDelta_eq W
    _ = S.positiveFramedDelta V :=
      (S.positiveFramedDelta_codomainIsometry V q ε hε hdet).symm
    _ = S.positiveDelta := (S.positiveDelta_eq V).symm


-- @@ L1450-1457 verbatim
theorem negativeDelta_codomainIsometry
    (q : F ≃ₗᵢ[ℝ] F) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hdet : (isometryMatrix q).det = ε) :
    (S.codomainEquiv q.toContinuousLinearEquiv).negativeDelta =
      S.negativeDelta := by
  unfold negativeDelta
  rw [S.codomainEquiv_neg,
    S.neg.positiveDelta_codomainIsometry q ε hε hdet]


-- @@ L1459-1459 verbatim
end FiberSign


-- @@ L1461-1461 verbatim
/-! ## Positive scalar postcomposition -/


-- @@ L1463-1464 verbatim
def positiveScaleEquiv (a : ℝ) (ha : 0 < a) : F ≃L[ℝ] F :=
  (Units.mk0 a (ne_of_gt ha)) • (1 : F ≃L[ℝ] F)


-- @@ L1466-1468 verbatim
@[simp] theorem positiveScaleEquiv_apply (a : ℝ) (ha : 0 < a) (x : F) :
    positiveScaleEquiv a ha x = a • x := by
  rfl


-- @@ L1470-1471 verbatim
def scaleMatrix (a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  a • (1 : Matrix (Fin n) (Fin n) ℝ)


-- @@ L1473-1475 verbatim
@[simp] theorem scaleMatrix_apply (a : ℝ) (i j : Fin n) :
    scaleMatrix a i j = if i = j then a else 0 := by
  simp [scaleMatrix, Matrix.one_apply]


-- @@ L1477-1478 verbatim
theorem det_scaleMatrix (a : ℝ) : (scaleMatrix (n := n) a).det = a ^ n := by
  rw [scaleMatrix, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]


-- @@ L1480-1483 verbatim
theorem normalRowAction_scaleMatrix (a : ℝ) (v : Fin n → E) (i : Fin n) :
    normalRowAction (scaleMatrix a) v i = a • v i := by
  classical
  simp [normalRowAction, scaleMatrix_apply]


-- @@ L1485-1485 verbatim
namespace FramedLevelSet


-- @@ L1487-1500 verbatim
theorem gradVec_positiveScale (X : FramedLevelSet n) (a : ℝ) (ha : 0 < a)
    (j : Fin n) (x : E) :
    gradVec (X.codomainEquiv (positiveScaleEquiv a ha)).g j x =
      a • gradVec X.g j x := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  intro w
  rw [inner_gradVec, X.fderiv_codomainEquiv, ContinuousLinearMap.comp_apply]
  rw [real_inner_smul_left, inner_gradVec]
  change (positiveScaleEquiv a ha
    (fderiv ℝ X.g x
      ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis w))) j = _
  rw [positiveScaleEquiv_apply]
  rfl


-- @@ L1502-1513 verbatim
theorem kerCross_positiveScale (X : FramedLevelSet n) (a : ℝ) (ha : 0 < a)
    (x : E) :
    kerCross (X.codomainEquiv (positiveScaleEquiv a ha)).g x =
      (a ^ n) • kerCross X.g x := by
  unfold kerCross
  rw [show (fun j => gradVec (X.codomainEquiv
      (positiveScaleEquiv a ha)).g j x) =
      normalRowAction (scaleMatrix a) (fun j => gradVec X.g j x) by
    funext j
    rw [normalRowAction_scaleMatrix]
    exact X.gradVec_positiveScale a ha j x]
  rw [crossVec_frameRowAction_normals, det_scaleMatrix]


-- @@ L1515-1527 verbatim
theorem tauField_positiveScale (X : FramedLevelSet n) (a : ℝ) (ha : 0 < a)
    (x : E) :
    tauField (X.codomainEquiv (positiveScaleEquiv a ha)).g x =
      tauField X.g x := by
  rw [tauField, X.kerCross_positiveScale, tauField]
  have hap : 0 < a ^ n := pow_pos ha n
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hap]
  by_cases hk : ‖kerCross X.g x‖ = 0
  · rw [hk]
    simp
  · rw [smul_smul]
    congr 1
    field_simp [ne_of_gt hap, hk]


-- @@ L1529-1529 verbatim
end FramedLevelSet


-- @@ L1531-1531 verbatim
namespace TamedField


-- @@ L1533-1533 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L1535-1551 verbatim
def positiveScale (a : ℝ) (ha : 0 < a) :
    TamedField (X.codomainEquiv (positiveScaleEquiv a ha)) where
  v := V.v
  delta := V.delta
  delta_pos := V.delta_pos
  smooth := V.smooth
  norm_le := V.norm_le
  eq_tau := by
    intro x hx
    have hx' : x ∈ Metric.cthickening V.delta X.fiber := by
      rwa [← X.fiber_codomainEquiv (positiveScaleEquiv a ha)]
    rw [V.eq_tau x hx', X.tauField_positiveScale a ha]
  fderiv_zero := by
    intro x
    rw [X.fderiv_codomainEquiv, ContinuousLinearMap.comp_apply, V.fderiv_zero,
      map_zero]
  lipschitz := V.lipschitz


-- @@ L1553-1554 verbatim
@[simp] theorem positiveScale_v (a : ℝ) (ha : 0 < a) (x : E) :
    (V.positiveScale a ha).v x = V.v x := rfl


-- @@ L1556-1564 verbatim
theorem positiveScale_flow (a : ℝ) (ha : 0 < a) (p : E) (t : ℝ) :
    (V.positiveScale a ha).flow p t = V.flow p t := by
  let W := V.positiveScale a ha
  have heq : W.flow p = V.flow p := by
    apply W.solution_unique (t₀ := 0)
    · exact W.hasDerivAt_flow p
    · exact V.hasDerivAt_flow p
    · simp
  exact congrFun heq t


-- @@ L1566-1572 verbatim
theorem positiveScale_orbit (a : ℝ) (ha : 0 < a) (p : E) :
    (V.positiveScale a ha).orbit p = V.orbit p := by
  ext x
  simp only [orbit, mem_range]
  constructor <;> rintro ⟨t, rfl⟩
  · exact ⟨t, (V.positiveScale_flow a ha p t).symm⟩
  · exact ⟨t, V.positiveScale_flow a ha p t⟩


-- @@ L1574-1587 verbatim
theorem positiveScale_fundamentalPeriod (a : ℝ) (ha : 0 < a)
    {p : E} (hp : p ∈ X.fiber) :
    (V.positiveScale a ha).fundamentalPeriod
        ((X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mpr hp) =
      V.fundamentalPeriod hp := by
  let W := V.positiveScale a ha
  let hp' : p ∈ (X.codomainEquiv (positiveScaleEquiv a ha)).fiber :=
    (X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mpr hp
  have hflow : W.flow p = V.flow p := funext (V.positiveScale_flow a ha p)
  apply le_antisymm
  · apply W.fundamentalPeriod_le_period hp' (V.fundamentalPeriod_pos hp)
    simpa [hflow] using V.fundamentalPeriod_periodic hp
  · apply V.fundamentalPeriod_le_period hp (W.fundamentalPeriod_pos hp')
    simpa [← hflow] using W.fundamentalPeriod_periodic hp'


-- @@ L1589-1589 verbatim
end TamedField


-- @@ L1591-1600 verbatim
theorem frameRowAction_scaleBlock (X : FramedLevelSet n)
    (a : ℝ) (ha : 0 < a) (x : E) :
    frameRowAction (tangentNormalBlock 1 (scaleMatrix a)) (frameAt X x) =
      frameAt (X.codomainEquiv (positiveScaleEquiv a ha)) x := by
  funext r
  rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨r, rfl⟩
  · simp [frameRowAction, Fin.sum_univ_succ, tangentNormalBlock,
      frameAt, X.tauField_positiveScale a ha]
  · simp only [frameAt, Fin.cons_succ, X.gradVec_positiveScale]
    simp [frameRowAction, Fin.sum_univ_succ, tangentNormalBlock]


-- @@ L1602-1603 verbatim
def scalePathCoeff (a : ℝ) (s : I) : ℝ :=
  (1 - (s : ℝ)) + (s : ℝ) * a


-- @@ L1605-1612 verbatim
theorem scalePathCoeff_pos (a : ℝ) (ha : 0 < a) (s : I) :
    0 < scalePathCoeff a s := by
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hs : (s : ℝ) = 0
  · simp [scalePathCoeff, hs]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs1)
      (mul_pos (lt_of_le_of_ne hs0 (Ne.symm hs)) ha)


-- @@ L1614-1615 verbatim
@[simp] theorem scalePathCoeff_zero (a : ℝ) : scalePathCoeff a 0 = 1 := by
  simp [scalePathCoeff]


-- @@ L1617-1618 verbatim
@[simp] theorem scalePathCoeff_one (a : ℝ) : scalePathCoeff a 1 = a := by
  simp [scalePathCoeff]


-- @@ L1620-1622 verbatim
theorem continuous_scalePathCoeff (a : ℝ) : Continuous (scalePathCoeff a) := by
  unfold scalePathCoeff
  fun_prop


-- @@ L1624-1626 verbatim
def scalePathBlock (a : ℝ) (s : I) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  tangentNormalBlock 1 (scaleMatrix (scalePathCoeff a s))


-- @@ L1628-1637 verbatim
@[simp] theorem scalePathBlock_zero (a : ℝ) :
    scalePathBlock (n := n) a 0 = 1 := by
  ext r c
  rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨r, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨c, rfl⟩
  · simp [scalePathBlock]
  · rw [Matrix.one_apply]
    simp [scalePathBlock, (Fin.succ_ne_zero c).symm]
  · simp [scalePathBlock]
  · simp [scalePathBlock, Matrix.one_apply]


-- @@ L1639-1642 verbatim
@[simp] theorem scalePathBlock_one (a : ℝ) :
    scalePathBlock (n := n) a 1 = tangentNormalBlock 1 (scaleMatrix a) := by
  unfold scalePathBlock
  rw [scalePathCoeff_one]


-- @@ L1644-1647 verbatim
theorem det_scalePathBlock_pos (a : ℝ) (ha : 0 < a) (s : I) :
    0 < (scalePathBlock (n := n) a s).det := by
  rw [scalePathBlock, det_tangentNormalBlock, one_mul, det_scaleMatrix]
  exact pow_pos (scalePathCoeff_pos a ha s) n


-- @@ L1649-1651 verbatim
def positiveScaleMovingFrame (X : FramedLevelSet n) (a : ℝ)
    (γ : C(I, E)) (p : I × I) : Fin (n + 1) → E :=
  frameRowAction (scalePathBlock a p.1) (frameAt X (γ p.2))


-- @@ L1653-1659 verbatim
theorem positiveScaleMovingFrame_det_pos (X : FramedLevelSet n)
    (a : ℝ) (ha : 0 < a) (γ : C(I, E))
    (hreg : ∀ u, γ u ∈ regularSet X.g) (p : I × I) :
    0 < (rowsMatrix (positiveScaleMovingFrame X a γ p)).det := by
  rw [positiveScaleMovingFrame, det_rowsMatrix_frameRowAction]
  exact mul_pos (det_scalePathBlock_pos a ha p.1)
    (det_rowsMatrix_frameAt_pos X (hreg p.2))


-- @@ L1661-1672 verbatim
theorem continuous_scalePathBlock_apply (a : ℝ) (r c : Fin (n + 1)) :
    Continuous fun s : I => scalePathBlock (n := n) a s r c := by
  rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨r, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨c, rfl⟩
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · by_cases hrc : r = c
    · subst c
      simpa [scalePathBlock, scaleMatrix_apply] using continuous_scalePathCoeff a
    · simpa [scalePathBlock, scaleMatrix_apply, hrc] using
        (continuous_const : Continuous fun _ : I => (0 : ℝ))


-- @@ L1674-1686 verbatim
theorem continuous_positiveScaleMovingFrame (X : FramedLevelSet n)
    (a : ℝ) (γ : C(I, E)) (hreg : ∀ u, γ u ∈ regularSet X.g)
    (r : Fin (n + 1)) :
    Continuous fun p : I × I => positiveScaleMovingFrame X a γ p r := by
  unfold positiveScaleMovingFrame frameRowAction
  apply continuous_finsetSum
  intro j _
  have hmatrix : Continuous fun p : I × I => scalePathBlock a p.1 r j :=
    (continuous_scalePathBlock_apply a r j).comp continuous_fst
  have hframe : Continuous fun p : I × I => frameAt X (γ p.2) j :=
    continuous_frameAt_comp X (γ.continuous.comp continuous_snd)
      (fun p => hreg p.2) j
  exact hmatrix.smul hframe


-- @@ L1688-1722 verbatim
def positiveScaleFrameHomotopy (X : FramedLevelSet n)
    (a : ℝ) (ha : 0 < a) (γ : C(I, E)) (hγ : ∀ u, γ u ∈ X.fiber) :
    ContinuousMap.Homotopy
      (regularFrameLoop X γ (fun u => X.fiber_subset_regularSet (hγ u)))
      (regularFrameLoop (X.codomainEquiv (positiveScaleEquiv a ha)) γ
        (fun u => (X.codomainEquiv (positiveScaleEquiv a ha)).fiber_subset_regularSet
          ((X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mpr (hγ u)))) where
  toFun p := positiveFrameSO (positiveScaleMovingFrame X a γ p)
    (positiveScaleMovingFrame_det_pos X a ha γ
      (fun u => X.fiber_subset_regularSet (hγ u)) p)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro r c
    have hInd : ∀ p : I × I,
        LinearIndependent ℝ (positiveScaleMovingFrame X a γ p) := fun p =>
      linearIndependent_of_det_rowsMatrix_ne_zero _
        (ne_of_gt (positiveScaleMovingFrame_det_pos X a ha γ
          (fun u => X.fiber_subset_regularSet (hγ u)) p))
    have hgs := continuous_gramSchmidtNormed_family
      (A := positiveScaleMovingFrame X a γ)
      (continuous_positiveScaleMovingFrame X a γ
        (fun u => X.fiber_subset_regularSet (hγ u))) hInd r
    exact (EuclideanSpace.proj c).continuous.comp hgs
  map_zero_left := by
    intro u
    apply Subtype.ext
    simp only [positiveFrameSO_coe, positiveScaleMovingFrame,
      scalePathBlock_zero, frameRowAction_one, regularFrameLoop_apply_coe]
  map_one_left := by
    intro u
    apply Subtype.ext
    simp only [positiveFrameSO_coe, positiveScaleMovingFrame,
      scalePathBlock_one, regularFrameLoop_apply_coe]
    rw [frameRowAction_scaleBlock X a ha (γ u)]


-- @@ L1724-1724 verbatim
namespace TamedField


-- @@ L1726-1726 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L1728-1734 verbatim
def scaleForwardFrameLoop (a : ℝ) (ha : 0 < a) {p : E}
    (hp : p ∈ X.fiber) : C(I, SOGroup (n + 1)) :=
  regularFrameLoop (X.codomainEquiv (positiveScaleEquiv a ha))
    (V.fundamentalCurve hp)
    (fun u => (X.codomainEquiv (positiveScaleEquiv a ha)).fiber_subset_regularSet
      ((X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mpr
        (V.fundamentalCurve_mem_fiber hp u)))


-- @@ L1736-1741 verbatim
theorem scaleForwardFrameLoop_closed (a : ℝ) (ha : 0 < a)
    {p : E} (hp : p ∈ X.fiber) :
    V.scaleForwardFrameLoop a ha hp 0 = V.scaleForwardFrameLoop a ha hp 1 := by
  apply Subtype.ext
  simp only [scaleForwardFrameLoop, regularFrameLoop_apply_coe]
  rw [V.fundamentalCurve_closed hp]


-- @@ L1743-1775 verbatim
theorem fundamentalFrameLoop_scale_freeHomotopy_class
    (a : ℝ) (ha : 0 < a) {p : E} (hp : p ∈ X.fiber) :
    loopClassZ2 (V.fundamentalFrameLoop hp) (V.fundamentalFrameLoop_closed hp) =
      loopClassZ2 (V.scaleForwardFrameLoop a ha hp)
        (V.scaleForwardFrameLoop_closed a ha hp) := by
  let H := positiveScaleFrameHomotopy X a ha (V.fundamentalCurve hp)
    (V.fundamentalCurve_mem_fiber hp)
  let R₀ := regularFrameLoop X (V.fundamentalCurve hp)
    (fun u => X.fiber_subset_regularSet (V.fundamentalCurve_mem_fiber hp u))
  let R₁ := V.scaleForwardFrameLoop a ha hp
  have hR₀ : R₀ 0 = R₀ 1 := by
    apply Subtype.ext
    simp only [R₀, regularFrameLoop_apply_coe]
    rw [V.fundamentalCurve_closed hp]
  have hR₁ : R₁ 0 = R₁ 1 := V.scaleForwardFrameLoop_closed a ha hp
  have hH : ∀ s, H (s, 0) = H (s, 1) := by
    intro s
    apply Subtype.ext
    change rowsMatrix (gramSchmidtNormed ℝ
        (positiveScaleMovingFrame X a (V.fundamentalCurve hp) (s, 0))) =
      rowsMatrix (gramSchmidtNormed ℝ
        (positiveScaleMovingFrame X a (V.fundamentalCurve hp) (s, 1)))
    congr 2
    unfold positiveScaleMovingFrame
    rw [V.fundamentalCurve_closed hp]
  calc
    loopClassZ2 (V.fundamentalFrameLoop hp) (V.fundamentalFrameLoop_closed hp) =
        loopClassZ2 R₀ hR₀ :=
      loopClassZ2_congr_fun _ _ (V.fundamentalFrameLoop_eq_regularFrameLoop hp)
    _ = loopClassZ2 R₁ hR₁ := by
      exact loopClassZ2_congr hR₀ hR₁ H hH
    _ = loopClassZ2 (V.scaleForwardFrameLoop a ha hp)
          (V.scaleForwardFrameLoop_closed a ha hp) := by rfl


-- @@ L1777-1793 verbatim
theorem positiveScale_fundamentalFrameLoop_eq_forward
    (a : ℝ) (ha : 0 < a) {p : E} (hp : p ∈ X.fiber) :
    (V.positiveScale a ha).fundamentalFrameLoop
        ((X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mpr hp) =
      V.scaleForwardFrameLoop a ha hp := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop (X.codomainEquiv (positiveScaleEquiv a ha))
      ((V.positiveScale a ha).flow p)
        ((u : ℝ) * (V.positiveScale a ha).fundamentalPeriod
          ((X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mpr hp)) = _
  rw [V.positiveScale_fundamentalPeriod a ha hp]
  have hfun : (V.positiveScale a ha).flow p = V.flow p :=
    funext (V.positiveScale_flow a ha p)
  rw [hfun]
  rfl


-- @@ L1795-1810 verbatim
theorem positiveScale_fundamentalFrameClass
    (a : ℝ) (ha : 0 < a) {p : E} (hp : p ∈ X.fiber) :
    (V.positiveScale a ha).fundamentalFrameClass
        ((X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mpr hp) =
      V.fundamentalFrameClass hp := by
  unfold fundamentalFrameClass
  calc
    loopClassZ2 ((V.positiveScale a ha).fundamentalFrameLoop
        ((X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mpr hp)) _ =
        loopClassZ2 (V.scaleForwardFrameLoop a ha hp)
          (V.scaleForwardFrameLoop_closed a ha hp) :=
      loopClassZ2_congr_fun _ _
        (V.positiveScale_fundamentalFrameLoop_eq_forward a ha hp)
    _ = loopClassZ2 (V.fundamentalFrameLoop hp)
        (V.fundamentalFrameLoop_closed hp) :=
      (V.fundamentalFrameLoop_scale_freeHomotopy_class a ha hp).symm


-- @@ L1812-1825 verbatim
theorem positiveScale_orbitFinset (a : ℝ) (ha : 0 < a) :
    (V.positiveScale a ha).orbitFinset = V.orbitFinset := by
  apply Finset.ext
  intro O
  simp only [(V.positiveScale a ha).mem_orbitFinset, V.mem_orbitFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p ∈ X.fiber :=
      (X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mp hp
    exact ⟨p, hp', V.positiveScale_orbit a ha p⟩
  · rintro ⟨p, hp, rfl⟩
    have hp' : p ∈ (X.codomainEquiv (positiveScaleEquiv a ha)).fiber :=
      (X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mpr hp
    exact ⟨p, hp', (V.positiveScale_orbit a ha p).symm⟩


-- @@ L1827-1836 verbatim
def positiveScaleOrbitEquiv (a : ℝ) (ha : 0 < a) :
    V.OrbitIndex ≃ (V.positiveScale a ha).OrbitIndex where
  toFun O := ⟨O.1, by
    rw [V.positiveScale_orbitFinset a ha]
    exact O.2⟩
  invFun O := ⟨O.1, by
    rw [← V.positiveScale_orbitFinset a ha]
    exact O.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L1838-1841 verbatim
@[simp] theorem positiveScaleOrbitEquiv_coe (a : ℝ) (ha : 0 < a)
    (O : V.OrbitIndex) :
    ((V.positiveScaleOrbitEquiv a ha O : (V.positiveScale a ha).OrbitIndex) :
      Set E) = O := rfl


-- @@ L1843-1866 verbatim
theorem positiveScale_orbitFrameClass (a : ℝ) (ha : 0 < a)
    (O : V.OrbitIndex) :
    V.orbitFrameClass O =
      (V.positiveScale a ha).orbitFrameClass (V.positiveScaleOrbitEquiv a ha O) := by
  let W := V.positiveScale a ha
  let e := V.positiveScaleOrbitEquiv a ha
  let p : E := V.orbitPoint O
  let q : E := W.orbitPoint (e O)
  have hp : p ∈ X.fiber := V.orbitPoint_mem_fiber O
  have hqW : q ∈ (X.codomainEquiv (positiveScaleEquiv a ha)).fiber :=
    W.orbitPoint_mem_fiber (e O)
  have hq : q ∈ X.fiber :=
    (X.mem_fiber_codomainEquiv (positiveScaleEquiv a ha)).mp hqW
  have hsets : (O : Set E) = ((e O : W.OrbitIndex) : Set E) := rfl
  have hqOrbit : q ∈ V.orbit p := by
    have hOp : (O : Set E) = V.orbit p := V.orbitPoint_orbit O
    have hOq : ((e O : W.OrbitIndex) : Set E) = W.orbit q :=
      W.orbitPoint_orbit (e O)
    rw [← hOp, hsets, hOq, V.positiveScale_orbit a ha q]
    exact V.mem_orbit_self q
  have hbase : V.fundamentalFrameClass hq = V.fundamentalFrameClass hp :=
    V.fundamentalFrameClass_eq_of_mem_orbit hp hqOrbit
  change V.fundamentalFrameClass hp = W.fundamentalFrameClass hqW
  rw [V.positiveScale_fundamentalFrameClass a ha hq, hbase]


-- @@ L1868-1873 verbatim
theorem positiveScale_orbitContribution (a : ℝ) (ha : 0 < a)
    (O : V.OrbitIndex) :
    V.orbitContribution O =
      (V.positiveScale a ha).orbitContribution (V.positiveScaleOrbitEquiv a ha O) := by
  unfold orbitContribution
  rw [V.positiveScale_orbitFrameClass a ha O]


-- @@ L1875-1878 verbatim
def positiveScaleDeltaTransport (a : ℝ) (ha : 0 < a) :
    V.DeltaTransport (V.positiveScale a ha) where
  orbitEquiv := V.positiveScaleOrbitEquiv a ha
  contribution_eq := V.positiveScale_orbitContribution a ha


-- @@ L1880-1880 verbatim
end TamedField


-- @@ L1882-1882 verbatim
namespace FiberSign


-- @@ L1884-1884 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L1886-1899 verbatim
theorem positiveFramedDelta_positiveScale (V : TamedField X)
    (a : ℝ) (ha : 0 < a) :
    S.positiveFramedDelta V =
      (S.codomainEquiv (positiveScaleEquiv a ha)).positiveFramedDelta
        (V.positiveScale a ha) := by
  let W := V.positiveScale a ha
  let T := V.positiveScaleDeltaTransport a ha
  apply V.deltaOn_eq_of_transport T
  intro O
  change (O : Set E) ⊆ S.positivePart ↔
    ((T.orbitEquiv O : W.OrbitIndex) : Set E) ⊆
      (S.codomainEquiv (positiveScaleEquiv a ha)).positivePart
  rw [S.positivePart_codomainEquiv]
  rfl


-- @@ L1901-1912 verbatim
theorem positiveDelta_positiveScale (a : ℝ) (ha : 0 < a) :
    (S.codomainEquiv (positiveScaleEquiv a ha)).positiveDelta =
      S.positiveDelta := by
  let V := X.exists_tamedField.some
  let W := V.positiveScale a ha
  calc
    (S.codomainEquiv (positiveScaleEquiv a ha)).positiveDelta =
        (S.codomainEquiv (positiveScaleEquiv a ha)).positiveFramedDelta W :=
      (S.codomainEquiv (positiveScaleEquiv a ha)).positiveDelta_eq W
    _ = S.positiveFramedDelta V :=
      (S.positiveFramedDelta_positiveScale V a ha).symm
    _ = S.positiveDelta := (S.positiveDelta_eq V).symm


-- @@ L1914-1918 verbatim
theorem negativeDelta_positiveScale (a : ℝ) (ha : 0 < a) :
    (S.codomainEquiv (positiveScaleEquiv a ha)).negativeDelta =
      S.negativeDelta := by
  unfold negativeDelta
  rw [S.codomainEquiv_neg, S.neg.positiveDelta_positiveScale a ha]


-- @@ L1920-1920 verbatim
end FiberSign


-- @@ L1922-1922 verbatim
/-! ## The actual background equivalence -/


-- @@ L1924-1926 verbatim
theorem backgroundScale_pos_F {c₁ c₂ : F} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    0 < backgroundScale c₁ c₂ :=
  div_pos (norm_pos_iff.mpr h₂) (norm_pos_iff.mpr h₁)


-- @@ L1928-1930 verbatim
def backgroundDifference (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) : F :=
  positiveScaleEquiv (backgroundScale c₁ c₂)
      (backgroundScale_pos_F h₁ h₂) c₁ - c₂


-- @@ L1932-1934 verbatim
def backgroundReflection (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    F ≃ₗᵢ[ℝ] F :=
  Submodule.reflection (ℝ ∙ (backgroundDifference c₁ c₂ h₁ h₂))ᗮ


-- @@ L1936-1943 verbatim
theorem backgroundEquiv_eq_scale_trans_reflection
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    backgroundEquiv c₁ c₂ h₁ h₂ =
      (positiveScaleEquiv (backgroundScale c₁ c₂)
        (backgroundScale_pos_F h₁ h₂)).trans
        (backgroundReflection c₁ c₂ h₁ h₂).toContinuousLinearEquiv := by
  apply ContinuousLinearEquiv.ext
  rfl


-- @@ L1945-1958 verbatim
theorem isometryMatrix_backgroundReflection_det
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (isometryMatrix (backgroundReflection c₁ c₂ h₁ h₂)).det =
      if backgroundDifference c₁ c₂ h₁ h₂ = 0 then 1 else -1 := by
  let u := backgroundDifference c₁ c₂ h₁ h₂
  rw [isometryMatrix, LinearMap.det_toMatrix]
  change LinearMap.det (Submodule.reflection (ℝ ∙ u)ᗮ).toLinearMap = _
  rw [Submodule.det_reflection]
  by_cases hu : u = 0
  · rw [if_pos hu, Submodule.orthogonal_orthogonal, hu]
    rw [Submodule.span_zero_singleton, finrank_bot, pow_zero]
  · rw [if_neg hu, Submodule.orthogonal_orthogonal,
      finrank_span_singleton hu]
    norm_num


-- @@ L1960-1960 verbatim
namespace FramedLevelSet


-- @@ L1962-1966 verbatim
theorem codomainEquiv_trans (X : FramedLevelSet n) (e₁ e₂ : F ≃L[ℝ] F) :
    (X.codomainEquiv e₁).codomainEquiv e₂ = X.codomainEquiv (e₁.trans e₂) := by
  apply FramedLevelSet.eq_of_g_eq
  funext x
  rfl


-- @@ L1968-1968 verbatim
end FramedLevelSet


-- @@ L1970-1971 verbatim
def backgroundReflectionSign (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) : ℝ :=
  if backgroundDifference c₁ c₂ h₁ h₂ = 0 then 1 else -1


-- @@ L1973-1978 verbatim
theorem backgroundReflectionSign_cases (c₁ c₂ : F)
    (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    backgroundReflectionSign c₁ c₂ h₁ h₂ = 1 ∨
      backgroundReflectionSign c₁ c₂ h₁ h₂ = -1 := by
  unfold backgroundReflectionSign
  split <;> simp


-- @@ L1980-1984 verbatim
theorem isometryMatrix_backgroundReflection_det_sign
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (isometryMatrix (backgroundReflection c₁ c₂ h₁ h₂)).det =
      backgroundReflectionSign c₁ c₂ h₁ h₂ := by
  exact isometryMatrix_backgroundReflection_det c₁ c₂ h₁ h₂


-- @@ L1986-1994 verbatim
theorem backgroundFactor_fls_eq (X : FramedLevelSet n)
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (X.codomainEquiv
        (positiveScaleEquiv (backgroundScale c₁ c₂)
          (backgroundScale_pos_F h₁ h₂))).codomainEquiv
        (backgroundReflection c₁ c₂ h₁ h₂).toContinuousLinearEquiv =
      X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂) := by
  rw [X.codomainEquiv_trans,
    backgroundEquiv_eq_scale_trans_reflection c₁ c₂ h₁ h₂]


-- @@ L1996-1996 verbatim
namespace TamedField


-- @@ L1998-1998 verbatim
variable {X Y Z : FramedLevelSet n}


-- @@ L2000-2002 verbatim
/-- Transport a tamed field across equality of framed-level-set presentations. -/
def cast (V : TamedField X) (hXY : X = Y) : TamedField Y :=
  hXY ▸ V


-- @@ L2004-2008 verbatim
/-- Equality of presentations induces the tautological bijection of orbit ledgers. -/
def castOrbitEquiv (V : TamedField X) (hXY : X = Y) :
    V.OrbitIndex ≃ (V.cast hXY).OrbitIndex := by
  subst Y
  exact Equiv.refl _


-- @@ L2010-2014 verbatim
@[simp] theorem castOrbitEquiv_coe (V : TamedField X) (hXY : X = Y)
    (O : V.OrbitIndex) :
    ((V.castOrbitEquiv hXY O : (V.cast hXY).OrbitIndex) : Set E) = O := by
  subst Y
  rfl


-- @@ L2016-2021 verbatim
theorem cast_orbitFrameClass (V : TamedField X) (hXY : X = Y)
    (O : V.OrbitIndex) :
    V.orbitFrameClass O =
      (V.cast hXY).orbitFrameClass (V.castOrbitEquiv hXY O) := by
  subst Y
  rfl


-- @@ L2023-2028 verbatim
theorem cast_orbitContribution (V : TamedField X) (hXY : X = Y)
    (O : V.OrbitIndex) :
    V.orbitContribution O =
      (V.cast hXY).orbitContribution (V.castOrbitEquiv hXY O) := by
  unfold orbitContribution
  rw [V.cast_orbitFrameClass hXY O]


-- @@ L2030-2033 verbatim
def castDeltaTransport (V : TamedField X) (hXY : X = Y) :
    V.DeltaTransport (V.cast hXY) where
  orbitEquiv := V.castOrbitEquiv hXY
  contribution_eq := V.cast_orbitContribution hXY


-- @@ L2035-2035 verbatim
namespace DeltaTransport


-- @@ L2037-2043 verbatim
/-- Composition of component ledgers. -/
def trans {V : TamedField X} {W : TamedField Y} {U : TamedField Z}
    (T₁ : V.DeltaTransport W) (T₂ : W.DeltaTransport U) :
    V.DeltaTransport U where
  orbitEquiv := T₁.orbitEquiv.trans T₂.orbitEquiv
  contribution_eq O := (T₁.contribution_eq O).trans
    (T₂.contribution_eq (T₁.orbitEquiv O))


-- @@ L2045-2045 verbatim
end DeltaTransport


-- @@ L2047-2047 verbatim
section BackgroundTransport


-- @@ L2049-2049 verbatim
variable {X : FramedLevelSet n}


-- @@ L2051-2054 verbatim
/-- The first, positive-scaling stage of background harmonization. -/
def backgroundScaled (V : TamedField X)
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :=
  V.positiveScale (backgroundScale c₁ c₂) (backgroundScale_pos_F h₁ h₂)


-- @@ L2056-2063 verbatim
/-- The second, Householder-isometry stage of background harmonization. -/
def backgroundReflected (V : TamedField X)
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :=
  (V.backgroundScaled c₁ c₂ h₁ h₂).codomainIsometry
    (backgroundReflection c₁ c₂ h₁ h₂)
    (backgroundReflectionSign c₁ c₂ h₁ h₂)
    (backgroundReflectionSign_cases c₁ c₂ h₁ h₂)
    (isometryMatrix_backgroundReflection_det_sign c₁ c₂ h₁ h₂)


-- @@ L2065-2070 verbatim
/-- A tamed field on the actual `backgroundEquiv` presentation. -/
def backgroundTransport (V : TamedField X)
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    TamedField (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂)) :=
  (V.backgroundReflected c₁ c₂ h₁ h₂).cast
    (backgroundFactor_fls_eq X c₁ c₂ h₁ h₂)


-- @@ L2072-2084 verbatim
/-- The full component ledger for the actual background equivalence. -/
def backgroundDeltaTransport (V : TamedField X)
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    V.DeltaTransport (V.backgroundTransport c₁ c₂ h₁ h₂) :=
  (V.positiveScaleDeltaTransport (backgroundScale c₁ c₂)
      (backgroundScale_pos_F h₁ h₂)).trans
    (((V.backgroundScaled c₁ c₂ h₁ h₂).codomainIsometryDeltaTransport
      (backgroundReflection c₁ c₂ h₁ h₂)
      (backgroundReflectionSign c₁ c₂ h₁ h₂)
      (backgroundReflectionSign_cases c₁ c₂ h₁ h₂)
      (isometryMatrix_backgroundReflection_det_sign c₁ c₂ h₁ h₂)).trans
    ((V.backgroundReflected c₁ c₂ h₁ h₂).castDeltaTransport
      (backgroundFactor_fls_eq X c₁ c₂ h₁ h₂)))


-- @@ L2086-2113 verbatim
@[simp] theorem backgroundDeltaTransport_orbitEquiv_coe
    (V : TamedField X) (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (O : V.OrbitIndex) :
    (((V.backgroundDeltaTransport c₁ c₂ h₁ h₂).orbitEquiv O :
      (V.backgroundTransport c₁ c₂ h₁ h₂).OrbitIndex) : Set E) = O := by
  let a := backgroundScale c₁ c₂
  let ha : 0 < a := backgroundScale_pos_F h₁ h₂
  let q := backgroundReflection c₁ c₂ h₁ h₂
  let ε := backgroundReflectionSign c₁ c₂ h₁ h₂
  let hε : ε = 1 ∨ ε = -1 := backgroundReflectionSign_cases c₁ c₂ h₁ h₂
  let hdet : (isometryMatrix q).det = ε :=
    isometryMatrix_backgroundReflection_det_sign c₁ c₂ h₁ h₂
  let V₁ := V.positiveScale a ha
  let V₂ := V₁.codomainIsometry q ε hε hdet
  let hX := backgroundFactor_fls_eq X c₁ c₂ h₁ h₂
  change ((V₂.castOrbitEquiv hX
    (V₁.codomainIsometryOrbitEquiv q ε hε hdet
      (V.positiveScaleOrbitEquiv a ha O)) : (V₂.cast hX).OrbitIndex) : Set E) = O
  calc
    ((V₂.castOrbitEquiv hX
        (V₁.codomainIsometryOrbitEquiv q ε hε hdet
          (V.positiveScaleOrbitEquiv a ha O)) : (V₂.cast hX).OrbitIndex) : Set E) =
        ((V₁.codomainIsometryOrbitEquiv q ε hε hdet
          (V.positiveScaleOrbitEquiv a ha O) : V₂.OrbitIndex) : Set E) :=
      V₂.castOrbitEquiv_coe hX _
    _ = ((V.positiveScaleOrbitEquiv a ha O : V₁.OrbitIndex) : Set E) :=
      V₁.codomainIsometryOrbitEquiv_coe q ε hε hdet _
    _ = O := V.positiveScaleOrbitEquiv_coe a ha O


-- @@ L2115-2148 verbatim
theorem backgroundTransport_orbitFrameClass
    (V : TamedField X) (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (O : V.OrbitIndex) :
    V.orbitFrameClass O =
      (V.backgroundTransport c₁ c₂ h₁ h₂).orbitFrameClass
        ((V.backgroundDeltaTransport c₁ c₂ h₁ h₂).orbitEquiv O) := by
  let a := backgroundScale c₁ c₂
  let ha : 0 < a := backgroundScale_pos_F h₁ h₂
  let q := backgroundReflection c₁ c₂ h₁ h₂
  let ε := backgroundReflectionSign c₁ c₂ h₁ h₂
  let hε : ε = 1 ∨ ε = -1 := backgroundReflectionSign_cases c₁ c₂ h₁ h₂
  let hdet : (isometryMatrix q).det = ε :=
    isometryMatrix_backgroundReflection_det_sign c₁ c₂ h₁ h₂
  let V₁ := V.positiveScale a ha
  let V₂ := V₁.codomainIsometry q ε hε hdet
  let hX := backgroundFactor_fls_eq X c₁ c₂ h₁ h₂
  change V.orbitFrameClass O =
    (V₂.cast hX).orbitFrameClass
      (V₂.castOrbitEquiv hX
        (V₁.codomainIsometryOrbitEquiv q ε hε hdet
          (V.positiveScaleOrbitEquiv a ha O)))
  calc
    V.orbitFrameClass O =
        V₁.orbitFrameClass (V.positiveScaleOrbitEquiv a ha O) :=
      V.positiveScale_orbitFrameClass a ha O
    _ = V₂.orbitFrameClass
        (V₁.codomainIsometryOrbitEquiv q ε hε hdet
          (V.positiveScaleOrbitEquiv a ha O)) :=
      V₁.codomainIsometry_orbitFrameClass q ε hε hdet _
    _ = (V₂.cast hX).orbitFrameClass
        (V₂.castOrbitEquiv hX
          (V₁.codomainIsometryOrbitEquiv q ε hε hdet
            (V.positiveScaleOrbitEquiv a ha O))) :=
      V₂.cast_orbitFrameClass hX _


-- @@ L2150-2150 verbatim
end BackgroundTransport


-- @@ L2152-2152 verbatim
end TamedField


-- @@ L2154-2154 verbatim
namespace FiberSign


-- @@ L2156-2161 verbatim
theorem codomainEquiv_trans_heq {X : FramedLevelSet n} (S : FiberSign X)
    (e₁ e₂ : F ≃L[ℝ] F) :
    HEq ((S.codomainEquiv e₁).codomainEquiv e₂)
      (S.codomainEquiv (e₁.trans e₂)) := by
  apply FiberSign.heq_of_eq_toFun (X.codomainEquiv_trans e₁ e₂)
  rfl


-- @@ L2163-2168 verbatim
theorem positiveDelta_codomainEquiv_trans {X : FramedLevelSet n} (S : FiberSign X)
    (e₁ e₂ : F ≃L[ℝ] F) :
    ((S.codomainEquiv e₁).codomainEquiv e₂).positiveDelta =
      (S.codomainEquiv (e₁.trans e₂)).positiveDelta :=
  FiberSign.positiveDelta_eq_of_heq (X.codomainEquiv_trans e₁ e₂)
    (S.codomainEquiv_trans_heq e₁ e₂)


-- @@ L2170-2184 verbatim
/-- The signed component ledger is unchanged by the actual background equivalence. -/
theorem positiveFramedDelta_backgroundEquiv {X : FramedLevelSet n} (S : FiberSign X)
    (V : TamedField X) (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    S.positiveFramedDelta V =
      (S.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂)).positiveFramedDelta
        (V.backgroundTransport c₁ c₂ h₁ h₂) := by
  let W := V.backgroundTransport c₁ c₂ h₁ h₂
  let T := V.backgroundDeltaTransport c₁ c₂ h₁ h₂
  apply V.deltaOn_eq_of_transport T
  intro O
  change (O : Set E) ⊆ S.positivePart ↔
    ((T.orbitEquiv O : W.OrbitIndex) : Set E) ⊆
      (S.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂)).positivePart
  rw [S.positivePart_codomainEquiv,
    V.backgroundDeltaTransport_orbitEquiv_coe c₁ c₂ h₁ h₂ O]


-- @@ L2186-2211 verbatim
theorem positiveDelta_backgroundEquiv {X : FramedLevelSet n} (S : FiberSign X)
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (S.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂)).positiveDelta =
      S.positiveDelta := by
  let a := backgroundScale c₁ c₂
  let ha : 0 < a := backgroundScale_pos_F h₁ h₂
  let e₁ : F ≃L[ℝ] F := positiveScaleEquiv a ha
  let q := backgroundReflection c₁ c₂ h₁ h₂
  have he : backgroundEquiv c₁ c₂ h₁ h₂ =
      e₁.trans q.toContinuousLinearEquiv :=
    backgroundEquiv_eq_scale_trans_reflection c₁ c₂ h₁ h₂
  rw [he]
  rw [← S.positiveDelta_codomainEquiv_trans e₁ q.toContinuousLinearEquiv]
  by_cases hu : backgroundDifference c₁ c₂ h₁ h₂ = 0
  · have hdet : (isometryMatrix q).det = 1 := by
      simpa [q, hu] using
        isometryMatrix_backgroundReflection_det c₁ c₂ h₁ h₂
    rw [(S.codomainEquiv e₁).positiveDelta_codomainIsometry q 1
      (Or.inl rfl) hdet]
    exact S.positiveDelta_positiveScale a ha
  · have hdet : (isometryMatrix q).det = -1 := by
      simpa [q, hu] using
        isometryMatrix_backgroundReflection_det c₁ c₂ h₁ h₂
    rw [(S.codomainEquiv e₁).positiveDelta_codomainIsometry q (-1)
      (Or.inr rfl) hdet]
    exact S.positiveDelta_positiveScale a ha


-- @@ L2213-2219 verbatim
theorem negativeDelta_backgroundEquiv {X : FramedLevelSet n} (S : FiberSign X)
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (S.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂)).negativeDelta =
      S.negativeDelta := by
  unfold negativeDelta
  rw [S.codomainEquiv_neg]
  exact S.neg.positiveDelta_backgroundEquiv c₁ c₂ h₁ h₂


-- @@ L2221-2221 verbatim
end FiberSign


-- @@ L2223-2223 verbatim
namespace ZeroFramedConfiguration


-- @@ L2225-2225 verbatim
variable (m : ℕ)


-- @@ L2227-2231 verbatim
/-- The transported tamed field on the harmonized class-zero presentation. -/
abbrev harmonizedTamedField (V : TamedField (X m)) : TamedField (harmonizedX m) :=
  V.backgroundTransport (bridge m).flatBackground
    (CompactBirth.background (m + 1)) (flatBackground_ne_zero m)
    (CompactBirth.background_ne_zero (m + 1))


-- @@ L2233-2238 verbatim
/-- The orbit-component ledger for `toCompactBirthBackground`. -/
def harmonizedDeltaTransport (V : TamedField (X m)) :
    V.DeltaTransport (harmonizedTamedField m V) :=
  V.backgroundDeltaTransport (bridge m).flatBackground
    (CompactBirth.background (m + 1)) (flatBackground_ne_zero m)
    (CompactBirth.background_ne_zero (m + 1))


-- @@ L2240-2245 verbatim
@[simp] theorem harmonizedDeltaTransport_orbitEquiv_coe
    (V : TamedField (X m)) (O : V.OrbitIndex) :
    (((harmonizedDeltaTransport m V).orbitEquiv O :
      (harmonizedTamedField m V).OrbitIndex) :
      Set (EuclideanSpace ℝ (Fin (m + 3)))) = O := by
  exact V.backgroundDeltaTransport_orbitEquiv_coe _ _ _ _ O


-- @@ L2247-2251 verbatim
theorem harmonized_orbitFrameClass (V : TamedField (X m)) (O : V.OrbitIndex) :
    V.orbitFrameClass O =
      (harmonizedTamedField m V).orbitFrameClass
        ((harmonizedDeltaTransport m V).orbitEquiv O) := by
  exact V.backgroundTransport_orbitFrameClass _ _ _ _ O


-- @@ L2253-2255 verbatim
theorem harmonized_positiveDelta :
    (harmonizedSign m).positiveDelta = (sign m).positiveDelta := by
  exact (sign m).positiveDelta_backgroundEquiv _ _ _ _


-- @@ L2257-2259 verbatim
theorem harmonized_negativeDelta :
    (harmonizedSign m).negativeDelta = (sign m).negativeDelta := by
  exact (sign m).negativeDelta_backgroundEquiv _ _ _ _


-- @@ L2261-2261 verbatim
end ZeroFramedConfiguration


-- @@ L2263-2263 verbatim
end Submission
