import Mathlib
import Submission.OrbitUnknottingSmoothOrbit
import Submission.SOGramSchmidtSmooth


-- @@ L5-17 verbatim
/-!
# A smooth framed tube along an intrinsic orbit

The framed level-set data gives a canonical full frame along every orbit: the
unit tangent followed by the gradients of the defining map.  Smooth
Gram--Schmidt turns this into a smooth orthonormal frame.  Its last `n`
vectors define a periodic normal-coordinate map around the orbit.

This file constructs that tube map and computes its derivative on the zero
section.  The derivative is the scaled tangent together with the orthonormal
normal frame, which is the exact input needed for the local inverse function
theorem.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false

-- @@ L20-20 verbatim
set_option maxHeartbeats 800000


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set Function Module Finset InnerProductSpace

-- @@ L25-25 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L27-27 verbatim
namespace Submission

-- @@ L28-28 verbatim
namespace TamedField


-- @@ L30-30 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L32-32 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L33-33 verbatim
local notation "N" => EuclideanSpace ℝ (Fin n)


-- @@ L35-49 verbatim
/-- Every vector in the canonical frame is smooth along the rescaled orbit
lift. -/
theorem contDiff_frameAt_intrinsicOrbitLift (O : V.OrbitIndex)
    (i : Fin (n + 1)) :
    ContDiff ℝ ∞ (fun u => frameAt X (V.intrinsicOrbitLift O u) i) := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · change ContDiff ℝ ∞ (tauField X.g ∘ V.intrinsicOrbitLift O)
    exact (contDiffOn_tauField X.smooth).comp_contDiff
      (V.contDiff_intrinsicOrbitLift O) fun u =>
        X.fiber_subset_regularSet
          (V.flow_mem_fiber (V.orbitPoint_mem_fiber O)
            (u * V.orbitPeriod O))
  · change ContDiff ℝ ∞ (gradVec X.g j ∘ V.intrinsicOrbitLift O)
    exact (contDiff_gradVec X.g X.smooth j).comp
      (V.contDiff_intrinsicOrbitLift O)


-- @@ L51-67 verbatim
/-- Smoothness survives normalized Gram--Schmidt along the orbit because the
framed level-set vectors are linearly independent at every fiber point. -/
theorem contDiff_orbitFrameVector (O : V.OrbitIndex) (i : Fin (n + 1)) :
    ContDiff ℝ ∞ (fun u =>
      gramSchmidtNormed ℝ (frameAt X (V.intrinsicOrbitLift O u)) i) := by
  let A : ℝ → Fin (n + 1) → E := fun u j =>
    frameAt X (V.intrinsicOrbitLift O u) j
  have hA : ∀ j, ContDiff ℝ ∞ (fun u => A u j) := by
    intro j
    exact V.contDiff_frameAt_intrinsicOrbitLift O j
  have hInd : ∀ u, LinearIndependent ℝ (A u) := by
    intro u
    exact linearIndependent_frameAt X (X.fiber_subset_regularSet
      (V.flow_mem_fiber (V.orbitPoint_mem_fiber O)
        (u * V.orbitPeriod O)))
  exact contDiff_gramSchmidtNormed_family
    (T := ℝ) (m := n + 1) (A := A) hA hInd i


-- @@ L69-83 verbatim
/-- The first Gram--Schmidt vector is the already normalized unit tangent. -/
theorem orbitFrameVector_zero (O : V.OrbitIndex) (u : ℝ) :
    gramSchmidtNormed ℝ (frameAt X (V.intrinsicOrbitLift O u)) 0 =
      tauField X.g (V.intrinsicOrbitLift O u) := by
  have hmem : V.intrinsicOrbitLift O u ∈ X.fiber :=
    V.flow_mem_fiber (V.orbitPoint_mem_fiber O) (u * V.orbitPeriod O)
  have hnorm : ‖tauField X.g (V.intrinsicOrbitLift O u)‖ = 1 :=
    norm_tauField (X.fiber_subset_regularSet hmem)
  change gramSchmidtNormed ℝ
      (frameAt X (V.intrinsicOrbitLift O u)) (⊥ : Fin (n + 1)) = _
  rw [gramSchmidtNormed, gramSchmidt_bot]
  change ‖tauField X.g (V.intrinsicOrbitLift O u)‖⁻¹ •
      tauField X.g (V.intrinsicOrbitLift O u) = _
  rw [hnorm]
  simp


-- @@ L85-87 verbatim
/-- One vector of the smooth orthonormal frame along the orbit. -/
def orbitFrameVector (O : V.OrbitIndex) (i : Fin (n + 1)) (u : ℝ) : E :=
  gramSchmidtNormed ℝ (frameAt X (V.intrinsicOrbitLift O u)) i


-- @@ L89-91 verbatim
/-- The `j`-th normal vector, namely row `j+1` of the orthonormal frame. -/
def orbitNormal (O : V.OrbitIndex) (j : Fin n) (u : ℝ) : E :=
  V.orbitFrameVector O j.succ u


-- @@ L93-95 verbatim
theorem contDiff_orbitNormal (O : V.OrbitIndex) (j : Fin n) :
    ContDiff ℝ ∞ (V.orbitNormal O j) := by
  exact V.contDiff_orbitFrameVector O j.succ


-- @@ L97-101 verbatim
/-- The framed tube lift over `ℝ × ℝⁿ`.  Periodicity in the first coordinate
will later descend it to `AddCircle 1 × ℝⁿ`. -/
def orbitTubeLift (O : V.OrbitIndex) (q : ℝ × N) : E :=
  V.intrinsicOrbitLift O q.1 +
    ∑ j : Fin n, q.2 j • V.orbitNormal O j q.1


-- @@ L103-109 verbatim
theorem contDiff_orbitTubeLift (O : V.OrbitIndex) :
    ContDiff ℝ ∞ (V.orbitTubeLift O) := by
  apply (V.contDiff_intrinsicOrbitLift O).comp contDiff_fst |>.add
  apply ContDiff.sum
  intro j _
  exact ((EuclideanSpace.proj j).contDiff.comp contDiff_snd).smul
    ((V.contDiff_orbitNormal O j).comp contDiff_fst)


-- @@ L111-113 verbatim
@[simp] theorem orbitTubeLift_zero (O : V.OrbitIndex) (u : ℝ) :
    V.orbitTubeLift O (u, 0) = V.intrinsicOrbitLift O u := by
  simp [orbitTubeLift]


-- @@ L115-125 verbatim
/-- The whole framed tube lift is period one, not only its zero section. -/
theorem periodic_orbitTubeLift (O : V.OrbitIndex) (z : N) :
    Function.Periodic (fun u => V.orbitTubeLift O (u, z)) 1 := by
  intro u
  simp only [orbitTubeLift]
  rw [V.periodic_intrinsicOrbitLift O u]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp [orbitNormal, orbitFrameVector, V.periodic_intrinsicOrbitLift O u]


-- @@ L127-138 verbatim
/-- The expected derivative of the tube map on the zero section: the first
parameter maps to the positively scaled unit tangent, while the remaining
parameters map to the normal frame. -/
def orbitTubeDeriv (O : V.OrbitIndex) (u : ℝ) :
    (ℝ × N) →L[ℝ] E :=
  (ContinuousLinearMap.toSpanSingleton ℝ
      (V.orbitPeriod O • V.v (V.intrinsicOrbitLift O u))).comp
      (ContinuousLinearMap.fst ℝ ℝ N) +
    ∑ j : Fin n,
      (((EuclideanSpace.proj j).comp
        (ContinuousLinearMap.snd ℝ ℝ N)).smulRight
          (V.orbitNormal O j u))


-- @@ L140-144 verbatim
@[simp] theorem orbitTubeDeriv_apply (O : V.OrbitIndex) (u a : ℝ) (z : N) :
    V.orbitTubeDeriv O u (a, z) =
      a • (V.orbitPeriod O • V.v (V.intrinsicOrbitLift O u)) +
        ∑ j : Fin n, z j • V.orbitNormal O j u := by
  simp [orbitTubeDeriv]


-- @@ L146-200 verbatim
/-- The explicit linear map above is the actual derivative of the tube map at
every point of its zero section. -/
theorem hasFDerivAt_orbitTubeLift_zero (O : V.OrbitIndex) (u : ℝ) :
    HasFDerivAt (V.orbitTubeLift O) (V.orbitTubeDeriv O u) (u, 0) := by
  have houter : HasFDerivAt (V.intrinsicOrbitLift O)
      (ContinuousLinearMap.toSpanSingleton ℝ
        (V.orbitPeriod O • V.v (V.intrinsicOrbitLift O u))) u :=
    (V.hasDerivAt_intrinsicOrbitLift O u).hasFDerivAt
  have hfst : HasFDerivAt (fun q : ℝ × N => q.1)
      (ContinuousLinearMap.fst ℝ ℝ N) (u, 0) :=
    hasFDerivAt_fst
  have hbase : HasFDerivAt
      (fun q : ℝ × N => V.intrinsicOrbitLift O q.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (V.orbitPeriod O • V.v (V.intrinsicOrbitLift O u))).comp
        (ContinuousLinearMap.fst ℝ ℝ N)) (u, 0) := by
    change HasFDerivAt
      (V.intrinsicOrbitLift O ∘ fun q : ℝ × N => q.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (V.orbitPeriod O • V.v (V.intrinsicOrbitLift O u))).comp
        (ContinuousLinearMap.fst ℝ ℝ N)) (u, 0)
    exact houter.comp (f := fun q : ℝ × N => q.1)
      (g := V.intrinsicOrbitLift O) (u, 0) hfst
  have hnormal' : HasFDerivAt
      (∑ j : Fin n, fun q : ℝ × N =>
        q.2 j • V.orbitNormal O j q.1)
      (∑ j : Fin n,
        (((EuclideanSpace.proj j).comp
          (ContinuousLinearMap.snd ℝ ℝ N)).smulRight
            (V.orbitNormal O j u))) (u, 0) := by
    apply HasFDerivAt.sum
    intro j _
    have hc := ((EuclideanSpace.proj j).comp
      (ContinuousLinearMap.snd ℝ ℝ N)).hasFDerivAt
      (x := (u, (0 : N)))
    have hN : HasFDerivAt
        (fun q : ℝ × N => V.orbitNormal O j q.1)
        (fderiv ℝ (fun q : ℝ × N => V.orbitNormal O j q.1) (u, 0))
        (u, 0) :=
      ((V.contDiff_orbitNormal O j).comp contDiff_fst).differentiable
        (by simp) (u, 0) |>.hasFDerivAt
    convert hc.smul hN using 1
    · rfl
    · simp
  have hnormal : HasFDerivAt
      (fun q : ℝ × N =>
        ∑ j : Fin n, q.2 j • V.orbitNormal O j q.1)
      (∑ j : Fin n,
        (((EuclideanSpace.proj j).comp
          (ContinuousLinearMap.snd ℝ ℝ N)).smulRight
            (V.orbitNormal O j u))) (u, 0) := by
    convert hnormal' using 1
    funext q
    simp
  exact hbase.add hnormal


-- @@ L202-265 verbatim
/-- The derivative of the tube map is invertible all along the zero section:
its columns are the positive multiple of the unit tangent followed by an
orthonormal normal basis. -/
theorem orbitTubeDeriv_bijective (O : V.OrbitIndex) (u : ℝ) :
    Function.Bijective (V.orbitTubeDeriv O u) := by
  let B : Fin (n + 1) → E := fun i => V.orbitFrameVector O i u
  have hmem : V.intrinsicOrbitLift O u ∈ X.fiber :=
    V.flow_mem_fiber (V.orbitPoint_mem_fiber O) (u * V.orbitPeriod O)
  have hInd : LinearIndependent ℝ (frameAt X (V.intrinsicOrbitLift O u)) :=
    linearIndependent_frameAt X (X.fiber_subset_regularSet hmem)
  have horth : Orthonormal ℝ B := gramSchmidtNormed_orthonormal hInd
  have hinner : ∀ i j, ⟪B i, B j⟫_ℝ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp horth
  have hv : V.v (V.intrinsicOrbitLift O u) = B 0 := by
    rw [V.v_eq_tau_of_mem_fiber hmem]
    exact (V.orbitFrameVector_zero O u).symm
  have hinj : Function.Injective (V.orbitTubeDeriv O u) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, z⟩ hzero
    have hformula :
        a • (V.orbitPeriod O • B 0) +
          ∑ j : Fin n, z j • B j.succ = 0 := by
      simpa [hv, orbitNormal] using hzero
    have haeq : a * V.orbitPeriod O = 0 := by
      have h := congrArg (fun x : E => ⟪B 0, x⟫_ℝ) hformula
      simp only [inner_add_right, real_inner_smul_right, inner_sum,
        inner_zero_right] at h
      rw [hinner 0 0] at h
      have hsum : ∑ j : Fin n, z j * ⟪B 0, B j.succ⟫_ℝ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hinner 0 j.succ]
        rw [if_neg (Ne.symm j.succ_ne_zero)]
        simp
      rw [hsum, add_zero] at h
      simpa [smul_eq_mul] using h
    have ha : a = 0 :=
      (mul_eq_zero.mp haeq).resolve_right (ne_of_gt (V.orbitPeriod_pos O))
    have hz : z = 0 := by
      ext j
      have h := congrArg (fun x : E => ⟪B j.succ, x⟫_ℝ) hformula
      simp only [inner_add_right, real_inner_smul_right, inner_sum,
        inner_zero_right] at h
      rw [ha, zero_mul, zero_add] at h
      have hsum :
          ∑ k : Fin n, z k * ⟪B j.succ, B k.succ⟫_ℝ = z j := by
        rw [Finset.sum_eq_single j]
        · rw [hinner j.succ j.succ]
          simp
        · intro k _ hkj
          rw [hinner j.succ k.succ]
          have hjk : j ≠ k := Ne.symm hkj
          rw [if_neg ((Fin.succ_injective n).ne hjk)]
          simp
        · simp
      rw [hsum] at h
      simpa using h
    exact Prod.ext ha hz
  refine ⟨hinj, ?_⟩
  have hfr : finrank ℝ (ℝ × N) = finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_self,
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj


-- @@ L267-272 verbatim
/-- The center derivative as a continuous linear equivalence. -/
def orbitTubeDerivEquiv (O : V.OrbitIndex) (u : ℝ) :
    (ℝ × N) ≃L[ℝ] E :=
  (LinearEquiv.ofBijective
      ((V.orbitTubeDeriv O u) : (ℝ × N) →ₗ[ℝ] E)
      (V.orbitTubeDeriv_bijective O u)).toContinuousLinearEquiv


-- @@ L274-279 verbatim
@[simp] theorem orbitTubeDerivEquiv_coe (O : V.OrbitIndex) (u : ℝ) :
    (V.orbitTubeDerivEquiv O u : (ℝ × N) →L[ℝ] E) =
      V.orbitTubeDeriv O u := by
  apply ContinuousLinearMap.ext
  intro q
  rfl


-- @@ L281-290 verbatim
/-- The local inverse-function-theorem chart of the framed tube at phase `u`.
Its underlying forward map is exactly `orbitTubeLift`. -/
def orbitTubeLocalHomeomorph (O : V.OrbitIndex) (u : ℝ) :
    OpenPartialHomeomorph (ℝ × N) E :=
  (V.contDiff_orbitTubeLift O).contDiffAt.toOpenPartialHomeomorph
    (V.orbitTubeLift O)
    (by
      rw [V.orbitTubeDerivEquiv_coe O u]
      exact V.hasFDerivAt_orbitTubeLift_zero O u)
    (by simp)


-- @@ L292-295 verbatim
@[simp] theorem orbitTubeLocalHomeomorph_coe (O : V.OrbitIndex) (u : ℝ) :
    (V.orbitTubeLocalHomeomorph O u : (ℝ × N) → E) =
      V.orbitTubeLift O := by
  rfl


-- @@ L297-304 verbatim
theorem orbitTube_center_mem_localSource (O : V.OrbitIndex) (u : ℝ) :
    (u, (0 : N)) ∈ (V.orbitTubeLocalHomeomorph O u).source := by
  exact (V.contDiff_orbitTubeLift O).contDiffAt
    |>.mem_toOpenPartialHomeomorph_source
      (by
        rw [V.orbitTubeDerivEquiv_coe O u]
        exact V.hasFDerivAt_orbitTubeLift_zero O u)
      (by simp)


-- @@ L306-311 verbatim
/-- The tube map is injective on its IFT source neighborhood. -/
theorem orbitTube_injOn_localSource (O : V.OrbitIndex) (u : ℝ) :
    Set.InjOn (V.orbitTubeLift O)
      (V.orbitTubeLocalHomeomorph O u).source := by
  rw [← V.orbitTubeLocalHomeomorph_coe O u]
  exact (V.orbitTubeLocalHomeomorph O u).injOn


-- @@ L313-313 verbatim
end TamedField

-- @@ L314-314 verbatim
end Submission
