import Mathlib
import Submission.FramedMorseDefiniteNormalLimit
import Submission.FramedMorseDefiniteFrameLinearization
import Submission.CodomainEquivDelta


-- @@ L6-15 verbatim
/-!
# The full limiting frame at a definite Morse center

At a definite critical point the spatial derivative has a two-dimensional
kernel and an `m`-dimensional range, where the output dimension is `m + 1`.
This file chooses an orthonormal basis of that range, pulls it back by the
adjoint to obtain the `m` transverse normal rows, and adjoins the angular and
rescaled normal rows.  The center pairing calculation then proves that the
resulting `m + 2` rows form a basis.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Set Function Filter InnerProductSpace Matrix

-- @@ L20-20 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L22-22 verbatim
namespace Submission


-- @@ L24-24 verbatim
set_option autoImplicit false

-- @@ L25-25 verbatim
set_option maxHeartbeats 800000


-- @@ L27-27 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L29-29 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L31-31 verbatim
variable {m : ℕ}

-- @@ L32-32 verbatim
variable {C : FramedLevelCobordism (m + 1)} {ι : Type*} [Fintype ι]

-- @@ L33-33 verbatim
variable {B : FiniteIFTSurfaceCover C ι}

-- @@ L34-34 verbatim
variable {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L36-36 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (m + 2))

-- @@ L37-37 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L38-38 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 1))


-- @@ L40-57 verbatim
/-- A choice of orthonormal basis of the actual spatial range at the critical
center.  Its cardinality is exactly `m`. -/
def criticalTransverseRangeBasis
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    OrthonormalBasis (Fin m) ℝ
      (LinearMap.range
        (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
          (R.criticalCenter p)).toLinearMap) := by
  let C' := R.amplitude.toVerticalAmplitude.pullback C
  let center := R.criticalCenter p
  let K := LinearMap.range (spatialDeriv C'.G center).toLinearMap
  have hcenter : center ∈ timeCritical C'.G :=
    R.criticalCenter_mem_timeCritical p hp
  have hdim : Module.finrank ℝ K = m := by
    simpa [K] using
      (finrank_range_spatialDeriv_of_mem_timeCritical C' hcenter)
  exact (stdOrthonormalBasis ℝ K).reindex (finCongr hdim)


-- @@ L59-70 verbatim
/-- The adjoint of the spatial derivative, restricted to its range. -/
def criticalAdjointOnRange
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) :
    (LinearMap.range
        (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
          (R.criticalCenter p)).toLinearMap) →ₗ[ℝ] E₁ where
  toFun y := ContinuousLinearMap.adjoint
    (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalCenter p)) y.1
  map_add' y z := by simp
  map_smul' a y := by simp


-- @@ L72-78 verbatim
/-- Pull the range basis back by the adjoint.  These are the nondegenerating
normal rows at the critical center. -/
def criticalTransverseNormal
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (i : Fin m) : E₁ :=
  R.criticalAdjointOnRange p (R.criticalTransverseRangeBasis p hp i)


-- @@ L80-105 verbatim
/-- The adjoint is injective when restricted to the range of the original
map. -/
theorem criticalAdjointOnRange_injective
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) :
    Injective (R.criticalAdjointOnRange p) := by
  let A := spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
    (R.criticalCenter p)
  intro y z hyz
  have hadj : ContinuousLinearMap.adjoint A (y.1 - z.1) = 0 := by
    change R.criticalAdjointOnRange p (y - z) = 0
    rw [map_sub, hyz, sub_self]
  have hyrange : y.1 - z.1 ∈ LinearMap.range A.toLinearMap := by
    exact sub_mem y.2 z.2
  obtain ⟨x, hx⟩ := hyrange
  have hself : ⟪y.1 - z.1, y.1 - z.1⟫_ℝ = 0 := by
    calc
      ⟪y.1 - z.1, y.1 - z.1⟫_ℝ = ⟪y.1 - z.1, A x⟫_ℝ := by
        congr 1
        exact hx.symm
      _ = ⟪ContinuousLinearMap.adjoint A (y.1 - z.1), x⟫_ℝ := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ = 0 := by rw [hadj, inner_zero_left]
  have hsub : y.1 - z.1 = 0 := inner_self_eq_zero.mp hself
  apply Subtype.ext
  exact sub_eq_zero.mp hsub


-- @@ L107-120 verbatim
/-- The `m` transverse rows are linearly independent. -/
theorem linearIndependent_criticalTransverseNormal
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    LinearIndependent ℝ (R.criticalTransverseNormal p hp) := by
  let b := R.criticalTransverseRangeBasis p hp
  have hb : LinearIndependent ℝ (fun i => b i) :=
    b.toBasis.linearIndependent
  have hker : (R.criticalAdjointOnRange p).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (R.criticalAdjointOnRange_injective p)
  have hmapped := hb.map' (R.criticalAdjointOnRange p) hker
  change LinearIndependent ℝ (fun i =>
    R.criticalAdjointOnRange p (R.criticalTransverseRangeBasis p hp i))
  simpa [b, Function.comp_def] using hmapped


-- @@ L122-122 verbatim
/-! ## The transverse rows annihilate the center tangent plane -/


-- @@ L124-146 verbatim
/-- Every parameter direction at the Morse origin maps into the kernel of the
spatial derivative. -/
theorem spatialDeriv_criticalSurfaceSpatialTangent_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (w : E₂) :
    spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalCenter p)
        (R.criticalSurfaceSpatialTangent p hp 0 w) = 0 := by
  have hzero : ‖(0 : E₂)‖ < (R.criticalModelShrink p hp).radius := by
    simpa using (R.criticalModelShrink p hp).radius_pos
  have hmodel :
      fderiv ℝ (fun z : E₂ =>
        G.localSeparatedTime p p.2 +
          morseQuadratic (G.localMorseNormalForm p hp).index (z 0, z 1))
        0 w = 0 := by
    rw [fderiv_const_add_morseQuadratic_apply]
    cases (G.localMorseNormalForm p hp).index <;>
      simp [morseHessianPairing]
  have h := R.spatialDeriv_criticalSurfaceParam_eq_zero_of_model_tangent
    p hp 0 hzero w hmodel
  simpa [criticalSurfaceSpatialTangent,
    R.criticalSurfaceParam_zero p hp] using h


-- @@ L148-162 verbatim
/-- The full installed surface tangent has zero time component at the Morse
origin. -/
theorem tcoord_fderiv_criticalSurfaceParam_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (w : E₂) :
    tcoord (fderiv ℝ (R.criticalSurfaceParam p hp) 0 w) = 0 := by
  have hzero : ‖(0 : E₂)‖ < (R.criticalModelShrink p hp).radius := by
    simpa using (R.criticalModelShrink p hp).radius_pos
  rw [← R.fderiv_criticalSurfaceParam_time_apply p hp 0 hzero w]
  have hmodel := congrArg (fun L : E₂ →L[ℝ] ℝ => L w)
    (R.fderiv_criticalSurfaceParam_time p hp 0 hzero)
  rw [hmodel, fderiv_const_add_morseQuadratic_apply]
  cases (G.localMorseNormalForm p hp).index <;>
    simp [morseHessianPairing]


-- @@ L164-195 verbatim
/-- The spatial differential of the surface parameter is injective at the
critical origin. -/
theorem criticalSurfaceSpatialTangent_zero_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    {w : E₂} (hw : w ≠ 0) :
    R.criticalSurfaceSpatialTangent p hp 0 w ≠ 0 := by
  obtain ⟨r, hr, _hrle, hinj⟩ :=
    R.exists_criticalSurfaceParam_injective_radius p hp
  have hzeroRadius : ‖(0 : E₂)‖ < r := by simpa using hr
  have hfullinj : Injective
      (fderiv ℝ (R.criticalSurfaceParam p hp) 0) := hinj 0 hzeroRadius
  intro hspace
  change spacePart (fderiv ℝ (R.criticalSurfaceParam p hp) 0 w) = 0 at hspace
  let z := fderiv ℝ (R.criticalSurfaceParam p hp) 0 w
  have htime : tcoord z = 0 := by
    exact R.tcoord_fderiv_criticalSurfaceParam_zero p hp w
  have hz : z = 0 := by
    calc
      z = cobSpaceTime (spacePart z) (tcoord z) :=
        (spaceTime_spacePart z).symm
      _ = cobSpaceTime 0 0 := by rw [hspace, htime]
      _ = 0 := by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [spaceTime_apply_last]
          rfl
        · rw [spaceTime_apply_castSucc]
          rfl
  apply hw
  apply hfullinj
  simpa [z] using hz


-- @@ L197-204 verbatim
theorem criticalDefiniteUnitTangent_zero_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalDefiniteUnitTangent p hp 0 theta ≠ 0 := by
  rw [← R.criticalSurfaceSpatialTangent_zero_tangent_eq p hp theta]
  exact R.criticalSurfaceSpatialTangent_zero_ne_zero p hp
    (definiteCircleTangentParam_unit_ne_zero theta)


-- @@ L206-221 verbatim
/-- Every transverse adjoint row is orthogonal to the transported center
tangent plane. -/
theorem inner_criticalTransverseNormal_surfaceTangent_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (i : Fin m) (w : E₂) :
    ⟪R.criticalTransverseNormal p hp i,
      R.criticalSurfaceSpatialTangent p hp 0 w⟫_ℝ = 0 := by
  let A := spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
    (R.criticalCenter p)
  change ⟪ContinuousLinearMap.adjoint A
      (R.criticalTransverseRangeBasis p hp i : F),
    R.criticalSurfaceSpatialTangent p hp 0 w⟫_ℝ = 0
  rw [ContinuousLinearMap.adjoint_inner_left,
    R.spatialDeriv_criticalSurfaceSpatialTangent_zero p hp w,
    inner_zero_right]


-- @@ L223-230 verbatim
theorem inner_criticalTransverseNormal_radial_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (i : Fin m) (theta : ℝ) :
    ⟪R.criticalTransverseNormal p hp i,
      R.criticalDefiniteRadialTangent p hp theta⟫_ℝ = 0 := by
  exact R.inner_criticalTransverseNormal_surfaceTangent_zero p hp i
    (definiteCircleParam 1 theta)


-- @@ L232-240 verbatim
theorem inner_criticalTransverseNormal_unitTangent_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (i : Fin m) (theta : ℝ) :
    ⟪R.criticalTransverseNormal p hp i,
      R.criticalDefiniteUnitTangent p hp 0 theta⟫_ℝ = 0 := by
  rw [← R.criticalSurfaceSpatialTangent_zero_tangent_eq p hp theta]
  exact R.inner_criticalTransverseNormal_surfaceTangent_zero p hp i
    (definiteCircleTangentParam 1 theta)


-- @@ L242-242 verbatim
/-! ## The full center rows are a basis -/


-- @@ L244-249 verbatim
/-- Abstract row-ordering used below: tangent first, then all persistent
transverse normals, and the rescaled normal last. -/
def centerRowsWith
    (transverse : Fin m → E₁) (tangent normal : E₁) :
    Fin (m + 2) → E₁ :=
  Fin.cons tangent (Fin.snoc transverse normal)


-- @@ L251-303 verbatim
/-- A pairing criterion tailored to the center block.  The radial test vector
kills every transverse row and detects the last row; the tangent itself then
kills the remaining last/transverse block and detects the first row. -/
theorem linearIndependent_centerRowsWith
    (transverse : Fin m → E₁) (tangent normal radial : E₁)
    (htransverse : LinearIndependent ℝ transverse)
    (htangent : tangent ≠ 0)
    (htransverseTangent : ∀ i, ⟪transverse i, tangent⟫_ℝ = 0)
    (htransverseRadial : ∀ i, ⟪transverse i, radial⟫_ℝ = 0)
    (hnormalTangent : ⟪normal, tangent⟫_ℝ = 0)
    (hnormalRadial : ⟪normal, radial⟫_ℝ ≠ 0) :
    LinearIndependent ℝ (centerRowsWith transverse tangent normal) := by
  have hnormalSpan : normal ∉ Submodule.span ℝ (Set.range transverse) := by
    intro hmem
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    have hpair : ⟪normal, radial⟫_ℝ = 0 := by
      calc
        ⟪normal, radial⟫_ℝ =
            ⟪∑ i, c i • transverse i, radial⟫_ℝ := by rw [hc]
        _ = ∑ i, ⟪c i • transverse i, radial⟫_ℝ := by rw [sum_inner]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _hi
          rw [real_inner_smul_left, htransverseRadial i, mul_zero]
    exact hnormalRadial hpair
  have htail : LinearIndependent ℝ (Fin.snoc transverse normal) :=
    linearIndependent_fin_snoc.mpr ⟨htransverse, hnormalSpan⟩
  have htangentSpan :
      tangent ∉ Submodule.span ℝ (Set.range (Fin.snoc transverse normal)) := by
    intro hmem
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    have hrowPair : ∀ i : Fin (m + 1),
        ⟪(Fin.snoc transverse normal : Fin (m + 1) → E₁) i,
          tangent⟫_ℝ = 0 := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hnormalTangent
      · simpa only [Fin.snoc_castSucc] using htransverseTangent j
    have hself : ⟪tangent, tangent⟫_ℝ = 0 := by
      calc
        ⟪tangent, tangent⟫_ℝ =
            ⟪∑ i, c i • Fin.snoc transverse normal i, tangent⟫_ℝ := by
              rw [hc]
        _ = ∑ i, ⟪c i • Fin.snoc transverse normal i, tangent⟫_ℝ := by
              rw [sum_inner]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _hi
          rw [real_inner_smul_left, hrowPair i, mul_zero]
    exact htangent (inner_self_eq_zero.mp hself)
  exact linearIndependent_fin_cons.mpr ⟨htail, htangentSpan⟩


-- @@ L305-361 verbatim
/-- A more flexible test-vector criterion.  Unlike
`linearIndependent_centerRowsWith`, this does not require the last row to be
orthogonal to the tangent; it only requires one vector that annihilates the
whole preceding block and detects the last row. -/
theorem linearIndependent_centerRowsWith_test
    (transverse : Fin m → E₁) (tangent last test : E₁)
    (htransverse : LinearIndependent ℝ transverse)
    (htangent : tangent ≠ 0)
    (htransverseTangent : ∀ i, ⟪transverse i, tangent⟫_ℝ = 0)
    (htransverseTest : ∀ i, ⟪transverse i, test⟫_ℝ = 0)
    (htangentTest : ⟪tangent, test⟫_ℝ = 0)
    (hlastTest : ⟪last, test⟫_ℝ ≠ 0) :
    LinearIndependent ℝ (centerRowsWith transverse tangent last) := by
  have htangentSpan : tangent ∉ Submodule.span ℝ (Set.range transverse) := by
    intro hmem
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    have hself : ⟪tangent, tangent⟫_ℝ = 0 := by
      calc
        ⟪tangent, tangent⟫_ℝ =
            ⟪∑ i, c i • transverse i, tangent⟫_ℝ := by rw [hc]
        _ = ∑ i, ⟪c i • transverse i, tangent⟫_ℝ := by rw [sum_inner]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _hi
          rw [real_inner_smul_left, htransverseTangent i, mul_zero]
    exact htangent (inner_self_eq_zero.mp hself)
  have hfront : LinearIndependent ℝ (Fin.cons tangent transverse) :=
    linearIndependent_fin_cons.mpr ⟨htransverse, htangentSpan⟩
  have hlastSpan :
      last ∉ Submodule.span ℝ (Set.range (Fin.cons tangent transverse)) := by
    intro hmem
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    have hfrontPair : ∀ i : Fin (m + 1),
        ⟪(Fin.cons tangent transverse : Fin (m + 1) → E₁) i,
          test⟫_ℝ = 0 := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using htangentTest
      · simpa only [Fin.cons_succ] using htransverseTest j
    have hpair : ⟪last, test⟫_ℝ = 0 := by
      calc
        ⟪last, test⟫_ℝ =
            ⟪∑ i, c i • Fin.cons tangent transverse i, test⟫_ℝ := by rw [hc]
        _ = ∑ i, ⟪c i • Fin.cons tangent transverse i, test⟫_ℝ := by
              rw [sum_inner]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _hi
          rw [real_inner_smul_left, hfrontPair i, mul_zero]
    exact hlastTest hpair
  have hsnoc : LinearIndependent ℝ
      (Fin.snoc (Fin.cons tangent transverse) last) :=
    linearIndependent_fin_snoc.mpr ⟨hfront, hlastSpan⟩
  rw [centerRowsWith, Fin.cons_snoc_eq_snoc_cons]
  exact hsnoc


-- @@ L363-365 verbatim
/-- Remove the tangent component of a radial vector. -/
def tangentOrthogonalRadial (tangent radial : E₁) : E₁ :=
  radial - (⟪radial, tangent⟫_ℝ / ⟪tangent, tangent⟫_ℝ) • tangent


-- @@ L367-376 verbatim
theorem inner_tangent_tangentOrthogonalRadial
    (tangent radial : E₁) (htangent : tangent ≠ 0) :
    ⟪tangent, tangentOrthogonalRadial tangent radial⟫_ℝ = 0 := by
  have hself : ⟪tangent, tangent⟫_ℝ ≠ 0 := by
    intro h
    exact htangent (inner_self_eq_zero.mp h)
  rw [tangentOrthogonalRadial, inner_sub_right, real_inner_smul_right,
    real_inner_comm tangent radial]
  field_simp
  ring


-- @@ L378-384 verbatim
theorem inner_left_tangentOrthogonalRadial_eq
    (tangent radial left : E₁)
    (hleft : ⟪left, tangent⟫_ℝ = 0) :
    ⟪left, tangentOrthogonalRadial tangent radial⟫_ℝ =
      ⟪left, radial⟫_ℝ := by
  rw [tangentOrthogonalRadial, inner_sub_right, real_inner_smul_right,
    hleft, mul_zero, sub_zero]


-- @@ L386-405 verbatim
theorem inner_radial_tangentOrthogonalRadial_eq_self
    (tangent radial : E₁) (htangent : tangent ≠ 0) :
    ⟪radial, tangentOrthogonalRadial tangent radial⟫_ℝ =
      ⟪tangentOrthogonalRadial tangent radial,
        tangentOrthogonalRadial tangent radial⟫_ℝ := by
  let q := tangentOrthogonalRadial tangent radial
  let c := ⟪radial, tangent⟫_ℝ / ⟪tangent, tangent⟫_ℝ
  have hq : ⟪tangent, q⟫_ℝ = 0 :=
    inner_tangent_tangentOrthogonalRadial tangent radial htangent
  have hdecomp : radial = q + c • tangent := by
    dsimp [q, c, tangentOrthogonalRadial]
    module
  have hcalc : ⟪radial, q⟫_ℝ = ⟪q, q⟫_ℝ := by
    calc
      ⟪radial, q⟫_ℝ = ⟪q + c • tangent, q⟫_ℝ :=
        congrArg (fun x : E₁ => ⟪x, q⟫_ℝ) hdecomp
      _ = ⟪q, q⟫_ℝ + c * ⟪tangent, q⟫_ℝ := by
        rw [inner_add_left, real_inner_smul_left]
      _ = ⟪q, q⟫_ℝ := by rw [hq, mul_zero, add_zero]
  simpa [q] using hcalc


-- @@ L407-408 verbatim
/-- The sign `±1` that turns a nonzero scalar into a positive one. -/
def nonzeroOrientationSign (x : ℝ) : ℝ := if 0 < x then 1 else -1


-- @@ L410-413 verbatim
theorem nonzeroOrientationSign_eq_one_or_neg_one (x : ℝ) :
    nonzeroOrientationSign x = 1 ∨ nonzeroOrientationSign x = -1 := by
  unfold nonzeroOrientationSign
  split_ifs <;> simp


-- @@ L415-418 verbatim
theorem nonzeroOrientationSign_ne_zero (x : ℝ) :
    nonzeroOrientationSign x ≠ 0 := by
  rcases nonzeroOrientationSign_eq_one_or_neg_one x with h | h <;>
    rw [h] <;> norm_num


-- @@ L420-426 verbatim
theorem nonzeroOrientationSign_mul_pos {x : ℝ} (hx : x ≠ 0) :
    0 < nonzeroOrientationSign x * x := by
  unfold nonzeroOrientationSign
  split_ifs with hpos
  · simpa using hpos
  · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx
    simpa using neg_pos.mpr hneg


-- @@ L428-435 verbatim
/-- Center rows for a minimum, using the counterclockwise angular tangent. -/
def criticalMinimumCenterRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) : Fin (m + 2) → E₁ :=
  centerRowsWith (R.criticalTransverseNormal p hp)
    (R.criticalDefiniteUnitTangent p hp 0 theta)
    (R.criticalDefiniteNormalRow p hp 0 theta)


-- @@ L437-445 verbatim
/-- Center rows for a maximum.  The clockwise tangent is the boundary
orientation of the shrinking pre-death disk. -/
def criticalMaximumCenterRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) : Fin (m + 2) → E₁ :=
  centerRowsWith (R.criticalTransverseNormal p hp)
    (R.criticalDefiniteUnitTangentRev p hp 0 theta)
    (R.criticalDefiniteNormalRow p hp 0 theta)


-- @@ L447-463 verbatim
theorem linearIndependent_criticalMinimumCenterRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    LinearIndependent ℝ (R.criticalMinimumCenterRows p hp theta) := by
  apply linearIndependent_centerRowsWith
  · exact R.linearIndependent_criticalTransverseNormal p hp
  · exact R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta
  · intro i
    exact R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta
  · intro i
    exact R.inner_criticalTransverseNormal_radial_zero p hp i theta
  · exact R.inner_criticalDefiniteNormalRow_zero_unitTangent_minimum
      p hp hindex theta
  · exact R.inner_criticalDefiniteNormalRow_zero_radial_minimum_ne_zero
      p hp hindex theta


-- @@ L465-486 verbatim
theorem linearIndependent_criticalMaximumCenterRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    LinearIndependent ℝ (R.criticalMaximumCenterRows p hp theta) := by
  apply linearIndependent_centerRowsWith
  · exact R.linearIndependent_criticalTransverseNormal p hp
  · exact neg_ne_zero.mpr
      (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta)
  · intro i
    rw [criticalDefiniteUnitTangentRev, inner_neg_right,
      R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta,
      neg_zero]
  · intro i
    exact R.inner_criticalTransverseNormal_radial_zero p hp i theta
  · rw [criticalDefiniteUnitTangentRev, inner_neg_right,
      R.inner_criticalDefiniteNormalRow_zero_unitTangent_maximum
        p hp hindex theta,
      neg_zero]
  · exact R.inner_criticalDefiniteNormalRow_zero_radial_maximum_ne_zero
      p hp hindex theta


-- @@ L488-493 verbatim
/-- The raw limiting center matrix for a minimum. -/
def criticalMinimumCenterMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  rowsMatrix (R.criticalMinimumCenterRows p hp theta)


-- @@ L495-500 verbatim
/-- The raw limiting center matrix for a maximum. -/
def criticalMaximumCenterMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  rowsMatrix (R.criticalMaximumCenterRows p hp theta)


-- @@ L502-515 verbatim
theorem det_criticalMinimumCenterMatrix_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    (R.criticalMinimumCenterMatrix p hp theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (R.criticalMinimumCenterMatrix p hp theta).row :=
    (linearIndependent_rowsMatrix_iff
      (R.criticalMinimumCenterRows p hp theta)).mpr
      (R.linearIndependent_criticalMinimumCenterRows p hp hindex theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L517-530 verbatim
theorem det_criticalMaximumCenterMatrix_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    (R.criticalMaximumCenterMatrix p hp theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (R.criticalMaximumCenterMatrix p hp theta).row :=
    (linearIndependent_rowsMatrix_iff
      (R.criticalMaximumCenterRows p hp theta)).mpr
      (R.linearIndependent_criticalMaximumCenterRows p hp hindex theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L532-532 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L534-534 verbatim
end Submission
