import Mathlib
import Submission.FramedMorseDefiniteCenterFrame


-- @@ L4-10 verbatim
/-!
# The stable class of the definite center frame

This file deforms the rescaled center normal row to the transported radial
row through nonsingular frames.  The radial endpoint is a fixed linear image
of the elementary first/last-plane rotation, so its stable loop class is one.
-/


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
open Set Function Filter InnerProductSpace Matrix

-- @@ L15-15 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L17-17 verbatim
namespace Submission


-- @@ L19-19 verbatim
set_option autoImplicit false

-- @@ L20-20 verbatim
set_option maxHeartbeats 1600000


-- @@ L22-22 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L24-24 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L26-26 verbatim
variable {m : ℕ}

-- @@ L27-27 verbatim
variable {C : FramedLevelCobordism (m + 1)} {ι : Type*} [Fintype ι]

-- @@ L28-28 verbatim
variable {B : FiniteIFTSurfaceCover C ι}

-- @@ L29-29 verbatim
variable {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L31-31 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L33-33 verbatim
/-! ## The radial comparison frame -/


-- @@ L35-41 verbatim
def criticalMinimumRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) : Fin (m + 2) → E₁ :=
  centerRowsWith (R.criticalTransverseNormal p hp)
    (R.criticalDefiniteUnitTangent p hp 0 theta)
    (R.criticalDefiniteRadialTangent p hp theta)


-- @@ L43-49 verbatim
def criticalMaximumRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) : Fin (m + 2) → E₁ :=
  centerRowsWith (R.criticalTransverseNormal p hp)
    (R.criticalDefiniteUnitTangentRev p hp 0 theta)
    (R.criticalDefiniteRadialTangent p hp theta)


-- @@ L51-59 verbatim
/-- Orthogonal complement of the angular tangent inside the transported
radial direction, for a minimum. -/
def criticalMinimumRadialTest
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) : E₁ :=
  tangentOrthogonalRadial
    (R.criticalDefiniteUnitTangent p hp 0 theta)
    (R.criticalDefiniteRadialTangent p hp theta)


-- @@ L61-68 verbatim
/-- The analogous test vector for the clockwise maximum tangent. -/
def criticalMaximumRadialTest
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) : E₁ :=
  tangentOrthogonalRadial
    (R.criticalDefiniteUnitTangentRev p hp 0 theta)
    (R.criticalDefiniteRadialTangent p hp theta)


-- @@ L70-77 verbatim
theorem inner_criticalMinimumTangent_radialTest
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    ⟪R.criticalDefiniteUnitTangent p hp 0 theta,
      R.criticalMinimumRadialTest p hp theta⟫_ℝ = 0 := by
  exact inner_tangent_tangentOrthogonalRadial _ _
    (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta)


-- @@ L79-86 verbatim
theorem inner_criticalMaximumTangent_radialTest
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    ⟪R.criticalDefiniteUnitTangentRev p hp 0 theta,
      R.criticalMaximumRadialTest p hp theta⟫_ℝ = 0 := by
  exact inner_tangent_tangentOrthogonalRadial _ _
    (neg_ne_zero.mpr (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta))


-- @@ L88-97 verbatim
theorem inner_criticalTransverseNormal_minimumRadialTest
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (i : Fin m) (theta : ℝ) :
    ⟪R.criticalTransverseNormal p hp i,
      R.criticalMinimumRadialTest p hp theta⟫_ℝ = 0 := by
  rw [criticalMinimumRadialTest,
    inner_left_tangentOrthogonalRadial_eq _ _ _
      (R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta),
    R.inner_criticalTransverseNormal_radial_zero p hp i theta]


-- @@ L99-112 verbatim
theorem inner_criticalTransverseNormal_maximumRadialTest
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (i : Fin m) (theta : ℝ) :
    ⟪R.criticalTransverseNormal p hp i,
      R.criticalMaximumRadialTest p hp theta⟫_ℝ = 0 := by
  have htan : ⟪R.criticalTransverseNormal p hp i,
      R.criticalDefiniteUnitTangentRev p hp 0 theta⟫_ℝ = 0 := by
    rw [criticalDefiniteUnitTangentRev, inner_neg_right,
      R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta,
      neg_zero]
  rw [criticalMaximumRadialTest,
    inner_left_tangentOrthogonalRadial_eq _ _ _ htan,
    R.inner_criticalTransverseNormal_radial_zero p hp i theta]


-- @@ L114-127 verbatim
theorem inner_criticalNormal_minimumRadialTest
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalMinimumRadialTest p hp theta⟫_ℝ =
      -(2 * R.criticalDefiniteTimeNormalCoefficient p hp) := by
  rw [criticalMinimumRadialTest,
    inner_left_tangentOrthogonalRadial_eq _ _ _
      (R.inner_criticalDefiniteNormalRow_zero_unitTangent_minimum
        p hp hindex theta)]
  exact R.inner_criticalDefiniteNormalRow_zero_radial_minimum
    p hp hindex theta


-- @@ L129-146 verbatim
theorem inner_criticalNormal_maximumRadialTest
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalMaximumRadialTest p hp theta⟫_ℝ =
      2 * R.criticalDefiniteTimeNormalCoefficient p hp := by
  have htan : ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalDefiniteUnitTangentRev p hp 0 theta⟫_ℝ = 0 := by
    rw [criticalDefiniteUnitTangentRev, inner_neg_right,
      R.inner_criticalDefiniteNormalRow_zero_unitTangent_maximum
        p hp hindex theta,
      neg_zero]
  rw [criticalMaximumRadialTest,
    inner_left_tangentOrthogonalRadial_eq _ _ _ htan]
  exact R.inner_criticalDefiniteNormalRow_zero_radial_maximum
    p hp hindex theta


-- @@ L148-159 verbatim
theorem criticalMinimumRadialTest_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    R.criticalMinimumRadialTest p hp theta ≠ 0 := by
  intro hzero
  have hpair := R.inner_criticalNormal_minimumRadialTest
    p hp hindex theta
  rw [hzero, inner_zero_right] at hpair
  exact (R.criticalDefiniteTimeNormalCoefficient_ne_zero p hp) (by
    nlinarith)


-- @@ L161-172 verbatim
theorem criticalMaximumRadialTest_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    R.criticalMaximumRadialTest p hp theta ≠ 0 := by
  intro hzero
  have hpair := R.inner_criticalNormal_maximumRadialTest
    p hp hindex theta
  rw [hzero, inner_zero_right] at hpair
  exact (R.criticalDefiniteTimeNormalCoefficient_ne_zero p hp) (by
    nlinarith)


-- @@ L174-186 verbatim
theorem inner_criticalRadial_minimumRadialTest_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteRadialTangent p hp theta,
      R.criticalMinimumRadialTest p hp theta⟫_ℝ ≠ 0 := by
  rw [criticalMinimumRadialTest,
    inner_radial_tangentOrthogonalRadial_eq_self _ _
      (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta)]
  intro hzero
  exact R.criticalMinimumRadialTest_ne_zero p hp hindex theta
    (inner_self_eq_zero.mp hzero)


-- @@ L188-203 verbatim
theorem inner_criticalRadial_maximumRadialTest_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteRadialTangent p hp theta,
      R.criticalMaximumRadialTest p hp theta⟫_ℝ ≠ 0 := by
  have htangent : R.criticalDefiniteUnitTangentRev p hp 0 theta ≠ 0 := by
    exact neg_ne_zero.mpr
      (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta)
  rw [criticalMaximumRadialTest,
    inner_radial_tangentOrthogonalRadial_eq_self _ _
      htangent]
  intro hzero
  exact R.criticalMaximumRadialTest_ne_zero p hp hindex theta
    (inner_self_eq_zero.mp hzero)


-- @@ L205-220 verbatim
theorem linearIndependent_criticalMinimumRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    LinearIndependent ℝ (R.criticalMinimumRadialRows p hp theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact R.linearIndependent_criticalTransverseNormal p hp
  · exact R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta
  · intro i
    exact R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta
  · intro i
    exact R.inner_criticalTransverseNormal_minimumRadialTest p hp i theta
  · exact R.inner_criticalMinimumTangent_radialTest p hp theta
  · exact R.inner_criticalRadial_minimumRadialTest_ne_zero
      p hp hindex theta


-- @@ L222-240 verbatim
theorem linearIndependent_criticalMaximumRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    LinearIndependent ℝ (R.criticalMaximumRadialRows p hp theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact R.linearIndependent_criticalTransverseNormal p hp
  · exact neg_ne_zero.mpr
      (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta)
  · intro i
    rw [criticalDefiniteUnitTangentRev, inner_neg_right,
      R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta,
      neg_zero]
  · intro i
    exact R.inner_criticalTransverseNormal_maximumRadialTest p hp i theta
  · exact R.inner_criticalMaximumTangent_radialTest p hp theta
  · exact R.inner_criticalRadial_maximumRadialTest_ne_zero
      p hp hindex theta


-- @@ L242-242 verbatim
/-! ## Nonsingular normal-to-radial deformation -/


-- @@ L244-247 verbatim
def criticalMinimumCenterPairingScalar
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) : ℝ :=
  -(2 * R.criticalDefiniteTimeNormalCoefficient p hp)


-- @@ L249-252 verbatim
def criticalMaximumCenterPairingScalar
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) : ℝ :=
  2 * R.criticalDefiniteTimeNormalCoefficient p hp


-- @@ L254-259 verbatim
theorem criticalMinimumCenterPairingScalar_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalMinimumCenterPairingScalar p hp ≠ 0 := by
  exact neg_ne_zero.mpr (mul_ne_zero (by norm_num)
    (R.criticalDefiniteTimeNormalCoefficient_ne_zero p hp))


-- @@ L261-266 verbatim
theorem criticalMaximumCenterPairingScalar_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalMaximumCenterPairingScalar p hp ≠ 0 := by
  exact mul_ne_zero (by norm_num)
    (R.criticalDefiniteTimeNormalCoefficient_ne_zero p hp)


-- @@ L268-277 verbatim
/-- The last row in the minimum deformation.  At `s = 0` it is the normal
row with its pairing sign corrected; at `s = 1` it is the radial row. -/
def criticalMinimumNormalRadialLast
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : E₁ :=
  (1 - (s : ℝ)) •
      (nonzeroOrientationSign (R.criticalMinimumCenterPairingScalar p hp) •
        R.criticalDefiniteNormalRow p hp 0 theta) +
    (s : ℝ) • R.criticalDefiniteRadialTangent p hp theta


-- @@ L279-287 verbatim
/-- The corresponding last row for a maximum. -/
def criticalMaximumNormalRadialLast
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : E₁ :=
  (1 - (s : ℝ)) •
      (nonzeroOrientationSign (R.criticalMaximumCenterPairingScalar p hp) •
        R.criticalDefiniteNormalRow p hp 0 theta) +
    (s : ℝ) • R.criticalDefiniteRadialTangent p hp theta


-- @@ L289-295 verbatim
def criticalMinimumNormalRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : Fin (m + 2) → E₁ :=
  centerRowsWith (R.criticalTransverseNormal p hp)
    (R.criticalDefiniteUnitTangent p hp 0 theta)
    (R.criticalMinimumNormalRadialLast p hp s theta)


-- @@ L297-303 verbatim
def criticalMaximumNormalRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : Fin (m + 2) → E₁ :=
  centerRowsWith (R.criticalTransverseNormal p hp)
    (R.criticalDefiniteUnitTangentRev p hp 0 theta)
    (R.criticalMaximumNormalRadialLast p hp s theta)


-- @@ L305-316 verbatim
@[simp] theorem criticalMinimumNormalRadialRows_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalMinimumNormalRadialRows p hp 0 theta =
      centerRowsWith (R.criticalTransverseNormal p hp)
        (R.criticalDefiniteUnitTangent p hp 0 theta)
        (nonzeroOrientationSign
            (R.criticalMinimumCenterPairingScalar p hp) •
          R.criticalDefiniteNormalRow p hp 0 theta) := by
  simp [criticalMinimumNormalRadialRows,
    criticalMinimumNormalRadialLast]


-- @@ L318-325 verbatim
@[simp] theorem criticalMinimumNormalRadialRows_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalMinimumNormalRadialRows p hp 1 theta =
      R.criticalMinimumRadialRows p hp theta := by
  simp [criticalMinimumNormalRadialRows,
    criticalMinimumNormalRadialLast, criticalMinimumRadialRows]


-- @@ L327-338 verbatim
@[simp] theorem criticalMaximumNormalRadialRows_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalMaximumNormalRadialRows p hp 0 theta =
      centerRowsWith (R.criticalTransverseNormal p hp)
        (R.criticalDefiniteUnitTangentRev p hp 0 theta)
        (nonzeroOrientationSign
            (R.criticalMaximumCenterPairingScalar p hp) •
          R.criticalDefiniteNormalRow p hp 0 theta) := by
  simp [criticalMaximumNormalRadialRows,
    criticalMaximumNormalRadialLast]


-- @@ L340-347 verbatim
@[simp] theorem criticalMaximumNormalRadialRows_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalMaximumNormalRadialRows p hp 1 theta =
      R.criticalMaximumRadialRows p hp theta := by
  simp [criticalMaximumNormalRadialRows,
    criticalMaximumNormalRadialLast, criticalMaximumRadialRows]


-- @@ L349-384 verbatim
theorem inner_criticalMinimumNormalRadialLast_radialTest_pos
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) (theta : ℝ) :
    0 < ⟪R.criticalMinimumNormalRadialLast p hp s theta,
      R.criticalMinimumRadialTest p hp theta⟫_ℝ := by
  have hpair : ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalMinimumRadialTest p hp theta⟫_ℝ =
      R.criticalMinimumCenterPairingScalar p hp := by
    exact R.inner_criticalNormal_minimumRadialTest p hp hindex theta
  have hnormal : 0 < nonzeroOrientationSign
        (R.criticalMinimumCenterPairingScalar p hp) *
      R.criticalMinimumCenterPairingScalar p hp :=
    nonzeroOrientationSign_mul_pos
      (R.criticalMinimumCenterPairingScalar_ne_zero p hp)
  have hradialEq := inner_radial_tangentOrthogonalRadial_eq_self
    (R.criticalDefiniteUnitTangent p hp 0 theta)
    (R.criticalDefiniteRadialTangent p hp theta)
    (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta)
  have hradial : 0 < ⟪R.criticalDefiniteRadialTangent p hp theta,
      R.criticalMinimumRadialTest p hp theta⟫_ℝ := by
    rw [criticalMinimumRadialTest, hradialEq]
    exact real_inner_self_pos.mpr
      (R.criticalMinimumRadialTest_ne_zero p hp hindex theta)
  rw [criticalMinimumNormalRadialLast, inner_add_left,
    real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, hpair]
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hsone : (s : ℝ) = 1
  · simpa [hsone] using hradial
  have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hs1 hsone
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr hslt) hnormal)
    (mul_nonneg hs0 hradial.le)


-- @@ L386-423 verbatim
theorem inner_criticalMaximumNormalRadialLast_radialTest_pos
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) (theta : ℝ) :
    0 < ⟪R.criticalMaximumNormalRadialLast p hp s theta,
      R.criticalMaximumRadialTest p hp theta⟫_ℝ := by
  have hpair : ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalMaximumRadialTest p hp theta⟫_ℝ =
      R.criticalMaximumCenterPairingScalar p hp := by
    exact R.inner_criticalNormal_maximumRadialTest p hp hindex theta
  have hnormal : 0 < nonzeroOrientationSign
        (R.criticalMaximumCenterPairingScalar p hp) *
      R.criticalMaximumCenterPairingScalar p hp :=
    nonzeroOrientationSign_mul_pos
      (R.criticalMaximumCenterPairingScalar_ne_zero p hp)
  have htangent : R.criticalDefiniteUnitTangentRev p hp 0 theta ≠ 0 := by
    exact neg_ne_zero.mpr
      (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta)
  have hradialEq := inner_radial_tangentOrthogonalRadial_eq_self
    (R.criticalDefiniteUnitTangentRev p hp 0 theta)
    (R.criticalDefiniteRadialTangent p hp theta) htangent
  have hradial : 0 < ⟪R.criticalDefiniteRadialTangent p hp theta,
      R.criticalMaximumRadialTest p hp theta⟫_ℝ := by
    rw [criticalMaximumRadialTest, hradialEq]
    exact real_inner_self_pos.mpr
      (R.criticalMaximumRadialTest_ne_zero p hp hindex theta)
  rw [criticalMaximumNormalRadialLast, inner_add_left,
    real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, hpair]
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hsone : (s : ℝ) = 1
  · simpa [hsone] using hradial
  have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hs1 hsone
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr hslt) hnormal)
    (mul_nonneg hs0 hradial.le)


-- @@ L425-442 verbatim
theorem linearIndependent_criticalMinimumNormalRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) (theta : ℝ) :
    LinearIndependent ℝ
      (R.criticalMinimumNormalRadialRows p hp s theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact R.linearIndependent_criticalTransverseNormal p hp
  · exact R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta
  · intro i
    exact R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta
  · intro i
    exact R.inner_criticalTransverseNormal_minimumRadialTest p hp i theta
  · exact R.inner_criticalMinimumTangent_radialTest p hp theta
  · exact ne_of_gt
      (R.inner_criticalMinimumNormalRadialLast_radialTest_pos
        p hp hindex s theta)


-- @@ L444-464 verbatim
theorem linearIndependent_criticalMaximumNormalRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) (theta : ℝ) :
    LinearIndependent ℝ
      (R.criticalMaximumNormalRadialRows p hp s theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact R.linearIndependent_criticalTransverseNormal p hp
  · exact neg_ne_zero.mpr
      (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta)
  · intro i
    rw [criticalDefiniteUnitTangentRev, inner_neg_right,
      R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta,
      neg_zero]
  · intro i
    exact R.inner_criticalTransverseNormal_maximumRadialTest p hp i theta
  · exact R.inner_criticalMaximumTangent_radialTest p hp theta
  · exact ne_of_gt
      (R.inner_criticalMaximumNormalRadialLast_radialTest_pos
        p hp hindex s theta)


-- @@ L466-470 verbatim
def criticalMinimumNormalRadialMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  rowsMatrix (R.criticalMinimumNormalRadialRows p hp s theta)


-- @@ L472-476 verbatim
def criticalMaximumNormalRadialMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  rowsMatrix (R.criticalMaximumNormalRadialRows p hp s theta)


-- @@ L478-492 verbatim
theorem det_criticalMinimumNormalRadialMatrix_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) (theta : ℝ) :
    (R.criticalMinimumNormalRadialMatrix p hp s theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (R.criticalMinimumNormalRadialMatrix p hp s theta).row :=
    (linearIndependent_rowsMatrix_iff
      (R.criticalMinimumNormalRadialRows p hp s theta)).mpr
      (R.linearIndependent_criticalMinimumNormalRadialRows
        p hp hindex s theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L494-508 verbatim
theorem det_criticalMaximumNormalRadialMatrix_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) (theta : ℝ) :
    (R.criticalMaximumNormalRadialMatrix p hp s theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (R.criticalMaximumNormalRadialMatrix p hp s theta).row :=
    (linearIndependent_rowsMatrix_iff
      (R.criticalMaximumNormalRadialRows p hp s theta)).mpr
      (R.linearIndependent_criticalMaximumNormalRadialRows
        p hp hindex s theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L510-510 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L512-524 verbatim
/-! ## Oriented radial factorization and the class-one center loop

The preceding deformation is nonsingular, but its radial endpoint still
contains the arbitrary linear embedding of the Morse parameter plane and the
arbitrary transverse range basis.  We now remove that constant ambiguity.

For a cobordism of dimension `a + 2`, the center frame has size `a + 3`, so
the standard birth loop acts in its first/last row plane.  We first orient the
angular row by the same fixed sign as the literal standard birth frame.  We
then multiply on the right by the inverse of the radial frame at angle zero.
The normalized radial endpoint is therefore *exactly* the standard birth
plane rotation, not merely homotopic to it.
-/


-- @@ L526-526 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L528-528 verbatim
variable {a : ℕ}

-- @@ L529-529 verbatim
variable {C : FramedLevelCobordism (a + 2)} {ι : Type*} [Fintype ι]

-- @@ L530-530 verbatim
variable {B : FiniteIFTSurfaceCover C ι}

-- @@ L531-531 verbatim
variable {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L533-533 verbatim
local notation "E₁a" => EuclideanSpace ℝ (Fin (a + 3))


-- @@ L535-535 verbatim
/-! ### Rotation identities in the transported Morse plane -/


-- @@ L537-544 verbatim
theorem definiteCircleTangentParam_unit_rotation (theta : ℝ) :
    definiteCircleTangentParam 1 theta =
      Real.cos theta • definiteCircleTangentParam 1 0 -
        Real.sin theta • definiteCircleParam 1 0 := by
  ext i
  fin_cases i <;>
    simp [definiteCircleTangentParam, definiteCircleParam,
      pairToMorseParam]


-- @@ L546-553 verbatim
theorem definiteCircleParam_unit_rotation (theta : ℝ) :
    definiteCircleParam 1 theta =
      Real.sin theta • definiteCircleTangentParam 1 0 +
        Real.cos theta • definiteCircleParam 1 0 := by
  ext i
  fin_cases i <;>
    simp [definiteCircleTangentParam, definiteCircleParam,
      pairToMorseParam]


-- @@ L555-571 verbatim
theorem criticalDefiniteUnitTangent_zero_rotation
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalDefiniteUnitTangent p hp 0 theta =
      Real.cos theta • R.criticalDefiniteUnitTangent p hp 0 0 -
        Real.sin theta • R.criticalDefiniteRadialTangent p hp 0 := by
  rw [← R.criticalSurfaceSpatialTangent_zero_tangent_eq p hp theta,
    ← R.criticalSurfaceSpatialTangent_zero_tangent_eq p hp 0]
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] E₁a :=
    criticalSpacePartCLM.comp
      (fderiv ℝ (R.criticalSurfaceParam p hp) 0)
  change L (definiteCircleTangentParam 1 theta) =
    Real.cos theta • L (definiteCircleTangentParam 1 0) -
      Real.sin theta • L (definiteCircleParam 1 0)
  rw [definiteCircleTangentParam_unit_rotation, map_sub,
    map_smul, map_smul]


-- @@ L573-587 verbatim
theorem criticalDefiniteRadialTangent_rotation
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalDefiniteRadialTangent p hp theta =
      Real.sin theta • R.criticalDefiniteUnitTangent p hp 0 0 +
        Real.cos theta • R.criticalDefiniteRadialTangent p hp 0 := by
  rw [← R.criticalSurfaceSpatialTangent_zero_tangent_eq p hp 0]
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] E₁a :=
    criticalSpacePartCLM.comp
      (fderiv ℝ (R.criticalSurfaceParam p hp) 0)
  change L (definiteCircleParam 1 theta) =
    Real.sin theta • L (definiteCircleTangentParam 1 0) +
      Real.cos theta • L (definiteCircleParam 1 0)
  rw [definiteCircleParam_unit_rotation, map_add, map_smul, map_smul]


-- @@ L589-589 verbatim
/-! ### The oriented center deformation -/


-- @@ L591-600 verbatim
/-- The minimum center deformation with the angular row oriented exactly as
the literal standard-birth angular row. -/
def criticalMinimumOrientedNormalRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : Fin (a + 3) → E₁a :=
  centerRowsWith (R.criticalTransverseNormal p hp)
    (StandardBirth.orientationSign a •
      R.criticalDefiniteUnitTangent p hp 0 theta)
    (R.criticalMinimumNormalRadialLast p hp s theta)


-- @@ L602-612 verbatim
/-- At a maximum the boundary tangent is clockwise.  Multiplying it by the
opposite standard-birth sign gives the same oriented angular row as at a
minimum, so both definite events have the same normalized radial endpoint. -/
def criticalMaximumOrientedNormalRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : Fin (a + 3) → E₁a :=
  centerRowsWith (R.criticalTransverseNormal p hp)
    ((-StandardBirth.orientationSign a) •
      R.criticalDefiniteUnitTangentRev p hp 0 theta)
    (R.criticalMaximumNormalRadialLast p hp s theta)


-- @@ L614-618 verbatim
def criticalMinimumOrientedNormalRadialMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (R.criticalMinimumOrientedNormalRadialRows p hp s theta)


-- @@ L620-624 verbatim
def criticalMaximumOrientedNormalRadialMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (R.criticalMaximumOrientedNormalRadialRows p hp s theta)


-- @@ L626-633 verbatim
@[simp] theorem criticalMinimumOrientedNormalRadialRows_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) :
    R.criticalMinimumOrientedNormalRadialRows p hp s theta 0 =
      StandardBirth.orientationSign a •
        R.criticalDefiniteUnitTangent p hp 0 theta := by
  simp [criticalMinimumOrientedNormalRadialRows, centerRowsWith]


-- @@ L635-642 verbatim
@[simp] theorem criticalMinimumOrientedNormalRadialRows_last
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) :
    R.criticalMinimumOrientedNormalRadialRows p hp s theta
        (Fin.last (a + 2)) =
      R.criticalMinimumNormalRadialLast p hp s theta := by
  simp [criticalMinimumOrientedNormalRadialRows, centerRowsWith]


-- @@ L644-651 verbatim
@[simp] theorem criticalMinimumOrientedNormalRadialRows_middle
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (s : I) (theta : ℝ) (i : Fin (a + 1)) :
    R.criticalMinimumOrientedNormalRadialRows p hp s theta
        i.castSucc.succ =
      R.criticalTransverseNormal p hp i := by
  simp [criticalMinimumOrientedNormalRadialRows, centerRowsWith]


-- @@ L653-675 verbatim
theorem linearIndependent_criticalMinimumOrientedNormalRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) (theta : ℝ) :
    LinearIndependent ℝ
      (R.criticalMinimumOrientedNormalRadialRows p hp s theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact R.linearIndependent_criticalTransverseNormal p hp
  · exact smul_ne_zero
      (StandardBirth.orientationSign_ne_zero a)
      (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta)
  · intro i
    rw [real_inner_smul_right,
      R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta,
      mul_zero]
  · intro i
    exact R.inner_criticalTransverseNormal_minimumRadialTest p hp i theta
  · rw [real_inner_smul_left,
      R.inner_criticalMinimumTangent_radialTest p hp theta, mul_zero]
  · exact ne_of_gt
      (R.inner_criticalMinimumNormalRadialLast_radialTest_pos
        p hp hindex s theta)


-- @@ L677-701 verbatim
theorem linearIndependent_criticalMaximumOrientedNormalRadialRows
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) (theta : ℝ) :
    LinearIndependent ℝ
      (R.criticalMaximumOrientedNormalRadialRows p hp s theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact R.linearIndependent_criticalTransverseNormal p hp
  · exact smul_ne_zero
      (neg_ne_zero.mpr (StandardBirth.orientationSign_ne_zero a))
      (neg_ne_zero.mpr
        (R.criticalDefiniteUnitTangent_zero_ne_zero p hp theta))
  · intro i
    rw [real_inner_smul_right, criticalDefiniteUnitTangentRev,
      inner_neg_right,
      R.inner_criticalTransverseNormal_unitTangent_zero p hp i theta,
      neg_zero, mul_zero]
  · intro i
    exact R.inner_criticalTransverseNormal_maximumRadialTest p hp i theta
  · rw [real_inner_smul_left,
      R.inner_criticalMaximumTangent_radialTest p hp theta, mul_zero]
  · exact ne_of_gt
      (R.inner_criticalMaximumNormalRadialLast_radialTest_pos
        p hp hindex s theta)


-- @@ L703-717 verbatim
theorem det_criticalMinimumOrientedNormalRadialMatrix_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) (theta : ℝ) :
    (R.criticalMinimumOrientedNormalRadialMatrix p hp s theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (R.criticalMinimumOrientedNormalRadialMatrix p hp s theta).row :=
    (linearIndependent_rowsMatrix_iff
      (R.criticalMinimumOrientedNormalRadialRows p hp s theta)).mpr
      (R.linearIndependent_criticalMinimumOrientedNormalRadialRows
        p hp hindex s theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L719-733 verbatim
theorem det_criticalMaximumOrientedNormalRadialMatrix_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) (theta : ℝ) :
    (R.criticalMaximumOrientedNormalRadialMatrix p hp s theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (R.criticalMaximumOrientedNormalRadialMatrix p hp s theta).row :=
    (linearIndependent_rowsMatrix_iff
      (R.criticalMaximumOrientedNormalRadialRows p hp s theta)).mpr
      (R.linearIndependent_criticalMaximumOrientedNormalRadialRows
        p hp hindex s theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L735-735 verbatim
/-! ### Exact factorization of the radial endpoint -/


-- @@ L737-755 verbatim
theorem criticalOrientedTangent_rotation
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    StandardBirth.orientationSign a •
        R.criticalDefiniteUnitTangent p hp 0 theta =
      Real.cos (StandardBirth.orientationSign a * theta) •
          (StandardBirth.orientationSign a •
            R.criticalDefiniteUnitTangent p hp 0 0) -
        Real.sin (StandardBirth.orientationSign a * theta) •
          R.criticalDefiniteRadialTangent p hp 0 := by
  rcases StandardBirth.orientationSign_eq_one_or_neg_one a with h | h
  · rw [h]
    simp only [one_mul, one_smul]
    exact R.criticalDefiniteUnitTangent_zero_rotation p hp theta
  · rw [h]
    simp only [neg_mul, neg_smul, Real.cos_neg, Real.sin_neg, one_mul]
    rw [R.criticalDefiniteUnitTangent_zero_rotation p hp theta]
    module


-- @@ L757-774 verbatim
theorem criticalOrientedRadial_rotation
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalDefiniteRadialTangent p hp theta =
      Real.sin (StandardBirth.orientationSign a * theta) •
          (StandardBirth.orientationSign a •
            R.criticalDefiniteUnitTangent p hp 0 0) +
        Real.cos (StandardBirth.orientationSign a * theta) •
          R.criticalDefiniteRadialTangent p hp 0 := by
  rcases StandardBirth.orientationSign_eq_one_or_neg_one a with h | h
  · rw [h]
    simp only [one_mul, one_smul]
    exact R.criticalDefiniteRadialTangent_rotation p hp theta
  · rw [h]
    simp only [neg_mul, neg_smul, Real.cos_neg, Real.sin_neg, one_mul]
    rw [R.criticalDefiniteRadialTangent_rotation p hp theta]
    module


-- @@ L776-822 verbatim
theorem criticalMinimumOrientedRadialMatrix_rotation
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalMinimumOrientedNormalRadialMatrix p hp 1 theta =
      twistMat a
          (StandardBirth.orientationSign a * theta) *
        R.criticalMinimumOrientedNormalRadialMatrix p hp 1 0 := by
  ext i j
  rw [StandardBirth.twistMat_mul_apply_birth]
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos rfl]
    simp only [criticalMinimumOrientedNormalRadialMatrix, rowsMatrix,
      Matrix.of_apply,
      R.criticalMinimumOrientedNormalRadialRows_zero,
      R.criticalMinimumOrientedNormalRadialRows_last]
    simp only [criticalMinimumNormalRadialLast, Set.Icc.coe_one]
    simp
    have h := congrArg (fun v : E₁a => v j)
      (R.criticalOrientedTangent_rotation p hp theta)
    simpa [sub_eq_add_neg] using h
  · rw [if_neg hi0]
    by_cases hil : i = Fin.last (a + 2)
    · subst i
      rw [if_pos rfl]
      simp only [criticalMinimumOrientedNormalRadialMatrix, rowsMatrix,
        Matrix.of_apply,
        R.criticalMinimumOrientedNormalRadialRows_zero,
        R.criticalMinimumOrientedNormalRadialRows_last]
      simp [criticalMinimumNormalRadialLast]
      have h := congrArg (fun v : E₁a => v j)
        (R.criticalOrientedRadial_rotation p hp theta)
      simpa using h
    · rw [if_neg hil]
      simp only [criticalMinimumOrientedNormalRadialMatrix, rowsMatrix,
        Matrix.of_apply]
      obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
      induction k using Fin.lastCases with
      | last =>
          exfalso
          apply hil
          apply Fin.ext
          simp
      | cast k =>
          rw [R.criticalMinimumOrientedNormalRadialRows_middle,
            R.criticalMinimumOrientedNormalRadialRows_middle]


-- @@ L824-847 verbatim
theorem criticalMaximumOrientedRadialMatrix_rotation
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalMaximumOrientedNormalRadialMatrix p hp 1 theta =
      twistMat a
          (StandardBirth.orientationSign a * theta) *
        R.criticalMaximumOrientedNormalRadialMatrix p hp 1 0 := by
  have hrows (x : ℝ) : R.criticalMaximumOrientedNormalRadialRows p hp 1 x =
      R.criticalMinimumOrientedNormalRadialRows p hp 1 x := by
    funext i
    simp [criticalMaximumOrientedNormalRadialRows,
      criticalMinimumOrientedNormalRadialRows,
      criticalDefiniteUnitTangentRev,
      criticalMaximumNormalRadialLast,
      criticalMinimumNormalRadialLast]
  have hrows0 : R.criticalMaximumOrientedNormalRadialRows p hp 1 0 =
      R.criticalMinimumOrientedNormalRadialRows p hp 1 0 := by
    exact hrows 0
  rw [criticalMaximumOrientedNormalRadialMatrix,
    criticalMaximumOrientedNormalRadialMatrix, hrows theta, hrows0,
    ← criticalMinimumOrientedNormalRadialMatrix,
    ← criticalMinimumOrientedNormalRadialMatrix]
  exact R.criticalMinimumOrientedRadialMatrix_rotation p hp theta


-- @@ L849-849 verbatim
/-! ### Right normalization by the radial base frame -/


-- @@ L851-860 verbatim
def criticalMinimumOrientedRadialBaseUnit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    (Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det
      (R.criticalMinimumOrientedNormalRadialMatrix p hp 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (R.det_criticalMinimumOrientedNormalRadialMatrix_ne_zero
        p hp hindex 1 0))).unit


-- @@ L862-871 verbatim
def criticalMaximumOrientedRadialBaseUnit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    (Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det
      (R.criticalMaximumOrientedNormalRadialMatrix p hp 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (R.det_criticalMaximumOrientedNormalRadialMatrix_ne_zero
        p hp hindex 1 0))).unit


-- @@ L873-884 verbatim
@[simp] theorem coe_criticalMinimumOrientedRadialBaseUnit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    (R.criticalMinimumOrientedRadialBaseUnit p hp hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      R.criticalMinimumOrientedNormalRadialMatrix p hp 1 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det
      (R.criticalMinimumOrientedNormalRadialMatrix p hp 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (R.det_criticalMinimumOrientedNormalRadialMatrix_ne_zero
        p hp hindex 1 0))).unit_spec


-- @@ L886-897 verbatim
@[simp] theorem coe_criticalMaximumOrientedRadialBaseUnit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    (R.criticalMaximumOrientedRadialBaseUnit p hp hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      R.criticalMaximumOrientedNormalRadialMatrix p hp 1 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det
      (R.criticalMaximumOrientedNormalRadialMatrix p hp 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (R.det_criticalMaximumOrientedNormalRadialMatrix_ne_zero
        p hp hindex 1 0))).unit_spec


-- @@ L899-906 verbatim
def criticalMinimumNormalizedCenterMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) (theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  R.criticalMinimumOrientedNormalRadialMatrix p hp s theta *
    (↑(R.criticalMinimumOrientedRadialBaseUnit p hp hindex)⁻¹ :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L908-915 verbatim
def criticalMaximumNormalizedCenterMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) (theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  R.criticalMaximumOrientedNormalRadialMatrix p hp s theta *
    (↑(R.criticalMaximumOrientedRadialBaseUnit p hp hindex)⁻¹ :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L917-928 verbatim
theorem criticalMinimumNormalizedCenterMatrix_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    R.criticalMinimumNormalizedCenterMatrix p hp hindex 1 theta =
      twistMat a
        (StandardBirth.orientationSign a * theta) := by
  rw [criticalMinimumNormalizedCenterMatrix,
    R.criticalMinimumOrientedRadialMatrix_rotation p hp theta,
    ← R.coe_criticalMinimumOrientedRadialBaseUnit p hp hindex]
  rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]


-- @@ L930-941 verbatim
theorem criticalMaximumNormalizedCenterMatrix_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    R.criticalMaximumNormalizedCenterMatrix p hp hindex 1 theta =
      twistMat a
        (StandardBirth.orientationSign a * theta) := by
  rw [criticalMaximumNormalizedCenterMatrix,
    R.criticalMaximumOrientedRadialMatrix_rotation p hp theta,
    ← R.coe_criticalMaximumOrientedRadialBaseUnit p hp hindex]
  rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]


-- @@ L943-943 verbatim
/-! ### Continuity, periodicity, and positivity of the normalized deformation -/


-- @@ L945-953 verbatim
theorem continuous_criticalDefiniteUnitTangent_zero_angle
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    Continuous fun theta : ℝ =>
      R.criticalDefiniteUnitTangent p hp 0 theta := by
  rw [continuous_iff_continuousAt]
  intro theta
  exact (R.continuousAt_criticalDefiniteUnitTangent_zero p hp theta).comp
    (continuous_const.prodMk continuous_id).continuousAt


-- @@ L955-960 verbatim
theorem continuous_criticalDefiniteUnitTangentRev_zero_angle
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    Continuous fun theta : ℝ =>
      R.criticalDefiniteUnitTangentRev p hp 0 theta :=
  (R.continuous_criticalDefiniteUnitTangent_zero_angle p hp).neg


-- @@ L962-970 verbatim
theorem continuous_criticalDefiniteNormalRow_zero_angle
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    Continuous fun theta : ℝ =>
      R.criticalDefiniteNormalRow p hp 0 theta := by
  rw [continuous_iff_continuousAt]
  intro theta
  exact (R.continuousAt_criticalDefiniteNormalRow_zero p hp theta).comp
    (continuous_const.prodMk continuous_id).continuousAt


-- @@ L972-985 verbatim
theorem continuous_criticalDefiniteRadialTangent_angle
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    Continuous fun theta : ℝ =>
      R.criticalDefiniteRadialTangent p hp theta := by
  have heq : (fun theta : ℝ =>
      R.criticalDefiniteRadialTangent p hp theta) =
      fun theta =>
        Real.sin theta • R.criticalDefiniteUnitTangent p hp 0 0 +
          Real.cos theta • R.criticalDefiniteRadialTangent p hp 0 := by
    funext theta
    exact R.criticalDefiniteRadialTangent_rotation p hp theta
  rw [heq]
  fun_prop


-- @@ L987-1008 verbatim
theorem continuous_criticalMinimumNormalRadialLast
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    Continuous fun q : I × ℝ =>
      R.criticalMinimumNormalRadialLast p hp q.1 q.2 := by
  have hs : Continuous fun q : I × ℝ => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hn : Continuous fun q : I × ℝ =>
      R.criticalDefiniteNormalRow p hp 0 q.2 :=
    (R.continuous_criticalDefiniteNormalRow_zero_angle p hp).comp
      continuous_snd
  have hr : Continuous fun q : I × ℝ =>
      R.criticalDefiniteRadialTangent p hp q.2 :=
    (R.continuous_criticalDefiniteRadialTangent_angle p hp).comp
      continuous_snd
  have hsign : Continuous fun _ : I × ℝ =>
      (nonzeroOrientationSign
        (R.criticalMinimumCenterPairingScalar p hp) : ℝ) :=
    continuous_const
  unfold criticalMinimumNormalRadialLast
  exact ((continuous_const.sub hs).smul
      (hsign.smul hn)).add (hs.smul hr)


-- @@ L1010-1031 verbatim
theorem continuous_criticalMaximumNormalRadialLast
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    Continuous fun q : I × ℝ =>
      R.criticalMaximumNormalRadialLast p hp q.1 q.2 := by
  have hs : Continuous fun q : I × ℝ => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hn : Continuous fun q : I × ℝ =>
      R.criticalDefiniteNormalRow p hp 0 q.2 :=
    (R.continuous_criticalDefiniteNormalRow_zero_angle p hp).comp
      continuous_snd
  have hr : Continuous fun q : I × ℝ =>
      R.criticalDefiniteRadialTangent p hp q.2 :=
    (R.continuous_criticalDefiniteRadialTangent_angle p hp).comp
      continuous_snd
  have hsign : Continuous fun _ : I × ℝ =>
      (nonzeroOrientationSign
        (R.criticalMaximumCenterPairingScalar p hp) : ℝ) :=
    continuous_const
  unfold criticalMaximumNormalRadialLast
  exact ((continuous_const.sub hs).smul
      (hsign.smul hn)).add (hs.smul hr)


-- @@ L1033-1066 verbatim
theorem continuous_criticalMinimumOrientedNormalRadialMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    Continuous fun q : I × ℝ =>
      R.criticalMinimumOrientedNormalRadialMatrix p hp q.1 q.2 := by
  have ht : Continuous fun q : I × ℝ =>
      StandardBirth.orientationSign a •
        R.criticalDefiniteUnitTangent p hp 0 q.2 :=
    (continuous_const : Continuous fun _ : I × ℝ =>
      (StandardBirth.orientationSign a : ℝ)).smul
      ((R.continuous_criticalDefiniteUnitTangent_zero_angle p hp).comp
        continuous_snd)
  have hl : Continuous fun q : I × ℝ =>
      R.criticalMinimumNormalRadialLast p hp q.1 q.2 :=
    R.continuous_criticalMinimumNormalRadialLast p hp
  apply continuous_matrix
  intro i j
  have hrow : Continuous fun q : I × ℝ =>
      R.criticalMinimumOrientedNormalRadialRows p hp q.1 q.2 i := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simpa only [R.criticalMinimumOrientedNormalRadialRows_zero] using ht
    · induction i using Fin.lastCases with
      | last =>
          have hlast : (Fin.last (a + 1)).succ =
              (Fin.last (a + 2) : Fin (a + 3)) := by
            apply Fin.ext
            simp
          rw [hlast]
          simpa only [R.criticalMinimumOrientedNormalRadialRows_last] using hl
      | cast i =>
          simpa only [R.criticalMinimumOrientedNormalRadialRows_middle] using
            (continuous_const : Continuous fun _ : I × ℝ =>
              R.criticalTransverseNormal p hp i)
  exact (EuclideanSpace.proj j).continuous.comp hrow


-- @@ L1068-1099 verbatim
theorem continuous_criticalMaximumOrientedNormalRadialMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    Continuous fun q : I × ℝ =>
      R.criticalMaximumOrientedNormalRadialMatrix p hp q.1 q.2 := by
  have ht : Continuous fun q : I × ℝ =>
      (-StandardBirth.orientationSign a) •
        R.criticalDefiniteUnitTangentRev p hp 0 q.2 :=
    (continuous_const : Continuous fun _ : I × ℝ =>
      (-StandardBirth.orientationSign a : ℝ)).smul
      ((R.continuous_criticalDefiniteUnitTangentRev_zero_angle p hp).comp
        continuous_snd)
  have hl : Continuous fun q : I × ℝ =>
      R.criticalMaximumNormalRadialLast p hp q.1 q.2 :=
    R.continuous_criticalMaximumNormalRadialLast p hp
  apply continuous_matrix
  intro i j
  have hrow : Continuous fun q : I × ℝ =>
      R.criticalMaximumOrientedNormalRadialRows p hp q.1 q.2 i := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simpa [criticalMaximumOrientedNormalRadialRows,
        centerRowsWith] using ht
    · induction i using Fin.lastCases with
      | last =>
          simpa [criticalMaximumOrientedNormalRadialRows,
            centerRowsWith] using hl
      | cast i =>
          simpa [criticalMaximumOrientedNormalRadialRows,
            centerRowsWith] using
            (continuous_const : Continuous fun _ : I × ℝ =>
              R.criticalTransverseNormal p hp i)
  exact (EuclideanSpace.proj j).continuous.comp hrow


-- @@ L1101-1109 verbatim
theorem continuous_criticalMinimumNormalizedCenterMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    Continuous fun q : I × ℝ =>
      R.criticalMinimumNormalizedCenterMatrix p hp hindex q.1 q.2 := by
  unfold criticalMinimumNormalizedCenterMatrix
  exact (R.continuous_criticalMinimumOrientedNormalRadialMatrix p hp).matrix_mul
    continuous_const


-- @@ L1111-1119 verbatim
theorem continuous_criticalMaximumNormalizedCenterMatrix
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    Continuous fun q : I × ℝ =>
      R.criticalMaximumNormalizedCenterMatrix p hp hindex q.1 q.2 := by
  unfold criticalMaximumNormalizedCenterMatrix
  exact (R.continuous_criticalMaximumOrientedNormalRadialMatrix p hp).matrix_mul
    continuous_const


-- @@ L1121-1127 verbatim
theorem criticalDefiniteUnitTangent_zero_two_pi
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalDefiniteUnitTangent p hp 0 (2 * Real.pi) =
      R.criticalDefiniteUnitTangent p hp 0 0 := by
  rw [R.criticalDefiniteUnitTangent_zero_rotation p hp]
  simp [Real.cos_two_pi, Real.sin_two_pi]


-- @@ L1129-1135 verbatim
theorem criticalDefiniteRadialTangent_two_pi
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalDefiniteRadialTangent p hp (2 * Real.pi) =
      R.criticalDefiniteRadialTangent p hp 0 := by
  rw [R.criticalDefiniteRadialTangent_rotation p hp]
  simp [Real.cos_two_pi, Real.sin_two_pi]


-- @@ L1137-1147 verbatim
theorem criticalDefiniteNormalRow_zero_two_pi
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalDefiniteNormalRow p hp 0 (2 * Real.pi) =
      R.criticalDefiniteNormalRow p hp 0 0 := by
  rw [R.criticalDefiniteNormalRow_zero,
    R.criticalDefiniteNormalRow_zero]
  congr 1
  ext i
  fin_cases i <;> simp [definiteCircleParam, pairToMorseParam,
    Real.cos_two_pi, Real.sin_two_pi]


-- @@ L1149-1163 verbatim
theorem criticalMinimumNormalizedCenterMatrix_two_pi
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) :
    R.criticalMinimumNormalizedCenterMatrix p hp hindex s
        (2 * Real.pi) =
      R.criticalMinimumNormalizedCenterMatrix p hp hindex s 0 := by
  unfold criticalMinimumNormalizedCenterMatrix
    criticalMinimumOrientedNormalRadialMatrix
    criticalMinimumOrientedNormalRadialRows
    criticalMinimumNormalRadialLast
  rw [R.criticalDefiniteUnitTangent_zero_two_pi p hp,
    R.criticalDefiniteNormalRow_zero_two_pi p hp,
    R.criticalDefiniteRadialTangent_two_pi p hp]


-- @@ L1165-1180 verbatim
theorem criticalMaximumNormalizedCenterMatrix_two_pi
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) :
    R.criticalMaximumNormalizedCenterMatrix p hp hindex s
        (2 * Real.pi) =
      R.criticalMaximumNormalizedCenterMatrix p hp hindex s 0 := by
  unfold criticalMaximumNormalizedCenterMatrix
    criticalMaximumOrientedNormalRadialMatrix
    criticalMaximumOrientedNormalRadialRows
    criticalMaximumNormalRadialLast
    criticalDefiniteUnitTangentRev
  rw [R.criticalDefiniteUnitTangent_zero_two_pi p hp,
    R.criticalDefiniteNormalRow_zero_two_pi p hp,
    R.criticalDefiniteRadialTangent_two_pi p hp]


-- @@ L1182-1196 verbatim
theorem det_criticalMinimumNormalizedCenterMatrix_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) (theta : ℝ) :
    (R.criticalMinimumNormalizedCenterMatrix p hp hindex s theta).det ≠ 0 := by
  rw [criticalMinimumNormalizedCenterMatrix, Matrix.det_mul]
  apply mul_ne_zero
  · exact R.det_criticalMinimumOrientedNormalRadialMatrix_ne_zero
      p hp hindex s theta
  · have hu : IsUnit
        (↑(R.criticalMinimumOrientedRadialBaseUnit p hp hindex)⁻¹ :
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) := Units.isUnit _
    exact isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp hu)


-- @@ L1198-1212 verbatim
theorem det_criticalMaximumNormalizedCenterMatrix_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) (theta : ℝ) :
    (R.criticalMaximumNormalizedCenterMatrix p hp hindex s theta).det ≠ 0 := by
  rw [criticalMaximumNormalizedCenterMatrix, Matrix.det_mul]
  apply mul_ne_zero
  · exact R.det_criticalMaximumOrientedNormalRadialMatrix_ne_zero
      p hp hindex s theta
  · have hu : IsUnit
        (↑(R.criticalMaximumOrientedRadialBaseUnit p hp hindex)⁻¹ :
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) := Units.isUnit _
    exact isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp hu)


-- @@ L1214-1242 verbatim
theorem det_criticalMinimumNormalizedCenterMatrix_pos
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) (theta : ℝ) :
    0 < (R.criticalMinimumNormalizedCenterMatrix p hp hindex s theta).det := by
  let d : I → ℝ := fun u =>
    (R.criticalMinimumNormalizedCenterMatrix p hp hindex u theta).det
  change 0 < d s
  have hd : Continuous d := by
    change Continuous fun u : I =>
      (R.criticalMinimumNormalizedCenterMatrix p hp hindex u theta).det
    exact ((R.continuous_criticalMinimumNormalizedCenterMatrix p hp hindex).comp
      (continuous_id.prodMk continuous_const)).matrix_det
  have hdne : ∀ u, d u ≠ 0 := fun u =>
    R.det_criticalMinimumNormalizedCenterMatrix_ne_zero
      p hp hindex u theta
  have hd1 : d 1 = 1 := by
    dsimp [d]
    rw [R.criticalMinimumNormalizedCenterMatrix_one p hp hindex theta,
      StandardBirth.det_twistMat]
  by_contra hpos
  have hsneg : d s < 0 :=
    lt_of_le_of_ne (le_of_not_gt hpos) (hdne s)
  have hmem : (0 : ℝ) ∈ Set.Icc (d s) (d 1) := by
    rw [hd1]
    exact ⟨hsneg.le, by norm_num⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ s 1 hd hmem
  exact hdne u hu


-- @@ L1244-1272 verbatim
theorem det_criticalMaximumNormalizedCenterMatrix_pos
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) (theta : ℝ) :
    0 < (R.criticalMaximumNormalizedCenterMatrix p hp hindex s theta).det := by
  let d : I → ℝ := fun u =>
    (R.criticalMaximumNormalizedCenterMatrix p hp hindex u theta).det
  change 0 < d s
  have hd : Continuous d := by
    change Continuous fun u : I =>
      (R.criticalMaximumNormalizedCenterMatrix p hp hindex u theta).det
    exact ((R.continuous_criticalMaximumNormalizedCenterMatrix p hp hindex).comp
      (continuous_id.prodMk continuous_const)).matrix_det
  have hdne : ∀ u, d u ≠ 0 := fun u =>
    R.det_criticalMaximumNormalizedCenterMatrix_ne_zero
      p hp hindex u theta
  have hd1 : d 1 = 1 := by
    dsimp [d]
    rw [R.criticalMaximumNormalizedCenterMatrix_one p hp hindex theta,
      StandardBirth.det_twistMat]
  by_contra hpos
  have hsneg : d s < 0 :=
    lt_of_le_of_ne (le_of_not_gt hpos) (hdne s)
  have hmem : (0 : ℝ) ∈ Set.Icc (d s) (d 1) := by
    rw [hd1]
    exact ⟨hsneg.le, by norm_num⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ s 1 hd hmem
  exact hdne u hu


-- @@ L1274-1274 verbatim
/-! ### The closed center loops and their positive matrix homotopies -/


-- @@ L1276-1279 verbatim
def definiteCenterLoopParam : C(I, I × ℝ) where
  toFun u := (0, 2 * Real.pi * (u : ℝ))
  continuous_toFun := continuous_const.prodMk
    (continuous_const.mul continuous_subtype_val)


-- @@ L1281-1284 verbatim
def definiteCenterHomotopyParam : C(I × I, I × ℝ) where
  toFun q := (q.1, 2 * Real.pi * (q.2 : ℝ))
  continuous_toFun := continuous_fst.prodMk
    (continuous_const.mul (continuous_subtype_val.comp continuous_snd))


-- @@ L1286-1293 verbatim
def criticalMinimumNormalizedCenterMatrixMap
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    C(I × ℝ, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun q := R.criticalMinimumNormalizedCenterMatrix p hp hindex q.1 q.2
  continuous_toFun :=
    R.continuous_criticalMinimumNormalizedCenterMatrix p hp hindex


-- @@ L1295-1302 verbatim
def criticalMaximumNormalizedCenterMatrixMap
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    C(I × ℝ, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun q := R.criticalMaximumNormalizedCenterMatrix p hp hindex q.1 q.2
  continuous_toFun :=
    R.continuous_criticalMaximumNormalizedCenterMatrix p hp hindex


-- @@ L1304-1310 verbatim
def criticalMinimumNormalizedCenterLoop
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  (R.criticalMinimumNormalizedCenterMatrixMap p hp hindex).comp
    definiteCenterLoopParam


-- @@ L1312-1318 verbatim
def criticalMaximumNormalizedCenterLoop
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  (R.criticalMaximumNormalizedCenterMatrixMap p hp hindex).comp
    definiteCenterLoopParam


-- @@ L1320-1329 verbatim
theorem criticalMinimumNormalizedCenterLoop_closed
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    R.criticalMinimumNormalizedCenterLoop p hp hindex 0 =
      R.criticalMinimumNormalizedCenterLoop p hp hindex 1 := by
  simpa [criticalMinimumNormalizedCenterLoop,
    criticalMinimumNormalizedCenterMatrixMap, definiteCenterLoopParam] using
      (R.criticalMinimumNormalizedCenterMatrix_two_pi
        p hp hindex 0).symm


-- @@ L1331-1340 verbatim
theorem criticalMaximumNormalizedCenterLoop_closed
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    R.criticalMaximumNormalizedCenterLoop p hp hindex 0 =
      R.criticalMaximumNormalizedCenterLoop p hp hindex 1 := by
  simpa [criticalMaximumNormalizedCenterLoop,
    criticalMaximumNormalizedCenterMatrixMap, definiteCenterLoopParam] using
      (R.criticalMaximumNormalizedCenterMatrix_two_pi
        p hp hindex 0).symm


-- @@ L1342-1349 verbatim
theorem criticalMinimumNormalizedCenterLoop_det_pos
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (u : I) :
    0 < (R.criticalMinimumNormalizedCenterLoop p hp hindex u).det :=
  R.det_criticalMinimumNormalizedCenterMatrix_pos p hp hindex 0
    (2 * Real.pi * (u : ℝ))


-- @@ L1351-1358 verbatim
theorem criticalMaximumNormalizedCenterLoop_det_pos
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (u : I) :
    0 < (R.criticalMaximumNormalizedCenterLoop p hp hindex u).det :=
  R.det_criticalMaximumNormalizedCenterMatrix_pos p hp hindex 0
    (2 * Real.pi * (u : ℝ))


-- @@ L1360-1374 verbatim
theorem criticalMinimumNormalizedCenterMatrix_one_eq_birthPlaneMatrixLoop
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (u : I) :
    R.criticalMinimumNormalizedCenterMatrix p hp hindex 1
        (2 * Real.pi * (u : ℝ)) =
      StandardBirth.birthPlaneMatrixLoop a u := by
  rw [R.criticalMinimumNormalizedCenterMatrix_one p hp hindex]
  change twistMat a
      (StandardBirth.orientationSign a * (2 * Real.pi * (u : ℝ))) =
    (StandardBirth.birthPlaneLoop a u :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
  rw [StandardBirth.birthPlaneLoop_coe]
  rfl


-- @@ L1376-1390 verbatim
theorem criticalMaximumNormalizedCenterMatrix_one_eq_birthPlaneMatrixLoop
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (u : I) :
    R.criticalMaximumNormalizedCenterMatrix p hp hindex 1
        (2 * Real.pi * (u : ℝ)) =
      StandardBirth.birthPlaneMatrixLoop a u := by
  rw [R.criticalMaximumNormalizedCenterMatrix_one p hp hindex]
  change twistMat a
      (StandardBirth.orientationSign a * (2 * Real.pi * (u : ℝ))) =
    (StandardBirth.birthPlaneLoop a u :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
  rw [StandardBirth.birthPlaneLoop_coe]
  rfl


-- @@ L1392-1405 verbatim
def criticalMinimumCenterBirthMatrixHomotopy
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    ContinuousMap.Homotopy
      (R.criticalMinimumNormalizedCenterLoop p hp hindex)
      (StandardBirth.birthPlaneMatrixLoop a) where
  toContinuousMap :=
    (R.criticalMinimumNormalizedCenterMatrixMap p hp hindex).comp
      definiteCenterHomotopyParam
  map_zero_left _u := rfl
  map_one_left u :=
    R.criticalMinimumNormalizedCenterMatrix_one_eq_birthPlaneMatrixLoop
      p hp hindex u


-- @@ L1407-1420 verbatim
def criticalMaximumCenterBirthMatrixHomotopy
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    ContinuousMap.Homotopy
      (R.criticalMaximumNormalizedCenterLoop p hp hindex)
      (StandardBirth.birthPlaneMatrixLoop a) where
  toContinuousMap :=
    (R.criticalMaximumNormalizedCenterMatrixMap p hp hindex).comp
      definiteCenterHomotopyParam
  map_zero_left _u := rfl
  map_one_left u :=
    R.criticalMaximumNormalizedCenterMatrix_one_eq_birthPlaneMatrixLoop
      p hp hindex u


-- @@ L1422-1430 verbatim
@[simp] theorem criticalMinimumCenterBirthMatrixHomotopy_apply
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (q : I × I) :
    R.criticalMinimumCenterBirthMatrixHomotopy p hp hindex q =
      R.criticalMinimumNormalizedCenterMatrix p hp hindex q.1
        (2 * Real.pi * (q.2 : ℝ)) :=
  rfl


-- @@ L1432-1440 verbatim
@[simp] theorem criticalMaximumCenterBirthMatrixHomotopy_apply
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (q : I × I) :
    R.criticalMaximumCenterBirthMatrixHomotopy p hp hindex q =
      R.criticalMaximumNormalizedCenterMatrix p hp hindex q.1
        (2 * Real.pi * (q.2 : ℝ)) :=
  rfl


-- @@ L1442-1449 verbatim
theorem criticalMinimumCenterBirthMatrixHomotopy_det_pos
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (q : I × I) :
    0 < (R.criticalMinimumCenterBirthMatrixHomotopy p hp hindex q).det :=
  R.det_criticalMinimumNormalizedCenterMatrix_pos p hp hindex q.1
    (2 * Real.pi * (q.2 : ℝ))


-- @@ L1451-1458 verbatim
theorem criticalMaximumCenterBirthMatrixHomotopy_det_pos
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (q : I × I) :
    0 < (R.criticalMaximumCenterBirthMatrixHomotopy p hp hindex q).det :=
  R.det_criticalMaximumNormalizedCenterMatrix_pos p hp hindex q.1
    (2 * Real.pi * (q.2 : ℝ))


-- @@ L1460-1469 verbatim
theorem criticalMinimumCenterBirthMatrixHomotopy_closed
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (s : I) :
    R.criticalMinimumCenterBirthMatrixHomotopy p hp hindex (s, 0) =
      R.criticalMinimumCenterBirthMatrixHomotopy p hp hindex (s, 1) := by
  simpa using
      (R.criticalMinimumNormalizedCenterMatrix_two_pi
        p hp hindex s).symm


-- @@ L1471-1480 verbatim
theorem criticalMaximumCenterBirthMatrixHomotopy_closed
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (s : I) :
    R.criticalMaximumCenterBirthMatrixHomotopy p hp hindex (s, 0) =
      R.criticalMaximumCenterBirthMatrixHomotopy p hp hindex (s, 1) := by
  simpa using
      (R.criticalMaximumNormalizedCenterMatrix_two_pi
        p hp hindex s).symm


-- @@ L1482-1482 verbatim
/-! ### Stable class of the definite center frame -/


-- @@ L1484-1505 verbatim
theorem loopClassZ2_criticalMinimumNormalizedCenter_eq_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    loopClassZ2
        (positiveMatrixSOMap
          (R.criticalMinimumNormalizedCenterLoop p hp hindex)
          (R.criticalMinimumNormalizedCenterLoop_det_pos p hp hindex))
        (positiveMatrixSOMap_closed
          (R.criticalMinimumNormalizedCenterLoop p hp hindex)
          (R.criticalMinimumNormalizedCenterLoop_det_pos p hp hindex)
          (R.criticalMinimumNormalizedCenterLoop_closed p hp hindex)) = 1 := by
  have hclass := loopClassZ2_positiveMatrixHomotopy_congr
    (R.criticalMinimumCenterBirthMatrixHomotopy p hp hindex)
    (R.criticalMinimumNormalizedCenterLoop_det_pos p hp hindex)
    (StandardBirth.birthPlaneMatrixLoop_det_pos a)
    (R.criticalMinimumCenterBirthMatrixHomotopy_det_pos p hp hindex)
    (R.criticalMinimumNormalizedCenterLoop_closed p hp hindex)
    (StandardBirth.birthPlaneMatrixLoop_closed a)
    (R.criticalMinimumCenterBirthMatrixHomotopy_closed p hp hindex)
  exact hclass.trans
    (StandardBirth.loopClassZ2_positiveMatrixSOMap_birthPlaneMatrixLoop a)


-- @@ L1507-1528 verbatim
theorem loopClassZ2_criticalMaximumNormalizedCenter_eq_one
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    loopClassZ2
        (positiveMatrixSOMap
          (R.criticalMaximumNormalizedCenterLoop p hp hindex)
          (R.criticalMaximumNormalizedCenterLoop_det_pos p hp hindex))
        (positiveMatrixSOMap_closed
          (R.criticalMaximumNormalizedCenterLoop p hp hindex)
          (R.criticalMaximumNormalizedCenterLoop_det_pos p hp hindex)
          (R.criticalMaximumNormalizedCenterLoop_closed p hp hindex)) = 1 := by
  have hclass := loopClassZ2_positiveMatrixHomotopy_congr
    (R.criticalMaximumCenterBirthMatrixHomotopy p hp hindex)
    (R.criticalMaximumNormalizedCenterLoop_det_pos p hp hindex)
    (StandardBirth.birthPlaneMatrixLoop_det_pos a)
    (R.criticalMaximumCenterBirthMatrixHomotopy_det_pos p hp hindex)
    (R.criticalMaximumNormalizedCenterLoop_closed p hp hindex)
    (StandardBirth.birthPlaneMatrixLoop_closed a)
    (R.criticalMaximumCenterBirthMatrixHomotopy_closed p hp hindex)
  exact hclass.trans
    (StandardBirth.loopClassZ2_positiveMatrixSOMap_birthPlaneMatrixLoop a)


-- @@ L1530-1530 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L1532-1532 verbatim
end Submission
