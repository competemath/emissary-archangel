import Mathlib
import Submission.PTInverse


-- @@ L4-11 verbatim
/-!
# Canonical signed collapse at a bridge endpoint

The northern cutoff already attached to a bridge presentation determines an
especially simple signed Pontryagin--Thom numerator.  Its horizontal part is the
cutoff multiple of the regular-value equation and its last coordinate records the
sign by the affine function `2 * cutoff - 1`.
-/


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
open scoped Topology unitInterval RealInnerProductSpace ContDiff

-- @@ L16-16 verbatim
open Metric Set Function Topology.Homotopy


-- @@ L18-18 verbatim
namespace Submission


-- @@ L20-20 verbatim
variable {n : ℕ}

-- @@ L21-22 verbatim
variable {z : HomotopyGroup (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}


-- @@ L24-24 verbatim
namespace BridgeData


-- @@ L26-26 verbatim
variable (B : BridgeData n z)


-- @@ L28-28 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L29-29 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L31-31 verbatim
/-! ## The raw signed collapse -/


-- @@ L33-37 verbatim
/-- Canonical signed numerator: the northern equation in the horizontal directions
and the affine sign coordinate in the last direction. -/
def signedCollapseRaw (x : E) : E :=
  B.northCutoff x • embedCLM n (B.fls.g x) +
    (2 * B.northCutoff x - 1) • eLast n


-- @@ L39-42 verbatim
lemma contDiff_signedCollapseRaw : ContDiff ℝ ∞ B.signedCollapseRaw := by
  exact (B.contDiff_northCutoff.smul
      ((embedCLM n).contDiff.comp B.fls.smooth)).add
    (((contDiff_const.mul B.contDiff_northCutoff).sub contDiff_const).smul contDiff_const)


-- @@ L44-85 verbatim
/-- The canonical northern cutoff is compactly supported in the Euclidean bridge
domain. -/
theorem hasCompactSupport_northCutoff : HasCompactSupport B.northCutoff := by
  have hsupp : support B.northCutoff ⊆
      Metric.closedBall (0 : E) (n + 1 : ℝ) := by
    intro x hx
    have hnc : WithLp.ofLp x ∉ closedAmbientCollar (Fin (n + 1)) := by
      intro hcollar
      apply hx
      rw [northCutoff, northSource, nprep_of_mem_collar B.approx hcollar]
      apply plateauA_of_le
      show (-eLast n : E) (Fin.last n) ≤ -(1 / 2 : ℝ)
      simp [eLast]
      norm_num
    have hcoord : ∀ i, |x i| ≤ 1 := by
      intro i
      have h : ¬(x i ≤ 1 / 5 ∨ 4 / 5 ≤ x i) := fun hi => hnc ⟨i, hi⟩
      rw [not_or, not_le, not_le] at h
      exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    have hnorm : ‖x‖ ≤ n + 1 := by
      have hsq : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := norm_sq_eq_sum x
      have hsum : (∑ i, x i ^ 2) ≤ ∑ _i : Fin (n + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hcoord i
        nlinarith [abs_nonneg (x i), sq_abs (x i)]
      have hone : (∑ _i : Fin (n + 1), (1 : ℝ)) = n + 1 := by simp
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn1 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      have hsq' : ‖x‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
        calc
          ‖x‖ ^ 2 = ∑ i, x i ^ 2 := hsq
          _ ≤ n + 1 := hsum.trans_eq hone
          _ ≤ ((n : ℝ) + 1) ^ 2 := hn1
      nlinarith [norm_nonneg x]
    rw [mem_closedBall, dist_zero_right]
    exact hnorm
  have htsupp : tsupport B.northCutoff ⊆
      Metric.closedBall (0 : E) (n + 1 : ℝ) :=
    closure_minimal hsupp Metric.isClosed_closedBall
  exact IsCompact.of_isClosed_subset
    (ProperSpace.isCompact_closedBall (0 : E) (n + 1 : ℝ)) isClosed_closure htsupp


-- @@ L87-92 verbatim
/-- The signed and Milnor-style northern collapses have exactly the same horizontal
component. -/
lemma initCLM_signedCollapseRaw (x : E) :
    initCLM n (B.signedCollapseRaw x) = B.northCutoff x • B.fls.g x := by
  rw [signedCollapseRaw, map_add, map_smul, map_smul, initCLM_embedCLM,
    initCLM_eLast, smul_zero, add_zero]


-- @@ L94-96 verbatim
lemma initCLM_signedCollapseRaw_eq_northThomRaw (x : E) :
    initCLM n (B.signedCollapseRaw x) = initCLM n (B.northThomRaw x) := by
  rw [B.initCLM_signedCollapseRaw, B.initCLM_northThomRaw]


-- @@ L98-101 verbatim
lemma vertC_signedCollapseRaw (x : E) :
    vertC (B.signedCollapseRaw x) = 2 * B.northCutoff x - 1 := by
  rw [signedCollapseRaw]
  simp [vertC, eLast]


-- @@ L103-104 verbatim
lemma fls_g_eq_northSource (x : E) :
    B.fls.g x = initCLM n (B.northSource x) - B.y := rfl


-- @@ L106-123 verbatim
/-- Closed form for the pairing with the original bridge sphere point. -/
lemma inner_signedCollapseRaw_source (x : E) :
    ⟪B.signedCollapseRaw x, B.northSource x⟫ =
      B.northCutoff x *
          (1 - vertC (B.northSource x) ^ 2 -
            ⟪B.y, initCLM n (B.northSource x)⟫) +
        (2 * B.northCutoff x - 1) * vertC (B.northSource x) := by
  let u := B.northSource x
  let h := initCLM n u
  let t := vertC u
  have hnorm := norm_sq_split u
  rw [B.norm_northSource x] at hnorm
  have hhh : ⟪h, h⟫ = 1 - t ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith
  rw [signedCollapseRaw, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, inner_embedCLM_left (n := n), inner_eLast_left,
    B.fls_g_eq_northSource, inner_sub_left, hhh]


-- @@ L125-176 verbatim
/-- The signed numerator lies in the open hemisphere centered at the original
bridge point.  This simultaneously proves nonvanishing and supplies the chord
homotopy used below. -/
lemma inner_signedCollapseRaw_source_pos (x : E) :
    0 < ⟪B.signedCollapseRaw x, B.northSource x⟫ := by
  rw [B.inner_signedCollapseRaw_source]
  let u := B.northSource x
  let t := vertC u
  let h := initCLM n u
  let c := B.northCutoff x
  let q := ⟪B.y, h⟫
  have hu : ‖u‖ = 1 := B.norm_northSource x
  have htAbs : |t| ≤ 1 := abs_vertC_le_one hu
  have htLower : -1 ≤ t := neg_le_of_abs_le htAbs
  have htUpper : t ≤ 1 := le_of_abs_le htAbs
  have hh : ‖h‖ ≤ 1 := by
    have hs := norm_sq_split u
    rw [hu] at hs
    have hh0 := norm_nonneg h
    nlinarith [sq_nonneg t]
  have hqAbs : |q| < 1 / 8 := by
    calc
      |⟪B.y, h⟫| ≤ ‖B.y‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖B.y‖ * 1 := mul_le_mul_of_nonneg_left hh (norm_nonneg B.y)
      _ < 1 / 8 := by simpa [q] using B.norm_y_lt
  have hqUpper : q < 1 / 8 := lt_of_le_of_lt (le_abs_self q) hqAbs
  have hc0 : 0 ≤ c := B.northCutoff_nonneg x
  have hc1 : c ≤ 1 := B.northCutoff_le_one x
  change 0 < c * (1 - t ^ 2 - q) + (2 * c - 1) * t
  by_cases hlow : t ≤ -(1 / 2)
  · have hc : c = 0 := by
      dsimp [c, t, u]
      rw [northCutoff, plateauA_of_le hlow]
    rw [hc]
    linarith
  by_cases hhigh : -(1 / 4) ≤ t
  · have hc : c = 1 := by
      dsimp [c, t, u]
      rw [northCutoff, plateauA_of_ge hhigh]
    rw [hc]
    have ht : -(1 / 4) ≤ t := hhigh
    nlinarith [sq_nonneg (t - 1 / 2)]
  · have htneg : t < -(1 / 4) := lt_of_not_ge hhigh
    have httrans : -(1 / 2) < t := lt_of_not_ge hlow
    by_cases hbr : 0 ≤ 1 + 2 * t - t ^ 2 - q
    · have hp : 0 ≤ c * (1 + 2 * t - t ^ 2 - q) := mul_nonneg hc0 hbr
      nlinarith
    · have hbrneg : 1 + 2 * t - t ^ 2 - q < 0 := lt_of_not_ge hbr
      have hp : 1 + 2 * t - t ^ 2 - q ≤
          c * (1 + 2 * t - t ^ 2 - q) := by
        nlinarith
      nlinarith [sq_nonneg (t + 1 / 2)]


-- @@ L178-182 verbatim
lemma signedCollapseRaw_ne_zero (x : E) : B.signedCollapseRaw x ≠ 0 := by
  intro hzero
  have hpos := B.inner_signedCollapseRaw_source_pos x
  rw [hzero, inner_zero_left] at hpos
  exact lt_irrefl 0 hpos


-- @@ L184-184 verbatim
/-! ## Normalization and exact fibers -/


-- @@ L186-190 verbatim
/-- Sphere-valued normalization of the signed numerator. -/
def signedCollapse (x : E) : UnitSphere E :=
  ⟨‖B.signedCollapseRaw x‖⁻¹ • B.signedCollapseRaw x,
    mem_sphere_zero_iff_norm.mpr
      (norm_normalize (B.signedCollapseRaw_ne_zero x))⟩


-- @@ L192-194 verbatim
@[simp] lemma signedCollapse_coe (x : E) :
    (B.signedCollapse x : E) =
      ‖B.signedCollapseRaw x‖⁻¹ • B.signedCollapseRaw x := rfl


-- @@ L196-198 verbatim
lemma contDiff_signedCollapse :
    ContDiff ℝ ∞ fun x => (B.signedCollapse x : E) :=
  contDiff_normalize_comp B.contDiff_signedCollapseRaw B.signedCollapseRaw_ne_zero


-- @@ L200-201 verbatim
lemma continuous_signedCollapse : Continuous B.signedCollapse :=
  Continuous.subtype_mk B.contDiff_signedCollapse.continuous _


-- @@ L203-204 verbatim
def signedCollapseCM : C(E, UnitSphere E) :=
  ⟨B.signedCollapse, B.continuous_signedCollapse⟩


-- @@ L206-211 verbatim
lemma signedCollapseRaw_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) :
    B.signedCollapseRaw x = eLast n := by
  rw [signedCollapseRaw, B.northCutoff_of_northFiber hx,
    B.fls_g_of_northFiber hx]
  norm_num


-- @@ L213-217 verbatim
lemma northCutoff_of_southFiber {x : E}
    (hx : B.northSource x = southPointOf B.y) :
    B.northCutoff x = 0 := by
  rw [northCutoff, hx]
  exact plateauA_of_le B.southPointOf_mem_southCap


-- @@ L219-224 verbatim
lemma fls_g_of_southFiber {x : E}
    (hx : B.northSource x = southPointOf B.y) : B.fls.g x = 0 := by
  change bridgeHMapE B.approx x - B.y = 0
  apply sub_eq_zero.mpr
  change initCLM n (B.northSource x) = B.y
  rw [hx, initCLM_southPointOf]


-- @@ L226-231 verbatim
lemma signedCollapseRaw_of_southFiber {x : E}
    (hx : B.northSource x = southPointOf B.y) :
    B.signedCollapseRaw x = -eLast n := by
  rw [signedCollapseRaw, B.northCutoff_of_southFiber hx,
    B.fls_g_of_southFiber hx]
  module


-- @@ L233-239 verbatim
theorem signedCollapse_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) :
    B.signedCollapse x = ptNorthPole := by
  apply Subtype.ext
  rw [signedCollapse_coe, B.signedCollapseRaw_of_northFiber hx,
    ptNorthPole_coe, norm_eLast]
  simp


-- @@ L241-247 verbatim
theorem signedCollapse_of_southFiber {x : E}
    (hx : B.northSource x = southPointOf B.y) :
    B.signedCollapse x = southPole n := by
  apply Subtype.ext
  rw [signedCollapse_coe, B.signedCollapseRaw_of_southFiber hx,
    southPole_coe, norm_neg, norm_eLast]
  simp


-- @@ L249-249 verbatim
/-! ## Cubical loop and comparison with the bridge representative -/


-- @@ L251-262 verbatim
lemma signedCollapseRaw_cube_boundary {t : I^(Fin (n + 1))}
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    B.signedCollapseRaw (cubeToBridgeDomain t) = -eLast n := by
  have hsource := B.northSource_cube_boundary ht
  have hcut : B.northCutoff (cubeToBridgeDomain t) = 0 := by
    rw [northCutoff, hsource]
    apply plateauA_of_le
    show (-eLast n : E) (Fin.last n) ≤ -(1 / 2 : ℝ)
    simp [eLast]
    norm_num
  rw [signedCollapseRaw, hcut]
  module


-- @@ L264-270 verbatim
theorem signedCollapse_cube_boundary {t : I^(Fin (n + 1))}
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    B.signedCollapse (cubeToBridgeDomain t) = southPole n := by
  apply Subtype.ext
  rw [signedCollapse_coe, B.signedCollapseRaw_cube_boundary ht,
    southPole_coe, norm_neg, norm_eLast]
  simp


-- @@ L272-277 verbatim
/-- Cubical generalized loop of the canonical signed collapse. -/
def signedCollapseLoop :
    Ω^ (Fin (n + 1)) (UnitSphere E) (southPole n) :=
  ⟨B.signedCollapseCM.comp
      ⟨cubeToBridgeDomain, continuous_cubeToBridgeDomain⟩,
    fun _ ht => B.signedCollapse_cube_boundary ht⟩


-- @@ L279-280 verbatim
@[simp] lemma signedCollapseLoop_apply (t : I^(Fin (n + 1))) :
    B.signedCollapseLoop t = B.signedCollapse (cubeToBridgeDomain t) := rfl


-- @@ L282-287 verbatim
lemma inner_signedCollapse_source_pos (x : E) :
    0 < ⟪(B.signedCollapse x : E), B.northSource x⟫ := by
  rw [signedCollapse_coe, real_inner_smul_left]
  exact mul_pos
    (inv_pos.mpr (norm_pos_iff.mpr (B.signedCollapseRaw_ne_zero x)))
    (B.inner_signedCollapseRaw_source_pos x)


-- @@ L289-298 verbatim
lemma northSourcePoint_ne_neg_signedCollapse (x : E) :
    B.northSourcePoint x ≠ -B.signedCollapse x := by
  intro heq
  have hcoe : B.northSource x = -(B.signedCollapse x : E) := by
    have h := congrArg Subtype.val heq
    simpa [northSourcePoint_coe, coe_neg_sphere] using h
  have hpos := B.inner_signedCollapse_source_pos x
  rw [hcoe, inner_neg_right, real_inner_self_eq_norm_sq,
    UnitSphere.norm_coe] at hpos
  norm_num at hpos


-- @@ L300-302 verbatim
lemma dist_northSourcePoint_signedCollapse_lt_two (x : E) :
    dist (B.northSourcePoint x) (B.signedCollapse x) < 2 :=
  dist_lt_two_of_ne_neg _ _ (B.northSourcePoint_ne_neg_signedCollapse x)


-- @@ L304-307 verbatim
lemma dist_prepLoop_signedCollapseLoop_lt_two (t : I^(Fin (n + 1))) :
    dist (prepLoop B.approx t) (B.signedCollapseLoop t) < 2 := by
  rw [B.prepLoop_eq_northSourcePoint, signedCollapseLoop_apply]
  exact B.dist_northSourcePoint_signedCollapse_lt_two _


-- @@ L309-317 verbatim
/-- Normalize straight chords from the original bridge representative to the signed
collapse.  On the whole cube boundary both endpoints are the south pole. -/
def prepLoopToSignedCollapseHomotopy :
    ContinuousMap.HomotopyRel (prepLoop B.approx).1 B.signedCollapseLoop.1
      (Cube.boundary (Fin (n + 1))) :=
  chordHomotopyRel (prepLoop B.approx).1 B.signedCollapseLoop.1
    B.dist_prepLoop_signedCollapseLoop_lt_two
    (Cube.boundary (Fin (n + 1))) fun t ht =>
      ((prepLoop B.approx).2 t ht).trans (B.signedCollapseLoop.2 t ht).symm


-- @@ L319-321 verbatim
theorem prepLoop_homotopic_signedCollapseLoop :
    GenLoop.Homotopic (prepLoop B.approx) B.signedCollapseLoop :=
  ⟨B.prepLoopToSignedCollapseHomotopy⟩


-- @@ L323-326 verbatim
theorem signedCollapseLoop_homotopic_northThomLoop :
    GenLoop.Homotopic B.signedCollapseLoop B.northThomLoop :=
  B.prepLoop_homotopic_signedCollapseLoop.symm.trans
    B.prepLoop_homotopic_northThomLoop


-- @@ L328-336 verbatim
/-- The canonical signed collapse at the bridge endpoint represents the original
homotopy class. -/
theorem signedCollapseLoop_class_eq :
    (⟦B.signedCollapseLoop⟧ : HomotopyGroup (Fin (n + 1))
      (UnitSphere E) (southPole n)) = z := by
  calc
    ⟦B.signedCollapseLoop⟧ = ⟦prepLoop B.approx⟧ :=
      (Quotient.sound B.prepLoop_homotopic_signedCollapseLoop).symm
    _ = z := B.prepLoop_class_eq


-- @@ L338-343 verbatim
/-- Consequently the new canonical signed loop and the previously constructed
northern Thom loop have the same homotopy class. -/
theorem signedCollapseLoop_class_eq_northThomLoop :
    (⟦B.signedCollapseLoop⟧ : HomotopyGroup (Fin (n + 1))
      (UnitSphere E) (southPole n)) = ⟦B.northThomLoop⟧ := by
  rw [B.signedCollapseLoop_class_eq, B.northThomLoop_class_eq]


-- @@ L345-345 verbatim
end BridgeData


-- @@ L347-347 verbatim
end Submission
