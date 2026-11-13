import Mathlib
import Submission.MorsePerturb


-- @@ L4-16 verbatim
/-!
# Transport of the compact slab fiber by a small vertical diffeomorphism

A `SmallVerticalAmplitude` is zero on both outer collars and has Lipschitz
constant strictly below one.  Comparing an interior point with the point of the
same spatial coordinate on either collar boundary shows that its vertical shift
cannot cross that boundary.  Consequently the global vertical diffeomorphism
restricts to an equivalence between the original compact slab fiber and the
fiber of the pulled-back cobordism.

This is the global coverage bridge needed after the finite IFT cover has been
chosen on the original cobordism.
-/


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open Set Function Metric

-- @@ L21-21 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L23-23 verbatim
namespace Submission


-- @@ L25-25 verbatim
variable {n : ℕ}


-- @@ L27-27 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L29-42 verbatim
/-- Changing only the time coordinate changes Euclidean distance by exactly
the absolute time difference. -/
theorem dist_spaceTime_same_space (v : E') (t : ℝ) :
    dist v (spaceTime (initCLM (n + 1) v) t) = |tcoord v - t| := by
  rw [dist_eq_norm]
  have hdiff :
      v - spaceTime (initCLM (n + 1) v) t =
        (tcoord v - t) • timeVec := by
    conv_lhs =>
      lhs
      rw [← spaceTime_init_vert v]
    rw [spaceTime_eq_affine, spaceTime_eq_affine, sub_smul]
    abel
  rw [hdiff, norm_smul, norm_timeVec, mul_one, Real.norm_eq_abs]


-- @@ L44-44 verbatim
namespace SmallVerticalAmplitude


-- @@ L46-46 verbatim
variable (a : SmallVerticalAmplitude (n := n))


-- @@ L48-66 verbatim
/-- The amplitude at an interior point is smaller than its distance from the
incoming collar boundary. -/
theorem abs_apply_lt_sub_quarter {v : E'} (hv : 1 / 4 < tcoord v) :
    |a v| < tcoord v - 1 / 4 := by
  let w : E' := spaceTime (initCLM (n + 1) v) (1 / 4)
  have hwt : tcoord w = 1 / 4 := by
    change tcoord (spaceTime (initCLM (n + 1) v) (1 / 4)) = 1 / 4
    exact tcoord_spaceTime (initCLM (n + 1) v) (1 / 4)
  have haw : a w = 0 :=
    a.toVerticalAmplitude.collar_zero w (Or.inl (by rw [hwt]))
  have hlip := a.lipschitz.dist_le_mul v w
  have hK : (a.K : ℝ) < 1 := by exact_mod_cast a.K_lt_one
  have hdist : dist v w = tcoord v - 1 / 4 := by
    change dist v (spaceTime (initCLM (n + 1) v) (1 / 4)) = _
    rw [dist_spaceTime_same_space, abs_of_pos (by linarith)]
  rw [Real.dist_eq, haw, sub_zero, hdist] at hlip
  exact hlip.trans_lt (by
    have hpos : 0 < tcoord v - 1 / 4 := by linarith
    nlinarith [a.K.coe_nonneg])


-- @@ L68-87 verbatim
/-- The amplitude at an interior point is smaller than its distance from the
outgoing collar boundary. -/
theorem abs_apply_lt_threeQuarter_sub {v : E'} (hv : tcoord v < 3 / 4) :
    |a v| < 3 / 4 - tcoord v := by
  let w : E' := spaceTime (initCLM (n + 1) v) (3 / 4)
  have hwt : tcoord w = 3 / 4 := by
    change tcoord (spaceTime (initCLM (n + 1) v) (3 / 4)) = 3 / 4
    exact tcoord_spaceTime (initCLM (n + 1) v) (3 / 4)
  have haw : a w = 0 :=
    a.toVerticalAmplitude.collar_zero w (Or.inr (by rw [hwt]))
  have hlip := a.lipschitz.dist_le_mul v w
  have hK : (a.K : ℝ) < 1 := by exact_mod_cast a.K_lt_one
  have hdist : dist v w = 3 / 4 - tcoord v := by
    change dist v (spaceTime (initCLM (n + 1) v) (3 / 4)) = _
    rw [dist_spaceTime_same_space, abs_of_neg (by linarith)]
    ring
  rw [Real.dist_eq, haw, sub_zero, hdist] at hlip
  exact hlip.trans_lt (by
    have hpos : 0 < 3 / 4 - tcoord v := by linarith
    nlinarith [a.K.coe_nonneg])


-- @@ L89-99 verbatim
/-- A nonnegative time coordinate stays nonnegative after the small vertical
shift. -/
theorem zero_le_tcoord_verticalShift {v : E'} (hv : 0 ≤ tcoord v) :
    0 ≤ tcoord (verticalShift a v) := by
  rw [tcoord_verticalShift]
  by_cases hleft : tcoord v ≤ 1 / 4
  · rw [a.toVerticalAmplitude.collar_zero v (Or.inl hleft), add_zero]
    exact hv
  · have habs := a.abs_apply_lt_sub_quarter (lt_of_not_ge hleft)
    have hneg : -|a v| ≤ a v := neg_abs_le _
    linarith


-- @@ L101-111 verbatim
/-- A time coordinate at most one stays at most one after the small vertical
shift. -/
theorem tcoord_verticalShift_le_one {v : E'} (hv : tcoord v ≤ 1) :
    tcoord (verticalShift a v) ≤ 1 := by
  rw [tcoord_verticalShift]
  by_cases hright : 3 / 4 ≤ tcoord v
  · rw [a.toVerticalAmplitude.collar_zero v (Or.inr hright), add_zero]
    exact hv
  · have habs := a.abs_apply_lt_threeQuarter_sub (lt_of_not_ge hright)
    have hpos : a v ≤ |a v| := le_abs_self _
    linarith


-- @@ L113-119 verbatim
/-- The global vertical diffeomorphism preserves the closed time slab. -/
theorem verticalShift_mem_timeSlab {v : E'}
    (hv : 0 ≤ tcoord v ∧ tcoord v ≤ 1) :
    0 ≤ tcoord (verticalShift a v) ∧
      tcoord (verticalShift a v) ≤ 1 :=
  ⟨a.zero_le_tcoord_verticalShift hv.1,
    a.tcoord_verticalShift_le_one hv.2⟩


-- @@ L121-128 verbatim
/-- A point of the pulled-back slab fiber maps to a point of the original slab
fiber. -/
theorem verticalShift_mem_fiber {C : FramedLevelCobordism n} {v : E'}
    (hv : v ∈ (a.toVerticalAmplitude.pullback C).fiber) :
    verticalShift a v ∈ C.fiber := by
  refine ⟨hv.1, ?_, ?_⟩
  · exact a.zero_le_tcoord_verticalShift hv.2.1
  · exact a.tcoord_verticalShift_le_one hv.2.2


-- @@ L130-162 verbatim
/-- The inverse diffeomorphism also carries the original closed slab into the
closed slab.  Here only collar identity is needed: an inverse point outside the
middle region is fixed. -/
theorem symm_mem_timeSlab {w : E'} (hw : 0 ≤ tcoord w ∧ tcoord w ≤ 1) :
    0 ≤ tcoord (a.diffeomorph.symm w) ∧
      tcoord (a.diffeomorph.symm w) ≤ 1 := by
  let v : E' := a.diffeomorph.symm w
  have hshift : verticalShift a v = w := by
    change a.diffeomorph v = w
    exact a.diffeomorph.apply_symm_apply w
  constructor
  · by_cases hleft : tcoord v ≤ 1 / 4
    · have ha : a v = 0 :=
        a.toVerticalAmplitude.collar_zero v (Or.inl hleft)
      have htime : tcoord v = tcoord w := by
        rw [← hshift, tcoord_verticalShift, ha, add_zero]
      change 0 ≤ tcoord v
      rw [htime]
      exact hw.1
    · have : 1 / 4 < tcoord v := lt_of_not_ge hleft
      change 0 ≤ tcoord v
      linarith
  · by_cases hright : 3 / 4 ≤ tcoord v
    · have ha : a v = 0 :=
        a.toVerticalAmplitude.collar_zero v (Or.inr hright)
      have htime : tcoord v = tcoord w := by
        rw [← hshift, tcoord_verticalShift, ha, add_zero]
      change tcoord v ≤ 1
      rw [htime]
      exact hw.2
    · have : tcoord v < 3 / 4 := lt_of_not_ge hright
      change tcoord v ≤ 1
      linarith


-- @@ L164-174 verbatim
/-- A point of the original slab fiber pulls back to a point of the perturbed
slab fiber. -/
theorem symm_mem_pullback_fiber {C : FramedLevelCobordism n} {w : E'}
    (hw : w ∈ C.fiber) :
    a.diffeomorph.symm w ∈ (a.toVerticalAmplitude.pullback C).fiber := by
  have hshift : verticalShift a (a.diffeomorph.symm w) = w := by
    change a.diffeomorph (a.diffeomorph.symm w) = w
    exact a.diffeomorph.apply_symm_apply w
  refine ⟨?_, (a.symm_mem_timeSlab hw.2).1, (a.symm_mem_timeSlab hw.2).2⟩
  rw [VerticalAmplitude.pullback_G, hshift]
  exact hw.1


-- @@ L176-189 verbatim
/-- The vertical diffeomorphism restricts to an actual equivalence of the two
compact slab fibers. -/
def slabFiberEquiv (C : FramedLevelCobordism n) :
    (a.toVerticalAmplitude.pullback C).fiber ≃ C.fiber where
  toFun v := ⟨verticalShift a v, a.verticalShift_mem_fiber v.2⟩
  invFun w := ⟨a.diffeomorph.symm w, a.symm_mem_pullback_fiber w.2⟩
  left_inv v := by
    apply Subtype.ext
    change a.diffeomorph.symm (a.diffeomorph v) = v
    exact a.diffeomorph.symm_apply_apply v
  right_inv w := by
    apply Subtype.ext
    change a.diffeomorph (a.diffeomorph.symm w) = w
    exact a.diffeomorph.apply_symm_apply w


-- @@ L191-191 verbatim
end SmallVerticalAmplitude


-- @@ L193-193 verbatim
end Submission
