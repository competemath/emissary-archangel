import Mathlib
import Submission.BridgeLevel
import Submission.TubeApproximation


-- @@ L5-13 verbatim
/-!
# A genuine bridge built from the explicit tube approximation

This module feeds `tubeApproximation` into the forward bridge construction.
Unlike `chosenBridge`, the approximation is completely explicit; only the
small Sard-regular horizontal value is chosen.  The northern sheet lies in the
region where the southern plateau is the identity, so it can be compared
directly with the tube's differential frame.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Topology.Homotopy Function

-- @@ L18-18 verbatim
open scoped Topology unitInterval ContDiff


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
variable {m : ℕ}


-- @@ L24-24 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L25-25 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L27-27 verbatim
/-! ## The plateau is invisible on the northern sheet -/


-- @@ L29-31 verbatim
@[simp] theorem vertC_plateauAux (u : E) :
    vertC (plateauAux u) = plateauB (vertC u) := by
  simp [plateauAux, vertC, eLast]


-- @@ L33-38 verbatim
theorem tubeApproximation_nraw (k : ℕ) (v : Fin (m + 3) → ℝ) :
    nraw (tubeApproximation (m := m) k) v = tubeApproxRaw k v := by
  rw [nraw]
  change ‖tubeApproxRaw k v‖⁻¹ • tubeApproxRaw k v = tubeApproxRaw k v
  rw [norm_tubeApproxRaw]
  simp


-- @@ L40-79 verbatim
/-- A positive vertical coordinate after plateauing forces the input latitude
to be positive.  Consequently the plateau was already the identity. -/
theorem tubeApproximation_nprep_eq_raw_of_vert_pos (k : ℕ)
    (v : Fin (m + 3) → ℝ)
    (hpos : 0 < vertC (nprep (tubeApproximation (m := m) k) v)) :
    nprep (tubeApproximation (m := m) k) v = tubeApproxRaw k v := by
  let u : E := tubeApproxRaw k v
  have hu : ‖u‖ = 1 := norm_tubeApproxRaw k v
  have hpraw : praw (tubeApproximation (m := m) k) v = plateauAux u := by
    rw [praw, tubeApproximation_nraw]
  have hpraw0 : praw (tubeApproximation (m := m) k) v ≠ 0 :=
    praw_ne_zero _ v
  have hnormpos : 0 < ‖praw (tubeApproximation (m := m) k) v‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr hpraw0)
  have hpvert : 0 < vertC (praw (tubeApproximation (m := m) k) v) := by
    change 0 < ‖praw (tubeApproximation (m := m) k) v‖⁻¹ *
      vertC (praw (tubeApproximation (m := m) k) v) at hpos
    rcases mul_pos_iff.mp hpos with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (le_of_lt hnormpos)) h.1)
  have hbpos : 0 < plateauB (vertC u) := by
    rw [hpraw, vertC_plateauAux] at hpvert
    exact hpvert
  have htLower : -1 ≤ vertC u :=
    neg_le_of_abs_le (abs_vertC_le_one hu)
  have htUpper : vertC u ≤ 1 :=
    le_of_abs_le (abs_vertC_le_one hu)
  have ha0 : 0 ≤ plateauA (vertC u) := plateauA_nonneg _
  have ha1 : plateauA (vertC u) ≤ 1 := plateauA_le_one _
  have hlat : 0 < vertC u := by
    rw [plateauB] at hbpos
    have hmul : plateauA (vertC u) * (1 + vertC u) ≤
        1 + vertC u := by
      nlinarith
    linarith
  have hplateau : plateauAux u = u :=
    plateauAux_of_ge (by linarith)
  rw [nprep, hpraw, hplateau, hu]
  simp
  rfl


-- @@ L81-104 verbatim
theorem tubeApproximation_nprep_eq_north_iff (k : ℕ)
    (v : Fin (m + 3) → ℝ) (y : EuclideanSpace ℝ (Fin (m + 2)))
    (hy : ‖y‖ < 1) :
    nprep (tubeApproximation (m := m) k) v = northPoint y ↔
      tubeApproxRaw k v = northPoint y := by
  constructor
  · intro h
    have hpos : 0 < vertC
        (nprep (tubeApproximation (m := m) k) v) := by
      rw [h]
      exact vertC_northPoint_pos hy
    rw [tubeApproximation_nprep_eq_raw_of_vert_pos k v hpos] at h
    exact h
  · intro h
    have hu : ‖tubeApproxRaw (m := m) k v‖ = 1 := norm_tubeApproxRaw k v
    have hvert : -(1 / 4 : ℝ) ≤ vertC (tubeApproxRaw k v) := by
      rw [h]
      rw [vertC_northPoint]
      have hsqrt : (0 : ℝ) ≤ Real.sqrt (1 - ‖y‖ ^ 2) := Real.sqrt_nonneg _
      linarith
    rw [nprep, praw, tubeApproximation_nraw,
      plateauAux_of_ge hvert, hu]
    simp
    exact h


-- @@ L106-106 verbatim
/-! ## The northern tube level lies inside the coordinate tube -/


-- @@ L108-110 verbatim
/-- The normal offset over a small northern horizontal value. -/
def tubeNorthOffset (y : F) : F :=
  (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ • y


-- @@ L112-118 verbatim
theorem norm_northPoint_of_norm_lt_one (y : F) (hy : ‖y‖ < 1) :
    ‖northPoint y‖ = 1 := by
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hsq0 : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith
  have hsplit := norm_sq_split (northPoint y)
  rw [initCLM_northPoint, vertC_northPoint, Real.sq_sqrt hsq0] at hsplit
  nlinarith [norm_nonneg (northPoint y)]


-- @@ L120-131 verbatim
theorem tubeNorthOffset_norm_lt_quarter (y : F) (hy : ‖y‖ < 1 / 8) :
    ‖tubeNorthOffset y‖ < 1 / 4 := by
  let s : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hsq0 : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 - ‖y‖ ^ 2 := Real.sq_sqrt hsq0
  have hsHalf : 1 / 2 < s := by nlinarith
  have hs : 0 < s := by linarith
  rw [tubeNorthOffset, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs), inv_mul_eq_div, div_lt_iff₀ hs]
  nlinarith


-- @@ L133-217 verbatim
/-- A small northern value cannot acquire a preimage in the cutoff transition
annulus.  Its entire preimage lies in the radius-`1/4` tube and has the fixed
normal coordinate `tubeNorthOffset y`. -/
theorem tubeThomVec_eq_northPoint_inner_and_wCoord (k : ℕ) (x : E) (y : F)
    (hy : ‖y‖ < 1 / 8) (h : tubeThomVec k x = northPoint y) :
    x ∈ tubeRegion (1 / 4) ∧ wCoord k x = tubeNorthOffset y := by
  let a : ℝ := ‖tubeCollapseRaw k x‖⁻¹
  let c : ℝ := tubeCutoff x
  let s : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)
  have ha : 0 < a := by
    exact inv_pos.mpr (norm_pos_iff.mpr (tubeCollapseRaw_ne_zero k x))
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hsq0 : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 - ‖y‖ ^ 2 := Real.sq_sqrt hsq0
  have hs : 0 < s := by
    nlinarith
  have hlast : a * (2 * c - 1) = s := by
    have h' := congrArg (fun z : E => z (Fin.last (m + 2))) h
    change ‖tubeCollapseRaw k x‖⁻¹ *
        tubeCollapseRaw k x (Fin.last (m + 2)) =
      northPoint y (Fin.last (m + 2)) at h'
    rw [tubeCollapseRaw_last] at h'
    change ‖tubeCollapseRaw k x‖⁻¹ * (2 * tubeCutoff x - 1) =
      vertC (northPoint y) at h'
    rw [vertC_northPoint] at h'
    exact h'
  have hcHalf : 1 / 2 < c := by
    have hprod : 0 < a * (2 * c - 1) := hlast.symm ▸ hs
    rcases mul_pos_iff.mp hprod with hp | hn
    · linarith [hp.2]
    · exact False.elim ((not_lt_of_ge (le_of_lt ha)) hn.1)
  have hc0 : 0 ≤ c := tubeCutoff_nonneg x
  have hc1 : c ≤ 1 := tubeCutoff_le_one x
  have hgood : x ∈ tubeGood :=
    tubeGood_of_tubeCutoff_ne_zero (by linarith)
  have hinitRaw : initCLM (m + 2) (tubeCollapseRaw k x) =
      tubeCollapseHorizontal k x := by
    apply (WithLp.equiv 2 _).injective
    funext i
    exact tubeCollapseRaw_coord k x i
  have hhoriz : a • tubeCollapseHorizontal k x = y := by
    have h' := congrArg (initCLM (m + 2)) h
    rw [tubeThomVec, map_smul, hinitRaw, initCLM_northPoint] at h'
    exact h'
  have hinner : x ∈ tubeRegion (1 / 4) := by
    by_contra hout
    have hdist : 1 / 16 ≤ tubeDistSq x := by
      change ¬ tubeDistSq x < (1 / 4 : ℝ) ^ 2 at hout
      norm_num at hout ⊢
      exact hout
    have hwSq : ‖wCoord k x‖ ^ 2 = tubeDistSq x :=
      norm_wCoord_sq k hgood
    have hw0 : 0 ≤ ‖wCoord k x‖ := norm_nonneg _
    have hwQuarter : 1 / 4 ≤ ‖wCoord k x‖ := by
      nlinarith
    have hnorm : a * c * ‖wCoord k x‖ = ‖y‖ := by
      have hn := congrArg norm hhoriz
      rw [tubeCollapseHorizontal, norm_smul, norm_smul,
        Real.norm_eq_abs, abs_of_pos ha] at hn
      change a * (|c| * ‖wCoord k x‖) = ‖y‖ at hn
      rw [abs_of_nonneg hc0] at hn
      nlinarith
    have hsc : s ≤ a * c := by
      rw [← hlast]
      nlinarith [mul_nonneg (le_of_lt ha) (by linarith : 0 ≤ c - (2 * c - 1))]
    have hsy : s ≤ 4 * ‖y‖ := by
      nlinarith [mul_nonneg (mul_nonneg (le_of_lt ha) hc0)
        (sub_nonneg.mpr hwQuarter)]
    have hsHalf : 1 / 2 < s := by
      nlinarith
    nlinarith
  refine ⟨hinner, ?_⟩
  have hc : c = 1 := tubeCutoff_eq_one_on_inner hinner
  have hhoriz' : a • wCoord k x = y := by
    simpa [tubeCollapseHorizontal, c, hc] using hhoriz
  have has : a = s := by
    rw [hc] at hlast
    linarith
  change wCoord k x = s⁻¹ • y
  calc
    wCoord k x = (s⁻¹ * s) • wCoord k x := by
      rw [inv_mul_cancel₀ hs.ne', one_smul]
    _ = s⁻¹ • (s • wCoord k x) := by rw [smul_smul]
    _ = s⁻¹ • y := by rw [← has, hhoriz']


-- @@ L219-259 verbatim
/-- Conversely, the fixed small normal coordinate produces exactly the
northern sphere point. -/
theorem tubeThomVec_eq_northPoint_of_inner_wCoord (k : ℕ) (x : E) (y : F)
    (hy : ‖y‖ < 1 / 8) (hinner : x ∈ tubeRegion (1 / 4))
    (hw : wCoord k x = tubeNorthOffset y) :
    tubeThomVec k x = northPoint y := by
  let s : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hsq0 : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 - ‖y‖ ^ 2 := Real.sq_sqrt hsq0
  have hs : 0 < s := by nlinarith
  have hc : tubeCutoff x = 1 := tubeCutoff_eq_one_on_inner hinner
  have hhoriz : tubeCollapseHorizontal k x = tubeNorthOffset y := by
    rw [tubeCollapseHorizontal, hc, one_smul, hw]
  have hraw : tubeCollapseRaw k x = s⁻¹ • northPoint y := by
    apply (WithLp.equiv 2 _).injective
    funext j
    induction j using Fin.lastCases with
    | last =>
        change tubeCollapseRaw k x (Fin.last (m + 2)) =
          s⁻¹ * vertC (northPoint y)
        rw [tubeCollapseRaw_last, hc, vertC_northPoint]
        change 2 * 1 - 1 = s⁻¹ * s
        rw [inv_mul_cancel₀ hs.ne']
        norm_num
    | cast i =>
        change tubeCollapseRaw k x i.castSucc =
          s⁻¹ * northPoint y i.castSucc
        rw [tubeCollapseRaw_coord, hhoriz, tubeNorthOffset]
        change s⁻¹ * y i = s⁻¹ * northPoint y i.castSucc
        have hi := congrArg (fun z : F => z i) (initCLM_northPoint y)
        change northPoint y i.castSucc = y i at hi
        rw [hi]
  have hnormNorth : ‖northPoint y‖ = 1 :=
    norm_northPoint_of_norm_lt_one y (hy.trans (by norm_num))
  have hnormRaw : ‖tubeCollapseRaw k x‖ = s⁻¹ := by
    rw [hraw, norm_smul, hnormNorth, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hs)]
  rw [tubeThomVec, hnormRaw, hraw, inv_inv, smul_smul,
    mul_inv_cancel₀ hs.ne', one_smul]


-- @@ L261-268 verbatim
theorem tubeThomVec_eq_northPoint_iff (k : ℕ) (x : E) (y : F)
    (hy : ‖y‖ < 1 / 8) :
    tubeThomVec k x = northPoint y ↔
      x ∈ tubeRegion (1 / 4) ∧ wCoord k x = tubeNorthOffset y := by
  constructor
  · exact tubeThomVec_eq_northPoint_inner_and_wCoord k x y hy
  · rintro ⟨hinner, hw⟩
    exact tubeThomVec_eq_northPoint_of_inner_wCoord k x y hy hinner hw


-- @@ L270-272 verbatim
/-- The offset circle in the ambient tube chart. -/
def tubeOffsetCirclePoint (k : ℕ) (y : F) (θ : ℝ) : E :=
  tubeMap k θ (tubeNorthOffset y)


-- @@ L274-283 verbatim
/-- Every tube-chart point with normal coordinate of norm below `1/4` lies in
the inner tube. -/
theorem tubeMap_mem_inner_of_norm_lt_quarter (k : ℕ) (θ : ℝ) {w : F}
    (hw : ‖w‖ < 1 / 4) :
    tubeMap k θ w ∈ tubeRegion (m := m) (1 / 4) := by
  have hA : 0 < tubeA k θ w :=
    tubeA_pos k θ (hw.trans (by norm_num))
  change tubeDistSq (tubeMap k θ w) < (1 / 4 : ℝ) ^ 2
  rw [tubeDistSq_tubeMap k θ hA]
  nlinarith [norm_nonneg w]


-- @@ L285-290 verbatim
/-- The explicit offset circle is a smooth parametrized curve. -/
theorem contDiff_tubeOffsetCirclePoint (k : ℕ) (y : F) :
    ContDiff ℝ ∞ (tubeOffsetCirclePoint k y) := by
  change ContDiff ℝ ∞ fun θ => tubeMap k θ (tubeNorthOffset y)
  simpa only [Function.comp_def, id_eq, tubeNorthOffset] using
    (contDiff_tubeMap k).comp (contDiff_id.prodMk contDiff_const)


-- @@ L292-297 verbatim
theorem tubeOffsetCirclePoint_mem_inner (k : ℕ) (y : F)
    (hy : ‖y‖ < 1 / 8) (θ : ℝ) :
    tubeOffsetCirclePoint k y θ ∈ tubeRegion (1 / 4) := by
  have hq : ‖tubeNorthOffset y‖ < 1 / 4 :=
    tubeNorthOffset_norm_lt_quarter y hy
  exact tubeMap_mem_inner_of_norm_lt_quarter k θ hq


-- @@ L299-306 verbatim
theorem tubeThomVec_offsetCirclePoint (k : ℕ) (y : F)
    (hy : ‖y‖ < 1 / 8) (θ : ℝ) :
    tubeThomVec k (tubeOffsetCirclePoint k y θ) = northPoint y := by
  apply tubeThomVec_eq_northPoint_of_inner_wCoord k _ y hy
    (tubeOffsetCirclePoint_mem_inner k y hy θ)
  unfold tubeOffsetCirclePoint
  exact wCoord_tubeMap k θ
    (tubeA_pos k θ ((tubeNorthOffset_norm_lt_quarter y hy).trans (by norm_num)))


-- @@ L308-326 verbatim
/-- Exact global description of the small northern fiber: one offset tube
circle, with no transition-annulus components. -/
theorem tubeThomVec_north_fiber_eq_range (k : ℕ) (y : F)
    (hy : ‖y‖ < 1 / 8) :
    {x : E | tubeThomVec k x = northPoint y} =
      Set.range (tubeOffsetCirclePoint k y) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hinner, hw⟩ :=
      (tubeThomVec_eq_northPoint_iff k x y hy).mp hx
    have hgood : x ∈ tubeGood := innerTube_subset_tubeGood hinner
    obtain ⟨θ, hc, hs⟩ := exists_angle hgood
    refine ⟨θ, ?_⟩
    unfold tubeOffsetCirclePoint
    rw [← hw]
    exact tubeMap_wCoord k hgood hc hs
  · rintro ⟨θ, rfl⟩
    exact tubeThomVec_offsetCirclePoint k y hy θ


-- @@ L328-328 verbatim
/-! ## The special bridge -/


-- @@ L330-353 verbatim
/-- A forward bridge whose approximation is the exact affine tube model. -/
def tubeExplicitBridge (k : ℕ) :
    BridgeData (m + 2) (tubeThomStableClass (m := m) k) := by
  let hex := exists_bridge_regular_value
    (tubeApproximation (m := m) k) (by omega : 0 < m + 2)
  let y := Classical.choose hex
  have hy := Classical.choose_spec hex
  refine {
    p := tubeThomStableGenLoop k
    approx := tubeApproximation k
    y := y
    norm_y_pos := hy.1
    norm_y_lt := hy.2.1
    axis_pos := ?_
    regular_y := hy.2.2.2
    class_eq := ?_
  }
  · intro hn
    convert hy.2.2.1 using 1
  · calc
      tubeThomStableClass k = ⟦tubeThomStableGenLoop k⟧ :=
        (tubeThomStableGenLoop_class k).symm
      _ = ⟦collared (tubeThomStableGenLoop k)⟧ :=
        Quotient.sound (homotopic_collared _)


-- @@ L355-367 verbatim
/-- The positive sheet of the special bridge is an actual level set of the
explicit tube map; the auxiliary southern plateau introduces no extra points. -/
theorem tubeExplicitBridge_north_iff (k : ℕ) (x : E) :
    nprep (tubeExplicitBridge (m := m) k).approx (WithLp.ofLp x) =
        northPoint (tubeExplicitBridge (m := m) k).y ↔
      tubeApproxRaw k (WithLp.ofLp x) =
        northPoint (tubeExplicitBridge (m := m) k).y := by
  change nprep (tubeApproximation (m := m) k) (WithLp.ofLp x) =
      northPoint (tubeExplicitBridge (m := m) k).y ↔
    tubeApproxRaw k (WithLp.ofLp x) =
      northPoint (tubeExplicitBridge (m := m) k).y
  exact tubeApproximation_nprep_eq_north_iff k _ _
    (tubeExplicitBridge (m := m) k).norm_y_lt_one


-- @@ L369-371 verbatim
/-- The offset circle pulled back through the affine bridge coordinates. -/
def tubeBridgeCirclePoint (k : ℕ) (y : F) (θ : ℝ) : E :=
  WithLp.toLp 2 fun i => (tubeOffsetCirclePoint k y θ i + 6) / 12


-- @@ L373-384 verbatim
/-- The affine pullback of the offset circle to bridge coordinates is smooth. -/
theorem contDiff_tubeBridgeCirclePoint (k : ℕ) (y : F) :
    ContDiff ℝ ∞ (tubeBridgeCirclePoint k y) := by
  have h : tubeBridgeCirclePoint k y = fun θ =>
      (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm
        (fun i => (tubeOffsetCirclePoint k y θ i + 6) / 12) := rfl
  rw [h]
  apply (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm.contDiff.comp
  rw [contDiff_pi]
  intro i
  exact (((EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff.comp
    (contDiff_tubeOffsetCirclePoint k y)).add contDiff_const).div_const 12


-- @@ L386-390 verbatim
@[simp] theorem tubeBridgeCirclePoint_apply (k : ℕ) (y : F) (θ : ℝ)
    (i : Fin (m + 3)) :
    tubeBridgeCirclePoint k y θ i =
      (tubeOffsetCirclePoint k y θ i + 6) / 12 :=
  rfl


-- @@ L392-399 verbatim
theorem tubeApproxAmbient_bridgeCirclePoint (k : ℕ) (y : F) (θ : ℝ) :
    tubeApproxAmbient (WithLp.ofLp (tubeBridgeCirclePoint k y θ)) =
      tubeOffsetCirclePoint k y θ := by
  apply (EuclideanSpace.equiv (Fin (m + 3)) ℝ).injective
  funext i
  change 12 * ((tubeOffsetCirclePoint k y θ i + 6) / 12) - 6 =
    tubeOffsetCirclePoint k y θ i
  ring


-- @@ L401-433 verbatim
/-- Exact positive/northern fiber of the special `BridgeData` in its own source
coordinates. -/
theorem tubeExplicitBridge_north_fiber_eq_range (k : ℕ) :
    {x : E |
      nprep (tubeExplicitBridge (m := m) k).approx (WithLp.ofLp x) =
        northPoint (tubeExplicitBridge (m := m) k).y} =
      Set.range (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y) := by
  let B := tubeExplicitBridge (m := m) k
  have hy : ‖B.y‖ < 1 / 8 := B.norm_y_lt
  ext x
  constructor
  · intro hx
    have hraw := (tubeExplicitBridge_north_iff (m := m) k x).mp hx
    change tubeThomVec k (tubeApproxAmbient (WithLp.ofLp x)) =
      northPoint B.y at hraw
    have hmem : tubeApproxAmbient (WithLp.ofLp x) ∈
        {z : E | tubeThomVec k z = northPoint B.y} := hraw
    rw [tubeThomVec_north_fiber_eq_range k B.y hy] at hmem
    obtain ⟨θ, hθ⟩ := hmem
    refine ⟨θ, ?_⟩
    apply (EuclideanSpace.equiv (Fin (m + 3)) ℝ).injective
    funext i
    have hi := congrArg (fun z : E => z i) hθ.symm
    change 12 * x i - 6 = tubeOffsetCirclePoint k B.y θ i at hi
    change (tubeOffsetCirclePoint k B.y θ i + 6) / 12 = x i
    linarith
  · rintro ⟨θ, rfl⟩
    apply (tubeExplicitBridge_north_iff (m := m) k _).mpr
    change tubeThomVec k
      (tubeApproxAmbient (WithLp.ofLp (tubeBridgeCirclePoint k B.y θ))) =
        northPoint B.y
    rw [tubeApproxAmbient_bridgeCirclePoint]
    exact tubeThomVec_offsetCirclePoint k B.y hy θ


-- @@ L435-435 verbatim
end Submission
