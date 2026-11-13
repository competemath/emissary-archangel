import Mathlib
import Submission.TubeExplicitLedger
import Submission.TubeFrameClass


-- @@ L5-12 verbatim
/-!
# Frame comparison for the explicit tube bridge

This module connects the intrinsic frame used by `Delta` to the already
computed derivative frame of the explicit tube.  The normal coordinate of the
northern sphere chart is Mathlib's smooth diffeomorphism from Euclidean space
to the open unit ball.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace Submission


-- @@ L18-18 verbatim
open Set Function Metric InnerProductSpace

-- @@ L19-19 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval ContDiff


-- @@ L21-21 verbatim
variable {m : ℕ}


-- @@ L23-23 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L24-24 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L26-28 verbatim
/-- Horizontal coordinates of the normalized vector `(w, 1)`. -/
def tubeHorizontalChart : F → F :=
  OpenPartialHomeomorph.univUnitBall


-- @@ L30-32 verbatim
@[simp] theorem tubeHorizontalChart_apply (w : F) :
    tubeHorizontalChart w = (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ • w :=
  rfl


-- @@ L34-37 verbatim
theorem tubeHorizontalChart_mem_ball (w : F) :
    tubeHorizontalChart w ∈ Metric.ball (0 : F) 1 := by
  apply OpenPartialHomeomorph.univUnitBall.map_source
  exact Set.mem_univ w


-- @@ L39-85 verbatim
/-- The unit-ball chart has a surjective derivative everywhere.  We derive this
from its smooth local inverse rather than expanding the derivative formula. -/
theorem surjective_fderiv_tubeHorizontalChart (w : F) :
    Function.Surjective (fderiv ℝ tubeHorizontalChart w) := by
  let e : OpenPartialHomeomorph F F := OpenPartialHomeomorph.univUnitBall
  let y : F := e w
  have hw : w ∈ e.source := by
    change w ∈ (Set.univ : Set F)
    exact Set.mem_univ w
  have hy : y ∈ Metric.ball (0 : F) 1 := by
    exact e.map_source hw
  have hleft : e.symm y = w := by
    exact e.left_inv hw
  have hf : DifferentiableAt ℝ (e : F → F) w := by
    have hfcd : ContDiffAt ℝ ∞ (e : F → F) w := by
      have hglobal : ContDiff ℝ ∞
          (OpenPartialHomeomorph.univUnitBall : F → F) :=
        OpenPartialHomeomorph.contDiff_univUnitBall
      simpa [e] using hglobal.contDiffAt
    exact hfcd.differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (e.symm : F → F) y := by
    have hOn : ContDiffOn ℝ ∞
        (OpenPartialHomeomorph.univUnitBall.symm : F → F)
        (Metric.ball (0 : F) 1) :=
      OpenPartialHomeomorph.contDiffOn_univUnitBall_symm
    have hgcd : ContDiffAt ℝ ∞ (e.symm : F → F) y := by
      simpa [e] using hOn.contDiffAt (isOpen_ball.mem_nhds hy)
    exact hgcd.differentiableAt (by simp)
  have hf' : DifferentiableAt ℝ (e : F → F) (e.symm y) := by
    rwa [hleft]
  have hcomp := fderiv_comp (x := y) hf' hg
  have hright : ((e : F → F) ∘ (e.symm : F → F)) =ᶠ[𝓝 y] id := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact e.right_inv hz
  have hid := hright.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_id] at hid
  rw [hleft] at hcomp
  have hmaps :
      (fderiv ℝ (e : F → F) w).comp
          (fderiv ℝ (e.symm : F → F) y) =
        ContinuousLinearMap.id ℝ F := by
    rw [← hcomp]
    exact hid
  intro z
  refine ⟨fderiv ℝ (e.symm : F → F) y z, ?_⟩
  have hz := congrArg (fun L : F →L[ℝ] F => L z) hmaps
  simpa [tubeHorizontalChart, e] using hz


-- @@ L87-104 verbatim
/-- At the origin the unit-ball chart has identity differential. -/
theorem fderiv_tubeHorizontalChart_zero :
    fderiv ℝ (tubeHorizontalChart (m := m)) 0 =
      ContinuousLinearMap.id ℝ F := by
  let a : F → ℝ := fun w => (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹
  have ha : DifferentiableAt ℝ a 0 := by
    have hcd : ContDiff ℝ ∞ a := by
      dsimp only [a]
      have hpos : ∀ w : F, (0 : ℝ) < 1 + ‖w‖ ^ 2 := fun w => by positivity
      exact ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt
        fun w => (hpos w).ne').inv fun w => Real.sqrt_ne_zero'.mpr (hpos w)
    exact hcd.differentiable (by simp) 0
  have hid : DifferentiableAt ℝ (id : F → F) 0 := differentiableAt_id
  have heq : tubeHorizontalChart (m := m) = fun w => a w • w := rfl
  rw [heq]
  change fderiv ℝ (fun w => a w • id w) 0 = _
  rw [fderiv_fun_smul ha hid]
  simp [a]


-- @@ L106-106 verbatim
/-! ## The bridge map in inner tube coordinates -/


-- @@ L108-135 verbatim
/-- On the inner tube, the horizontal part of the normalized collapse is the
standard diffeomorphism from the normal space to its open unit ball. -/
theorem initCLM_tubeThomVec_of_mem_inner (k : ℕ) {x : E}
    (hx : x ∈ tubeRegion (m := m) (1 / 4)) :
    initCLM (m + 2) (tubeThomVec k x) =
      tubeHorizontalChart (wCoord k x) := by
  have hc : tubeCutoff x = 1 := tubeCutoff_eq_one_on_inner hx
  have hinitRaw : initCLM (m + 2) (tubeCollapseRaw k x) = wCoord k x := by
    apply PiLp.ext
    intro i
    change tubeCollapseRaw k x i.castSucc = wCoord k x i
    rw [tubeCollapseRaw_coord,
      tubeCollapseHorizontal_eq_wCoord_of_mem_inner k hx]
  have hvertRaw : vertC (tubeCollapseRaw k x) = 1 := by
    change tubeCollapseRaw k x (Fin.last (m + 2)) = 1
    rw [tubeCollapseRaw_last, hc]
    norm_num
  have hsplit := norm_sq_split (tubeCollapseRaw k x)
  rw [hinitRaw, hvertRaw] at hsplit
  have hnorm : ‖tubeCollapseRaw k x‖ =
      Real.sqrt (1 + ‖wCoord k x‖ ^ 2) := by
    calc
      ‖tubeCollapseRaw k x‖ = Real.sqrt (‖tubeCollapseRaw k x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (1 + ‖wCoord k x‖ ^ 2) := by
        congr 1
        linarith
  rw [tubeThomVec, map_smul, hinitRaw, hnorm, tubeHorizontalChart_apply]


-- @@ L137-147 verbatim
/-- The normalized collapse has positive vertical coordinate throughout the
inner tube. -/
theorem vertC_tubeThomVec_pos_of_mem_inner (k : ℕ) {x : E}
    (hx : x ∈ tubeRegion (m := m) (1 / 4)) :
    0 < vertC (tubeThomVec k x) := by
  have hc : tubeCutoff x = 1 := tubeCutoff_eq_one_on_inner hx
  change 0 < ‖tubeCollapseRaw k x‖⁻¹ *
    tubeCollapseRaw k x (Fin.last (m + 2))
  rw [tubeCollapseRaw_last, hc]
  norm_num
  exact tubeCollapseRaw_ne_zero k x


-- @@ L149-164 verbatim
/-- On points whose affine image lies in the inner tube, the northern plateau
does nothing to the explicit approximation. -/
theorem tubeApproximation_nprep_eq_tubeThomVec_of_mem_inner (k : ℕ)
    (v : Fin (m + 3) → ℝ)
    (hv : tubeApproxAmbient v ∈ tubeRegion (m := m) (1 / 4)) :
    nprep (tubeApproximation (m := m) k) v =
      tubeThomVec k (tubeApproxAmbient v) := by
  have hvert : 0 < vertC (tubeThomVec k (tubeApproxAmbient v)) :=
    vertC_tubeThomVec_pos_of_mem_inner k hv
  have hvert' : -(1 / 4 : ℝ) ≤
      vertC (tubeThomVec k (tubeApproxAmbient v)) := by
    linarith
  rw [nprep, praw, tubeApproximation_nraw]
  change ‖plateauAux (tubeThomVec k (tubeApproxAmbient v))‖⁻¹ •
      plateauAux (tubeThomVec k (tubeApproxAmbient v)) = _
  rw [plateauAux_of_ge hvert', norm_tubeThomVec, inv_one, one_smul]


-- @@ L166-176 verbatim
/-- Exact local formula for the horizontal bridge map. -/
theorem bridgeHMapE_tubeApproximation_of_mem_inner (k : ℕ) (x : E)
    (hx : tubeApproxAmbient (WithLp.ofLp x) ∈
      tubeRegion (m := m) (1 / 4)) :
    bridgeHMapE (tubeApproximation (m := m) k) x =
      tubeHorizontalChart
        (wCoord k (tubeApproxAmbient (WithLp.ofLp x))) := by
  change initCLM (m + 2)
      (nprep (tubeApproximation (m := m) k) (WithLp.ofLp x)) = _
  rw [tubeApproximation_nprep_eq_tubeThomVec_of_mem_inner k _ hx]
  exact initCLM_tubeThomVec_of_mem_inner k hx


-- @@ L178-178 verbatim
/-! ## Regularity along the radial frame homotopy -/


-- @@ L180-207 verbatim
/-- The normal-coordinate differential has the prescribed right inverse not
only on the core circle, but at every sufficiently small normal offset. -/
theorem fderiv_wCoord_comp_normalSumCLM_tubeMap (k : ℕ) (θ : ℝ) {w : F}
    (hw : ‖w‖ < 1 / 4) :
    (fderiv ℝ (wCoord (m := m) k) (tubeMap k θ w)).comp
        (normalSumCLM k θ) =
      ContinuousLinearMap.id ℝ F := by
  have hinner : tubeMap k θ w ∈ tubeRegion (m := m) (1 / 4) :=
    tubeMap_mem_inner_of_norm_lt_quarter k θ hw
  have hgood : tubeMap k θ w ∈ tubeGood := innerTube_subset_tubeGood hinner
  have hwDiff : DifferentiableAt ℝ (wCoord (m := m) k) (tubeMap k θ w) :=
    ((contDiffOn_wCoord k).contDiffAt (isOpen_tubeGood.mem_nhds hgood)).differentiableAt
      (by simp)
  have hwDeriv : HasFDerivAt (wCoord (m := m) k)
      (fderiv ℝ (wCoord k) (tubeMap k θ w)) (normalSlice k θ w) := by
    simpa only [normalSlice] using hwDiff.hasFDerivAt
  have hcomp := hwDeriv.comp w (hasFDerivAt_normalSlice k θ w)
  have hopen : IsOpen {u : F | ‖u‖ < 1 / 2} :=
    isOpen_lt continuous_norm continuous_const
  have hwHalf : w ∈ {u : F | ‖u‖ < 1 / 2} :=
    hw.trans (by norm_num)
  have heq : ((wCoord (m := m) k) ∘ normalSlice k θ) =ᶠ[𝓝 w] id := by
    filter_upwards [hopen.mem_nhds hwHalf] with u hu
    exact wCoord_tubeMap k θ (tubeA_pos k θ hu)
  have hid : HasFDerivAt ((wCoord (m := m) k) ∘ normalSlice k θ)
      (ContinuousLinearMap.id ℝ F) w :=
    (hasFDerivAt_id (𝕜 := ℝ) w).congr_of_eventuallyEq heq
  exact hcomp.unique hid


-- @@ L209-217 verbatim
theorem surjective_fderiv_wCoord_tubeMap (k : ℕ) (θ : ℝ) {w : F}
    (hw : ‖w‖ < 1 / 4) :
    Function.Surjective
      (fderiv ℝ (wCoord (m := m) k) (tubeMap k θ w)) := by
  intro y
  refine ⟨normalSumCLM k θ y, ?_⟩
  have h := congrArg (fun L : F →L[ℝ] F => L y)
    (fderiv_wCoord_comp_normalSumCLM_tubeMap k θ hw)
  exact h


-- @@ L219-222 verbatim
/-- The affine source expansion, now regarded as a map between Euclidean
spaces. -/
def tubeBridgeAmbient (x : E) : E :=
  tubeApproxAmbient (WithLp.ofLp x)


-- @@ L224-226 verbatim
theorem tubeBridgeAmbient_apply (x : E) (i : Fin (m + 3)) :
    tubeBridgeAmbient x i = 12 * x i - 6 :=
  rfl


-- @@ L228-240 verbatim
theorem hasFDerivAt_tubeBridgeAmbient (x : E) :
    HasFDerivAt (tubeBridgeAmbient (m := m))
      ((12 : ℝ) • ContinuousLinearMap.id ℝ E) x := by
  let c : E := WithLp.toLp 2 fun _ => 6
  have heq : tubeBridgeAmbient (m := m) =
      fun z : E => (12 : ℝ) • z - c := by
    funext z
    apply PiLp.ext
    intro i
    simp [tubeBridgeAmbient_apply, c]
  rw [heq]
  simpa only [Pi.smul_apply, id_eq] using
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (R := ℝ) (12 : ℝ)).sub_const c


-- @@ L242-248 verbatim
theorem surjective_fderiv_tubeBridgeAmbient (x : E) :
    Function.Surjective (fderiv ℝ (tubeBridgeAmbient (m := m)) x) := by
  rw [(hasFDerivAt_tubeBridgeAmbient x).fderiv]
  intro y
  refine ⟨(12 : ℝ)⁻¹ • y, ?_⟩
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  exact smul_inv_smul₀ (by norm_num : (12 : ℝ) ≠ 0) y


-- @@ L250-252 verbatim
/-- The local expression of the bridge map on the inner tube. -/
def tubeBridgeLocalMap (k : ℕ) (x : E) : F :=
  tubeHorizontalChart (wCoord k (tubeBridgeAmbient x))


-- @@ L254-285 verbatim
theorem surjective_fderiv_tubeBridgeLocalMap (k : ℕ) (θ : ℝ) {w : F}
    (hw : ‖w‖ < 1 / 4) {x : E}
    (hx : tubeBridgeAmbient x = tubeMap k θ w) :
    Function.Surjective (fderiv ℝ (tubeBridgeLocalMap k) x) := by
  have hA : DifferentiableAt ℝ (tubeBridgeAmbient (m := m)) x :=
    (hasFDerivAt_tubeBridgeAmbient x).differentiableAt
  have hW : DifferentiableAt ℝ (wCoord (m := m) k) (tubeBridgeAmbient x) := by
    rw [hx]
    exact ((contDiffOn_wCoord k).contDiffAt
      (isOpen_tubeGood.mem_nhds
        (innerTube_subset_tubeGood
          (tubeMap_mem_inner_of_norm_lt_quarter k θ hw)))).differentiableAt (by simp)
  have hC : DifferentiableAt ℝ (tubeHorizontalChart (m := m))
      (wCoord k (tubeBridgeAmbient x)) := by
    have hglobal : ContDiff ℝ ∞ (tubeHorizontalChart (m := m)) := by
      simpa [tubeHorizontalChart] using
        (OpenPartialHomeomorph.contDiff_univUnitBall :
          ContDiff ℝ ∞ (OpenPartialHomeomorph.univUnitBall : F → F))
    exact hglobal.differentiable (by simp) _
  have hCW := fderiv_comp (x := tubeBridgeAmbient x) hC hW
  have hAll := fderiv_comp (x := x) (hC.comp _ hW) hA
  have hsurjA := surjective_fderiv_tubeBridgeAmbient x
  have hsurjW : Function.Surjective
      (fderiv ℝ (wCoord (m := m) k) (tubeBridgeAmbient x)) := by
    rw [hx]
    exact surjective_fderiv_wCoord_tubeMap k θ hw
  have hsurjC := surjective_fderiv_tubeHorizontalChart
    (wCoord k (tubeBridgeAmbient x))
  change Function.Surjective
    (fderiv ℝ ((tubeHorizontalChart ∘ wCoord k) ∘ tubeBridgeAmbient) x)
  rw [hAll, hCW]
  exact hsurjC.comp (hsurjW.comp hsurjA)


-- @@ L287-287 verbatim
/-! ## A regular radial homotopy of the explicit circle -/


-- @@ L289-293 verbatim
/-- Pull the tube point with radial normal offset `s` back through the affine
bridge coordinates.  At `s = 1` this is the northern bridge circle; at `s = 0`
it is the core circle where the derivative frame is completely explicit. -/
def tubeBridgeFrameHomotopyPoint (k : ℕ) (y : F) (s θ : ℝ) : E :=
  WithLp.toLp 2 fun i => (tubeMap k θ (s • tubeNorthOffset y) i + 6) / 12


-- @@ L295-299 verbatim
@[simp] theorem tubeBridgeFrameHomotopyPoint_apply (k : ℕ) (y : F)
    (s θ : ℝ) (i : Fin (m + 3)) :
    tubeBridgeFrameHomotopyPoint k y s θ i =
      (tubeMap k θ (s • tubeNorthOffset y) i + 6) / 12 :=
  rfl


-- @@ L301-308 verbatim
theorem tubeBridgeAmbient_frameHomotopyPoint (k : ℕ) (y : F)
    (s θ : ℝ) :
    tubeBridgeAmbient (tubeBridgeFrameHomotopyPoint k y s θ) =
      tubeMap k θ (s • tubeNorthOffset y) := by
  apply PiLp.ext
  intro i
  rw [tubeBridgeAmbient_apply, tubeBridgeFrameHomotopyPoint_apply]
  ring


-- @@ L310-315 verbatim
@[simp] theorem tubeBridgeFrameHomotopyPoint_one (k : ℕ) (y : F)
    (θ : ℝ) :
    tubeBridgeFrameHomotopyPoint k y 1 θ = tubeBridgeCirclePoint k y θ := by
  apply PiLp.ext
  intro i
  simp [tubeBridgeCirclePoint, tubeOffsetCirclePoint]


-- @@ L317-319 verbatim
/-- The affine pullback of the tube core circle. -/
def tubeBridgeCorePoint (k : ℕ) (θ : ℝ) : E :=
  WithLp.toLp 2 fun i => (circleAt θ i + 6) / 12


-- @@ L321-324 verbatim
@[simp] theorem tubeBridgeCorePoint_apply (k : ℕ) (θ : ℝ)
    (i : Fin (m + 3)) :
    tubeBridgeCorePoint k θ i = (circleAt θ i + 6) / 12 :=
  rfl


-- @@ L326-331 verbatim
theorem tubeBridgeAmbient_corePoint (k : ℕ) (θ : ℝ) :
    tubeBridgeAmbient (tubeBridgeCorePoint (m := m) k θ) = circleAt θ := by
  apply PiLp.ext
  intro i
  rw [tubeBridgeAmbient_apply, tubeBridgeCorePoint_apply]
  ring


-- @@ L333-339 verbatim
@[simp] theorem tubeBridgeFrameHomotopyPoint_zero (k : ℕ) (y : F)
    (θ : ℝ) :
    tubeBridgeFrameHomotopyPoint k y 0 θ = tubeBridgeCorePoint k θ := by
  apply PiLp.ext
  intro i
  simp [tubeBridgeFrameHomotopyPoint_apply, tubeBridgeCorePoint_apply,
    tubeMap_zero]


-- @@ L341-359 verbatim
/-- The two-parameter source family is smooth. -/
theorem contDiff_tubeBridgeFrameHomotopyPoint (k : ℕ) (y : F) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ =>
      tubeBridgeFrameHomotopyPoint k y p.1 p.2 := by
  have hTube : ContDiff ℝ ∞ fun p : ℝ × ℝ =>
      tubeMap k p.2 (p.1 • tubeNorthOffset y) := by
    have hparam : ContDiff ℝ ∞ fun p : ℝ × ℝ =>
        (p.2, p.1 • tubeNorthOffset y) := by
      fun_prop
    simpa only [Function.comp_def] using (contDiff_tubeMap k).comp hparam
  have heq : (fun p : ℝ × ℝ => tubeBridgeFrameHomotopyPoint k y p.1 p.2) =
      fun p => (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm
        (fun i => (tubeMap k p.2 (p.1 • tubeNorthOffset y) i + 6) / 12) := rfl
  rw [heq]
  apply (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm.contDiff.comp
  rw [contDiff_pi]
  intro i
  exact (((EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff.comp hTube).add
    contDiff_const).div_const 12


-- @@ L361-366 verbatim
theorem norm_smul_tubeNorthOffset_lt_quarter (y : F) (hy : ‖y‖ < 1 / 8)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖s • tubeNorthOffset y‖ < 1 / 4 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hq := tubeNorthOffset_norm_lt_quarter y hy
  nlinarith [norm_nonneg (tubeNorthOffset y)]


-- @@ L368-383 verbatim
/-- Near an inner-tube point, the actual bridge map and its explicit local
formula have the same derivative. -/
theorem fderiv_bridgeHMapE_tubeApproximation_eq_local (k : ℕ) {x : E}
    (hx : tubeBridgeAmbient x ∈ tubeRegion (m := m) (1 / 4)) :
    fderiv ℝ (bridgeHMapE (tubeApproximation (m := m) k)) x =
      fderiv ℝ (tubeBridgeLocalMap k) x := by
  have hcont : ContinuousAt (tubeBridgeAmbient (m := m)) x :=
    (hasFDerivAt_tubeBridgeAmbient x).continuousAt
  have hinner : ∀ᶠ z in 𝓝 x,
      tubeBridgeAmbient z ∈ tubeRegion (m := m) (1 / 4) :=
    hcont ((isOpen_tubeRegion (m := m) (1 / 4)).mem_nhds hx)
  have heq : bridgeHMapE (tubeApproximation (m := m) k) =ᶠ[𝓝 x]
      tubeBridgeLocalMap k := by
    filter_upwards [hinner] with z hz
    exact bridgeHMapE_tubeApproximation_of_mem_inner k z hz
  exact heq.fderiv_eq


-- @@ L385-385 verbatim
/-! ## The frame at the contracted core -/


-- @@ L387-416 verbatim
theorem fderiv_tubeBridgeLocalMap_core (k : ℕ) (θ : ℝ) :
    fderiv ℝ (tubeBridgeLocalMap (m := m) k) (tubeBridgeCorePoint k θ) =
      (fderiv ℝ (wCoord (m := m) k) (circleAt θ)).comp
        ((12 : ℝ) • ContinuousLinearMap.id ℝ E) := by
  let x := tubeBridgeCorePoint (m := m) k θ
  have hxA : tubeBridgeAmbient x = circleAt θ :=
    tubeBridgeAmbient_corePoint k θ
  have hA : DifferentiableAt ℝ (tubeBridgeAmbient (m := m)) x :=
    (hasFDerivAt_tubeBridgeAmbient x).differentiableAt
  have hW : DifferentiableAt ℝ (wCoord (m := m) k) (circleAt θ) :=
    (contDiffAt_wCoord_circleAt k θ).differentiableAt (by simp)
  have hC0 : DifferentiableAt ℝ (tubeHorizontalChart (m := m)) 0 := by
    have hglobal : ContDiff ℝ ∞ (tubeHorizontalChart (m := m)) := by
      simpa [tubeHorizontalChart] using
        (OpenPartialHomeomorph.contDiff_univUnitBall :
          ContDiff ℝ ∞ (OpenPartialHomeomorph.univUnitBall : F → F))
    exact hglobal.differentiable (by simp) 0
  have hC : DifferentiableAt ℝ (tubeHorizontalChart (m := m))
      (wCoord k (circleAt θ)) := by
    simpa [wCoord_circleAt] using hC0
  have hCW := fderiv_comp (x := circleAt θ) hC hW
  have hOuter : DifferentiableAt ℝ (tubeHorizontalChart ∘ wCoord k)
      (tubeBridgeAmbient x) := by
    rw [hxA]
    exact hC.comp _ hW
  have hAll := fderiv_comp (x := x) hOuter hA
  change fderiv ℝ ((tubeHorizontalChart ∘ wCoord k) ∘ tubeBridgeAmbient) x = _
  rw [hAll, hxA, hCW, wCoord_circleAt, fderiv_tubeHorizontalChart_zero,
    (hasFDerivAt_tubeBridgeAmbient x).fderiv]
  simp


-- @@ L418-425 verbatim
theorem fderiv_tubeBridgeLocalMap_core_nuVec (k : ℕ) (θ : ℝ)
    (i : Fin (m + 2)) :
    fderiv ℝ (tubeBridgeLocalMap (m := m) k) (tubeBridgeCorePoint k θ)
        (nuVec k θ i) =
      (12 : ℝ) • EuclideanSpace.single i 1 := by
  rw [fderiv_tubeBridgeLocalMap_core, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul,
    fderiv_wCoord_nuVec]


-- @@ L427-434 verbatim
theorem fderiv_tubeBridgeLocalMap_core_tangentAt (k : ℕ) (θ : ℝ) :
    fderiv ℝ (tubeBridgeLocalMap (m := m) k) (tubeBridgeCorePoint k θ)
        (tangentAt θ) = 0 := by
  have ht := fderiv_tubeCollapseHorizontal_tangentAt m k θ
  rw [fderiv_tubeCollapseHorizontal_circleAt] at ht
  rw [fderiv_tubeBridgeLocalMap_core, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul,
    ht, smul_zero]


-- @@ L436-440 verbatim
theorem tubeBridgeAmbient_corePoint_mem_inner (k : ℕ) (θ : ℝ) :
    tubeBridgeAmbient (tubeBridgeCorePoint (m := m) k θ) ∈
      tubeRegion (m := m) (1 / 4) := by
  rw [tubeBridgeAmbient_corePoint]
  exact standardCircle_subset_innerTube (circleAt_mem_standardCircle θ)


-- @@ L442-454 verbatim
theorem fderiv_tubeExplicitBridge_core_nuVec (k : ℕ) (θ : ℝ)
    (i : Fin (m + 2)) :
    fderiv ℝ (tubeExplicitBridge (m := m) k).fls.g
        (tubeBridgeCorePoint k θ) (nuVec k θ i) =
      (12 : ℝ) • EuclideanSpace.single i 1 := by
  change fderiv ℝ (fun z : E =>
    bridgeHMapE (tubeApproximation (m := m) k) z -
      (tubeExplicitBridge (m := m) k).y) (tubeBridgeCorePoint k θ)
      (nuVec k θ i) = _
  rw [fderiv_sub_const,
    fderiv_bridgeHMapE_tubeApproximation_eq_local k
      (tubeBridgeAmbient_corePoint_mem_inner k θ),
    fderiv_tubeBridgeLocalMap_core_nuVec]


-- @@ L456-466 verbatim
theorem fderiv_tubeExplicitBridge_core_tangentAt (k : ℕ) (θ : ℝ) :
    fderiv ℝ (tubeExplicitBridge (m := m) k).fls.g
        (tubeBridgeCorePoint k θ) (tangentAt θ) = 0 := by
  change fderiv ℝ (fun z : E =>
    bridgeHMapE (tubeApproximation (m := m) k) z -
      (tubeExplicitBridge (m := m) k).y) (tubeBridgeCorePoint k θ)
      (tangentAt θ) = 0
  rw [fderiv_sub_const,
    fderiv_bridgeHMapE_tubeApproximation_eq_local k
      (tubeBridgeAmbient_corePoint_mem_inner k θ),
    fderiv_tubeBridgeLocalMap_core_tangentAt]


-- @@ L468-490 verbatim
/-- The bridge gradients on the contracted core are the prescribed normal
frame, scaled by the positive affine factor `12`. -/
theorem gradVec_tubeExplicitBridge_core (k : ℕ) (θ : ℝ)
    (i : Fin (m + 2)) :
    gradVec (tubeExplicitBridge (m := m) k).fls.g i
        (tubeBridgeCorePoint k θ) =
      (12 : ℝ) • nuVec k θ i := by
  apply ext_inner_right_basis (tubeFullONBasis m k θ).toBasis
  intro j
  change ⟪gradVec (tubeExplicitBridge (m := m) k).fls.g i
      (tubeBridgeCorePoint k θ), tubeFullONBasis m k θ j⟫_ℝ =
    ⟪(12 : ℝ) • nuVec k θ i, tubeFullONBasis m k θ j⟫_ℝ
  rw [tubeFullONBasis_apply]
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [tubeFullFrame, Fin.cons_zero, inner_gradVec, map_neg,
      fderiv_tubeExplicitBridge_core_tangentAt, neg_zero,
      real_inner_smul_left, inner_neg_right, inner_nuVec_tangentAt,
      neg_zero, mul_zero]
    rfl
  · rw [tubeFullFrame, Fin.cons_succ, inner_gradVec,
      fderiv_tubeExplicitBridge_core_nuVec, real_inner_smul_left,
      inner_nuVec_nuVec]
    simp [PiLp.single_apply]


-- @@ L492-496 verbatim
/-- The oriented core frame before normalizing the gradient rows. -/
def tubeBridgeScaledFullFrame (m k : ℕ) (θ : ℝ) :
    Fin (m + 3) → EuclideanSpace ℝ (Fin (m + 3)) :=
  Fin.cons (-(tangentAt (m := m) θ))
    (fun i => (12 : ℝ) • nuVec (m := m) k θ i)


-- @@ L498-506 verbatim
theorem rowsMatrix_tubeBridgeScaledFullFrame (m k : ℕ) (θ : ℝ) :
    rowsMatrix (tubeBridgeScaledFullFrame m k θ) =
      Matrix.of fun i j => (if i = 0 then (1 : ℝ) else 12) *
        rowsMatrix (tubeFullFrame m k θ) i j := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp [rowsMatrix, tubeBridgeScaledFullFrame, tubeFullFrame]
  · simp [rowsMatrix, tubeBridgeScaledFullFrame, tubeFullFrame,
      Pi.smul_apply, smul_eq_mul]


-- @@ L508-517 verbatim
theorem det_rowsMatrix_tubeBridgeScaledFullFrame_pos (m k : ℕ) (θ : ℝ) :
    0 < (rowsMatrix (tubeBridgeScaledFullFrame m k θ)).det := by
  rw [rowsMatrix_tubeBridgeScaledFullFrame, Matrix.det_mul_column,
    det_rowsMatrix_tubeFullFrame]
  have hprod : 0 < ∏ i : Fin (m + 3),
      (if i = 0 then (1 : ℝ) else 12) := by
    apply Finset.prod_pos
    intro i _
    split <;> norm_num
  simpa using hprod


-- @@ L519-575 verbatim
/-- The oriented unit kernel vector on the contracted bridge core is the
clockwise circle tangent.  Positivity of the scaled-frame determinant fixes the
sign. -/
theorem tauField_tubeExplicitBridge_core (k : ℕ) (θ : ℝ) :
    tauField (tubeExplicitBridge (m := m) k).fls.g
        (tubeBridgeCorePoint k θ) =
      -(tangentAt θ) := by
  let B := tubeExplicitBridge (m := m) k
  let x := tubeBridgeCorePoint (m := m) k θ
  let g := B.fls.g
  have hreg : x ∈ regularSet g := by
    change Function.Surjective (fderiv ℝ g x)
    change Function.Surjective
      (fderiv ℝ (fun z : E =>
        bridgeHMapE (tubeApproximation (m := m) k) z - B.y) x)
    rw [fderiv_sub_const,
      fderiv_bridgeHMapE_tubeApproximation_eq_local k
        (tubeBridgeAmbient_corePoint_mem_inner k θ)]
    apply surjective_fderiv_tubeBridgeLocalMap k θ
      (w := (0 : F)) (by norm_num)
    simpa [x, tubeMap_zero] using tubeBridgeAmbient_corePoint (m := m) k θ
  have hgrads : (fun i => gradVec g i x) =
      fun i => (12 : ℝ) • nuVec (m := m) k θ i := by
    funext i
    exact gradVec_tubeExplicitBridge_core k θ i
  have hdetNeg : 0 < crossDet (fun i => gradVec g i x) (-(tangentAt θ)) := by
    rw [hgrads]
    have hrows : crossRows (fun i => (12 : ℝ) • nuVec (m := m) k θ i)
        (-(tangentAt θ)) = rowsMatrix (tubeBridgeScaledFullFrame m k θ) := by
      ext i j
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
        simp [crossRows, rowsMatrix, tubeBridgeScaledFullFrame]
    rw [crossDet, hrows]
    exact det_rowsMatrix_tubeBridgeScaledFullFrame_pos m k θ
  have hkernel : fderiv ℝ g x (-(tangentAt θ)) = 0 := by
    rw [map_neg, fderiv_tubeExplicitBridge_core_tangentAt, neg_zero]
  have hmem : -(tangentAt θ) ∈
      Submodule.span ℝ {tauField g x} :=
    (fderiv_eq_zero_iff_mem_span_tauField hreg _).mp hkernel
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have hdetTau : 0 < crossDet (fun i => gradVec g i x) (tauField g x) :=
    crossDet_tauField_pos hreg
  have hdetEq := congrArg (crossDet (fun i => gradVec g i x)) ha
  rw [crossDet_smul] at hdetEq
  have hprod : 0 < a * crossDet (fun i => gradVec g i x) (tauField g x) := by
    rw [hdetEq]
    exact hdetNeg
  have haPos : 0 < a := by
    rcases mul_pos_iff.mp hprod with hp | hn
    · exact hp.1
    · exact False.elim ((not_lt_of_ge (le_of_lt hdetTau)) hn.2)
  have hnormEq := congrArg norm ha
  rw [norm_smul, norm_tauField hreg, mul_one, norm_neg, norm_tangentAt,
    Real.norm_eq_abs, abs_of_pos haPos] at hnormEq
  have haOne : a = 1 := hnormEq
  rw [haOne, one_smul] at ha
  exact ha


-- @@ L577-586 verbatim
theorem frameAt_tubeExplicitBridge_core (k : ℕ) (θ : ℝ) :
    frameAt (tubeExplicitBridge (m := m) k).fls
        (tubeBridgeCorePoint k θ) =
      tubeBridgeScaledFullFrame m k θ := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rw [frameAt, Fin.cons_zero, tubeBridgeScaledFullFrame, Fin.cons_zero,
      tauField_tubeExplicitBridge_core]
  · rw [frameAt, Fin.cons_succ, tubeBridgeScaledFullFrame, Fin.cons_succ,
      gradVec_tubeExplicitBridge_core]


-- @@ L588-594 verbatim
theorem tubeBridgeScaledFullFrame_eq_smul (m k : ℕ) (θ : ℝ)
    (i : Fin (m + 3)) :
    tubeBridgeScaledFullFrame m k θ i =
      (if i = 0 then (1 : ℝ) else 12) • tubeFullFrame m k θ i := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp [tubeBridgeScaledFullFrame, tubeFullFrame]
  · simp [tubeBridgeScaledFullFrame, tubeFullFrame]


-- @@ L596-613 verbatim
/-- Normalized Gram--Schmidt removes the positive factor `12` from the normal
rows and recovers the previously computed explicit tube frame exactly. -/
theorem gramSchmidtNormed_tubeBridgeScaledFullFrame (m k : ℕ) (θ : ℝ) :
    gramSchmidtNormed ℝ (tubeBridgeScaledFullFrame m k θ) =
      tubeFullFrame m k θ := by
  have horth : Pairwise
      (fun i j => ⟪tubeBridgeScaledFullFrame m k θ i,
        tubeBridgeScaledFullFrame m k θ j⟫_ℝ = 0) := by
    intro i j hij
    rw [tubeBridgeScaledFullFrame_eq_smul,
      tubeBridgeScaledFullFrame_eq_smul,
      real_inner_smul_left, real_inner_smul_right,
      (orthonormal_tubeFullFrame m k θ).2 hij, mul_zero, mul_zero]
  funext i
  rw [gramSchmidtNormed, gramSchmidt_of_orthogonal ℝ horth,
    tubeBridgeScaledFullFrame_eq_smul, norm_smul,
    (orthonormal_tubeFullFrame m k θ).1]
  by_cases hi : i = 0 <;> simp [hi, smul_smul]


-- @@ L615-621 verbatim
theorem gramSchmidtNormed_frameAt_tubeExplicitBridge_core (k : ℕ) (θ : ℝ) :
    gramSchmidtNormed ℝ
        (frameAt (tubeExplicitBridge (m := m) k).fls
          (tubeBridgeCorePoint k θ)) =
      tubeFullFrame m k θ := by
  rw [frameAt_tubeExplicitBridge_core,
    gramSchmidtNormed_tubeBridgeScaledFullFrame]


-- @@ L623-646 verbatim
/-- Every point of the radial frame homotopy is regular for the bridge level
map.  Fiber membership is required only at the northern endpoint, whereas
regularity holds throughout the disk swept by the normal offset. -/
theorem tubeBridgeFrameHomotopyPoint_mem_regularSet (k : ℕ) (y : F)
    (hy : ‖y‖ < 1 / 8) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (θ : ℝ) :
    tubeBridgeFrameHomotopyPoint k y s θ ∈
      regularSet (tubeExplicitBridge (m := m) k).fls.g := by
  let x := tubeBridgeFrameHomotopyPoint (m := m) k y s θ
  have hw : ‖s • tubeNorthOffset y‖ < 1 / 4 :=
    norm_smul_tubeNorthOffset_lt_quarter y hy hs0 hs1
  have hxA : tubeBridgeAmbient x = tubeMap k θ (s • tubeNorthOffset y) :=
    tubeBridgeAmbient_frameHomotopyPoint k y s θ
  have hxinner : tubeBridgeAmbient x ∈ tubeRegion (m := m) (1 / 4) := by
    rw [hxA]
    exact tubeMap_mem_inner_of_norm_lt_quarter k θ hw
  have hlocal : Function.Surjective (fderiv ℝ (tubeBridgeLocalMap k) x) :=
    surjective_fderiv_tubeBridgeLocalMap k θ hw hxA
  change Function.Surjective
    (fderiv ℝ (fun z : E =>
      bridgeHMapE (tubeApproximation (m := m) k) z -
        (tubeExplicitBridge (m := m) k).y) x)
  rw [fderiv_sub_const,
    fderiv_bridgeHMapE_tubeApproximation_eq_local k hxinner]
  exact hlocal


-- @@ L648-652 verbatim
/-- The radial two-parameter family, with the angular variable normalized to
the unit interval. -/
def tubeBridgeFrameHomotopyCurve (k : ℕ) (y : F) (p : I × I) : E :=
  tubeBridgeFrameHomotopyPoint k y (p.1 : ℝ)
    (2 * Real.pi * (p.2 : ℝ))


-- @@ L654-669 verbatim
theorem continuous_tubeBridgeFrameHomotopyCurve (k : ℕ) (y : F) :
    Continuous (tubeBridgeFrameHomotopyCurve (m := m) k y) := by
  have hparam : Continuous fun p : I × I =>
      ((p.1 : ℝ), 2 * Real.pi * (p.2 : ℝ)) := by
    fun_prop
  unfold tubeBridgeFrameHomotopyCurve tubeBridgeFrameHomotopyPoint
  apply (PiLp.continuous_toLp (2 : ENNReal)
    (fun _ : Fin (m + 3) => ℝ)).comp
  apply continuous_pi
  intro i
  have hi := (((EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff.comp
    (contDiff_tubeBridgeFrameHomotopyPoint k y)).continuous.comp hparam)
  change Continuous fun p : I × I =>
    tubeBridgeFrameHomotopyPoint k y (p.1 : ℝ)
      (2 * Real.pi * (p.2 : ℝ)) i at hi
  simpa only [Function.comp_def, tubeBridgeFrameHomotopyPoint_apply] using hi


-- @@ L671-676 verbatim
theorem tubeBridgeFrameHomotopyCurve_mem_regularSet (k : ℕ) (y : F)
    (hy : ‖y‖ < 1 / 8) (p : I × I) :
    tubeBridgeFrameHomotopyCurve k y p ∈
      regularSet (tubeExplicitBridge (m := m) k).fls.g :=
  tubeBridgeFrameHomotopyPoint_mem_regularSet k y hy
    p.1.property.1 p.1.property.2 _


-- @@ L678-689 verbatim
theorem tubeBridgeFrameHomotopyCurve_closed (k : ℕ) (y : F) (s : I) :
    tubeBridgeFrameHomotopyCurve (m := m) k y (s, 0) =
      tubeBridgeFrameHomotopyCurve k y (s, 1) := by
  unfold tubeBridgeFrameHomotopyCurve
  simp only [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one]
  unfold tubeBridgeFrameHomotopyPoint
  have hper := tubeMap_periodic (m := m) k
    ((s : ℝ) • tubeNorthOffset y) 0
  rw [zero_add] at hper
  change tubeMap k (2 * Real.pi) ((s : ℝ) • tubeNorthOffset y) =
    tubeMap k 0 ((s : ℝ) • tubeNorthOffset y) at hper
  rw [hper]


-- @@ L691-698 verbatim
/-- The Gram--Schmidt frame matrix on the radial parameter square.  The first
coordinate contracts the northern offset to the tube core; the second runs
once around the circle. -/
def tubeBridgeFrameHomotopyMatrix (k : ℕ) (y : F) (p : I × I) :
    Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ :=
  rowsMatrix (InnerProductSpace.gramSchmidtNormed ℝ
    (frameAt (tubeExplicitBridge (m := m) k).fls
      (tubeBridgeFrameHomotopyCurve k y p)))


-- @@ L700-708 verbatim
theorem continuous_tubeBridgeFrameHomotopyMatrix (k : ℕ) (y : F)
    (hy : ‖y‖ < 1 / 8) :
    Continuous (tubeBridgeFrameHomotopyMatrix (m := m) k y) := by
  exact continuous_frameMatrix_comp
    (n := m + 2) (T := I × I)
    (γ := tubeBridgeFrameHomotopyCurve k y)
    (tubeExplicitBridge (m := m) k).fls
    (continuous_tubeBridgeFrameHomotopyCurve k y)
    (tubeBridgeFrameHomotopyCurve_mem_regularSet k y hy)


-- @@ L710-717 verbatim
set_option maxHeartbeats 800000 in
theorem tubeBridgeFrameHomotopyMatrix_mem_SO (k : ℕ) (y : F)
    (hy : ‖y‖ < 1 / 8) (p : I × I) :
    tubeBridgeFrameHomotopyMatrix (m := m) k y p ∈
      SOGroup (m + 3) := by
  apply frameMatrix_mem_specialOrthogonalGroup_of_regular
  exact tubeBridgeFrameHomotopyPoint_mem_regularSet k y hy
    p.1.property.1 p.1.property.2 _


-- @@ L719-725 verbatim
/-- The radial contraction packaged as an `SO(m+3)`-valued homotopy. -/
def tubeBridgeFrameHomotopy (k : ℕ) (y : F) (hy : ‖y‖ < 1 / 8) :
    C(I × I, SOGroup (m + 3)) where
  toFun p := ⟨tubeBridgeFrameHomotopyMatrix k y p,
    tubeBridgeFrameHomotopyMatrix_mem_SO k y hy p⟩
  continuous_toFun :=
    (continuous_tubeBridgeFrameHomotopyMatrix k y hy).subtype_mk _


-- @@ L727-732 verbatim
@[simp] theorem tubeBridgeFrameHomotopy_coe (k : ℕ) (y : F)
    (hy : ‖y‖ < 1 / 8) (p : I × I) :
    (tubeBridgeFrameHomotopy (m := m) k y hy p :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      tubeBridgeFrameHomotopyMatrix k y p :=
  rfl


-- @@ L734-743 verbatim
/-- The `s = 1` edge is exactly the intrinsic Gram--Schmidt frame along the
explicit northern parametrization. -/
theorem tubeBridgeFrameHomotopyMatrix_one (k : ℕ) (y : F) (u : I) :
    tubeBridgeFrameHomotopyMatrix (m := m) k y (1, u) =
      frameLoop (tubeExplicitBridge (m := m) k).fls
        (tubeBridgeCirclePoint k y) (2 * Real.pi * (u : ℝ)) := by
  unfold tubeBridgeFrameHomotopyMatrix frameLoop
  unfold tubeBridgeFrameHomotopyCurve
  rw [show ((1 : I) : ℝ) = 1 by norm_num,
    tubeBridgeFrameHomotopyPoint_one]


-- @@ L745-752 verbatim
/-- The `s = 0` edge is the already computed explicit tube frame. -/
theorem tubeBridgeFrameHomotopyMatrix_zero (k : ℕ) (y : F) (u : I) :
    tubeBridgeFrameHomotopyMatrix (m := m) k y (0, u) =
      rowsMatrix (tubeFullFrame m k (2 * Real.pi * (u : ℝ))) := by
  unfold tubeBridgeFrameHomotopyMatrix tubeBridgeFrameHomotopyCurve
  rw [show ((0 : I) : ℝ) = 0 by norm_num,
    tubeBridgeFrameHomotopyPoint_zero,
    gramSchmidtNormed_frameAt_tubeExplicitBridge_core]


-- @@ L754-761 verbatim
theorem tubeBridgeFrameHomotopy_closed (k : ℕ) (y : F)
    (hy : ‖y‖ < 1 / 8) (s : I) :
    tubeBridgeFrameHomotopy (m := m) k y hy (s, 0) =
      tubeBridgeFrameHomotopy k y hy (s, 1) := by
  apply Subtype.ext
  rw [tubeBridgeFrameHomotopy_coe, tubeBridgeFrameHomotopy_coe]
  unfold tubeBridgeFrameHomotopyMatrix
  rw [tubeBridgeFrameHomotopyCurve_closed]


-- @@ L763-763 verbatim
/-! ## The explicit northern frame class -/


-- @@ L765-771 verbatim
/-- The intrinsic Gram--Schmidt frame along the explicit northern circle,
parametrized once counterclockwise. -/
def tubeExplicitBridgeParamFrameLoop (k : ℕ) : C(I, SOGroup (m + 3)) :=
  (tubeBridgeFrameHomotopy (m := m) k
    (tubeExplicitBridge (m := m) k).y
    (tubeExplicitBridge (m := m) k).norm_y_lt).comp
      ((ContinuousMap.const I (1 : I)).prodMk (ContinuousMap.id I))


-- @@ L773-784 verbatim
@[simp] theorem tubeExplicitBridgeParamFrameLoop_apply (k : ℕ) (u : I) :
    (tubeExplicitBridgeParamFrameLoop (m := m) k u :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
    frameLoop (tubeExplicitBridge (m := m) k).fls
      (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y)
      (2 * Real.pi * (u : ℝ)) := by
  change (tubeBridgeFrameHomotopy (m := m) k
    (tubeExplicitBridge (m := m) k).y
    (tubeExplicitBridge (m := m) k).norm_y_lt (1, u) :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) = _
  rw [tubeBridgeFrameHomotopy_coe,
    tubeBridgeFrameHomotopyMatrix_one]


-- @@ L786-797 verbatim
theorem tubeExplicitBridgeParamFrameLoop_closed (k : ℕ) :
    tubeExplicitBridgeParamFrameLoop (m := m) k 0 =
      tubeExplicitBridgeParamFrameLoop k 1 := by
  change tubeBridgeFrameHomotopy (m := m) k
      (tubeExplicitBridge (m := m) k).y
      (tubeExplicitBridge (m := m) k).norm_y_lt (1, 0) =
    tubeBridgeFrameHomotopy k
      (tubeExplicitBridge (m := m) k).y
      (tubeExplicitBridge (m := m) k).norm_y_lt (1, 1)
  exact tubeBridgeFrameHomotopy_closed k
    (tubeExplicitBridge (m := m) k).y
    (tubeExplicitBridge (m := m) k).norm_y_lt 1


-- @@ L799-806 verbatim
theorem tubeBridgeFrameHomotopy_zero_eq_tubeFrameLoop (k : ℕ) (u : I) :
    tubeBridgeFrameHomotopy (m := m) k
        (tubeExplicitBridge (m := m) k).y
        (tubeExplicitBridge (m := m) k).norm_y_lt (0, u) =
      tubeFrameLoop m k u := by
  apply Subtype.ext
  rw [tubeBridgeFrameHomotopy_coe, tubeFrameLoop_apply,
    tubeBridgeFrameHomotopyMatrix_zero]


-- @@ L808-820 verbatim
/-- The radial frame contraction as a free homotopy from the computed tube
frame loop to the actual frame along the explicit northern bridge circle. -/
def tubeExplicitBridgeParamFrameHomotopy (k : ℕ) :
    ContinuousMap.Homotopy (tubeFrameLoop m k)
      (tubeExplicitBridgeParamFrameLoop (m := m) k) where
  toFun := tubeBridgeFrameHomotopy (m := m) k
    (tubeExplicitBridge (m := m) k).y
    (tubeExplicitBridge (m := m) k).norm_y_lt
  continuous_toFun := (tubeBridgeFrameHomotopy (m := m) k
    (tubeExplicitBridge (m := m) k).y
    (tubeExplicitBridge (m := m) k).norm_y_lt).continuous
  map_zero_left := tubeBridgeFrameHomotopy_zero_eq_tubeFrameLoop k
  map_one_left := fun _ => rfl


-- @@ L822-835 verbatim
/-- The actual frame along the explicit northern parametrization has class
`k+1`; the extra `1` is the unavoidable tangent turn. -/
theorem loopClassZ2_tubeExplicitBridgeParamFrameLoop (k : ℕ) :
    loopClassZ2 (tubeExplicitBridgeParamFrameLoop (m := m) k)
        (tubeExplicitBridgeParamFrameLoop_closed k) =
      (k : ZMod 2) + 1 := by
  have hhom := loopClassZ2_congr
    (tubeFrameLoop_closed m k)
    (tubeExplicitBridgeParamFrameLoop_closed (m := m) k)
    (tubeExplicitBridgeParamFrameHomotopy (m := m) k)
    (tubeBridgeFrameHomotopy_closed k
      (tubeExplicitBridge (m := m) k).y
      (tubeExplicitBridge (m := m) k).norm_y_lt)
  exact hhom.symm.trans (loopClassZ2_tubeFrameLoop m k)


-- @@ L837-837 verbatim
end Submission
