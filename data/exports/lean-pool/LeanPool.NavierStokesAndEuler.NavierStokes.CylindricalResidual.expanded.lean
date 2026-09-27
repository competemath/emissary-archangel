/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisymmetricResidual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv


-- @@ L12-18 verbatim
/-!
# Actual Cartesian differential operators in cylindrical coordinates

The chart is `(r,theta,z) ↦ (r cos theta,r sin theta,z)`.  Coordinate
derivatives are actual Fréchet derivatives. Pulling Cartesian fields back
through this chart avoids choosing a global inverse angular coordinate.
-/


-- @@ L20-20 verbatim
@[expose] public section



-- @@ L23-23 verbatim
namespace NavierStokes.CylindricalResidual


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open ProblemStatement Filter

-- @@ L28-28 verbatim
open AxisymmetricFields (projection)

-- @@ L29-30 verbatim
open AxisymmetricResidual (pack pack_zero pack_one pack_two packDerivative
  packDerivative_apply hasFDerivAt_pack)

-- @@ L31-31 verbatim
open scoped BigOperators ContDiff Topology


-- @@ L33-33 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @@ L34-34 verbatim
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L36-38 verbatim
/-- The three arguments are `r`, `theta`, and `z`, respectively. -/
noncomputable def chart (q : Space) : Space :=
  pack (q 0 * Real.cos (q 1)) (q 0 * Real.sin (q 1)) (q 2)


-- @@ L40-42 verbatim
/-- Horizontal, given by `packDerivative (projection 0) (projection 1) 0`. -/
noncomputable def horizontal : Space →L[ℝ] Space :=
  packDerivative (projection 0) (projection 1) 0


-- @@ L44-46 verbatim
/-- Infinitesimal rotation: `(a,b,c) ↦ (-b,a,0)`. -/
noncomputable def connection : Space →L[ℝ] Space :=
  packDerivative (-(projection 1)) (projection 0) 0


-- @@ L48-50 verbatim
/-- Vertical, given by `packDerivative 0 0 (projection 2)`. -/
noncomputable def vertical : Space →L[ℝ] Space :=
  packDerivative 0 0 (projection 2)


-- @@ L52-54 verbatim
/-- Frame, given by `Real.cos θ • horizontal + Real.sin θ • connection + vertical`. -/
noncomputable def frame (θ : ℝ) : Space →L[ℝ] Space :=
  Real.cos θ • horizontal + Real.sin θ • connection + vertical


-- @@ L56-61 verbatim
theorem frame_apply (θ : ℝ) (v : Space) :
    frame θ v = pack (Real.cos θ * v 0 - Real.sin θ * v 1)
      (Real.sin θ * v 0 + Real.cos θ * v 1) (v 2) := by
  ext i
  fin_cases i <;> simp [frame, horizontal, connection, vertical, packDerivative,
    pack, coordinateVector] <;> ring


-- @@ L63-64 verbatim
theorem connection_apply (v : Space) : connection v = pack (-v 1) (v 0) 0 := by
  simp [connection, packDerivative_apply]


-- @@ L66-70 verbatim
theorem frame_connection (θ : ℝ) :
    (frame θ).comp connection = -Real.sin θ • horizontal + Real.cos θ • connection := by
  ext v i
  fin_cases i <;> simp [frame_apply, connection_apply, horizontal, packDerivative_apply]
  ring


-- @@ L72-79 verbatim
theorem frame_inverse (θ : ℝ) (v : Space) : frame (-θ) (frame θ v) = v := by
  ext i
  fin_cases i
  · simp [frame_apply, Real.cos_neg, Real.sin_neg]
    linear_combination (v 0) * Real.cos_sq_add_sin_sq θ
  · simp [frame_apply, Real.cos_neg, Real.sin_neg]
    linear_combination (v 1) * Real.cos_sq_add_sin_sq θ
  · simp [frame_apply]


-- @@ L81-82 verbatim
theorem frame_inverse' (θ : ℝ) (v : Space) : frame θ (frame (-θ) v) = v := by
  simpa only [neg_neg] using frame_inverse (-θ) v


-- @@ L84-87 verbatim
/-- Chart jacobian, given by `(frame (q 1)).comp (packDerivative (projection 0) (q 0 •
projection 1) (projection 2))`. -/
noncomputable def chartJacobian (q : Space) : Space →L[ℝ] Space :=
  (frame (q 1)).comp (packDerivative (projection 0) (q 0 • projection 1) (projection 2))


-- @@ L89-91 verbatim
theorem chartJacobian_apply (q v : Space) :
    chartJacobian q v = frame (q 1) (pack (v 0) (q 0 * v 1) (v 2)) := by
  simp [chartJacobian, packDerivative_apply]


-- @@ L93-99 verbatim
theorem hasFDerivAt_chart (q : Space) : HasFDerivAt chart (chartJacobian q) q := by
  have h0 := (projection 0).hasFDerivAt (x := q)
  have h1 := (projection 1).hasFDerivAt (x := q)
  have h2 := (projection 2).hasFDerivAt (x := q)
  convert! hasFDerivAt_pack (h0.mul h1.cos) (h0.mul h1.sin) h2 using 1
  ext v i
  fin_cases i <;> simp [chartJacobian_apply, frame_apply, packDerivative_apply] <;> ring


-- @@ L101-105 verbatim
theorem contDiff_chart {n : WithTop ℕ∞} : ContDiff ℝ n chart := by
  unfold chart pack
  exact ((((projection 0).contDiff.mul (projection 1).contDiff.cos).smul contDiff_const).add
    (((projection 0).contDiff.mul (projection 1).contDiff.sin).smul contDiff_const)).add
    ((projection 2).contDiff.smul contDiff_const)


-- @@ L107-109 verbatim
/-- D coord, given by `fderiv ℝ f q (coordinateVector i)`. -/
noncomputable def dCoord (i : Fin 3) (f : Space → E) (q : Space) : E :=
  fderiv ℝ f q (coordinateVector i)


-- @@ L111-113 verbatim
/-- Euclidean laplacian, given by `∑ i : Fin 3, dCoord i (dCoord i f) x`. -/
noncomputable def euclideanLaplacian (f : Space → E) (x : Space) : E :=
  ∑ i : Fin 3, dCoord i (dCoord i f) x


-- @@ L115-119 verbatim
/-- Scalar laplacian, given by `dCoord 0 (dCoord 0 f) q + (q 0)⁻¹ • dCoord 0 f q + ((q 0) ^ 2)⁻¹
• dCoord 1 (dCoord 1 f) q + dCoord 2 (dCoord 2 f) q`. -/
noncomputable def scalarLaplacian (f : Space → E) (q : Space) : E :=
  dCoord 0 (dCoord 0 f) q + (q 0)⁻¹ • dCoord 0 f q +
    ((q 0) ^ 2)⁻¹ • dCoord 1 (dCoord 1 f) q + dCoord 2 (dCoord 2 f) q


-- @@ L121-124 verbatim
theorem contDiffAt_dCoord {f : Space → E} {q : Space} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f q) (hmn : m + 1 ≤ n) (i : Fin 3) :
    ContDiffAt ℝ m (dCoord i f) q :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const


-- @@ L126-129 verbatim
theorem dCoord_congr {f g : Space → E} {q : Space}
    (h : f =ᶠ[𝓝 q] g) (i : Fin 3) : dCoord i f q = dCoord i g q := by
  unfold dCoord
  rw [h.fderiv_eq]


-- @@ L131-136 verbatim
theorem dCoord_add {f g : Space → E} {q : Space}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) (i : Fin 3) :
    dCoord i (fun y => f y + g y) q = dCoord i f q + dCoord i g q := by
  unfold dCoord
  rw [fderiv_fun_add hf hg]
  rfl


-- @@ L138-144 verbatim
theorem dCoord_map (L : E →L[ℝ] F) {f : Space → E} {q : Space}
    (hf : DifferentiableAt ℝ f q) (i : Fin 3) :
    dCoord i (fun y => L (f y)) q = L (dCoord i f q) := by
  unfold dCoord
  change (fderiv ℝ (L ∘ f) q) _ = _
  rw [(L.hasFDerivAt.comp q hf.hasFDerivAt).fderiv]
  rfl


-- @@ L146-151 verbatim
theorem fderiv_pullback {f : Space → E} {q : Space}
    (hf : DifferentiableAt ℝ f (chart q)) (v : Space) :
    fderiv ℝ (fun y => f (chart y)) q v = fderiv ℝ f (chart q) (chartJacobian q v) := by
  change (fderiv ℝ (f ∘ chart) q) _ = _
  rw [(hf.hasFDerivAt.comp q (hasFDerivAt_chart q)).fderiv]
  rfl


-- @@ L153-156 verbatim
/-- Resolve a Cartesian vector into chart-coordinate components. -/
noncomputable def chartVector (q v : Space) : Space :=
  let w := frame (-(q 1)) v
  pack (w 0) (w 1 / q 0) (w 2)


-- @@ L158-165 verbatim
theorem chartJacobian_chartVector (q v : Space) (hr : q 0 ≠ 0) :
    chartJacobian q (chartVector q v) = v := by
  rw [chartJacobian_apply]
  have hpack : pack ((chartVector q v) 0) (q 0 * (chartVector q v) 1)
      ((chartVector q v) 2) = frame (-(q 1)) v := by
    ext i
    fin_cases i <;> simp [chartVector, hr, mul_div_cancel₀]
  rw [hpack, frame_inverse']


-- @@ L167-172 verbatim
/-- Exact first-order bridge from ordinary Cartesian derivatives. -/
theorem cartesian_derivative_from_pullback {f : Space → E} {q : Space}
    (hf : DifferentiableAt ℝ f (chart q)) (hr : q 0 ≠ 0) (v : Space) :
    fderiv ℝ f (chart q) v =
      fderiv ℝ (fun y => f (chart y)) q (chartVector q v) := by
  rw [fderiv_pullback hf, chartJacobian_chartVector q v hr]


-- @@ L174-176 verbatim
/-- The actual second Fréchet derivative, with the two directions displayed. -/
noncomputable def hessian (f : Space → E) (x v w : Space) : E :=
  fderiv ℝ (fderiv ℝ f) x v w


-- @@ L178-185 verbatim
theorem dCoord_dCoord {f : Space → E} {q : Space}
    (hf : ContDiffAt ℝ 2 f q) (i : Fin 3) :
    dCoord i (dCoord i f) q = hessian f q (coordinateVector i) (coordinateVector i) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold dCoord hessian
  rw [fderiv_clm_apply hD (differentiableAt_const _)]
  simp


-- @@ L187-210 verbatim
theorem second_chain {f : Space → E} {g : Space → Space} {q : Space}
    (hf : ContDiffAt ℝ 2 f (g q)) (hg : ContDiffAt ℝ 2 g q) (i : Fin 3) :
    dCoord i (dCoord i (f ∘ g)) q =
      hessian f (g q) (dCoord i g q) (dCoord i g q) +
        fderiv ℝ f (g q) (dCoord i (dCoord i g) q) := by
  have hnear : dCoord i (f ∘ g) =ᶠ[𝓝 q]
      fun y => fderiv ℝ f (g y) (dCoord i g y) := by
    have hfnear : ∀ᶠ y in 𝓝 q, ContDiffAt ℝ 2 f (g y) :=
      hg.continuousAt (hf.eventually (by norm_num))
    filter_upwards [hfnear, hg.eventually (by norm_num)] with y hyf hyg
    exact congrArg (fun L : Space →L[ℝ] E => L (coordinateVector i))
      ((hyf.differentiableAt (by norm_num)).hasFDerivAt.comp y
        (hyg.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  rw [dCoord_congr hnear]
  have hD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgD := hg.differentiableAt (by norm_num)
  have hDi := (contDiffAt_dCoord hg (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  change (fderiv ℝ (fun y => ((fderiv ℝ f) ∘ g) y (dCoord i g y)) q)
    (coordinateVector i) = _
  rw [fderiv_clm_apply (hD.comp q hgD) hDi]
  rw [show fderiv ℝ ((fderiv ℝ f) ∘ g) q =
      (fderiv ℝ (fderiv ℝ f) (g q)).comp (fderiv ℝ g q) from
    (hD.hasFDerivAt.comp q hgD.hasFDerivAt).fderiv]
  simp [dCoord, hessian, add_comm]


-- @@ L212-215 verbatim
theorem dCoord_chart_zero (q : Space) :
    dCoord 0 chart q = pack (Real.cos (q 1)) (Real.sin (q 1)) 0 := by
  simp [dCoord, (hasFDerivAt_chart q).fderiv, chartJacobian_apply, frame_apply,
    coordinateVector]


-- @@ L217-221 verbatim
theorem dCoord_chart_one (q : Space) :
    dCoord 1 chart q = pack (-(q 0) * Real.sin (q 1)) (q 0 * Real.cos (q 1)) 0 := by
  simp [dCoord, (hasFDerivAt_chart q).fderiv, chartJacobian_apply, frame_apply,
    coordinateVector]
  ring_nf


-- @@ L223-225 verbatim
theorem dCoord_chart_two (q : Space) : dCoord 2 chart q = coordinateVector 2 := by
  simp [dCoord, (hasFDerivAt_chart q).fderiv, chartJacobian_apply, frame_apply,
    coordinateVector, pack]


-- @@ L227-235 verbatim
theorem dCoord_dCoord_chart_zero (q : Space) : dCoord 0 (dCoord 0 chart) q = 0 := by
  rw [show dCoord 0 chart = fun y => pack (Real.cos (y 1)) (Real.sin (y 1)) 0 from
    funext dCoord_chart_zero]
  have h1 : HasFDerivAt (fun y : Space => y 1) (projection 1) q :=
    (projection 1).hasFDerivAt
  have hz : HasFDerivAt (fun _ : Space => (0 : ℝ)) 0 q := hasFDerivAt_const (𝕜 := ℝ) 0 q
  unfold dCoord
  rw [(hasFDerivAt_pack h1.cos h1.sin hz).fderiv]
  simp [packDerivative_apply, coordinateVector, pack]


-- @@ L237-252 verbatim
theorem dCoord_dCoord_chart_one (q : Space) :
    dCoord 1 (dCoord 1 chart) q = -(q 0) • dCoord 0 chart q := by
  rw [show dCoord 1 chart = fun y =>
      pack (-(y 0) * Real.sin (y 1)) (y 0 * Real.cos (y 1)) 0 from
    funext dCoord_chart_one]
  have h0 : HasFDerivAt (fun y : Space => y 0) (projection 0) q :=
    (projection 0).hasFDerivAt
  have h1 : HasFDerivAt (fun y : Space => y 1) (projection 1) q :=
    (projection 1).hasFDerivAt
  have hz : HasFDerivAt (fun _ : Space => (0 : ℝ)) 0 q := hasFDerivAt_const (𝕜 := ℝ) 0 q
  change (fderiv ℝ (fun y => pack (-y 0 * Real.sin (y 1))
    (y 0 * Real.cos (y 1)) 0) q) _ = _
  rw [(hasFDerivAt_pack (h0.fun_neg.fun_mul h1.sin) (h0.fun_mul h1.cos) hz).fderiv,
    dCoord_chart_zero]
  ext i
  fin_cases i <;> simp [packDerivative_apply, coordinateVector]


-- @@ L254-256 verbatim
theorem dCoord_dCoord_chart_two (q : Space) : dCoord 2 (dCoord 2 chart) q = 0 := by
  rw [show dCoord 2 chart = fun _ => coordinateVector 2 from funext dCoord_chart_two]
  simp [dCoord]


-- @@ L258-263 verbatim
theorem dCoord_pullback {f : Space → E} {q : Space}
    (hf : DifferentiableAt ℝ f (chart q)) (i : Fin 3) :
    dCoord i (f ∘ chart) q =
      fderiv ℝ f (chart q) (dCoord i chart q) := by
  simpa only [dCoord, Function.comp_def, (hasFDerivAt_chart q).fderiv] using
    fderiv_pullback hf (coordinateVector i)


-- @@ L265-279 verbatim
/-- The cylindrical scalar Laplacian is the pullback of the Cartesian trace. -/
theorem scalarLaplacian_pullback {f : Space → E} {q : Space}
    (hf : ContDiffAt ℝ 2 f (chart q)) (hr : q 0 ≠ 0) :
    scalarLaplacian (fun y => f (chart y)) q = euclideanLaplacian f (chart q) := by
  have hc : ContDiffAt ℝ 2 chart q := contDiff_chart.contDiffAt
  change scalarLaplacian (f ∘ chart) q = _
  unfold scalarLaplacian euclideanLaplacian
  rw [second_chain hf hc 0, second_chain hf hc 1, second_chain hf hc 2,
    dCoord_pullback (hf.differentiableAt (by norm_num)) 0,
    dCoord_dCoord_chart_zero, dCoord_dCoord_chart_one, dCoord_dCoord_chart_two]
  simp only [Fin.sum_univ_three, dCoord_dCoord hf, dCoord_chart_zero,
    dCoord_chart_one, dCoord_chart_two, hessian, pack, map_add, map_smul,
    map_zero, _root_.add_apply, _root_.smul_apply,
    zero_smul, add_zero]
  match_scalars <;> field_simp [hr] <;> nlinarith [Real.cos_sq_add_sin_sq (q 1)]


-- @@ L281-284 verbatim
theorem contDiff_frame {n : WithTop ℕ∞} : ContDiff ℝ n frame := by
  unfold frame
  exact ((contDiff_id.cos.smul contDiff_const).add
    (contDiff_id.sin.smul contDiff_const)).add contDiff_const


-- @@ L286-295 verbatim
theorem hasFDerivAt_frameField (q : Space) :
    HasFDerivAt (fun y : Space => frame (y 1))
      ((projection 1).smulRight ((frame (q 1)).comp connection)) q := by
  have h1 : HasFDerivAt (fun y : Space => y 1) (projection 1) q :=
    (projection 1).hasFDerivAt
  convert! ((h1.cos.smul_const horizontal).add (h1.sin.smul_const connection)).add_const
    vertical using 1
  ext v w i
  fin_cases i <;> simp [ frame_apply, horizontal, connection, packDerivative,
    pack, coordinateVector] <;> ring


-- @@ L297-298 verbatim
/-- Cartesian representation of cylindrical vector components. -/
noncomputable def encode (w : Space → Space) (q : Space) : Space := frame (q 1) (w q)


-- @@ L300-302 verbatim
theorem contDiffAt_encode {w : Space → Space} {q : Space} {n : WithTop ℕ∞}
    (hw : ContDiffAt ℝ n w q) : ContDiffAt ℝ n (encode w) q :=
  (contDiff_frame.contDiffAt.comp q (projection 1).contDiff.contDiffAt).clm_apply hw


-- @@ L304-310 verbatim
theorem fderiv_encode {w : Space → Space} {q : Space}
    (hw : DifferentiableAt ℝ w q) (v : Space) :
    fderiv ℝ (encode w) q v =
      frame (q 1) (fderiv ℝ w q v + v 1 • connection (w q)) := by
  unfold encode
  rw [((hasFDerivAt_frameField q).clm_apply hw.hasFDerivAt).fderiv]
  simp [map_add, map_smul]


-- @@ L312-316 verbatim
theorem dCoord_encode {w : Space → Space} {q : Space}
    (hw : DifferentiableAt ℝ w q) (i : Fin 3) :
    dCoord i (encode w) q =
      frame (q 1) (dCoord i w q + (coordinateVector i) 1 • connection (w q)) :=
  fderiv_encode hw (coordinateVector i)


-- @@ L318-323 verbatim
theorem dCoord_const_smul {f : Space → E} {q : Space}
    (hf : DifferentiableAt ℝ f q) (a : ℝ) (i : Fin 3) :
    dCoord i (fun y => a • f y) q = a • dCoord i f q := by
  unfold dCoord
  rw [fderiv_fun_const_smul hf a]
  rfl


-- @@ L325-345 verbatim
theorem dCoord_dCoord_encode {w : Space → Space} {q : Space}
    (hw : ContDiffAt ℝ 2 w q) (i : Fin 3) :
    dCoord i (dCoord i (encode w)) q = frame (q 1)
      (dCoord i (dCoord i w) q +
        (2 * (coordinateVector i) 1) • connection (dCoord i w q) +
        ((coordinateVector i) 1) ^ 2 • connection (connection (w q))) := by
  have hwD := hw.differentiableAt (by norm_num)
  have hDi := (contDiffAt_dCoord hw (m := 1) (by norm_num) i).differentiableAt (by norm_num)
  have hJ : DifferentiableAt ℝ (fun y => connection (w y)) q :=
    connection.differentiableAt.comp q hwD
  have hnear : dCoord i (encode w) =ᶠ[𝓝 q]
      encode (fun y => dCoord i w y + (coordinateVector i) 1 • connection (w y)) := by
    filter_upwards [hw.eventually (by norm_num)] with y hy
    exact dCoord_encode (hy.differentiableAt (by norm_num)) i
  rw [dCoord_congr hnear i,
    dCoord_encode (hDi.fun_add (hJ.fun_const_smul _)) i,
    dCoord_add hDi (hJ.fun_const_smul _) i,
    dCoord_const_smul hJ _ i, dCoord_map connection hwD i]
  congr 1
  simp only [map_add, map_smul]
  module


-- @@ L347-350 verbatim
/-- Vector Laplacian of physical components in the moving cylindrical basis. -/
noncomputable def vectorLaplacian (w : Space → Space) (q : Space) : Space :=
  scalarLaplacian w q + (2 / (q 0) ^ 2) • connection (dCoord 1 w q) +
    ((q 0) ^ 2)⁻¹ • connection (connection (w q))


-- @@ L352-363 verbatim
theorem scalarLaplacian_encode {w : Space → Space} {q : Space}
    (hw : ContDiffAt ℝ 2 w q) :
    scalarLaplacian (encode w) q = frame (q 1) (vectorLaplacian w q) := by
  unfold scalarLaplacian vectorLaplacian
  rw [dCoord_dCoord_encode hw 0, dCoord_dCoord_encode hw 1,
    dCoord_dCoord_encode hw 2, dCoord_encode (hw.differentiableAt (by norm_num)) 0]
  simp only [coordinateVector, PiLp.single_apply, ↓reduceIte, Fin.reduceEq, mul_zero, zero_smul,
      zero_pow (by
      norm_num : 2 ≠ 0),
    add_zero, mul_one, one_pow, one_smul, map_add, map_smul]
  simp only [scalarLaplacian, map_add, map_smul]
  module


-- @@ L365-367 verbatim
/-- Cylindrical components of an arbitrary Cartesian vector field. -/
noncomputable def components (f : Space → Space) (q : Space) : Space :=
  frame (-(q 1)) (f (chart q))


-- @@ L369-372 verbatim
theorem encode_components (f : Space → Space) :
    encode (components f) = fun q => f (chart q) := by
  funext q
  exact frame_inverse' (q 1) (f (chart q))


-- @@ L374-378 verbatim
theorem differentiableAt_components {f : Space → Space} {q : Space}
    (hf : DifferentiableAt ℝ f (chart q)) : DifferentiableAt ℝ (components f) q :=
  (((contDiff_frame (n := 1)).differentiable (by norm_num) _).comp q
    (projection 1).differentiableAt.neg).clm_apply
      (hf.comp q (hasFDerivAt_chart q).differentiableAt)


-- @@ L380-383 verbatim
theorem contDiffAt_components {f : Space → Space} {q : Space} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f (chart q)) : ContDiffAt ℝ n (components f) q :=
  (contDiff_frame.contDiffAt.comp q (projection 1).contDiff.contDiffAt.neg).clm_apply
    (hf.comp q contDiff_chart.contDiffAt)


-- @@ L385-389 verbatim
theorem cartesianLaplacian_components {f : Space → Space} {q : Space}
    (hf : ContDiffAt ℝ 2 f (chart q)) (hr : q 0 ≠ 0) :
    euclideanLaplacian f (chart q) = frame (q 1) (vectorLaplacian (components f) q) := by
  rw [← scalarLaplacian_pullback hf hr, ← encode_components,
    scalarLaplacian_encode (contDiffAt_components hf)]


-- @@ L391-394 verbatim
theorem fderiv_pack (f : Space → E) (q : Space) (a b c : ℝ) :
    fderiv ℝ f q (pack a b c) =
      a • dCoord 0 f q + b • dCoord 1 f q + c • dCoord 2 f q := by
  simp [pack, dCoord]


-- @@ L396-406 verbatim
/-- Cartesian directional differentiation, resolved in the cylindrical frame. -/
theorem cartesianDerivative_components {f : Space → Space} {q : Space}
    (hf : DifferentiableAt ℝ f (chart q)) (hr : q 0 ≠ 0) (b : Space) :
    frame (-(q 1)) (fderiv ℝ f (chart q) (frame (q 1) b)) =
      b 0 • dCoord 0 (components f) q +
        (b 1 / q 0) • (dCoord 1 (components f) q + connection (components f q)) +
        b 2 • dCoord 2 (components f) q := by
  rw [cartesian_derivative_from_pullback hf hr, ← encode_components,
    fderiv_encode (differentiableAt_components hf), frame_inverse]
  simp only [chartVector, frame_inverse, fderiv_pack, pack_one]
  module


-- @@ L408-412 verbatim
/-- Vector advection, given by `w q 0 • dCoord 0 w q + (w q 1 / q 0) • (dCoord 1 w q +
connection (w q)) + w q 2 • dCoord 2 w q`. -/
noncomputable def vectorAdvection (w : Space → Space) (q : Space) : Space :=
  w q 0 • dCoord 0 w q + (w q 1 / q 0) • (dCoord 1 w q + connection (w q)) +
    w q 2 • dCoord 2 w q


-- @@ L414-422 verbatim
theorem cartesianAdvection_components {f : Space → Space} {q : Space}
    (hf : DifferentiableAt ℝ f (chart q)) (hr : q 0 ≠ 0) :
    fderiv ℝ f (chart q) (f (chart q)) =
      frame (q 1) (vectorAdvection (components f) q) := by
  have h := cartesianDerivative_components hf hr (components f q)
  have hrec : frame (q 1) (components f q) = f (chart q) := frame_inverse' _ _
  rw [hrec] at h
  unfold vectorAdvection
  rw [← h, frame_inverse']


-- @@ L424-426 verbatim
/-- Euclidean divergence, given by `∑ i : Fin 3, (fderiv ℝ f x (coordinateVector i)) i`. -/
noncomputable def euclideanDivergence (f : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ f x (coordinateVector i)) i


-- @@ L428-431 verbatim
/-- Vector divergence, given by `(dCoord 0 w q) 0 + w q 0 / q 0 + (dCoord 1 w q) 1 / q 0 +
(dCoord 2 w q) 2`. -/
noncomputable def vectorDivergence (w : Space → Space) (q : Space) : ℝ :=
  (dCoord 0 w q) 0 + w q 0 / q 0 + (dCoord 1 w q) 1 / q 0 + (dCoord 2 w q) 2


-- @@ L433-438 verbatim
theorem trace_rotation (A : Space →L[ℝ] Space) (θ : ℝ) :
    (∑ i : Fin 3, (A (coordinateVector i)) i) =
      ∑ i : Fin 3, (frame (-θ) (A (frame θ (coordinateVector i)))) i := by
  simp [Fin.sum_univ_three, frame_apply, pack, coordinateVector]
  linear_combination -((A (EuclideanSpace.single 0 1)) 0 +
    (A (EuclideanSpace.single 1 1)) 1) * Real.cos_sq_add_sin_sq θ


-- @@ L440-447 verbatim
theorem cartesianDivergence_components {f : Space → Space} {q : Space}
    (hf : DifferentiableAt ℝ f (chart q)) (hr : q 0 ≠ 0) :
    euclideanDivergence f (chart q) = vectorDivergence (components f) q := by
  unfold euclideanDivergence
  rw [trace_rotation _ (q 1)]
  simp_rw [cartesianDerivative_components hf hr]
  simp [Fin.sum_univ_three, vectorDivergence, coordinateVector, connection_apply]
  ring


-- @@ L449-451 verbatim
/-- Euclidean gradient, given by `∑ i : Fin 3, dCoord i f x • coordinateVector i`. -/
noncomputable def euclideanGradient (f : Space → ℝ) (x : Space) : Space :=
  ∑ i : Fin 3, dCoord i f x • coordinateVector i


-- @@ L453-455 verbatim
/-- Scalar gradient, given by `pack (dCoord 0 f q) (dCoord 1 f q / q 0) (dCoord 2 f q)`. -/
noncomputable def scalarGradient (f : Space → ℝ) (q : Space) : Space :=
  pack (dCoord 0 f q) (dCoord 1 f q / q 0) (dCoord 2 f q)


-- @@ L457-474 verbatim
theorem cartesianGradient_pullback {f : Space → ℝ} {q : Space}
    (hf : DifferentiableAt ℝ f (chart q)) (hr : q 0 ≠ 0) :
    euclideanGradient f (chart q) = frame (q 1) (scalarGradient (f ∘ chart) q) := by
  unfold scalarGradient
  rw [dCoord_pullback hf 0, dCoord_pullback hf 1, dCoord_pullback hf 2]
  rw [dCoord_chart_zero, dCoord_chart_one, dCoord_chart_two]
  ext i
  fin_cases i
  · simp [euclideanGradient, Fin.sum_univ_three, frame_apply, pack, dCoord, coordinateVector]
    field_simp [hr]
    linear_combination -(fderiv ℝ f (chart q) (EuclideanSpace.single 0 1)) *
      Real.cos_sq_add_sin_sq (q 1)
  · simp [euclideanGradient, Fin.sum_univ_three, frame_apply, pack, dCoord, coordinateVector]
    field_simp [hr]
    linear_combination -(fderiv ℝ f (chart q) (EuclideanSpace.single 1 1)) *
      Real.cos_sq_add_sin_sq (q 1)
  · simp [euclideanGradient, Fin.sum_univ_three, frame_apply,
      pack, dCoord, coordinateVector]


-- @@ L476-478 verbatim
/-- Pullback of a time-dependent velocity into the moving cylindrical frame. -/
noncomputable def velocityComponents (u : VelocityField) : VelocityField :=
  fun tq => components (fun x => u (tq.1, x)) tq.2


-- @@ L480-482 verbatim
/-- Pressure pullback, defined pointwise by `p (tq.1, chart tq.2)`. -/
noncomputable def pressurePullback (p : PressureField) : PressureField :=
  fun tq => p (tq.1, chart tq.2)


-- @@ L484-488 verbatim
/-- Cylindrical residual, constructed using `temporalDerivative`. -/
noncomputable def cylindricalResidual (w : VelocityField) (p : PressureField)
    (t : ℝ) (q : Space) : Space :=
  temporalDerivative w t q + vectorAdvection (fun y => w (t, y)) q -
    vectorLaplacian (fun y => w (t, y)) q + scalarGradient (fun y => p (t, y)) q


-- @@ L490-497 verbatim
theorem temporalDerivative_components {u : VelocityField} {t : ℝ} {q : Space}
    (ht : DifferentiableAt ℝ (fun s => u (s, chart q)) t) :
    temporalDerivative (velocityComponents u) t q =
      frame (-(q 1)) (temporalDerivative u t (chart q)) := by
  unfold temporalDerivative velocityComponents components
  change (fderiv ℝ ((frame (-(q 1))) ∘ (fun s => u (s, chart q))) t) 1 = _
  rw [((frame (-(q 1))).hasFDerivAt.comp t ht.hasFDerivAt).fderiv]
  rfl


-- @@ L499-520 verbatim
/-- The full actual Cartesian Navier--Stokes residual, under local regularity. -/
theorem navierStokesResidual_cylindrical_of_slices
    {u : VelocityField} {p : PressureField} {t : ℝ} {q : Space}
    (hu : ContDiffAt ℝ 2 (fun x => u (t, x)) (chart q))
    (ht : DifferentiableAt ℝ (fun s => u (s, chart q)) t)
    (hp : DifferentiableAt ℝ (fun x => p (t, x)) (chart q))
    (hr : 0 < q 0) :
    navierStokesResidual u p t (chart q) =
      frame (q 1) (cylindricalResidual (velocityComponents u) (pressurePullback p) t q) := by
  have hr' : q 0 ≠ 0 := ne_of_gt hr
  have huD := hu.differentiableAt (by norm_num)
  have ht' : temporalDerivative u t (chart q) =
      frame (q 1) (temporalDerivative (velocityComponents u) t q) := by
    rw [temporalDerivative_components ht, frame_inverse']
  change temporalDerivative u t (chart q) +
    fderiv ℝ (fun x => u (t, x)) (chart q) (u (t, chart q)) -
    euclideanLaplacian (fun x => u (t, x)) (chart q) +
    euclideanGradient (fun x => p (t, x)) (chart q) = _
  rw [ht', cartesianAdvection_components huD hr', cartesianLaplacian_components hu hr',
    cartesianGradient_pullback hp hr']
  simp only [cylindricalResidual, velocityComponents, pressurePullback, map_add, map_sub]
  rfl


-- @@ L522-534 verbatim
/-- Joint local C² regularity supplies all velocity slice hypotheses. -/
theorem navierStokesResidual_cylindrical
    {u : VelocityField} {p : PressureField} {t : ℝ} {q : Space}
    (hu : ContDiffAt ℝ 2 u (t, chart q))
    (hp : DifferentiableAt ℝ p (t, chart q)) (hr : 0 < q 0) :
    navierStokesResidual u p t (chart q) =
      frame (q 1) (cylindricalResidual (velocityComponents u) (pressurePullback p) t q) := by
  apply navierStokesResidual_cylindrical_of_slices
  · exact hu.comp (chart q) (contDiffAt_const.prodMk contDiffAt_id)
  · exact (hu.differentiableAt (by norm_num)).comp t
      (differentiableAt_id.prodMk (differentiableAt_const _))
  · exact hp.comp (chart q) ((differentiableAt_const _).prodMk differentiableAt_id)
  · exact hr


-- @@ L536-540 verbatim
theorem divergence_cylindrical {u : VelocityField} {t : ℝ} {q : Space}
    (hu : DifferentiableAt ℝ (fun x => u (t, x)) (chart q)) (hr : 0 < q 0) :
    spatialDivergence u t (chart q) =
      vectorDivergence (fun y => velocityComponents u (t, y)) q :=
  cartesianDivergence_components hu (ne_of_gt hr)


-- @@ L542-547 verbatim
theorem vectorAdvection_radial (w : Space → Space) (q : Space) :
    vectorAdvection w q 0 =
      w q 0 * dCoord 0 w q 0 + w q 1 / q 0 * dCoord 1 w q 0 +
        w q 2 * dCoord 2 w q 0 - (w q 1) ^ 2 / q 0 := by
  simp [vectorAdvection, connection_apply]
  ring


-- @@ L549-554 verbatim
theorem vectorAdvection_angular (w : Space → Space) (q : Space) :
    vectorAdvection w q 1 =
      w q 0 * dCoord 0 w q 1 + w q 1 / q 0 * dCoord 1 w q 1 +
        w q 2 * dCoord 2 w q 1 + w q 0 * w q 1 / q 0 := by
  simp [vectorAdvection, connection_apply]
  ring


-- @@ L556-560 verbatim
theorem vectorAdvection_axial (w : Space → Space) (q : Space) :
    vectorAdvection w q 2 =
      w q 0 * dCoord 0 w q 2 + w q 1 / q 0 * dCoord 1 w q 2 +
        w q 2 * dCoord 2 w q 2 := by
  simp [vectorAdvection, connection_apply]


-- @@ L562-566 verbatim
theorem vectorLaplacian_radial (w : Space → Space) (q : Space) :
    vectorLaplacian w q 0 = scalarLaplacian w q 0 -
      w q 0 / (q 0) ^ 2 - 2 * dCoord 1 w q 1 / (q 0) ^ 2 := by
  simp [vectorLaplacian, connection_apply]
  ring


-- @@ L568-572 verbatim
theorem vectorLaplacian_angular (w : Space → Space) (q : Space) :
    vectorLaplacian w q 1 = scalarLaplacian w q 1 -
      w q 1 / (q 0) ^ 2 + 2 * dCoord 1 w q 0 / (q 0) ^ 2 := by
  simp [vectorLaplacian, connection_apply]
  ring


-- @@ L574-576 verbatim
theorem vectorLaplacian_axial (w : Space → Space) (q : Space) :
    vectorLaplacian w q 2 = scalarLaplacian w q 2 := by
  simp [vectorLaplacian, connection_apply]


-- @@ L578-581 verbatim
theorem dCoord_eventuallyEq {f g : Space → E} {q : Space}
    (h : f =ᶠ[𝓝 q] g) (i : Fin 3) : dCoord i f =ᶠ[𝓝 q] dCoord i g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : Space →L[ℝ] E => L (coordinateVector i)) hy


-- @@ L583-587 verbatim
theorem scalarLaplacian_congr {f g : Space → E} {q : Space}
    (h : f =ᶠ[𝓝 q] g) : scalarLaplacian f q = scalarLaplacian g q := by
  simp only [scalarLaplacian, dCoord_congr (dCoord_eventuallyEq h 0) 0,
    dCoord_congr h 0, dCoord_congr (dCoord_eventuallyEq h 1) 1,
    dCoord_congr (dCoord_eventuallyEq h 2) 2]


-- @@ L589-604 verbatim
/-- Every cylindrical operator depends only on the local germ of its fields. -/
theorem cylindricalResidual_congr {u v : VelocityField} {p P : PressureField}
    {t : ℝ} {q : Space} (hu : u =ᶠ[𝓝 (t, q)] v) (hp : p =ᶠ[𝓝 (t, q)] P) :
    cylindricalResidual u p t q = cylindricalResidual v P t q := by
  have hs : (fun y => u (t, y)) =ᶠ[𝓝 q] (fun y => v (t, y)) :=
    hu.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have ht : (fun s => u (s, q)) =ᶠ[𝓝 t] (fun s => v (s, q)) :=
    hu.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hps : (fun y => p (t, y)) =ᶠ[𝓝 q] (fun y => P (t, y)) :=
    hp.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  unfold cylindricalResidual temporalDerivative vectorAdvection vectorLaplacian scalarGradient
  rw [ht.fderiv_eq]
  dsimp only
  rw [hs.eq_of_nhds]
  simp only [dCoord_congr hs 0, dCoord_congr hs 1, dCoord_congr hs 2,
    dCoord_congr hps 0, dCoord_congr hps 1, dCoord_congr hps 2, scalarLaplacian_congr hs]


-- @@ L606-621 verbatim
/-- Apply the coordinate law to an arbitrary locally specified cylindrical ansatz.
The velocity premise is an equality of values on a neighborhood, not an assumed
identity between derivatives or differential operators. -/
theorem navierStokesResidual_of_representation
    {u w : VelocityField} {p P : PressureField} {t : ℝ} {q : Space}
    (hu : ContDiffAt ℝ 2 u (t, chart q))
    (hp : DifferentiableAt ℝ p (t, chart q)) (hr : 0 < q 0)
    (hw : (fun tq : SpaceTime => u (tq.1, chart tq.2)) =ᶠ[𝓝 (t, q)]
      (fun tq => frame (tq.2 1) (w tq)))
    (hP : pressurePullback p =ᶠ[𝓝 (t, q)] P) :
    navierStokesResidual u p t (chart q) = frame (q 1) (cylindricalResidual w P t q) := by
  have hc : velocityComponents u =ᶠ[𝓝 (t, q)] w := by
    filter_upwards [hw] with tq hq
    change frame (-(tq.2 1)) (u (tq.1, chart tq.2)) = w tq
    rw [hq, frame_inverse]
  rw [navierStokesResidual_cylindrical hu hp hr, cylindricalResidual_congr hc hP]


-- @@ L623-635 verbatim
theorem navierStokesResidual_zero_iff
    {u : VelocityField} {p : PressureField} {t : ℝ} {q : Space}
    (hu : ContDiffAt ℝ 2 u (t, chart q))
    (hp : DifferentiableAt ℝ p (t, chart q)) (hr : 0 < q 0) :
    navierStokesResidual u p t (chart q) = 0 ↔
      cylindricalResidual (velocityComponents u) (pressurePullback p) t q = 0 := by
  rw [navierStokesResidual_cylindrical hu hp hr]
  constructor
  · intro h
    have h' := congrArg (frame (-(q 1))) h
    simpa only [frame_inverse, map_zero] using h'
  · intro h
    rw [h, map_zero]


-- @@ L637-644 verbatim
theorem dCoord_dCoord_map (L : E →L[ℝ] F) {f : Space → E} {q : Space}
    (hf : ContDiffAt ℝ 2 f q) (i : Fin 3) :
    dCoord i (dCoord i (fun y => L (f y))) q = L (dCoord i (dCoord i f) q) := by
  have hnear : dCoord i (fun y => L (f y)) =ᶠ[𝓝 q] fun y => L (dCoord i f y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact dCoord_map L (hy.differentiableAt (by norm_num)) i
  rw [dCoord_congr hnear, dCoord_map L
    ((contDiffAt_dCoord hf (m := 1) (by norm_num) i).differentiableAt (by norm_num))]


-- @@ L646-650 verbatim
theorem scalarLaplacian_map (L : E →L[ℝ] F) {f : Space → E} {q : Space}
    (hf : ContDiffAt ℝ 2 f q) :
    scalarLaplacian (fun y => L (f y)) q = L (scalarLaplacian f q) := by
  simp only [scalarLaplacian, dCoord_dCoord_map L hf,
    dCoord_map L (hf.differentiableAt (by norm_num)), map_add, map_smul]


-- @@ L652-656 verbatim
/-- The vector-valued scalar Laplacian has the expected actual scalar components. -/
theorem scalarLaplacian_component {w : Space → Space} {q : Space}
    (hw : ContDiffAt ℝ 2 w q) (j : Fin 3) :
    scalarLaplacian (fun y => w y j) q = scalarLaplacian w q j :=
  scalarLaplacian_map (projection j) hw


-- @@ L658-658 verbatim
end


-- @@ L660-660 verbatim
end NavierStokes.CylindricalResidual
