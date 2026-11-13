import Mathlib
import Submission.BridgeLevel
import Submission.SphereClose


-- @@ L5-21 verbatim
/-!
# The inverse Pontryagin--Thom comparison for bridge representatives

For bridge data `B`, this file constructs an explicit Thom-collapse representative
of the northern part of the regular fiber of `B.fls`.  Its ambient numerator is

`plateauAux u - plateauA (vertC u) • embedCLM n B.y`,

where `u = nprep B.approx x`.  Thus its horizontal coordinates are exactly
`plateauA (vertC u) • B.fls.g x`.  Along the northern fiber the cutoff is one,
so the differential in normal directions is the original regular-value framing.
On the southern cap the numerator is the south pole.

The numerator has positive inner product with `u`.  Consequently its normalization
is pointwise non-antipodal to the original bridge representative, and normalized
straight chords give the explicit relative homotopy proving equality of classes.
-/


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open scoped Topology unitInterval RealInnerProductSpace ContDiff

-- @@ L26-26 verbatim
open Metric Set Function Topology.Homotopy


-- @@ L28-28 verbatim
namespace Submission


-- @@ L30-30 verbatim
variable {n : ℕ}

-- @@ L31-32 verbatim
variable {z : HomotopyGroup (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}


-- @@ L34-34 verbatim
namespace BridgeData


-- @@ L36-36 verbatim
variable (B : BridgeData n z)


-- @@ L38-38 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L39-39 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L41-41 verbatim
/-! ## Ambient collapse -/


-- @@ L43-45 verbatim
/-- The everywhere-defined sphere representative underlying the bridge, transported
to the Euclidean domain. -/
def northSource (x : E) : E := nprep B.approx (WithLp.ofLp x)


-- @@ L47-48 verbatim
lemma norm_northSource (x : E) : ‖B.northSource x‖ = 1 :=
  norm_nprep B.approx (WithLp.ofLp x)


-- @@ L50-52 verbatim
lemma contDiff_northSource : ContDiff ℝ ∞ B.northSource := by
  exact (contDiff_nprep B.approx).comp
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).contDiff


-- @@ L54-56 verbatim
/-- The northern cutoff.  It is zero below latitude `-1/2` and one above
latitude `-1/4`. -/
def northCutoff (x : E) : ℝ := plateauA (vertC (B.northSource x))


-- @@ L58-59 verbatim
lemma northCutoff_nonneg (x : E) : 0 ≤ B.northCutoff x :=
  plateauA_nonneg _


-- @@ L61-62 verbatim
lemma northCutoff_le_one (x : E) : B.northCutoff x ≤ 1 :=
  plateauA_le_one _


-- @@ L64-65 verbatim
lemma contDiff_northCutoff : ContDiff ℝ ∞ B.northCutoff := by
  exact contDiff_plateauA.comp (contDiff_vertC.comp B.contDiff_northSource)


-- @@ L67-70 verbatim
/-- The unnormalized northern Thom collapse.  Near the northern fiber it is
`northSource x - embed B.y`; on the southern cap it is the south pole. -/
def northThomRaw (x : E) : E :=
  plateauAux (B.northSource x) - B.northCutoff x • embedCLM n B.y


-- @@ L72-74 verbatim
lemma contDiff_northThomRaw : ContDiff ℝ ∞ B.northThomRaw := by
  exact (contDiff_plateauAux.comp B.contDiff_northSource).sub
    (B.contDiff_northCutoff.smul contDiff_const)


-- @@ L76-82 verbatim
/-- Appending a zero coordinate is an isometry for the Euclidean norm. -/
lemma norm_embedCLM (y : F) : ‖embedCLM n y‖ = ‖y‖ := by
  have hs : ‖embedCLM n y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum, Fin.sum_univ_castSucc]
    simp only [embedCLM_apply_castSucc, embedCLM_apply_last]
    norm_num
  nlinarith [norm_nonneg y, norm_nonneg (embedCLM n y)]


-- @@ L84-88 verbatim
/-- The horizontal embedding is adjoint to forgetting the last coordinate. -/
lemma inner_embedCLM_left (y : F) (u : E) :
    ⟪embedCLM n y, u⟫ = ⟪y, initCLM n u⟫ := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_castSucc,
    embedCLM_apply_castSucc, embedCLM_apply_last, initCLM_apply]


-- @@ L90-100 verbatim
/-- Closed form for the pairing of the collapse numerator with the source point. -/
lemma inner_northThomRaw_source (x : E) :
    ⟪B.northThomRaw x, B.northSource x⟫ =
      plateauA (vertC (B.northSource x)) *
        (1 + vertC (B.northSource x) -
          ⟪B.y, initCLM n (B.northSource x)⟫) -
        vertC (B.northSource x) := by
  rw [northThomRaw, inner_sub_left, real_inner_smul_left,
    inner_plateauAux_self (B.norm_northSource x),
    inner_embedCLM_left (n := n), northCutoff]
  ring


-- @@ L102-137 verbatim
/-- The collapse numerator pairs positively with the original sphere point. -/
lemma inner_northThomRaw_source_pos (x : E) :
    0 < ⟪B.northThomRaw x, B.northSource x⟫ := by
  rw [B.inner_northThomRaw_source]
  let u := B.northSource x
  let t := vertC u
  let h := initCLM n u
  have hu : ‖u‖ = 1 := B.norm_northSource x
  have ht_abs : |t| ≤ 1 := abs_vertC_le_one hu
  have ht_lower : -1 ≤ t := neg_le_of_abs_le ht_abs
  have hh : ‖h‖ ≤ 1 := by
    have hs := norm_sq_split u
    rw [hu] at hs
    have hh0 := norm_nonneg h
    nlinarith [sq_nonneg t]
  have hip_abs : |⟪B.y, h⟫| < 1 / 8 := by
    calc
      |⟪B.y, h⟫| ≤ ‖B.y‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖B.y‖ * 1 := mul_le_mul_of_nonneg_left hh (norm_nonneg B.y)
      _ < 1 / 8 := by simpa using B.norm_y_lt
  by_cases hlow : t ≤ -(1 / 2)
  · rw [plateauA_of_le hlow]
    linarith
  by_cases hhigh : -(1 / 4) ≤ t
  · rw [plateauA_of_ge hhigh]
    have hip_lt : ⟪B.y, h⟫ < 1 / 8 :=
      lt_of_le_of_lt (le_abs_self _) hip_abs
    linarith
  · have htneg : t < -(1 / 4) := lt_of_not_ge hhigh
    have httrans : -(1 / 2) < t := lt_of_not_ge hlow
    have hip_lt : ⟪B.y, h⟫ < 1 / 8 :=
      lt_of_le_of_lt (le_abs_self _) hip_abs
    have hbracket : 0 < 1 + t - ⟪B.y, h⟫ := by linarith
    have hprod : 0 ≤ plateauA t * (1 + t - ⟪B.y, h⟫) :=
      mul_nonneg (plateauA_nonneg t) hbracket.le
    linarith


-- @@ L139-143 verbatim
lemma northThomRaw_ne_zero (x : E) : B.northThomRaw x ≠ 0 := by
  intro h0
  have hpos := B.inner_northThomRaw_source_pos x
  rw [h0, inner_zero_left] at hpos
  exact lt_irrefl 0 hpos


-- @@ L145-148 verbatim
/-- The normalized northern Thom collapse. -/
def northThom (x : E) : UnitSphere E :=
  ⟨‖B.northThomRaw x‖⁻¹ • B.northThomRaw x,
    mem_sphere_zero_iff_norm.mpr (norm_normalize (B.northThomRaw_ne_zero x))⟩


-- @@ L150-151 verbatim
lemma northThom_coe (x : E) :
    (B.northThom x : E) = ‖B.northThomRaw x‖⁻¹ • B.northThomRaw x := rfl


-- @@ L153-154 verbatim
lemma contDiff_northThom : ContDiff ℝ ∞ fun x => (B.northThom x : E) :=
  contDiff_normalize_comp B.contDiff_northThomRaw B.northThomRaw_ne_zero


-- @@ L156-157 verbatim
lemma continuous_northThom : Continuous B.northThom := by
  exact Continuous.subtype_mk B.contDiff_northThom.continuous _


-- @@ L159-160 verbatim
def northThomCM : C(E, UnitSphere E) :=
  ⟨B.northThom, B.continuous_northThom⟩


-- @@ L162-162 verbatim
/-! ## Local normal-coordinate contract -/


-- @@ L164-178 verbatim
/-- The horizontal coordinates of the raw collapse are the regular-value equation
multiplied by the cutoff. -/
lemma initCLM_northThomRaw (x : E) :
    initCLM n (B.northThomRaw x) = B.northCutoff x • B.fls.g x := by
  rw [northThomRaw, map_sub, map_smul, initCLM_embedCLM, plateauAux]
  simp only [map_add, map_smul, map_sub, initCLM_eLast, smul_zero, sub_zero,
    add_zero]
  change plateauA (vertC (B.northSource x)) •
      initCLM n (B.northSource x) - B.northCutoff x • B.y = _
  rw [northCutoff]
  change _ = plateauA (vertC (B.northSource x)) •
    (bridgeHMapE B.approx x - B.y)
  change _ = plateauA (vertC (B.northSource x)) •
    (initCLM n (B.northSource x) - B.y)
  exact (smul_sub _ _ _).symm


-- @@ L180-186 verbatim
/-- On the northern fiber the cutoff is identically one. -/
lemma northCutoff_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) : B.northCutoff x = 1 := by
  rw [northCutoff, hx]
  exact plateauA_of_ge (by
    have := vertC_northPoint_pos B.norm_y_lt_one
    linarith)


-- @@ L188-194 verbatim
/-- The regular-value equation vanishes on the northern fiber. -/
lemma fls_g_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) : B.fls.g x = 0 := by
  change bridgeHMapE B.approx x - B.y = 0
  apply sub_eq_zero.mpr
  change initCLM n (B.northSource x) = B.y
  rw [hx, initCLM_northPoint]


-- @@ L196-214 verbatim
/-- The horizontal derivative of the raw collapse along its northern zero fiber is
exactly the derivative furnishing the bridge framing.  No sign or rescaling is
introduced. -/
theorem fderiv_initCLM_northThomRaw_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) :
    fderiv ℝ (fun q => initCLM n (B.northThomRaw q)) x =
      fderiv ℝ B.fls.g x := by
  have hfun : (fun q => initCLM n (B.northThomRaw q)) =
      fun q => B.northCutoff q • B.fls.g q := by
    funext q
    exact B.initCLM_northThomRaw q
  rw [hfun]
  have hcd : DifferentiableAt ℝ B.northCutoff x :=
    B.contDiff_northCutoff.differentiable infty_ne_zero |>.differentiableAt
  have hgd : DifferentiableAt ℝ B.fls.g x :=
    B.fls.smooth.differentiable infty_ne_zero |>.differentiableAt
  rw [fderiv_fun_smul hcd hgd, B.fls_g_of_northFiber hx,
    B.northCutoff_of_northFiber hx]
  simp


-- @@ L216-221 verbatim
theorem surjective_fderiv_initCLM_northThomRaw_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) :
    Function.Surjective
      (fderiv ℝ (fun q => initCLM n (B.northThomRaw q)) x) := by
  rw [B.fderiv_initCLM_northThomRaw_of_northFiber hx]
  exact B.fls.regular x (B.fls_g_of_northFiber hx)


-- @@ L223-224 verbatim
/-- Horizontal north-pole chart applied to the normalized Thom collapse. -/
def northThomHorizontal (x : E) : F := initCLM n (B.northThom x : E)


-- @@ L226-230 verbatim
lemma northThomHorizontal_eq (x : E) :
    B.northThomHorizontal x =
      (‖B.northThomRaw x‖⁻¹ * B.northCutoff x) • B.fls.g x := by
  rw [northThomHorizontal, northThom_coe, map_smul,
    B.initCLM_northThomRaw, smul_smul]


-- @@ L232-255 verbatim
/-- After normalization, the north-pole chart derivative is a positive scalar
multiple of the bridge framing.  Hence normalization changes neither its
surjectivity nor its orientation class. -/
theorem fderiv_northThomHorizontal_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) :
    fderiv ℝ B.northThomHorizontal x =
      ‖B.northThomRaw x‖⁻¹ • fderiv ℝ B.fls.g x := by
  have hfun : B.northThomHorizontal = fun q =>
      (‖B.northThomRaw q‖⁻¹ * B.northCutoff q) • B.fls.g q := by
    funext q
    exact B.northThomHorizontal_eq q
  rw [hfun]
  have hrnorm : DifferentiableAt ℝ (fun q => ‖B.northThomRaw q‖) x :=
    B.contDiff_northThomRaw.differentiable infty_ne_zero |>.differentiableAt |>.norm
      ℝ (B.northThomRaw_ne_zero x)
  have hscalar : DifferentiableAt ℝ
      (fun q => ‖B.northThomRaw q‖⁻¹ * B.northCutoff q) x :=
    (hrnorm.inv (norm_ne_zero_iff.mpr (B.northThomRaw_ne_zero x))).mul
      (B.contDiff_northCutoff.differentiable infty_ne_zero |>.differentiableAt)
  have hgdiff : DifferentiableAt ℝ B.fls.g x :=
    B.fls.smooth.differentiable infty_ne_zero |>.differentiableAt
  rw [fderiv_fun_smul hscalar hgdiff, B.fls_g_of_northFiber hx,
    B.northCutoff_of_northFiber hx]
  simp


-- @@ L257-258 verbatim
lemma northThom_frameScale_pos (x : E) : 0 < ‖B.northThomRaw x‖⁻¹ :=
  inv_pos.mpr (norm_pos_iff.mpr (B.northThomRaw_ne_zero x))


-- @@ L260-269 verbatim
theorem surjective_fderiv_northThomHorizontal_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) :
    Function.Surjective (fderiv ℝ B.northThomHorizontal x) := by
  rw [B.fderiv_northThomHorizontal_of_northFiber hx]
  intro w
  obtain ⟨v, hv⟩ := B.fls.regular x (B.fls_g_of_northFiber hx)
    ((‖B.northThomRaw x‖⁻¹)⁻¹ • w)
  refine ⟨v, ?_⟩
  rw [smul_apply, hv, smul_smul,
    mul_inv_cancel₀ (B.northThom_frameScale_pos x).ne', one_smul]


-- @@ L271-271 verbatim
/-! ## Exact north fiber -/


-- @@ L273-275 verbatim
/-- The target north pole of the collapse. -/
def ptNorthPole : UnitSphere E :=
  ⟨eLast n, by rw [mem_sphere_zero_iff_norm, norm_eLast]⟩


-- @@ L277-277 verbatim
@[simp] lemma ptNorthPole_coe : (ptNorthPole (n := n) : E) = eLast n := rfl


-- @@ L279-288 verbatim
lemma northThomRaw_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) :
    B.northThomRaw x = Real.sqrt (1 - ‖B.y‖ ^ 2) • eLast n := by
  have hcut := B.northCutoff_of_northFiber hx
  have hge : -(1 / 4) ≤ vertC (B.northSource x) := by
    rw [hx]
    have := vertC_northPoint_pos B.norm_y_lt_one
    linarith
  rw [northThomRaw, plateauAux_of_ge hge, hcut, one_smul, hx, northPoint]
  module


-- @@ L290-294 verbatim
lemma sqrt_one_sub_norm_y_sq_pos : 0 < Real.sqrt (1 - ‖B.y‖ ^ 2) := by
  apply Real.sqrt_pos.mpr
  have h0 := norm_nonneg B.y
  have h1 := B.norm_y_lt_one
  nlinarith


-- @@ L296-304 verbatim
/-- The northern part of the regular fiber is sent to the collapse north pole. -/
theorem northThom_of_northFiber {x : E}
    (hx : B.northSource x = northPoint B.y) :
    B.northThom x = ptNorthPole := by
  apply Subtype.ext
  rw [northThom_coe, B.northThomRaw_of_northFiber hx, ptNorthPole_coe,
    norm_smul, norm_eLast, mul_one, Real.norm_eq_abs,
    abs_of_pos B.sqrt_one_sub_norm_y_sq_pos]
  rw [inv_smul_smul₀ B.sqrt_one_sub_norm_y_sq_pos.ne']


-- @@ L306-343 verbatim
/-- Exact fiber theorem: the north-pole fiber of the collapse is precisely the
northern preimage of the bridge regular value. -/
theorem northThom_eq_ptNorthPole_iff (x : E) :
    B.northThom x = ptNorthPole ↔
      B.northSource x = northPoint B.y := by
  constructor
  · intro hc
    have hnorm : 0 < ‖B.northThomRaw x‖ :=
      norm_pos_iff.mpr (B.northThomRaw_ne_zero x)
    have hcoe : ‖B.northThomRaw x‖⁻¹ • B.northThomRaw x = eLast n := by
      have := congrArg Subtype.val hc
      simpa [northThom_coe, ptNorthPole_coe] using this
    have hraw : B.northThomRaw x = ‖B.northThomRaw x‖ • eLast n := by
      calc
        B.northThomRaw x = ‖B.northThomRaw x‖ •
            (‖B.northThomRaw x‖⁻¹ • B.northThomRaw x) := by
              rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
        _ = ‖B.northThomRaw x‖ • eLast n := by rw [hcoe]
    have hpair := B.inner_northThomRaw_source_pos x
    rw [hraw, real_inner_smul_left, inner_eLast_left] at hpair
    have ht : 0 < vertC (B.northSource x) := by
      have hn := norm_nonneg (B.northThomRaw x)
      nlinarith
    have hcut : B.northCutoff x = 1 := by
      rw [northCutoff]
      exact plateauA_of_ge (by linarith)
    have hinit : initCLM n (B.northThomRaw x) = 0 := by
      rw [hraw, map_smul, initCLM_eLast, smul_zero]
    rw [B.initCLM_northThomRaw, hcut, one_smul] at hinit
    have hhor : initCLM n (B.northSource x) = B.y := by
      change bridgeHMapE B.approx x - B.y = 0 at hinit
      exact sub_eq_zero.mp hinit
    rcases (init_eq_iff (B.norm_northSource x) B.y).mp hhor with hn | hs
    · exact hn
    · exfalso
      rw [hs] at ht
      exact (not_lt_of_ge (le_of_lt (vertC_southPointOf_neg B.norm_y_lt_one))) ht
  · exact B.northThom_of_northFiber


-- @@ L345-345 verbatim
/-! ## Southern collapse and cubical loop -/


-- @@ L347-351 verbatim
lemma northThomRaw_of_southCap {x : E}
    (hx : vertC (B.northSource x) ≤ -(1 / 2)) :
    B.northThomRaw x = -eLast n := by
  rw [northThomRaw, plateauAux_of_le hx, northCutoff, plateauA_of_le hx]
  simp


-- @@ L353-359 verbatim
theorem northThom_of_southCap {x : E}
    (hx : vertC (B.northSource x) ≤ -(1 / 2)) :
    B.northThom x = southPole n := by
  apply Subtype.ext
  rw [northThom_coe, B.northThomRaw_of_southCap hx, southPole_coe,
    norm_neg, norm_eLast]
  simp


-- @@ L361-372 verbatim
lemma southPointOf_mem_southCap :
    vertC (southPointOf B.y) ≤ -(1 / 2) := by
  rw [vertC_southPointOf]
  have harg : 0 ≤ 1 - ‖B.y‖ ^ 2 := by
    have h0 := norm_nonneg B.y
    have h1 := B.norm_y_lt_one
    nlinarith
  have hs0 := Real.sqrt_nonneg (1 - ‖B.y‖ ^ 2)
  have hs2 := Real.sq_sqrt harg
  have hy0 := norm_nonneg B.y
  have hy8 := B.norm_y_lt
  nlinarith


-- @@ L374-381 verbatim
/-- The unwanted southern component of the two-point horizontal fiber is collapsed
to the basepoint, while the northern component is the exact north-pole fiber. -/
theorem northThom_of_southFiber {x : E}
    (hx : B.northSource x = southPointOf B.y) :
    B.northThom x = southPole n := by
  apply B.northThom_of_southCap
  rw [hx]
  exact B.southPointOf_mem_southCap


-- @@ L383-385 verbatim
/-- The unit cube as a subset of the Euclidean source used by `B.fls`. -/
def cubeToBridgeDomain (t : I^(Fin (n + 1))) : E :=
  WithLp.toLp 2 fun i => (t i : ℝ)


-- @@ L387-388 verbatim
@[simp] lemma cubeToBridgeDomain_apply (t : I^(Fin (n + 1))) (i : Fin (n + 1)) :
    cubeToBridgeDomain t i = (t i : ℝ) := rfl


-- @@ L390-398 verbatim
lemma continuous_cubeToBridgeDomain :
    Continuous (cubeToBridgeDomain (n := n)) := by
  have h : cubeToBridgeDomain (n := n) = fun t =>
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (fun i => (t i : ℝ)) := rfl
  rw [h]
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (continuous_apply i)


-- @@ L400-402 verbatim
lemma northSource_cube (t : I^(Fin (n + 1))) :
    B.northSource (cubeToBridgeDomain t) =
      nprep B.approx (fun i => (t i : ℝ)) := rfl


-- @@ L404-408 verbatim
lemma northSource_cube_boundary {t : I^(Fin (n + 1))}
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    B.northSource (cubeToBridgeDomain t) = -eLast n := by
  rw [B.northSource_cube]
  exact nprep_of_mem_collar B.approx (coords_mem_closedAmbientCollar ht)


-- @@ L410-417 verbatim
theorem northThom_cube_boundary {t : I^(Fin (n + 1))}
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    B.northThom (cubeToBridgeDomain t) = southPole n := by
  apply B.northThom_of_southCap
  rw [B.northSource_cube_boundary ht]
  show (-eLast n) (Fin.last n) ≤ -(1 / 2 : ℝ)
  simp [eLast]
  norm_num


-- @@ L419-424 verbatim
/-- The cubical generalized loop of the northern Thom collapse. -/
def northThomLoop :
    Ω^ (Fin (n + 1)) (UnitSphere E) (southPole n) :=
  ⟨B.northThomCM.comp
      ⟨cubeToBridgeDomain, continuous_cubeToBridgeDomain⟩,
    fun _ ht => B.northThom_cube_boundary ht⟩


-- @@ L426-427 verbatim
@[simp] lemma northThomLoop_apply (t : I^(Fin (n + 1))) :
    B.northThomLoop t = B.northThom (cubeToBridgeDomain t) := rfl


-- @@ L429-433 verbatim
theorem northThomLoop_eq_ptNorthPole_iff (t : I^(Fin (n + 1))) :
    B.northThomLoop t = ptNorthPole ↔
      nprep B.approx (fun i => (t i : ℝ)) = northPoint B.y := by
  rw [northThomLoop_apply, B.northThom_eq_ptNorthPole_iff,
    B.northSource_cube]


-- @@ L435-435 verbatim
/-! ## Explicit normalized-chord comparison -/


-- @@ L437-440 verbatim
/-- The original bridge source, packaged as a point of the unit sphere. -/
def northSourcePoint (x : E) : UnitSphere E :=
  ⟨B.northSource x,
    mem_sphere_zero_iff_norm.mpr (B.norm_northSource x)⟩


-- @@ L442-443 verbatim
@[simp] lemma northSourcePoint_coe (x : E) :
    (B.northSourcePoint x : E) = B.northSource x := rfl


-- @@ L445-449 verbatim
lemma inner_northThom_source_pos (x : E) :
    0 < ⟪(B.northThom x : E), B.northSource x⟫ := by
  rw [northThom_coe, real_inner_smul_left]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (B.northThomRaw_ne_zero x)))
    (B.inner_northThomRaw_source_pos x)


-- @@ L451-460 verbatim
lemma northSourcePoint_ne_neg_northThom (x : E) :
    B.northSourcePoint x ≠ -B.northThom x := by
  intro hc
  have hcoe : B.northSource x = -(B.northThom x : E) := by
    have := congrArg Subtype.val hc
    simpa [northSourcePoint_coe, coe_neg_sphere] using this
  have hpos := B.inner_northThom_source_pos x
  rw [hcoe, inner_neg_right, real_inner_self_eq_norm_sq,
    UnitSphere.norm_coe] at hpos
  norm_num at hpos


-- @@ L462-464 verbatim
lemma dist_northSourcePoint_northThom_lt_two (x : E) :
    dist (B.northSourcePoint x) (B.northThom x) < 2 :=
  dist_lt_two_of_ne_neg _ _ (B.northSourcePoint_ne_neg_northThom x)


-- @@ L466-469 verbatim
lemma prepLoop_eq_northSourcePoint (t : I^(Fin (n + 1))) :
    prepLoop B.approx t = B.northSourcePoint (cubeToBridgeDomain t) := by
  apply Subtype.ext
  rw [prepLoop_coe, northSourcePoint_coe, B.northSource_cube]


-- @@ L471-474 verbatim
lemma dist_prepLoop_northThomLoop_lt_two (t : I^(Fin (n + 1))) :
    dist (prepLoop B.approx t) (B.northThomLoop t) < 2 := by
  rw [B.prepLoop_eq_northSourcePoint, northThomLoop_apply]
  exact B.dist_northSourcePoint_northThom_lt_two _


-- @@ L476-485 verbatim
/-- The promised explicit Pontryagin--Thom homotopy: normalize the straight chord
from the bridge representative to the northern Thom collapse.  It is relative to
the entire cubical boundary. -/
def prepLoopToNorthThomHomotopy :
    ContinuousMap.HomotopyRel (prepLoop B.approx).1 B.northThomLoop.1
      (Cube.boundary (Fin (n + 1))) :=
  chordHomotopyRel (prepLoop B.approx).1 B.northThomLoop.1
    B.dist_prepLoop_northThomLoop_lt_two
    (Cube.boundary (Fin (n + 1))) fun t ht =>
      ((prepLoop B.approx).2 t ht).trans (B.northThomLoop.2 t ht).symm


-- @@ L487-489 verbatim
theorem prepLoop_homotopic_northThomLoop :
    GenLoop.Homotopic (prepLoop B.approx) B.northThomLoop :=
  ⟨B.prepLoopToNorthThomHomotopy⟩


-- @@ L491-500 verbatim
/-- Milnor PT injectivity for the concrete bridge representative: reconstructing
the collapse from its northern regular fiber and its induced normal framing gives
the original homotopy class. -/
theorem northThomLoop_class_eq :
    (⟦B.northThomLoop⟧ : HomotopyGroup (Fin (n + 1))
      (UnitSphere E) (southPole n)) = z := by
  calc
    ⟦B.northThomLoop⟧ = ⟦prepLoop B.approx⟧ :=
      (Quotient.sound B.prepLoop_homotopic_northThomLoop).symm
    _ = z := B.prepLoop_class_eq


-- @@ L502-502 verbatim
end BridgeData


-- @@ L504-504 verbatim
end Submission
