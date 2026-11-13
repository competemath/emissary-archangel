import Submission.MorseCriticalModelAssembly
import Submission.MorseAtlasAssembly
import Submission.PerturbedIFTSurfaceCover


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open Set Function Metric Filter

-- @@ L8-8 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L10-10 verbatim
namespace Submission


-- @@ L12-12 verbatim
variable {n : ℕ}


-- @@ L14-14 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L15-15 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L16-16 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L18-32 verbatim
private theorem iteratedDeriv_const_add_sq_mul (c a : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => c + x ^ 2 * a) 0 = 2 * a := by
  rw [show iteratedDeriv 2 (fun x : ℝ => c + x ^ 2 * a) 0 =
      deriv (deriv (fun x : ℝ => c + x ^ 2 * a)) 0 by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]]
  have hfirst : deriv (fun x : ℝ => c + x ^ 2 * a) =
      fun x : ℝ => (2 * x) * a := by
    funext x
    simpa [id_eq, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_const (x := x) c).add
        (((hasDerivAt_id x).pow 2).mul_const a)).deriv
  rw [hfirst]
  simpa [id_eq, mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const a).deriv


-- @@ L34-61 verbatim
private theorem iteratedDeriv_morseLine
    (e : MorseIndexTwo) (c : ℝ) (v : E₂) :
    iteratedDeriv 2
      (fun t : ℝ => c + morseQuadratic e ((t • v) 0, (t • v) 1)) 0 =
      match e with
      | .minimum => 2 * (v 0 ^ 2 + v 1 ^ 2)
      | .saddle => 2 * (v 0 ^ 2 - v 1 ^ 2)
      | .maximum => -2 * (v 0 ^ 2 + v 1 ^ 2) := by
  cases e with
  | minimum =>
      simp only [morseQuadratic, smul_eq_mul, PiLp.smul_apply]
      rw [show (fun t : ℝ => c + ((t * v 0) ^ 2 + (t * v 1) ^ 2)) =
          fun t : ℝ => c + t ^ 2 * (v 0 ^ 2 + v 1 ^ 2) by
        funext t; ring]
      rw [iteratedDeriv_const_add_sq_mul]
  | saddle =>
      simp only [morseQuadratic, smul_eq_mul, PiLp.smul_apply]
      rw [show (fun t : ℝ => c + ((t * v 0) ^ 2 - (t * v 1) ^ 2)) =
          fun t : ℝ => c + t ^ 2 * (v 0 ^ 2 - v 1 ^ 2) by
        funext t; ring]
      rw [iteratedDeriv_const_add_sq_mul]
  | maximum =>
      simp only [morseQuadratic, smul_eq_mul, PiLp.smul_apply]
      rw [show (fun t : ℝ => c + (-(t * v 0) ^ 2 - (t * v 1) ^ 2)) =
          fun t : ℝ => c + t ^ 2 * (-(v 0 ^ 2 + v 1 ^ 2)) by
        funext t; ring]
      rw [iteratedDeriv_const_add_sq_mul]
      ring


-- @@ L63-63 verbatim
namespace LocalMorseNormalForm


-- @@ L65-169 verbatim
/-- The exact nondegenerate quadratic identity forces the derivative of the
Morse parameter to be invertible at its origin.  This recovers the local
inverse property intentionally omitted from the compact normal-form record. -/
theorem fderiv_param_injective {f : E₂ → ℝ}
    (M : LocalMorseNormalForm f) (hf : ContDiffAt ℝ 2 f 0)
    (hcrit : fderiv ℝ f 0 = 0) :
    Injective (fderiv ℝ M.param 0) := by
  let J : E₂ →L[ℝ] E₂ := fderiv ℝ M.param 0
  have hparam2 : ContDiffAt ℝ 2 M.param 0 :=
    contDiffAt_infty.mp M.param_contDiffAt 2
  have hline (v : E₂) : ContDiffAt ℝ 2 (fun t : ℝ => t • v) 0 := by
    exact (contDiff_id.smul contDiff_const).contDiffAt
  have hcurve (v : E₂) :
      ContDiffAt ℝ 2 (fun t : ℝ => M.param (t • v)) 0 := by
    let l : ℝ → E₂ := fun t => t • v
    have hl : ContDiffAt ℝ 2 l 0 := hline v
    have hp : ContDiffAt ℝ 2 M.param (l 0) := by
      simpa [l] using hparam2
    exact ContDiffAt.fun_comp (f := l) (g := M.param) 0 hp hl
  have hcurve_deriv (v : E₂) :
      deriv (fun t : ℝ => M.param (t • v)) 0 = J v := by
    have hs : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hp : HasFDerivAt M.param J ((0 : ℝ) • v) := by
      simpa [J] using
        (hparam2.differentiableAt (by norm_num)).hasFDerivAt
    have hc := hp.comp_hasDerivAt 0 hs
    simpa [J, Function.comp_def] using hc.deriv
  have hevent (v : E₂) :
      (fun t : ℝ => f (M.param (t • v))) =ᶠ[nhds 0]
        (fun t : ℝ => f 0 +
          morseQuadratic M.index ((t • v) 0, (t • v) 1)) := by
    have ht : Tendsto (fun t : ℝ => t • v) (nhds 0) (nhds 0) := by
      simpa [id_eq] using (continuousAt_id.smul_const v :
        ContinuousAt (fun t : ℝ => t • v) 0)
    have hsmall := ht (ball_mem_nhds (0 : E₂) M.radius_pos)
    filter_upwards [hsmall] with t ht'
    apply M.exact
    simpa [mem_ball, dist_zero_right] using ht'
  have hmodel (v : E₂) :
      iteratedDeriv 2 (fun t : ℝ => f (M.param (t • v))) 0 =
        match M.index with
        | .minimum => 2 * (v 0 ^ 2 + v 1 ^ 2)
        | .saddle => 2 * (v 0 ^ 2 - v 1 ^ 2)
        | .maximum => -2 * (v 0 ^ 2 + v 1 ^ 2) := by
    rw [(hevent v).iteratedDeriv_eq 2]
    exact iteratedDeriv_morseLine M.index (f 0) v
  have hsecond (v : E₂) :
      iteratedDeriv 2 (fun t : ℝ => f (M.param (t • v))) 0 =
        iteratedFDeriv ℝ 2 f 0 (fun _ => J v) := by
    have hf0 : ContDiffAt ℝ 2 f (M.param ((0 : ℝ) • v)) := by
      simpa [M.param_zero] using hf
    have hcomp := iteratedDeriv_vcomp_two hf0 (hcurve v)
    change iteratedDeriv 2
      (f ∘ fun t : ℝ => M.param (t • v)) 0 = _
    rw [hcomp]
    simp only [zero_smul, M.param_zero, hcurve_deriv, hcrit, zero_apply,
      add_zero]
  have hker : ∀ v : E₂, J v = 0 → v = 0 := by
    intro v hv
    have hvzero :
        iteratedDeriv 2 (fun t : ℝ => f (M.param (t • v))) 0 = 0 := by
      rw [hsecond, hv]
      exact ContinuousMultilinearMap.map_zero _
    cases hi : M.index with
    | minimum =>
        rw [hmodel] at hvzero
        simp [hi] at hvzero
        have hv0 : v 0 = 0 := by
          nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
        have hv1 : v 1 = 0 := by
          nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
        ext i
        fin_cases i <;> simp [hv0, hv1]
    | maximum =>
        rw [hmodel] at hvzero
        simp [hi] at hvzero
        have hv0 : v 0 = 0 := by
          nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
        have hv1 : v 1 = 0 := by
          nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
        ext i
        fin_cases i <;> simp [hv0, hv1]
    | saddle =>
        rw [hmodel] at hvzero
        simp [hi] at hvzero
        let e₀ : E₂ := EuclideanSpace.single 0 1
        have hJadd : J (v + e₀) = J e₀ := by rw [map_add, hv, zero_add]
        have hcompare :
            iteratedDeriv 2 (fun t : ℝ => f (M.param (t • (v + e₀)))) 0 =
              iteratedDeriv 2 (fun t : ℝ => f (M.param (t • e₀))) 0 := by
          rw [hsecond, hsecond, hJadd]
        rw [hmodel, hmodel] at hcompare
        simp [hi, e₀] at hcompare
        have hv0 : v 0 = 0 := by nlinarith [hcompare]
        have hv1 : v 1 = 0 := by
          nlinarith [hvzero, sq_nonneg (v 1)]
        ext i
        fin_cases i
        · exact hv0
        · exact hv1
  intro v w hvw
  apply sub_eq_zero.mp
  apply hker (v - w)
  rw [map_sub, hvw, sub_self]


-- @@ L171-210 verbatim
/-- The Morse parameter fills a neighborhood of the origin, with its inverse
landing in any prescribed positive-radius ball. -/
theorem exists_preimage_norm_lt {f : E₂ → ℝ}
    (M : LocalMorseNormalForm f) (hf : ContDiffAt ℝ 2 f 0)
    (hcrit : fderiv ℝ f 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ y : E₂, ‖y‖ < δ →
      ∃ u : E₂, ‖u‖ < r ∧ M.param u = y := by
  let J : E₂ →L[ℝ] E₂ := fderiv ℝ M.param 0
  have hJinj : Injective J := M.fderiv_param_injective hf hcrit
  have hJsurj : Surjective J :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hJinj
  let e : E₂ ≃L[ℝ] E₂ := ContinuousLinearEquiv.ofBijective J
    (LinearMap.ker_eq_bot.mpr hJinj) (LinearMap.range_eq_top.mpr hJsurj)
  have he : (e : E₂ →L[ℝ] E₂) = J := rfl
  have hfd : HasFDerivAt M.param (e : E₂ →L[ℝ] E₂) 0 := by
    rw [he]
    exact (M.param_contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hs : HasStrictFDerivAt M.param (e : E₂ →L[ℝ] E₂) 0 :=
    M.param_contDiffAt.hasStrictFDerivAt' hfd (by simp)
  let inv : E₂ → E₂ := hs.localInverse M.param e 0
  have hright : ∀ᶠ y in nhds (0 : E₂), M.param (inv y) = y := by
    simpa [inv, M.param_zero] using hs.eventually_right_inverse
  have hinv : ∀ᶠ y in nhds (0 : E₂), ‖inv y‖ < r := by
    have ht := hs.localInverse_tendsto (ball_mem_nhds (0 : E₂) hr)
    change (hs.localInverse M.param e 0) ⁻¹' ball (0 : E₂) r ∈
      nhds (M.param 0) at ht
    rw [M.param_zero] at ht
    change inv ⁻¹' ball (0 : E₂) r ∈ nhds (0 : E₂) at ht
    filter_upwards [ht] with y hy
    simpa [mem_ball, dist_zero_right] using hy
  have hgood : {y : E₂ | M.param (inv y) = y ∧ ‖inv y‖ < r} ∈
      nhds (0 : E₂) := hright.and hinv
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hyball : y ∈ ball (0 : E₂) δ := by
    simpa [mem_ball, dist_zero_right] using hy
  have hy' := hball hyball
  refine ⟨inv y, ?_, hy'.1⟩
  exact hy'.2


-- @@ L212-248 verbatim
/-- On a sufficiently small ball, the derivative of the Morse parameter is
injective at every point.  This is the uniform differential form of the local
inverse property used by transported tangent and orientation calculations. -/
theorem exists_fderiv_param_injective_radius {f : E₂ → ℝ}
    (M : LocalMorseNormalForm f) (hf : ContDiffAt ℝ 2 f 0)
    (hcrit : fderiv ℝ f 0 = 0) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ r > 0, r ≤ r₀ ∧ ∀ u : E₂, ‖u‖ < r →
      Injective (fderiv ℝ M.param u) := by
  let J : E₂ →L[ℝ] E₂ := fderiv ℝ M.param 0
  have hJinj : Injective J := M.fderiv_param_injective hf hcrit
  have hJsurj : Surjective J :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hJinj
  let e : E₂ ≃L[ℝ] E₂ := ContinuousLinearEquiv.ofBijective J
    (LinearMap.ker_eq_bot.mpr hJinj) (LinearMap.range_eq_top.mpr hJsurj)
  have he : (e : E₂ →L[ℝ] E₂) = J := rfl
  have hopen : Set.range ((↑) : (E₂ ≃L[ℝ] E₂) → E₂ →L[ℝ] E₂) ∈
      nhds (fderiv ℝ M.param 0) := by
    change Set.range ((↑) : (E₂ ≃L[ℝ] E₂) → E₂ →L[ℝ] E₂) ∈ nhds J
    rw [← he]
    exact ContinuousLinearEquiv.nhds e
  have hcontinuous : ContinuousAt (fderiv ℝ M.param) 0 :=
    M.param_contDiffAt.continuousAt_fderiv (by simp)
  have hevent : ∀ᶠ u in nhds (0 : E₂),
      fderiv ℝ M.param u ∈
        Set.range ((↑) : (E₂ ≃L[ℝ] E₂) → E₂ →L[ℝ] E₂) :=
    hcontinuous hopen
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let r := min δ r₀
  have hr : 0 < r := lt_min hδ hr₀
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro u hu
  have hud : ‖u‖ < δ := hu.trans_le (min_le_left _ _)
  have huball : u ∈ ball (0 : E₂) δ := by
    simpa [mem_ball, dist_zero_right] using hud
  obtain ⟨e', he'⟩ := hball huball
  rw [← he']
  exact e'.injective


-- @@ L250-250 verbatim
end LocalMorseNormalForm


-- @@ L252-252 verbatim
namespace IFTSurfaceChart


-- @@ L254-259 verbatim
/-- The two ambient linear coordinates represented by `liftCovector`. -/
def recoveryCoordinates {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) : E' →L[ℝ] E₂ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 2 =>
      P.liftCovector (EuclideanSpace.single i 1))


-- @@ L261-266 verbatim
@[simp] theorem recoveryCoordinates_apply
    {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    (v : E') (i : Fin 2) :
    P.recoveryCoordinates v i =
      P.liftCovector (EuclideanSpace.single i 1) v := by
  rfl


-- @@ L268-275 verbatim
/-- The stored covector identity recovers the full chart parameter. -/
theorem recoveryCoordinates_param_sub_center
    {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    {u : E₂} (hu : u ∈ P.domain) :
    P.recoveryCoordinates (P.param u - P.center) = u := by
  ext i
  rw [P.recoveryCoordinates_apply, P.lift_param _ u hu]
  simp [EuclideanSpace.inner_single_left]


-- @@ L277-280 verbatim
/-- The defining map together with the recovered free coordinates. -/
def straightening {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) (v : E') : F × E₂ :=
  (C.G v, P.recoveryCoordinates (v - P.center))


-- @@ L282-285 verbatim
theorem contDiff_straightening {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) : ContDiff ℝ ∞ P.straightening := by
  exact C.smooth.prodMk
    (P.recoveryCoordinates.contDiff.comp (contDiff_id.sub contDiff_const))


-- @@ L287-292 verbatim
theorem straightening_param {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) {u : E₂} (hu : u ∈ P.domain) :
    P.straightening (P.param u) = ((0 : F), u) := by
  apply Prod.ext
  · exact P.param_fiber u hu
  · exact P.recoveryCoordinates_param_sub_center hu


-- @@ L294-304 verbatim
theorem hasFDerivAt_straightening {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) (x : E') :
    HasFDerivAt P.straightening
      ((fderiv ℝ C.G x).prod P.recoveryCoordinates) x := by
  have hcoord : HasFDerivAt
      (fun v : E' => P.recoveryCoordinates (v - P.center))
      P.recoveryCoordinates x := by
    simpa only [map_sub] using
      P.recoveryCoordinates.hasFDerivAt.sub_const
        (P.recoveryCoordinates P.center)
  exact (C.smooth.differentiable (by simp) x).hasFDerivAt.prodMk hcoord


-- @@ L306-358 verbatim
/-- The straightening derivative is an equivalence at every parameter in the
genuine open chart domain. -/
theorem straightening_fderiv_bijective
    {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    (hdom : IsOpen P.domain) {z : E₂} (hz : z ∈ P.domain) :
    Bijective (fderiv ℝ P.straightening (P.param z)) := by
  let x : E' := P.param z
  let A : E' →L[ℝ] E₂ := P.recoveryCoordinates
  let dG : E' →L[ℝ] F := fderiv ℝ C.G x
  let J : E₂ →L[ℝ] E' := fderiv ℝ P.param z
  let D : E' →L[ℝ] (F × E₂) := dG.prod A
  let ι₂ : E₂ →L[ℝ] (F × E₂) :=
    (0 : E₂ →L[ℝ] F).prod (ContinuousLinearMap.id ℝ E₂)
  have hD : fderiv ℝ P.straightening x = D := by
    exact (P.hasFDerivAt_straightening x).fderiv
  have hcomp : HasFDerivAt (P.straightening ∘ P.param) (D.comp J) z := by
    exact (P.hasFDerivAt_straightening x).comp z
      (P.param_smooth.differentiable (by simp) z).hasFDerivAt
  have hι : HasFDerivAt (fun u : E₂ => ((0 : F), u)) ι₂ z := by
    simpa [ι₂] using
      ((hasFDerivAt_const (x := z) (0 : F)).prodMk (hasFDerivAt_id z))
  have heq : (P.straightening ∘ P.param) =ᶠ[nhds z]
      (fun u : E₂ => ((0 : F), u)) := by
    filter_upwards [hdom.mem_nhds hz] with u hu
    exact P.straightening_param hu
  have hDJ : D.comp J = ι₂ := by
    rw [← hcomp.fderiv, heq.fderiv_eq, hι.fderiv]
  have hpair (u : E₂) : D (J u) = ((0 : F), u) := by
    change (D.comp J) u = ι₂ u
    rw [hDJ]
  have hxzero : C.G x = 0 := P.param_fiber z hz
  have hdGsurj : Surjective dG := by
    exact C.regular x hxzero
  have hDsurj : Surjective D := by
    intro y
    obtain ⟨v, hv⟩ := hdGsurj y.1
    let q : E₂ := y.2 - A v
    refine ⟨v + J q, ?_⟩
    have hq := hpair q
    have hq0 : dG (J q) = 0 := congrArg Prod.fst hq
    have hqq : A (J q) = q := congrArg Prod.snd hq
    apply Prod.ext
    · change dG (v + J q) = y.1
      rw [map_add, hv, hq0, add_zero]
    · change A (v + J q) = y.2
      rw [map_add, hqq]
      simp [q]
  have hdim : Module.finrank ℝ E' = Module.finrank ℝ (F × E₂) := by
    simp [finrank_euclideanSpace_fin]
  have hDinj : Injective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hDsurj
  rw [hD]
  exact ⟨hDinj, hDsurj⟩


-- @@ L360-425 verbatim
/-- A production IFT surface chart covers the fiber locally at every point of
its open domain, not only at its distinguished origin.  The recovered free
coordinate can be required to lie in any prescribed neighborhood. -/
theorem exists_param_of_fiber_near
    {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    (hdom : IsOpen P.domain) {z : E₂} (hz : z ∈ P.domain)
    {W : Set E₂} (hW : W ∈ nhds z) :
    ∃ ε > 0, ∀ v : E', dist v (P.param z) < ε → C.G v = 0 →
      ∃ u : E₂, u ∈ W ∧ u ∈ P.domain ∧ P.param u = v := by
  let x : E' := P.param z
  let D : E' →L[ℝ] (F × E₂) := fderiv ℝ P.straightening x
  have hbij : Bijective D := P.straightening_fderiv_bijective hdom hz
  let e : E' ≃L[ℝ] (F × E₂) := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have he : (e : E' →L[ℝ] (F × E₂)) = D := rfl
  have hfd : HasFDerivAt P.straightening
      (e : E' →L[ℝ] (F × E₂)) x := by
    rw [he]
    exact (P.contDiff_straightening.differentiable (by simp) x).hasFDerivAt
  have hs : HasStrictFDerivAt P.straightening
      (e : E' →L[ℝ] (F × E₂)) x :=
    P.contDiff_straightening.contDiffAt.hasStrictFDerivAt' hfd (by simp)
  let inv : (F × E₂) → E' :=
    hs.localInverse P.straightening e x
  let L : Set E' := {v | inv (P.straightening v) = v}
  have hL : L ∈ nhds x := by
    exact hs.eventually_left_inverse
  have hparamL : P.param ⁻¹' L ∈ nhds z := by
    have hp : Tendsto P.param (nhds z) (nhds x) := by
      change Tendsto P.param (nhds z) (nhds (P.param z))
      exact P.param_smooth.continuous.continuousAt
    exact hp hL
  let U : Set E₂ := W ∩ P.domain ∩ P.param ⁻¹' L
  have hU : U ∈ nhds z := by
    exact inter_mem (inter_mem hW (hdom.mem_nhds hz)) hparamL
  let coord : E' → E₂ := fun v => P.recoveryCoordinates (v - P.center)
  have hcoordx : coord x = z := by
    exact P.recoveryCoordinates_param_sub_center hz
  have hcoord : Tendsto coord (nhds x) (nhds z) := by
    have hc : ContinuousAt coord x := by
      exact P.recoveryCoordinates.continuous.continuousAt.comp
        (continuousAt_id.sub continuousAt_const)
    rw [← hcoordx]
    exact hc
  have hgood : L ∩ coord ⁻¹' U ∈ nhds x := inter_mem hL (hcoord hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨ε, hε, ?_⟩
  intro v hv hzero
  have hvball : v ∈ ball x ε := by
    simpa [mem_ball, x] using hv
  have hvgood := hball hvball
  let u : E₂ := coord v
  have huU : u ∈ U := hvgood.2
  have huW : u ∈ W := huU.1.1
  have hudom : u ∈ P.domain := huU.1.2
  have hparamL' : P.param u ∈ L := huU.2
  have hstraight : P.straightening (P.param u) = P.straightening v := by
    rw [P.straightening_param hudom]
    change ((0 : F), u) = (C.G v, coord v)
    simp [u, hzero]
  have hparam : P.param u = v := by
    calc
      P.param u = inv (P.straightening (P.param u)) := hparamL'.symm
      _ = inv (P.straightening v) := congrArg inv hstraight
      _ = v := hvgood.1
  exact ⟨u, huW, hudom, hparam⟩


-- @@ L427-427 verbatim
end IFTSurfaceChart


-- @@ L429-429 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L431-433 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceCover C ι}
  {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L435-441 verbatim
private theorem localSeparatedTime_contDiff_for_exactAssembly
    (p : Σ _ : ι, E₂) : ContDiff ℝ ∞ (G.localSeparatedTime p) := by
  change ContDiff ℝ ∞
    (fun u => (G.tilt p.1).tilted u + G.valueShift p)
  rw [(G.tilt p.1).tilted_eq]
  exact (contDiff_chartLinearTilt
    (B.chart p.1).contDiff_time (G.tilt p.1).q).add contDiff_const


-- @@ L443-462 verbatim
/-- A further positive radius inside the fixed production shrink on which the
Morse parameter has injective derivative at every point. -/
theorem exists_criticalModelShrink_fderiv_param_injective_radius
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ u : E₂, ‖u‖ < r →
        Injective
          (fderiv ℝ (G.localMorseNormalForm p hp).param u) := by
  have hsmooth : ContDiff ℝ ∞ (G.localSeparatedTime p) :=
    localSeparatedTime_contDiff_for_exactAssembly (G := G) p
  have hf : ContDiffAt ℝ 2
      (recenter (G.localSeparatedTime p) p.2) 0 :=
    contDiffAt_infty.mp (contDiff_recenter hsmooth p.2).contDiffAt 2
  have hcrit : fderiv ℝ (recenter (G.localSeparatedTime p) p.2) 0 = 0 :=
    fderiv_eq_zero_of_chartGradient_eq_zero
      (nondegenerateCriticalAt_recenter hsmooth
        (G.localSeparatedTime_nondegenerate p hp)).1
  exact (G.localMorseNormalForm p hp).exists_fderiv_param_injective_radius
    hf hcrit (R.criticalModelShrink p hp).radius_pos


-- @@ L464-538 verbatim
/-- The production IFT chart and the exact scalar Morse coordinate together
cover the actual pulled-back fiber near an installed critical center.  This is
the local-surjectivity field required by `InstalledMorseEventGeometry`; no
covering hypothesis is added to the finite installation record. -/
theorem covers_fiber_of_criticalModelShrink
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ∃ ε > 0, ∀ v : E',
      dist v (R.amplitude.diffeomorph.symm
        ((B.chart p.1).param p.2)) < ε →
      (R.amplitude.toVerticalAmplitude.pullback C).G v = 0 →
      ∃ u : E₂, ‖u‖ < (R.criticalNormalForm p hp).radius ∧
        R.amplitude.diffeomorph.symm
          ((B.chart p.1).param
            (p.2 + (R.criticalNormalForm p hp).param u)) = v := by
  let P := B.chart p.1
  let M := G.localMorseNormalForm p hp
  let S := R.criticalModelShrink p hp
  let x : E' := P.param p.2
  let c : E' := R.amplitude.diffeomorph.symm x
  have hsmooth : ContDiff ℝ ∞ (G.localSeparatedTime p) :=
    localSeparatedTime_contDiff_for_exactAssembly (G := G) p
  have hf : ContDiffAt ℝ 2
      (recenter (G.localSeparatedTime p) p.2) 0 :=
    contDiffAt_infty.mp (contDiff_recenter hsmooth p.2).contDiffAt 2
  have hcrit : fderiv ℝ (recenter (G.localSeparatedTime p) p.2) 0 = 0 :=
    fderiv_eq_zero_of_chartGradient_eq_zero
      (nondegenerateCriticalAt_recenter hsmooth
        (G.localSeparatedTime_nondegenerate p hp)).1
  obtain ⟨δ, hδ, hM⟩ := M.exists_preimage_norm_lt hf hcrit S.radius_pos
  have hpcore : p.2 ∈ B.core p.1 :=
    ((G.criticalPoints_spec p).mp hp).2
  have hpdom : p.2 ∈ P.domain := B.core_subset_domain p.1 hpcore
  obtain ⟨ε₀, hε₀, hP⟩ :=
    P.exists_param_of_fiber_near (B.domain_open p.1) hpdom
      (ball_mem_nhds p.2 hδ)
  have hforward : Tendsto (fun v : E' => R.amplitude.diffeomorph v)
      (nhds c) (nhds x) := by
    have hcx : R.amplitude.diffeomorph c = x := by
      dsimp [c]
      exact R.amplitude.diffeomorph.apply_symm_apply x
    rw [← hcx]
    exact R.amplitude.diffeomorph.continuous.continuousAt
  have hnear : (fun v : E' => R.amplitude.diffeomorph v) ⁻¹'
      ball x ε₀ ∈ nhds c :=
    hforward (ball_mem_nhds x hε₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε, hε, ?_⟩
  intro v hv hzero
  have hvball : v ∈ ball c ε := by
    simpa [mem_ball, c] using hv
  have hforwardBall : R.amplitude.diffeomorph v ∈ ball x ε₀ :=
    hball hvball
  have hforwardDist : dist (R.amplitude.diffeomorph v) (P.param p.2) < ε₀ := by
    simpa [mem_ball, x] using hforwardBall
  have hforwardZero : C.G (R.amplitude.diffeomorph v) = 0 := by
    simpa [VerticalAmplitude.pullback_G,
      SmallVerticalAmplitude.diffeomorph_apply] using hzero
  obtain ⟨z, hzball, _hzdom, hzparam⟩ :=
    hP (R.amplitude.diffeomorph v) hforwardDist hforwardZero
  have hy : ‖z - p.2‖ < δ := by
    simpa [mem_ball, dist_eq_norm] using hzball
  obtain ⟨u, hu, hMu⟩ := hM (z - p.2) hy
  refine ⟨u, ?_, ?_⟩
  · simpa [S] using hu
  · change R.amplitude.diffeomorph.symm
      (P.param (p.2 + M.param u)) = v
    calc
      R.amplitude.diffeomorph.symm (P.param (p.2 + M.param u)) =
          R.amplitude.diffeomorph.symm (P.param z) := by
            congr 2
            rw [hMu, add_sub_cancel]
      _ = R.amplitude.diffeomorph.symm
          (R.amplitude.diffeomorph v) := by rw [hzparam]
      _ = v := R.amplitude.diffeomorph.symm_apply_apply v


-- @@ L540-544 verbatim
/-- The actual center of a shrunk installed event in the pulled-back
cobordism. -/
def criticalCenter (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) : E' :=
  R.amplitude.diffeomorph.symm ((B.chart p.1).param p.2)


-- @@ L546-551 verbatim
/-- The actual surface parameter used by the shrunk installed event. -/
def criticalAmbientParam (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) (u : E₂) : E' :=
  R.amplitude.diffeomorph.symm
    ((B.chart p.1).param
      (p.2 + (R.criticalNormalForm p hp).param u))


-- @@ L553-558 verbatim
@[simp] theorem criticalAmbientParam_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalAmbientParam p hp 0 = R.criticalCenter p := by
  rw [criticalAmbientParam, criticalCenter,
    (R.criticalNormalForm p hp).param_zero, add_zero]


-- @@ L560-602 verbatim
/-- The production finite jet installation yields a genuine ambient event
geometry after the already-selected critical-model shrink. -/
def installedCriticalGeometry
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    InstalledMorseEventGeometry (n := n)
      (R.amplitude.toVerticalAmplitude.pullback C)
      (G.localSeparatedTime p) p.2 (R.criticalCenter p)
      (R.criticalNormalForm p hp) where
  ambientParam := R.criticalAmbientParam p hp
  ambientParam_smooth := by
    exact R.amplitude.contDiff_equiv_symm.contDiffAt.comp 0
      ((B.chart p.1).param_smooth.contDiffAt.comp 0
        (contDiffAt_const.add
          (R.criticalNormalForm p hp).param_contDiffAt))
  ambientParam_zero := R.criticalAmbientParam_zero p hp
  ambientParam_fiber := by
    intro u hu
    rw [VerticalAmplitude.pullback_G]
    change C.G (R.amplitude.diffeomorph
      (R.amplitude.diffeomorph.symm
        ((B.chart p.1).param
          (p.2 + (R.criticalNormalForm p hp).param u)))) = 0
    rw [R.amplitude.diffeomorph.apply_symm_apply]
    apply (B.chart p.1).param_fiber
    exact LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
      (M := G.localMorseNormalForm p hp)
      (R.criticalModelShrink p hp) u (by simpa using hu)
  time_lift := by
    intro u hu
    change tcoord (R.amplitude.diffeomorph.symm
      ((B.chart p.1).param
        (p.2 + (G.localMorseNormalForm p hp).param u))) = _
    simpa [recenter] using
      R.time_install_of_criticalModelShrink p hp
        (R.criticalModelShrink p hp) u (by simpa using hu)
  critical_model := by
    intro u hu
    simpa [criticalAmbientParam] using
      R.critical_model p hp u (by simpa using hu)
  covers_fiber := by
    simpa [criticalCenter, criticalAmbientParam] using
      R.covers_fiber_of_criticalModelShrink p hp


-- @@ L604-610 verbatim
/-- The fully assembled standard Morse event at one installed center. -/
def installedStandardMorseEvent
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    StandardMorseEventAt
      (R.amplitude.toVerticalAmplitude.pullback C) (R.criticalCenter p) :=
  (R.installedCriticalGeometry p hp).toStandardMorseEventAt


-- @@ L612-612 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L614-614 verbatim
end Submission
