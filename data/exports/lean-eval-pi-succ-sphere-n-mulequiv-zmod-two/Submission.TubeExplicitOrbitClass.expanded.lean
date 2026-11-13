import Mathlib
import Submission.BridgeDeltaAssembly
import Submission.DeltaFrameTransport
import Submission.TubeExplicitFrame


-- @@ L6-12 verbatim
/-!
# The intrinsic orbit class of the explicit tube bridge

The northern circle of the explicit bridge has already been computed using its
explicit angular parametrization.  This file compares that parametrization with
the intrinsic unit-speed flow parametrization used by `TamedField.orbitFrameClass`.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
set_option maxHeartbeats 1600000


-- @@ L18-18 verbatim
namespace Submission


-- @@ L20-20 verbatim
open Set Function Topology

-- @@ L21-21 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval


-- @@ L23-23 verbatim
variable {m : ℕ}


-- @@ L25-25 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))


-- @@ L27-37 verbatim
/-- The angle-zero point on the explicit northern bridge circle lies in the
regular fiber. -/
theorem tubeExplicitBridgeNorthBase_mem_fiber (k : ℕ) :
    tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y 0 ∈
      (tubeExplicitBridge (m := m) k).fls.fiber := by
  let B := tubeExplicitBridge (m := m) k
  have hp : tubeBridgeCirclePoint k B.y 0 ∈
      Set.range (tubeBridgeCirclePoint k B.y) := ⟨0, rfl⟩
  rw [← tubeExplicitBridge_north_fiber_eq_range (m := m) k] at hp
  rw [B.fiber_eq]
  exact Or.inl hp


-- @@ L39-52 verbatim
/-- The explicit once-around northern parametrization, regarded as a path in
the intrinsic flow orbit through its angle-zero point. -/
def tubeExplicitBridgeParamOrbitPath (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    C(I, V.orbit
      (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y 0)) where
  toFun u := ⟨tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y
      (2 * Real.pi * (u : ℝ)),
    tubeExplicitBridge_circle_mem_orbit k V _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (contDiff_tubeBridgeCirclePoint k
      (tubeExplicitBridge (m := m) k).y).continuous.comp
        ((continuous_const.mul continuous_const).mul continuous_subtype_val)


-- @@ L54-64 verbatim
/-- Phase of the explicit circle inside the intrinsic period circle. -/
def tubeExplicitBridgeParamPhase (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    C(I, AddCircle (V.fundamentalPeriod
      (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))) where
  toFun u := (V.orbitCircleHomeomorph
    (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)).symm
      (tubeExplicitBridgeParamOrbitPath k V u)
  continuous_toFun := (V.orbitCircleHomeomorph
    (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)).symm.continuous.comp
      (tubeExplicitBridgeParamOrbitPath k V).continuous


-- @@ L66-73 verbatim
theorem tubeExplicitBridgeParamPhase_homeomorph_apply (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) (u : I) :
    V.orbitCircleHomeomorph
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)
        (tubeExplicitBridgeParamPhase k V u) =
      tubeExplicitBridgeParamOrbitPath k V u := by
  exact (V.orbitCircleHomeomorph
    (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)).apply_symm_apply _


-- @@ L75-85 verbatim
@[simp] theorem tubeExplicitBridgeParamPhase_zero (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    tubeExplicitBridgeParamPhase k V 0 = 0 := by
  apply (V.orbitCircleHomeomorph
    (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)).injective
  rw [tubeExplicitBridgeParamPhase_homeomorph_apply]
  apply Subtype.ext
  change tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y
      (2 * Real.pi * (((0 : I) : ℝ))) =
    V.flow (tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y 0) 0
  simp


-- @@ L87-107 verbatim
theorem tubeExplicitBridgeParamPhase_closed (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    tubeExplicitBridgeParamPhase k V 0 =
      tubeExplicitBridgeParamPhase k V 1 := by
  apply (V.orbitCircleHomeomorph
    (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)).injective
  rw [tubeExplicitBridgeParamPhase_homeomorph_apply,
    tubeExplicitBridgeParamPhase_homeomorph_apply]
  apply Subtype.ext
  change tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y
      (2 * Real.pi * (((0 : I) : ℝ))) =
    tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y
      (2 * Real.pi * (((1 : I) : ℝ)))
  have hoff := (tubeMap_periodic (m := m) k
    (tubeNorthOffset (tubeExplicitBridge (m := m) k).y) 0).symm
  apply PiLp.ext
  intro i
  rw [tubeBridgeCirclePoint_apply, tubeBridgeCirclePoint_apply]
  norm_num
  exact congrArg (fun x : E => x i) (by
    simpa [tubeOffsetCirclePoint] using hoff)


-- @@ L109-169 verbatim
/-- The explicit angular parametrization is one-to-one on the half-open unit
interval; its only repetition on the closed interval is the endpoint pair. -/
theorem tubeExplicitBridgeParamPhase_eq_cases (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) {u v : I}
    (huv : tubeExplicitBridgeParamPhase k V u =
      tubeExplicitBridgeParamPhase k V v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  have hpoint :
      tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y
          (2 * Real.pi * (u : ℝ)) =
        tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y
          (2 * Real.pi * (v : ℝ)) := by
    have h := congrArg (V.orbitCircleHomeomorph
      (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)) huv
    rw [tubeExplicitBridgeParamPhase_homeomorph_apply,
      tubeExplicitBridgeParamPhase_homeomorph_apply] at h
    exact congrArg Subtype.val h
  have hamb := congrArg
    (fun x : E => tubeApproxAmbient (WithLp.ofLp x)) hpoint
  rw [tubeApproxAmbient_bridgeCirclePoint,
    tubeApproxAmbient_bridgeCirclePoint] at hamb
  have hq := tubeNorthOffset_norm_lt_quarter
    (tubeExplicitBridge (m := m) k).y
    (tubeExplicitBridge (m := m) k).norm_y_lt
  obtain ⟨z, hz⟩ := (tubeMap_inj (m := m)
    (hq.trans (by norm_num)) (hq.trans (by norm_num)) hamb).1
  have huvZ : (v : ℝ) = (u : ℝ) + (z : ℝ) := by
    have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    nlinarith
  have hzLowerR : (-1 : ℝ) ≤ (z : ℝ) := by
    nlinarith [u.2.2, v.2.1]
  have hzUpperR : (z : ℝ) ≤ 1 := by
    nlinarith [u.2.1, v.2.2]
  have hzLower : (-1 : ℤ) ≤ z := by exact_mod_cast hzLowerR
  have hzUpper : z ≤ (1 : ℤ) := by exact_mod_cast hzUpperR
  rcases (show z = -1 ∨ z = 0 ∨ z = 1 by omega) with hzv | hzv | hzv
  · right; right
    constructor <;> apply Subtype.ext
    · change (u : ℝ) = 1
      rw [hzv] at huvZ
      norm_num at huvZ
      nlinarith [u.2.2, v.2.1]
    · change (v : ℝ) = 0
      rw [hzv] at huvZ
      norm_num at huvZ
      nlinarith [u.2.2, v.2.1]
  · left
    apply Subtype.ext
    rw [hzv] at huvZ
    norm_num at huvZ
    exact huvZ.symm
  · right; left
    constructor <;> apply Subtype.ext
    · change (u : ℝ) = 0
      rw [hzv] at huvZ
      norm_num at huvZ
      nlinarith [u.2.1, v.2.2]
    · change (v : ℝ) = 1
      rw [hzv] at huvZ
      norm_num at huvZ
      nlinarith [u.2.1, v.2.2]


-- @@ L171-171 verbatim
/-! ## Lift of the explicit phase -/


-- @@ L173-181 verbatim
/-- The intrinsic-time lift of the explicit circle phase, starting at zero. -/
def tubeExplicitBridgeParamPhaseLift (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) : C(I, ℝ) := by
  let hp := tubeExplicitBridgeNorthBase_mem_fiber (m := m) k
  let T := V.fundamentalPeriod hp
  letI : Fact (0 < T) := ⟨V.fundamentalPeriod_pos hp⟩
  exact (AddCircle.isCoveringMap_coe T).liftPath
    (tubeExplicitBridgeParamPhase k V) 0
      (tubeExplicitBridgeParamPhase_zero k V)


-- @@ L183-187 verbatim
@[simp] theorem tubeExplicitBridgeParamPhaseLift_zero (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    tubeExplicitBridgeParamPhaseLift k V 0 = 0 := by
  unfold tubeExplicitBridgeParamPhaseLift
  apply IsCoveringMap.liftPath_zero


-- @@ L189-201 verbatim
theorem tubeExplicitBridgeParamPhaseLift_coe (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) (u : I) :
    ((tubeExplicitBridgeParamPhaseLift k V u : ℝ) :
        AddCircle (V.fundamentalPeriod
          (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))) =
      tubeExplicitBridgeParamPhase k V u := by
  let hp := tubeExplicitBridgeNorthBase_mem_fiber (m := m) k
  let T := V.fundamentalPeriod hp
  letI : Fact (0 < T) := ⟨V.fundamentalPeriod_pos hp⟩
  have h := congrFun ((AddCircle.isCoveringMap_coe T).liftPath_lifts
    (tubeExplicitBridgeParamPhase k V) 0
      (tubeExplicitBridgeParamPhase_zero k V)) u
  simpa [tubeExplicitBridgeParamPhaseLift, hp, T] using h


-- @@ L203-220 verbatim
theorem tubeExplicitBridgeParamPhaseLift_endpoint_zsmul (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    ∃ z : ℤ, tubeExplicitBridgeParamPhaseLift k V 1 =
      z • V.fundamentalPeriod
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k) := by
  let ψ := tubeExplicitBridgeParamPhaseLift k V
  let T := V.fundamentalPeriod
    (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)
  have hcoe : ((ψ 1 : ℝ) : AddCircle T) = 0 := by
    calc
      ((ψ 1 : ℝ) : AddCircle T) =
          tubeExplicitBridgeParamPhase k V 1 :=
        tubeExplicitBridgeParamPhaseLift_coe k V 1
      _ = tubeExplicitBridgeParamPhase k V 0 :=
        (tubeExplicitBridgeParamPhase_closed k V).symm
      _ = 0 := tubeExplicitBridgeParamPhase_zero k V
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff T).mp hcoe
  exact ⟨z, hz.symm⟩


-- @@ L222-307 verbatim
theorem tubeExplicitBridgeParamPhaseLift_one_ne_zero (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    tubeExplicitBridgeParamPhaseLift k V 1 ≠ 0 := by
  let ψ := tubeExplicitBridgeParamPhaseLift k V
  let φ := tubeExplicitBridgeParamPhase k V
  let c : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hc0 : (0 : I) < c := by change (0 : ℝ) < 1 / 2; norm_num
  have hc1 : c < (1 : I) := by change (1 / 2 : ℝ) < 1; norm_num
  have hφc : φ c ≠ φ 0 := by
    intro h
    rcases tubeExplicitBridgeParamPhase_eq_cases k V h with
      hEq | hEnds | hEnds
    · exact (ne_of_gt hc0) hEq
    · exact (zero_ne_one : (0 : I) ≠ 1) hEnds.2
    · exact (ne_of_lt hc1) hEnds.1
  have hψc : ψ c ≠ 0 := by
    intro hzero
    apply hφc
    calc
      φ c = ((ψ c : ℝ) : AddCircle
          (V.fundamentalPeriod
            (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))) :=
        (tubeExplicitBridgeParamPhaseLift_coe k V c).symm
      _ = ((ψ 0 : ℝ) : AddCircle
          (V.fundamentalPeriod
            (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))) := by
        rw [hzero, tubeExplicitBridgeParamPhaseLift_zero]
      _ = φ 0 := tubeExplicitBridgeParamPhaseLift_coe k V 0
  intro hψ1
  have hcont : Continuous ψ :=
    (tubeExplicitBridgeParamPhaseLift k V).continuous
  rcases lt_or_gt_of_ne hψc with hneg | hpos
  · let z : ℝ := ψ c / 2
    have hzL : z ∈ Icc (ψ c) (ψ 0) := by
      rw [tubeExplicitBridgeParamPhaseLift_zero]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨u, huI, hu⟩ := intermediate_value_Icc' (le_of_lt hc0)
      hcont.continuousOn hzL
    have hzR : z ∈ Icc (ψ c) (ψ 1) := by
      rw [hψ1]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨v, hvI, hv⟩ := intermediate_value_Icc (le_of_lt hc1)
      hcont.continuousOn hzR
    have hphase : φ u = φ v := by
      rw [← tubeExplicitBridgeParamPhaseLift_coe k V u,
        ← tubeExplicitBridgeParamPhaseLift_coe k V v, hu, hv]
    rcases tubeExplicitBridgeParamPhase_eq_cases k V hphase with
      huv | hends | hends
    · subst v
      have : u = c := le_antisymm huI.2 hvI.1
      subst u
      dsimp [z] at hu
      linarith
    · rw [hends.1, tubeExplicitBridgeParamPhaseLift_zero] at hu
      dsimp [z] at hu
      linarith
    · rw [hends.1, hψ1] at hu
      dsimp [z] at hu
      linarith
  · let z : ℝ := ψ c / 2
    have hzL : z ∈ Icc (ψ 0) (ψ c) := by
      rw [tubeExplicitBridgeParamPhaseLift_zero]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨u, huI, hu⟩ := intermediate_value_Icc (le_of_lt hc0)
      hcont.continuousOn hzL
    have hzR : z ∈ Icc (ψ 1) (ψ c) := by
      rw [hψ1]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨v, hvI, hv⟩ := intermediate_value_Icc' (le_of_lt hc1)
      hcont.continuousOn hzR
    have hphase : φ u = φ v := by
      rw [← tubeExplicitBridgeParamPhaseLift_coe k V u,
        ← tubeExplicitBridgeParamPhaseLift_coe k V v, hu, hv]
    rcases tubeExplicitBridgeParamPhase_eq_cases k V hphase with
      huv | hends | hends
    · subst v
      have : u = c := le_antisymm huI.2 hvI.1
      subst u
      dsimp [z] at hu
      linarith
    · rw [hends.1, tubeExplicitBridgeParamPhaseLift_zero] at hu
      dsimp [z] at hu
      linarith
    · rw [hends.1, hψ1] at hu
      dsimp [z] at hu
      linarith


-- @@ L309-327 verbatim
theorem tubeExplicitBridgeParamPhaseLift_injective (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    Function.Injective (tubeExplicitBridgeParamPhaseLift k V) := by
  intro u v huv
  have hphase : tubeExplicitBridgeParamPhase k V u =
      tubeExplicitBridgeParamPhase k V v := by
    rw [← tubeExplicitBridgeParamPhaseLift_coe k V u,
      ← tubeExplicitBridgeParamPhaseLift_coe k V v, huv]
  rcases tubeExplicitBridgeParamPhase_eq_cases k V hphase with
    hEq | hEnds | hEnds
  · exact hEq
  · exfalso
    apply tubeExplicitBridgeParamPhaseLift_one_ne_zero k V
    rw [← hEnds.2, ← huv, hEnds.1,
      tubeExplicitBridgeParamPhaseLift_zero]
  · exfalso
    apply tubeExplicitBridgeParamPhaseLift_one_ne_zero k V
    rw [← hEnds.1, huv, hEnds.2,
      tubeExplicitBridgeParamPhaseLift_zero]


-- @@ L329-410 verbatim
/-- The explicit simple circle runs through exactly one intrinsic period, with
one of the two possible orientations. -/
theorem tubeExplicitBridgeParamPhaseLift_one_eq_period_or_neg (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    tubeExplicitBridgeParamPhaseLift k V 1 =
        V.fundamentalPeriod
          (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k) ∨
      tubeExplicitBridgeParamPhaseLift k V 1 =
        -V.fundamentalPeriod
          (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k) := by
  let ψ := tubeExplicitBridgeParamPhaseLift k V
  let φ := tubeExplicitBridgeParamPhase k V
  let T := V.fundamentalPeriod
    (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)
  have hT : 0 < T := V.fundamentalPeriod_pos
    (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)
  obtain ⟨z, hz⟩ := tubeExplicitBridgeParamPhaseLift_endpoint_zsmul k V
  have hzR : ψ 1 = (z : ℝ) * T := by
    simpa [ψ, T, zsmul_eq_mul] using hz
  have hmonoanti := (tubeExplicitBridgeParamPhaseLift k V).continuous
    |>.strictMono_of_inj_boundedOrder'
      (tubeExplicitBridgeParamPhaseLift_injective k V)
  rcases hmonoanti with hmono | hanti
  · have hψ1pos : 0 < ψ 1 := by
      have h := hmono (show (0 : I) < 1 by norm_num)
      rwa [tubeExplicitBridgeParamPhaseLift_zero] at h
    have hzposR : (0 : ℝ) < (z : ℝ) := by nlinarith
    have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
    have hzle : z ≤ 1 := by
      by_contra hznot
      have hzge : (2 : ℤ) ≤ z := by omega
      have hzgeR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzge
      have hmem : T ∈ Icc (ψ 0) (ψ 1) := by
        rw [tubeExplicitBridgeParamPhaseLift_zero, hzR]
        constructor <;> nlinarith
      obtain ⟨u, hu⟩ := intermediate_value_univ (0 : I) (1 : I)
        (tubeExplicitBridgeParamPhaseLift k V).continuous hmem
      have hphase : φ u = φ 0 := by
        rw [← tubeExplicitBridgeParamPhaseLift_coe k V u,
          ← tubeExplicitBridgeParamPhaseLift_coe k V 0,
          hu, tubeExplicitBridgeParamPhaseLift_zero]
        exact AddCircle.coe_period T
      rcases tubeExplicitBridgeParamPhase_eq_cases k V hphase with
        hu0 | hbad | hu1
      · rw [hu0, tubeExplicitBridgeParamPhaseLift_zero] at hu
        linarith
      · exact (zero_ne_one : (0 : I) ≠ 1) hbad.2
      · rw [hu1.1, hzR] at hu
        nlinarith
    have hzone : z = 1 := by omega
    left
    simpa [T, hzone] using hzR
  · have hψ1neg : ψ 1 < 0 := by
      have h := hanti (show (0 : I) < 1 by norm_num)
      rwa [tubeExplicitBridgeParamPhaseLift_zero] at h
    have hznegR : (z : ℝ) < 0 := by nlinarith
    have hzneg : z < (0 : ℤ) := by exact_mod_cast hznegR
    have hzge : (-1 : ℤ) ≤ z := by
      by_contra hznot
      have hzle : z ≤ (-2 : ℤ) := by omega
      have hzleR : (z : ℝ) ≤ -2 := by exact_mod_cast hzle
      have hmem : -T ∈ Icc (ψ 1) (ψ 0) := by
        rw [tubeExplicitBridgeParamPhaseLift_zero, hzR]
        constructor <;> nlinarith
      obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) (0 : I)
        (tubeExplicitBridgeParamPhaseLift k V).continuous hmem
      have hphase : φ u = φ 0 := by
        rw [← tubeExplicitBridgeParamPhaseLift_coe k V u,
          ← tubeExplicitBridgeParamPhaseLift_coe k V 0,
          hu, tubeExplicitBridgeParamPhaseLift_zero]
        rw [AddCircle.coe_neg, AddCircle.coe_period, neg_zero]
        rfl
      rcases tubeExplicitBridgeParamPhase_eq_cases k V hphase with
        hu0 | hbad | hu1
      · rw [hu0, tubeExplicitBridgeParamPhaseLift_zero] at hu
        linarith
      · exact (zero_ne_one : (0 : I) ≠ 1) hbad.2
      · rw [hu1.1, hzR] at hu
        nlinarith
    have hzmone : z = -1 := by omega
    right
    simpa [T, hzmone] using hzR


-- @@ L412-412 verbatim
/-! ## Frame comparison after lifting -/


-- @@ L414-427 verbatim
/-- The explicit angular point is the intrinsic flow evaluated at the lifted
phase. -/
theorem tubeExplicitBridgeParamPoint_eq_flow_lift (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) (u : I) :
    tubeBridgeCirclePoint k (tubeExplicitBridge (m := m) k).y
        (2 * Real.pi * (u : ℝ)) =
      V.flow (tubeBridgeCirclePoint k
          (tubeExplicitBridge (m := m) k).y 0)
        (tubeExplicitBridgeParamPhaseLift k V u) := by
  have h := tubeExplicitBridgeParamPhase_homeomorph_apply k V u
  rw [← tubeExplicitBridgeParamPhaseLift_coe k V u] at h
  have hv := congrArg Subtype.val h
  rw [V.orbitCircleHomeomorph_coe] at hv
  simpa [tubeExplicitBridgeParamOrbitPath] using hv.symm


-- @@ L429-449 verbatim
/-- The frame loop written in lifted intrinsic flow time. -/
def tubeExplicitBridgeLiftedFrameLoop (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    C(I, SOGroup (m + 3)) where
  toFun u := ⟨frameLoop (tubeExplicitBridge (m := m) k).fls
      (V.flow (tubeBridgeCirclePoint k
        (tubeExplicitBridge (m := m) k).y 0))
      (tubeExplicitBridgeParamPhaseLift k V u),
    frameLoop_mem_specialOrthogonalGroup
      (tubeExplicitBridge (m := m) k).fls
      (V.flow_mem_fiber
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_frameLoop
      (tubeExplicitBridge (m := m) k).fls
      (V.continuous_flow (tubeBridgeCirclePoint k
        (tubeExplicitBridge (m := m) k).y 0))
      (V.flow_mem_fiber
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))).comp
      (tubeExplicitBridgeParamPhaseLift k V).continuous


-- @@ L451-461 verbatim
theorem tubeExplicitBridgeParamFrameLoop_eq_lifted (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    tubeExplicitBridgeParamFrameLoop (m := m) k =
      tubeExplicitBridgeLiftedFrameLoop k V := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [tubeExplicitBridgeParamFrameLoop_apply]
  unfold frameLoop
  rw [tubeExplicitBridgeParamPoint_eq_flow_lift k V u]
  rfl


-- @@ L463-484 verbatim
/-- The intrinsic frame loop run with orientation factor `ε`. -/
def tubeExplicitBridgeOrientedFrameLoop (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) (ε : ℝ) :
    C(I, SOGroup (m + 3)) where
  toFun u := ⟨frameLoop (tubeExplicitBridge (m := m) k).fls
      (V.flow (tubeBridgeCirclePoint k
        (tubeExplicitBridge (m := m) k).y 0))
      (ε * (u : ℝ) * V.fundamentalPeriod
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)),
    frameLoop_mem_specialOrthogonalGroup
      (tubeExplicitBridge (m := m) k).fls
      (V.flow_mem_fiber
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_frameLoop
      (tubeExplicitBridge (m := m) k).fls
      (V.continuous_flow (tubeBridgeCirclePoint k
        (tubeExplicitBridge (m := m) k).y 0))
      (V.flow_mem_fiber
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))).comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)


-- @@ L486-529 verbatim
/-- Straight-line interpolation between the lifted phase and a chosen
orientation of the intrinsic period. -/
def tubeExplicitBridgeFrameReparamHomotopy (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) (ε : ℝ) :
    ContinuousMap.Homotopy
      (tubeExplicitBridgeLiftedFrameLoop k V)
      (tubeExplicitBridgeOrientedFrameLoop k V ε) where
  toFun q := ⟨frameLoop (tubeExplicitBridge (m := m) k).fls
      (V.flow (tubeBridgeCirclePoint k
        (tubeExplicitBridge (m := m) k).y 0))
      ((1 - (q.1 : ℝ)) * tubeExplicitBridgeParamPhaseLift k V q.2 +
        (q.1 : ℝ) * (ε * (q.2 : ℝ) * V.fundamentalPeriod
          (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))),
    frameLoop_mem_specialOrthogonalGroup
      (tubeExplicitBridge (m := m) k).fls
      (V.flow_mem_fiber
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (continuous_frameLoop
      (tubeExplicitBridge (m := m) k).fls
      (V.continuous_flow (tubeBridgeCirclePoint k
        (tubeExplicitBridge (m := m) k).y 0))
      (V.flow_mem_fiber
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))).comp
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst) |>.mul
      ((tubeExplicitBridgeParamPhaseLift k V).continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
          continuous_const))
  map_zero_left := fun u => by
    apply Subtype.ext
    change frameLoop _ _
        ((1 - (((0 : I) : ℝ))) * tubeExplicitBridgeParamPhaseLift k V u +
          (((0 : I) : ℝ) * (ε * (u : ℝ) * _))) = _
    congr 2
    norm_num
  map_one_left := fun u => by
    apply Subtype.ext
    change frameLoop _ _
        ((1 - (((1 : I) : ℝ))) * tubeExplicitBridgeParamPhaseLift k V u +
          (((1 : I) : ℝ) * (ε * (u : ℝ) * _))) = _
    congr 2
    norm_num


-- @@ L531-541 verbatim
theorem tubeExplicitBridgeOrientedFrameLoop_one (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    tubeExplicitBridgeOrientedFrameLoop k V 1 =
      V.fundamentalFrameLoop
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop _ _ (1 * (u : ℝ) * _) = frameLoop _ _ ((u : ℝ) * _)
  congr 2
  ring


-- @@ L543-561 verbatim
theorem tubeExplicitBridgeOrientedFrameLoop_neg_one (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    tubeExplicitBridgeOrientedFrameLoop k V (-1) =
      reverseLoop (V.fundamentalFrameLoop
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  let hp := tubeExplicitBridgeNorthBase_mem_fiber (m := m) k
  let F := fun t : ℝ => frameLoop (tubeExplicitBridge (m := m) k).fls
    (V.flow (tubeBridgeCirclePoint k
      (tubeExplicitBridge (m := m) k).y 0)) t
  have hper : Function.Periodic F (V.fundamentalPeriod hp) :=
    frameLoop_periodic _ (V.fundamentalPeriod_periodic hp)
  change F ((-1 : ℝ) * (u : ℝ) * V.fundamentalPeriod hp) =
    F ((unitInterval.symm u : ℝ) * V.fundamentalPeriod hp)
  have h := hper ((-1 : ℝ) * (u : ℝ) * V.fundamentalPeriod hp)
  rw [show (unitInterval.symm u : ℝ) = 1 - (u : ℝ) by rfl]
  convert h.symm using 1 <;> ring


-- @@ L563-568 verbatim
theorem tubeExplicitBridgeLiftedFrameLoop_closed (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    tubeExplicitBridgeLiftedFrameLoop k V 0 =
      tubeExplicitBridgeLiftedFrameLoop k V 1 := by
  rw [← tubeExplicitBridgeParamFrameLoop_eq_lifted k V]
  exact tubeExplicitBridgeParamFrameLoop_closed k


-- @@ L570-599 verbatim
theorem tubeExplicitBridgeFrameReparamHomotopy_closed (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) (ε : ℝ)
    (hend : tubeExplicitBridgeParamPhaseLift k V 1 =
      ε * V.fundamentalPeriod
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))
    (hperiod : Function.Periodic
      (fun t : ℝ => frameLoop (tubeExplicitBridge (m := m) k).fls
        (V.flow (tubeBridgeCirclePoint k
          (tubeExplicitBridge (m := m) k).y 0)) t)
      (ε * V.fundamentalPeriod
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)))
    (s : I) :
    tubeExplicitBridgeFrameReparamHomotopy k V ε (s, 0) =
      tubeExplicitBridgeFrameReparamHomotopy k V ε (s, 1) := by
  apply Subtype.ext
  let T := V.fundamentalPeriod
    (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k)
  let F := fun t : ℝ => frameLoop (tubeExplicitBridge (m := m) k).fls
    (V.flow (tubeBridgeCirclePoint k
      (tubeExplicitBridge (m := m) k).y 0)) t
  change F ((1 - (s : ℝ)) * tubeExplicitBridgeParamPhaseLift k V 0 +
      (s : ℝ) * (ε * (((0 : I) : ℝ)) * T)) =
    F ((1 - (s : ℝ)) * tubeExplicitBridgeParamPhaseLift k V 1 +
      (s : ℝ) * (ε * (((1 : I) : ℝ)) * T))
  rw [tubeExplicitBridgeParamPhaseLift_zero, hend]
  norm_num
  change F 0 = F ((1 - (s : ℝ)) * (ε * T) + (s : ℝ) * (ε * T))
  rw [show (1 - (s : ℝ)) * (ε * T) + (s : ℝ) * (ε * T) =
    ε * T by ring]
  simpa [F, T] using (hperiod 0).symm


-- @@ L601-615 verbatim
theorem tubeExplicitBridgeOrientedFrameLoop_closed (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) (ε : ℝ)
    (hperiod : Function.Periodic
      (fun t : ℝ => frameLoop (tubeExplicitBridge (m := m) k).fls
        (V.flow (tubeBridgeCirclePoint k
          (tubeExplicitBridge (m := m) k).y 0)) t)
      (ε * V.fundamentalPeriod
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k))) :
    tubeExplicitBridgeOrientedFrameLoop k V ε 0 =
      tubeExplicitBridgeOrientedFrameLoop k V ε 1 := by
  apply Subtype.ext
  change frameLoop _ _ (ε * (((0 : I) : ℝ)) * _) =
    frameLoop _ _ (ε * (((1 : I) : ℝ)) * _)
  norm_num
  convert (hperiod 0).symm using 1 <;> ring


-- @@ L617-684 verbatim
/-- The explicit parametrized frame has the intrinsic fundamental frame class;
reversing the circle orientation is invisible over `ZMod 2`. -/
theorem tubeExplicitBridgeParamFrameClass_eq_fundamental (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    loopClassZ2 (tubeExplicitBridgeParamFrameLoop (m := m) k)
        (tubeExplicitBridgeParamFrameLoop_closed k) =
      V.fundamentalFrameClass
        (tubeExplicitBridgeNorthBase_mem_fiber (m := m) k) := by
  let hp := tubeExplicitBridgeNorthBase_mem_fiber (m := m) k
  let T := V.fundamentalPeriod hp
  let F := fun t : ℝ => frameLoop (tubeExplicitBridge (m := m) k).fls
    (V.flow (tubeBridgeCirclePoint k
      (tubeExplicitBridge (m := m) k).y 0)) t
  have hper : Function.Periodic F T :=
    frameLoop_periodic _ (V.fundamentalPeriod_periodic hp)
  have hloop := tubeExplicitBridgeParamFrameLoop_eq_lifted k V
  rcases tubeExplicitBridgeParamPhaseLift_one_eq_period_or_neg k V with
    hplus | hminus
  · have hend : tubeExplicitBridgeParamPhaseLift k V 1 =
        (1 : ℝ) * V.fundamentalPeriod hp := by simpa using hplus
    have hclosed := tubeExplicitBridgeFrameReparamHomotopy_closed k V 1 hend
      (by simpa [F, T] using hper)
    have horientedClosed := tubeExplicitBridgeOrientedFrameLoop_closed k V 1
      (by simpa [F, T] using hper)
    calc
      loopClassZ2 (tubeExplicitBridgeParamFrameLoop (m := m) k)
          (tubeExplicitBridgeParamFrameLoop_closed k) =
        loopClassZ2 (tubeExplicitBridgeLiftedFrameLoop k V)
          (tubeExplicitBridgeLiftedFrameLoop_closed k V) :=
        loopClassZ2_congr_fun (tubeExplicitBridgeParamFrameLoop_closed k)
          (tubeExplicitBridgeLiftedFrameLoop_closed k V) hloop
      _ = loopClassZ2 (tubeExplicitBridgeOrientedFrameLoop k V 1)
          horientedClosed :=
        loopClassZ2_congr (tubeExplicitBridgeLiftedFrameLoop_closed k V)
          horientedClosed
          (tubeExplicitBridgeFrameReparamHomotopy k V 1) hclosed
      _ = V.fundamentalFrameClass hp := by
        unfold TamedField.fundamentalFrameClass
        exact loopClassZ2_congr_fun horientedClosed
          (V.fundamentalFrameLoop_closed hp)
          (tubeExplicitBridgeOrientedFrameLoop_one k V)
  · have hend : tubeExplicitBridgeParamPhaseLift k V 1 =
        (-1 : ℝ) * V.fundamentalPeriod hp := by simpa using hminus
    have hclosed := tubeExplicitBridgeFrameReparamHomotopy_closed k V (-1) hend
      (by simpa [F, T] using hper.neg)
    have horientedClosed := tubeExplicitBridgeOrientedFrameLoop_closed k V (-1)
      (by simpa [F, T] using hper.neg)
    calc
      loopClassZ2 (tubeExplicitBridgeParamFrameLoop (m := m) k)
          (tubeExplicitBridgeParamFrameLoop_closed k) =
        loopClassZ2 (tubeExplicitBridgeLiftedFrameLoop k V)
          (tubeExplicitBridgeLiftedFrameLoop_closed k V) :=
        loopClassZ2_congr_fun (tubeExplicitBridgeParamFrameLoop_closed k)
          (tubeExplicitBridgeLiftedFrameLoop_closed k V) hloop
      _ = loopClassZ2 (tubeExplicitBridgeOrientedFrameLoop k V (-1))
          horientedClosed :=
        loopClassZ2_congr (tubeExplicitBridgeLiftedFrameLoop_closed k V)
          horientedClosed
          (tubeExplicitBridgeFrameReparamHomotopy k V (-1)) hclosed
      _ = loopClassZ2
          (reverseLoop (V.fundamentalFrameLoop hp))
          (reverseLoop_closed (V.fundamentalFrameLoop_closed hp)) := by
        exact loopClassZ2_congr_fun horientedClosed
          (reverseLoop_closed (V.fundamentalFrameLoop_closed hp))
          (tubeExplicitBridgeOrientedFrameLoop_neg_one k V)
      _ = V.fundamentalFrameClass hp := by
        exact loopClassZ2_reverse (V.fundamentalFrameLoop hp)
          (V.fundamentalFrameLoop_closed hp)


-- @@ L686-686 verbatim
/-! ## The explicit northern ledger value -/


-- @@ L688-716 verbatim
/-- The intrinsic orbit frame class of the unique northern orbit is the class
computed from the explicit angular parametrization. -/
theorem tubeExplicitBridge_north_orbitFrameClass (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    V.orbitFrameClass (tubeExplicitBridgeNorthOrbitIndex k V) =
      (k : ZMod 2) + 1 := by
  let O := tubeExplicitBridgeNorthOrbitIndex k V
  let p : E := tubeBridgeCirclePoint k
    (tubeExplicitBridge (m := m) k).y 0
  let hp : p ∈ (tubeExplicitBridge (m := m) k).fls.fiber :=
    tubeExplicitBridgeNorthBase_mem_fiber (m := m) k
  have hpoint : V.orbitPoint O ∈ V.orbit p := by
    change V.orbitPoint O ∈
      V.orbit (tubeBridgeCirclePoint k
        (tubeExplicitBridge (m := m) k).y 0)
    rw [← tubeExplicitBridgeNorthOrbitIndex_coe k V]
    change V.orbitPoint O ∈ (O : Set E)
    rw [V.orbitPoint_orbit O]
    exact V.mem_orbit_self (V.orbitPoint O)
  calc
    V.orbitFrameClass O =
        V.fundamentalFrameClass (V.orbitPoint_mem_fiber O) := rfl
    _ = V.fundamentalFrameClass hp :=
      V.fundamentalFrameClass_eq_of_mem_orbit hp hpoint
    _ = loopClassZ2 (tubeExplicitBridgeParamFrameLoop (m := m) k)
        (tubeExplicitBridgeParamFrameLoop_closed k) :=
      (tubeExplicitBridgeParamFrameClass_eq_fundamental k V).symm
    _ = (k : ZMod 2) + 1 :=
      loopClassZ2_tubeExplicitBridgeParamFrameLoop k


-- @@ L718-728 verbatim
/-- With the Pontryagin--Thom tangent correction, the unique northern orbit
contributes exactly `k mod 2`. -/
theorem tubeExplicitBridge_north_orbitContribution (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    V.orbitContribution (tubeExplicitBridgeNorthOrbitIndex k V) =
      (k : ZMod 2) := by
  unfold TamedField.orbitContribution
  rw [tubeExplicitBridge_north_orbitFrameClass]
  rw [add_assoc]
  rw [show (1 : ZMod 2) + 1 = 0 by
    exact CharTwo.two_eq_zero, add_zero]


-- @@ L730-736 verbatim
/-- Final northern ledger evaluation for the explicit tube bridge. -/
theorem tubeExplicitBridge_northFramedDelta (k : ℕ)
    (V : TamedField (tubeExplicitBridge (m := m) k).fls) :
    (tubeExplicitBridge (m := m) k).northFramedDelta V =
      (k : ZMod 2) := by
  rw [tubeExplicitBridge_northFramedDelta_eq_orbitContribution]
  exact tubeExplicitBridge_north_orbitContribution k V


-- @@ L738-743 verbatim
/-- Choice-free northern invariant of the explicit bridge. -/
@[simp] theorem tubeExplicitBridge_northDelta (k : ℕ) :
    (tubeExplicitBridge (m := m) k).northDelta = (k : ZMod 2) := by
  rw [(tubeExplicitBridge (m := m) k).northDelta_eq
    (tubeExplicitBridge (m := m) k).canonicalTamedField]
  exact tubeExplicitBridge_northFramedDelta k _


-- @@ L745-745 verbatim
end Submission
