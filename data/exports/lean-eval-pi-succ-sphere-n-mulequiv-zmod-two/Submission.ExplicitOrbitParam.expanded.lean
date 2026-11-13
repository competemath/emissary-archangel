import Mathlib
import Submission.DeltaFrameTransport


-- @@ L4-17 verbatim
/-!
# Explicit parametrizations of intrinsic fiber orbits

This file isolates the topological comparison which was previously carried out
only for the explicit tube.  A continuous parametrization of a fiber orbit
which is one-to-one except for its identified endpoints runs through exactly
one intrinsic flow period, possibly with reversed orientation.  Consequently
the frame loop read along that parametrization represents the intrinsic
`fundamentalFrameClass`.

The statement is deliberately independent of any particular Morse model.  It
is the common adapter used to turn the explicit circle/hyperbola frame
calculations in `MorseEvents` into the geometric orbit classes in `Delta`.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
set_option maxHeartbeats 1600000


-- @@ L23-23 verbatim
namespace Submission


-- @@ L25-25 verbatim
open Set Function Topology

-- @@ L26-26 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval


-- @@ L28-28 verbatim
variable {n : ℕ}


-- @@ L30-30 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L32-32 verbatim
namespace TamedField


-- @@ L34-57 verbatim
/-- A continuous real-parameter curve lying in one fiber cannot jump between
flow orbits.  This is the connectedness argument used repeatedly for explicit
circle models. -/
theorem continuousCurve_mem_orbit {X : FramedLevelSet n} (V : TamedField X)
    (γ : ℝ → E) (hγ : Continuous γ) (hγfiber : ∀ t, γ t ∈ X.fiber)
    (t : ℝ) : γ t ∈ V.orbit (γ 0) := by
  let A : Set ℝ := γ ⁻¹' V.orbit (γ 0)
  have hp : γ 0 ∈ X.fiber := hγfiber 0
  have hAS : A ⊆ (Set.univ : Set ℝ) := fun _ _ => Set.mem_univ _
  have hAclosed : IsClosed A := (V.isCompact_orbit hp).isClosed.preimage hγ
  have hAopen : ∀ s ∈ A, ∃ r > 0, (Set.univ : Set ℝ) ∩ Metric.ball s r ⊆ A := by
    intro s hs
    obtain ⟨r, hr, hrsub⟩ := V.orbit_isOpen_in_fiber hp hs
    have hopen : IsOpen (γ ⁻¹' Metric.ball (γ s) r) :=
      Metric.isOpen_ball.preimage hγ
    have hsmem : s ∈ γ ⁻¹' Metric.ball (γ s) r := Metric.mem_ball_self hr
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen s hsmem
    refine ⟨ε, hε, ?_⟩
    rintro u ⟨-, hus⟩
    exact hrsub ⟨hγfiber u, hεsub hus⟩
  have hA0 : A.Nonempty := ⟨0, V.mem_orbit_self (γ 0)⟩
  have hAll : (Set.univ : Set ℝ) ⊆ A :=
    subset_of_relOpen_closed isPreconnected_univ hAS hAclosed hAopen hA0
  exact hAll (Set.mem_univ t)


-- @@ L59-59 verbatim
end TamedField


-- @@ L61-72 verbatim
/-- A once-around parametrization of the flow orbit through `p`.  The last
field is the useful closed-interval formulation of simple closedness: the only
possible repetition is the pair of endpoints. -/
structure SimpleClosedOrbitParam (X : FramedLevelSet n) (V : TamedField X) where
  p : E
  hp : p ∈ X.fiber
  curve : C(I, E)
  curve_zero : curve 0 = p
  curve_closed : curve 0 = curve 1
  curve_mem_orbit : ∀ u, curve u ∈ V.orbit p
  curve_eq_cases : ∀ {u v : I}, curve u = curve v →
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)


-- @@ L74-74 verbatim
namespace SimpleClosedOrbitParam


-- @@ L76-76 verbatim
variable {X : FramedLevelSet n} {V : TamedField X}


-- @@ L78-81 verbatim
/-- The explicit curve, regarded as a path in its intrinsic flow orbit. -/
def orbitPath (P : SimpleClosedOrbitParam X V) : C(I, V.orbit P.p) where
  toFun u := ⟨P.curve u, P.curve_mem_orbit u⟩
  continuous_toFun := Continuous.subtype_mk P.curve.continuous _


-- @@ L83-88 verbatim
/-- Phase of the explicit curve in the intrinsic period circle. -/
def phase (P : SimpleClosedOrbitParam X V) :
    C(I, AddCircle (V.fundamentalPeriod P.hp)) where
  toFun u := (V.orbitCircleHomeomorph P.hp).symm (P.orbitPath u)
  continuous_toFun :=
    (V.orbitCircleHomeomorph P.hp).symm.continuous.comp P.orbitPath.continuous


-- @@ L90-92 verbatim
theorem orbitCircleHomeomorph_phase (P : SimpleClosedOrbitParam X V) (u : I) :
    V.orbitCircleHomeomorph P.hp (P.phase u) = P.orbitPath u := by
  exact (V.orbitCircleHomeomorph P.hp).apply_symm_apply _


-- @@ L94-99 verbatim
@[simp] theorem phase_zero (P : SimpleClosedOrbitParam X V) : P.phase 0 = 0 := by
  apply (V.orbitCircleHomeomorph P.hp).injective
  rw [P.orbitCircleHomeomorph_phase]
  apply Subtype.ext
  change P.curve 0 = V.flow P.p 0
  rw [P.curve_zero, V.flow_zero]


-- @@ L101-106 verbatim
theorem phase_closed (P : SimpleClosedOrbitParam X V) :
    P.phase 0 = P.phase 1 := by
  apply (V.orbitCircleHomeomorph P.hp).injective
  rw [P.orbitCircleHomeomorph_phase, P.orbitCircleHomeomorph_phase]
  apply Subtype.ext
  exact P.curve_closed


-- @@ L108-114 verbatim
theorem phase_eq_cases (P : SimpleClosedOrbitParam X V) {u v : I}
    (huv : P.phase u = P.phase v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  apply P.curve_eq_cases
  have h := congrArg (V.orbitCircleHomeomorph P.hp) huv
  rw [P.orbitCircleHomeomorph_phase, P.orbitCircleHomeomorph_phase] at h
  exact congrArg Subtype.val h


-- @@ L116-116 verbatim
/-! ## Lift of the phase -/


-- @@ L118-122 verbatim
/-- The intrinsic-time lift of the phase, starting at zero. -/
def phaseLift (P : SimpleClosedOrbitParam X V) : C(I, ℝ) := by
  let T := V.fundamentalPeriod P.hp
  letI : Fact (0 < T) := ⟨V.fundamentalPeriod_pos P.hp⟩
  exact (AddCircle.isCoveringMap_coe T).liftPath P.phase 0 P.phase_zero


-- @@ L124-127 verbatim
@[simp] theorem phaseLift_zero (P : SimpleClosedOrbitParam X V) :
    P.phaseLift 0 = 0 := by
  unfold phaseLift
  apply IsCoveringMap.liftPath_zero


-- @@ L129-135 verbatim
theorem phaseLift_coe (P : SimpleClosedOrbitParam X V) (u : I) :
    ((P.phaseLift u : ℝ) : AddCircle (V.fundamentalPeriod P.hp)) = P.phase u := by
  let T := V.fundamentalPeriod P.hp
  letI : Fact (0 < T) := ⟨V.fundamentalPeriod_pos P.hp⟩
  have h := congrFun
    ((AddCircle.isCoveringMap_coe T).liftPath_lifts P.phase 0 P.phase_zero) u
  simpa [phaseLift, T] using h


-- @@ L137-146 verbatim
theorem phaseLift_endpoint_zsmul (P : SimpleClosedOrbitParam X V) :
    ∃ z : ℤ, P.phaseLift 1 = z • V.fundamentalPeriod P.hp := by
  let T := V.fundamentalPeriod P.hp
  have hcoe : ((P.phaseLift 1 : ℝ) : AddCircle T) = 0 := by
    calc
      ((P.phaseLift 1 : ℝ) : AddCircle T) = P.phase 1 := P.phaseLift_coe 1
      _ = P.phase 0 := P.phase_closed.symm
      _ = 0 := P.phase_zero
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff T).mp hcoe
  exact ⟨z, hz.symm⟩


-- @@ L148-222 verbatim
theorem phaseLift_one_ne_zero (P : SimpleClosedOrbitParam X V) :
    P.phaseLift 1 ≠ 0 := by
  let ψ := P.phaseLift
  let φ := P.phase
  let c : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hc0 : (0 : I) < c := by change (0 : ℝ) < 1 / 2; norm_num
  have hc1 : c < (1 : I) := by change (1 / 2 : ℝ) < 1; norm_num
  have hφc : φ c ≠ φ 0 := by
    intro h
    rcases P.phase_eq_cases h with hEq | hEnds | hEnds
    · exact (ne_of_gt hc0) hEq
    · exact (zero_ne_one : (0 : I) ≠ 1) hEnds.2
    · exact (ne_of_lt hc1) hEnds.1
  have hψc : ψ c ≠ 0 := by
    intro hzero
    apply hφc
    calc
      φ c = ((ψ c : ℝ) : AddCircle (V.fundamentalPeriod P.hp)) :=
        (P.phaseLift_coe c).symm
      _ = ((ψ 0 : ℝ) : AddCircle (V.fundamentalPeriod P.hp)) := by
        rw [hzero, P.phaseLift_zero]
      _ = φ 0 := P.phaseLift_coe 0
  intro hψ1
  have hcont : Continuous ψ := P.phaseLift.continuous
  rcases lt_or_gt_of_ne hψc with hneg | hpos
  · let z : ℝ := ψ c / 2
    have hzL : z ∈ Icc (ψ c) (ψ 0) := by
      rw [P.phaseLift_zero]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨u, huI, hu⟩ := intermediate_value_Icc' (le_of_lt hc0)
      hcont.continuousOn hzL
    have hzR : z ∈ Icc (ψ c) (ψ 1) := by
      rw [hψ1]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨v, hvI, hv⟩ := intermediate_value_Icc (le_of_lt hc1)
      hcont.continuousOn hzR
    have hphase : φ u = φ v := by
      rw [← P.phaseLift_coe u, ← P.phaseLift_coe v, hu, hv]
    rcases P.phase_eq_cases hphase with huv | hends | hends
    · subst v
      have : u = c := le_antisymm huI.2 hvI.1
      subst u
      dsimp [z] at hu
      linarith
    · rw [hends.1, P.phaseLift_zero] at hu
      dsimp [z] at hu
      linarith
    · rw [hends.1, hψ1] at hu
      dsimp [z] at hu
      linarith
  · let z : ℝ := ψ c / 2
    have hzL : z ∈ Icc (ψ 0) (ψ c) := by
      rw [P.phaseLift_zero]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨u, huI, hu⟩ := intermediate_value_Icc (le_of_lt hc0)
      hcont.continuousOn hzL
    have hzR : z ∈ Icc (ψ 1) (ψ c) := by
      rw [hψ1]
      constructor <;> dsimp [z] <;> linarith
    obtain ⟨v, hvI, hv⟩ := intermediate_value_Icc' (le_of_lt hc1)
      hcont.continuousOn hzR
    have hphase : φ u = φ v := by
      rw [← P.phaseLift_coe u, ← P.phaseLift_coe v, hu, hv]
    rcases P.phase_eq_cases hphase with huv | hends | hends
    · subst v
      have : u = c := le_antisymm huI.2 hvI.1
      subst u
      dsimp [z] at hu
      linarith
    · rw [hends.1, P.phaseLift_zero] at hu
      dsimp [z] at hu
      linarith
    · rw [hends.1, hψ1] at hu
      dsimp [z] at hu
      linarith


-- @@ L224-236 verbatim
theorem phaseLift_injective (P : SimpleClosedOrbitParam X V) :
    Function.Injective P.phaseLift := by
  intro u v huv
  have hphase : P.phase u = P.phase v := by
    rw [← P.phaseLift_coe u, ← P.phaseLift_coe v, huv]
  rcases P.phase_eq_cases hphase with hEq | hEnds | hEnds
  · exact hEq
  · exfalso
    apply P.phaseLift_one_ne_zero
    rw [← hEnds.2, ← huv, hEnds.1, P.phaseLift_zero]
  · exfalso
    apply P.phaseLift_one_ne_zero
    rw [← hEnds.1, huv, hEnds.2, P.phaseLift_zero]


-- @@ L238-305 verbatim
/-- A simple closed orbit parametrization traverses exactly one period, with
one of the two possible orientations. -/
theorem phaseLift_one_eq_period_or_neg (P : SimpleClosedOrbitParam X V) :
    P.phaseLift 1 = V.fundamentalPeriod P.hp ∨
      P.phaseLift 1 = -V.fundamentalPeriod P.hp := by
  let ψ := P.phaseLift
  let φ := P.phase
  let T := V.fundamentalPeriod P.hp
  have hT : 0 < T := V.fundamentalPeriod_pos P.hp
  obtain ⟨z, hz⟩ := P.phaseLift_endpoint_zsmul
  have hzR : ψ 1 = (z : ℝ) * T := by
    simpa [ψ, T, zsmul_eq_mul] using hz
  have hmonoanti := P.phaseLift.continuous.strictMono_of_inj_boundedOrder'
    P.phaseLift_injective
  rcases hmonoanti with hmono | hanti
  · have hψ1pos : 0 < ψ 1 := by
      have h := hmono (show (0 : I) < 1 by norm_num)
      rwa [P.phaseLift_zero] at h
    have hzposR : (0 : ℝ) < (z : ℝ) := by nlinarith
    have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
    have hzle : z ≤ 1 := by
      by_contra hznot
      have hzge : (2 : ℤ) ≤ z := by omega
      have hzgeR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzge
      have hmem : T ∈ Icc (ψ 0) (ψ 1) := by
        rw [P.phaseLift_zero, hzR]
        constructor <;> nlinarith
      obtain ⟨u, hu⟩ := intermediate_value_univ (0 : I) (1 : I)
        P.phaseLift.continuous hmem
      have hphase : φ u = φ 0 := by
        rw [← P.phaseLift_coe u, ← P.phaseLift_coe 0, hu, P.phaseLift_zero]
        exact AddCircle.coe_period T
      rcases P.phase_eq_cases hphase with hu0 | hbad | hu1
      · rw [hu0, P.phaseLift_zero] at hu
        linarith
      · exact (zero_ne_one : (0 : I) ≠ 1) hbad.2
      · rw [hu1.1, hzR] at hu
        nlinarith
    have hzone : z = 1 := by omega
    left
    simpa [T, hzone] using hzR
  · have hψ1neg : ψ 1 < 0 := by
      have h := hanti (show (0 : I) < 1 by norm_num)
      rwa [P.phaseLift_zero] at h
    have hznegR : (z : ℝ) < 0 := by nlinarith
    have hzneg : z < (0 : ℤ) := by exact_mod_cast hznegR
    have hzge : (-1 : ℤ) ≤ z := by
      by_contra hznot
      have hzle : z ≤ (-2 : ℤ) := by omega
      have hzleR : (z : ℝ) ≤ -2 := by exact_mod_cast hzle
      have hmem : -T ∈ Icc (ψ 1) (ψ 0) := by
        rw [P.phaseLift_zero, hzR]
        constructor <;> nlinarith
      obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) (0 : I)
        P.phaseLift.continuous hmem
      have hphase : φ u = φ 0 := by
        rw [← P.phaseLift_coe u, ← P.phaseLift_coe 0, hu, P.phaseLift_zero]
        rw [AddCircle.coe_neg, AddCircle.coe_period, neg_zero]
        rfl
      rcases P.phase_eq_cases hphase with hu0 | hbad | hu1
      · rw [hu0, P.phaseLift_zero] at hu
        linarith
      · exact (zero_ne_one : (0 : I) ≠ 1) hbad.2
      · rw [hu1.1, hzR] at hu
        nlinarith
    have hzmone : z = -1 := by omega
    right
    simpa [T, hzmone] using hzR


-- @@ L307-307 verbatim
/-! ## Frame comparison -/


-- @@ L309-313 verbatim
/-- A harmless continuous extension of the unit-interval curve to the real
line.  `frameLoop` is historically stated for real-parameter curves, although
its value at a time depends only on the point at that time. -/
def realCurve (P : SimpleClosedOrbitParam X V) : ℝ → E :=
  fun t => P.curve (Set.projIcc (0 : ℝ) 1 zero_le_one t)


-- @@ L315-317 verbatim
theorem continuous_realCurve (P : SimpleClosedOrbitParam X V) :
    Continuous P.realCurve :=
  P.curve.continuous.comp continuous_projIcc


-- @@ L319-321 verbatim
@[simp] theorem realCurve_coe (P : SimpleClosedOrbitParam X V) (u : I) :
    P.realCurve (u : ℝ) = P.curve u := by
  rw [realCurve, Set.projIcc_val]


-- @@ L323-325 verbatim
theorem realCurve_mem_fiber (P : SimpleClosedOrbitParam X V) (t : ℝ) :
    P.realCurve t ∈ X.fiber :=
  V.orbit_subset_fiber P.hp (P.curve_mem_orbit _)


-- @@ L327-334 verbatim
/-- The frame read directly along the explicit curve. -/
def paramFrameLoop (P : SimpleClosedOrbitParam X V) : C(I, SOGroup (n + 1)) where
  toFun u := ⟨frameLoop X P.realCurve (u : ℝ),
    frameLoop_mem_specialOrthogonalGroup X P.realCurve_mem_fiber (u : ℝ)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_frameLoop X P.continuous_realCurve
      P.realCurve_mem_fiber).comp continuous_subtype_val


-- @@ L336-342 verbatim
theorem paramFrameLoop_closed (P : SimpleClosedOrbitParam X V) :
    P.paramFrameLoop 0 = P.paramFrameLoop 1 := by
  apply Subtype.ext
  change frameLoop X P.realCurve ((0 : I) : ℝ) =
    frameLoop X P.realCurve ((1 : I) : ℝ)
  unfold frameLoop
  rw [P.realCurve_coe, P.realCurve_coe, P.curve_closed]


-- @@ L344-351 verbatim
/-- The explicit curve is the intrinsic flow evaluated at its lifted phase. -/
theorem curve_eq_flow_phaseLift (P : SimpleClosedOrbitParam X V) (u : I) :
    P.curve u = V.flow P.p (P.phaseLift u) := by
  have h := P.orbitCircleHomeomorph_phase u
  rw [← P.phaseLift_coe u] at h
  have hv := congrArg Subtype.val h
  rw [V.orbitCircleHomeomorph_coe] at hv
  simpa [orbitPath] using hv.symm


-- @@ L353-361 verbatim
/-- The same frame loop, written in lifted intrinsic time. -/
def liftedFrameLoop (P : SimpleClosedOrbitParam X V) :
    C(I, SOGroup (n + 1)) where
  toFun u := ⟨frameLoop X (V.flow P.p) (P.phaseLift u),
    frameLoop_mem_specialOrthogonalGroup X (V.flow_mem_fiber P.hp) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_frameLoop X (V.continuous_flow P.p)
      (V.flow_mem_fiber P.hp)).comp P.phaseLift.continuous


-- @@ L363-371 verbatim
theorem paramFrameLoop_eq_lifted (P : SimpleClosedOrbitParam X V) :
    P.paramFrameLoop = P.liftedFrameLoop := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop X P.realCurve (u : ℝ) =
    frameLoop X (V.flow P.p) (P.phaseLift u)
  unfold frameLoop
  rw [P.realCurve_coe, P.curve_eq_flow_phaseLift u]


-- @@ L373-383 verbatim
/-- The intrinsic frame loop run with orientation factor `ε`. -/
def orientedFrameLoop (P : SimpleClosedOrbitParam X V) (ε : ℝ) :
    C(I, SOGroup (n + 1)) where
  toFun u := ⟨frameLoop X (V.flow P.p)
      (ε * (u : ℝ) * V.fundamentalPeriod P.hp),
    frameLoop_mem_specialOrthogonalGroup X (V.flow_mem_fiber P.hp) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_frameLoop X (V.continuous_flow P.p)
      (V.flow_mem_fiber P.hp)).comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)


-- @@ L385-415 verbatim
/-- Straight-line interpolation between the lifted phase and a chosen
orientation of the intrinsic period. -/
def frameReparamHomotopy (P : SimpleClosedOrbitParam X V) (ε : ℝ) :
    ContinuousMap.Homotopy P.liftedFrameLoop (P.orientedFrameLoop ε) where
  toFun q := ⟨frameLoop X (V.flow P.p)
      ((1 - (q.1 : ℝ)) * P.phaseLift q.2 +
        (q.1 : ℝ) * (ε * (q.2 : ℝ) * V.fundamentalPeriod P.hp)),
    frameLoop_mem_specialOrthogonalGroup X (V.flow_mem_fiber P.hp) _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (continuous_frameLoop X (V.continuous_flow P.p)
      (V.flow_mem_fiber P.hp)).comp
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst) |>.mul
      (P.phaseLift.continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
          continuous_const))
  map_zero_left := fun u => by
    apply Subtype.ext
    change frameLoop _ _
        ((1 - (((0 : I) : ℝ))) * P.phaseLift u +
          (((0 : I) : ℝ) * (ε * (u : ℝ) * _))) = _
    congr 2
    norm_num
  map_one_left := fun u => by
    apply Subtype.ext
    change frameLoop _ _
        ((1 - (((1 : I) : ℝ))) * P.phaseLift u +
          (((1 : I) : ℝ) * (ε * (u : ℝ) * _))) = _
    congr 2
    norm_num


-- @@ L417-424 verbatim
theorem orientedFrameLoop_one (P : SimpleClosedOrbitParam X V) :
    P.orientedFrameLoop 1 = V.fundamentalFrameLoop P.hp := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop _ _ (1 * (u : ℝ) * _) = frameLoop _ _ ((u : ℝ) * _)
  congr 2
  ring


-- @@ L426-438 verbatim
theorem orientedFrameLoop_neg_one (P : SimpleClosedOrbitParam X V) :
    P.orientedFrameLoop (-1) = reverseLoop (V.fundamentalFrameLoop P.hp) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  let F := fun t : ℝ => frameLoop X (V.flow P.p) t
  have hper : Function.Periodic F (V.fundamentalPeriod P.hp) :=
    frameLoop_periodic _ (V.fundamentalPeriod_periodic P.hp)
  change F ((-1 : ℝ) * (u : ℝ) * V.fundamentalPeriod P.hp) =
    F ((unitInterval.symm u : ℝ) * V.fundamentalPeriod P.hp)
  have h := hper ((-1 : ℝ) * (u : ℝ) * V.fundamentalPeriod P.hp)
  rw [show (unitInterval.symm u : ℝ) = 1 - (u : ℝ) by rfl]
  convert h.symm using 1 <;> ring


-- @@ L440-443 verbatim
theorem liftedFrameLoop_closed (P : SimpleClosedOrbitParam X V) :
    P.liftedFrameLoop 0 = P.liftedFrameLoop 1 := by
  rw [← P.paramFrameLoop_eq_lifted]
  exact P.paramFrameLoop_closed


-- @@ L445-462 verbatim
theorem frameReparamHomotopy_closed (P : SimpleClosedOrbitParam X V) (ε : ℝ)
    (hend : P.phaseLift 1 = ε * V.fundamentalPeriod P.hp)
    (hperiod : Function.Periodic (fun t : ℝ => frameLoop X (V.flow P.p) t)
      (ε * V.fundamentalPeriod P.hp)) (s : I) :
    P.frameReparamHomotopy ε (s, 0) = P.frameReparamHomotopy ε (s, 1) := by
  apply Subtype.ext
  let T := V.fundamentalPeriod P.hp
  let F := fun t : ℝ => frameLoop X (V.flow P.p) t
  change F ((1 - (s : ℝ)) * P.phaseLift 0 +
      (s : ℝ) * (ε * (((0 : I) : ℝ)) * T)) =
    F ((1 - (s : ℝ)) * P.phaseLift 1 +
      (s : ℝ) * (ε * (((1 : I) : ℝ)) * T))
  rw [P.phaseLift_zero, hend]
  norm_num
  change F 0 = F ((1 - (s : ℝ)) * (ε * T) + (s : ℝ) * (ε * T))
  rw [show (1 - (s : ℝ)) * (ε * T) + (s : ℝ) * (ε * T) =
    ε * T by ring]
  simpa [F, T] using (hperiod 0).symm


-- @@ L464-472 verbatim
theorem orientedFrameLoop_closed (P : SimpleClosedOrbitParam X V) (ε : ℝ)
    (hperiod : Function.Periodic (fun t : ℝ => frameLoop X (V.flow P.p) t)
      (ε * V.fundamentalPeriod P.hp)) :
    P.orientedFrameLoop ε 0 = P.orientedFrameLoop ε 1 := by
  apply Subtype.ext
  change frameLoop _ _ (ε * (((0 : I) : ℝ)) * _) =
    frameLoop _ _ (ε * (((1 : I) : ℝ)) * _)
  norm_num
  convert (hperiod 0).symm using 1 <;> ring


-- @@ L474-523 verbatim
/-- The frame loop along any simple closed orbit parametrization has the
intrinsic fundamental frame class.  Reversing orientation is invisible over
`ZMod 2`. -/
theorem paramFrameClass_eq_fundamental (P : SimpleClosedOrbitParam X V) :
    loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
      V.fundamentalFrameClass P.hp := by
  let T := V.fundamentalPeriod P.hp
  let F := fun t : ℝ => frameLoop X (V.flow P.p) t
  have hper : Function.Periodic F T :=
    frameLoop_periodic _ (V.fundamentalPeriod_periodic P.hp)
  have hloop := P.paramFrameLoop_eq_lifted
  rcases P.phaseLift_one_eq_period_or_neg with hplus | hminus
  · have hend : P.phaseLift 1 = (1 : ℝ) * V.fundamentalPeriod P.hp := by
      simpa using hplus
    have hclosed := P.frameReparamHomotopy_closed 1 hend
      (by simpa [F, T] using hper)
    have horientedClosed := P.orientedFrameLoop_closed 1
      (by simpa [F, T] using hper)
    calc
      loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
          loopClassZ2 P.liftedFrameLoop P.liftedFrameLoop_closed :=
        loopClassZ2_congr_fun P.paramFrameLoop_closed P.liftedFrameLoop_closed hloop
      _ = loopClassZ2 (P.orientedFrameLoop 1) horientedClosed :=
        loopClassZ2_congr P.liftedFrameLoop_closed horientedClosed
          (P.frameReparamHomotopy 1) hclosed
      _ = V.fundamentalFrameClass P.hp := by
        unfold TamedField.fundamentalFrameClass
        exact loopClassZ2_congr_fun horientedClosed
          (V.fundamentalFrameLoop_closed P.hp) P.orientedFrameLoop_one
  · have hend : P.phaseLift 1 = (-1 : ℝ) * V.fundamentalPeriod P.hp := by
      simpa using hminus
    have hclosed := P.frameReparamHomotopy_closed (-1) hend
      (by simpa [F, T] using hper.neg)
    have horientedClosed := P.orientedFrameLoop_closed (-1)
      (by simpa [F, T] using hper.neg)
    calc
      loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
          loopClassZ2 P.liftedFrameLoop P.liftedFrameLoop_closed :=
        loopClassZ2_congr_fun P.paramFrameLoop_closed P.liftedFrameLoop_closed hloop
      _ = loopClassZ2 (P.orientedFrameLoop (-1)) horientedClosed :=
        loopClassZ2_congr P.liftedFrameLoop_closed horientedClosed
          (P.frameReparamHomotopy (-1)) hclosed
      _ = loopClassZ2 (reverseLoop (V.fundamentalFrameLoop P.hp))
          (reverseLoop_closed (V.fundamentalFrameLoop_closed P.hp)) := by
        exact loopClassZ2_congr_fun horientedClosed
          (reverseLoop_closed (V.fundamentalFrameLoop_closed P.hp))
          P.orientedFrameLoop_neg_one
      _ = V.fundamentalFrameClass P.hp := by
        exact loopClassZ2_reverse (V.fundamentalFrameLoop P.hp)
          (V.fundamentalFrameLoop_closed P.hp)


-- @@ L525-525 verbatim
end SimpleClosedOrbitParam


-- @@ L527-527 verbatim
end Submission
