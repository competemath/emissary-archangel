import Mathlib
import Submission.OrbitUnknottingFourierEmbeddingTrack


-- @@ L4-13 verbatim
/-!
# Finite uniform C¹ subdivision of a Fourier circle track

The real lift of an embedded-circle track is jointly smooth in time and
phase.  Its phase derivative is therefore jointly continuous as well.  On
the compact time-phase square, the pair consisting of the lift and its phase
derivative is uniformly continuous.  Periodicity reduces an arbitrary real
phase to its fractional part, and an Archimedean choice of mesh then gives a
finite equal subdivision whose adjacent slices are uniformly C¹-close.
-/


-- @@ L15-15 verbatim
set_option autoImplicit false

-- @@ L16-16 verbatim
set_option maxHeartbeats 300000


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open Set Function

-- @@ L21-21 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L23-23 verbatim
namespace Submission

-- @@ L24-24 verbatim
namespace TamedField

-- @@ L25-25 verbatim
namespace FourierFiniteC1Subdivision


-- @@ L27-27 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L29-29 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L31-31 verbatim
variable {V} (h2 : 2 ≤ n) (O : V.OrbitIndex)


-- @@ L33-33 verbatim
open FourierEmbeddingTrack


-- @@ L35-35 verbatim
namespace EmbeddedCircleTrack


-- @@ L37-37 verbatim
variable (T : EmbeddedCircleTrack (V := V) h2 O)


-- @@ L39-41 verbatim
/-- The derivative in the real phase direction of the lifted circle track. -/
def phaseDeriv (s u : ℝ) : E :=
  deriv (T.lift s) u


-- @@ L43-44 verbatim
local notation "D" =>
  phaseDeriv (V := V) (h2 := h2) (O := O) T


-- @@ L46-58 verbatim
/-- Joint smoothness of the lift implies joint smoothness, hence continuity,
of its phase derivative. -/
theorem contDiff_phaseDeriv :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => D q.1 q.2) := by
  let f : (ℝ × ℝ) → ℝ → E := fun q u => T.lift q.1 u
  have hf : ContDiff ℝ ∞ (Function.uncurry f) := by
    exact T.smooth_lift.comp
      ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hd := ContDiff.fderiv_apply (m := ∞) (n := ∞) hf
    (g := fun q : ℝ × ℝ => q.2)
    (k := fun _ : ℝ × ℝ => (1 : ℝ))
    contDiff_snd contDiff_const (by simp)
  simpa [f, phaseDeriv, fderiv_apply_one_eq_deriv] using hd


-- @@ L60-62 verbatim
theorem continuous_phaseDeriv :
    Continuous (fun q : ℝ × ℝ => D q.1 q.2) :=
  (contDiff_phaseDeriv (V := V) (h2 := h2) (O := O) T).continuous


-- @@ L64-73 verbatim
/-- Differentiating the period-one identity shows that the phase derivative
is itself period one. -/
theorem periodic_phaseDeriv (s : ℝ) :
    Function.Periodic (D s) 1 := by
  have hfun : (fun u : ℝ => T.lift s (u + 1)) = T.lift s := by
    funext u
    exact T.periodic_lift s u
  intro u
  have h := congrArg (fun f : ℝ → E => deriv f u) hfun
  simpa only [phaseDeriv, deriv_comp_add_const] using h


-- @@ L75-84 verbatim
/-- Reduce the lift at an arbitrary real phase to the compact fundamental
interval via its fractional part. -/
theorem lift_eq_fract (s u : ℝ) :
    T.lift s u = T.lift s (Int.fract u) := by
  have hperiod := (T.periodic_lift s).zsmul ⌊u⌋
  have h := hperiod (Int.fract u)
  have hpoint : Int.fract u + ⌊u⌋ • (1 : ℝ) = u := by
    simpa [add_comm] using Int.fract_add_floor u
  rw [hpoint] at h
  exact h


-- @@ L86-95 verbatim
/-- The same compact-phase reduction for the phase derivative. -/
theorem phaseDeriv_eq_fract (s u : ℝ) :
    D s u = D s (Int.fract u) := by
  have hperiod :=
    (periodic_phaseDeriv (V := V) (h2 := h2) (O := O) T s).zsmul ⌊u⌋
  have h := hperiod (Int.fract u)
  have hpoint : Int.fract u + ⌊u⌋ • (1 : ℝ) = u := by
    simpa [add_comm] using Int.fract_add_floor u
  rw [hpoint] at h
  exact h


-- @@ L97-99 verbatim
/-- The C¹ jet used for one simultaneous uniform-continuity estimate. -/
def c1Jet (q : ℝ × ℝ) : E × E :=
  (T.lift q.1 q.2, D q.1 q.2)


-- @@ L101-104 verbatim
theorem continuous_c1Jet :
    Continuous (c1Jet (V := V) (h2 := h2) (O := O) (T := T)) := by
  exact T.smooth_lift.continuous.prodMk
    (continuous_phaseDeriv (V := V) (h2 := h2) (O := O) T)


-- @@ L106-179 verbatim
/-- For every positive tolerance, a finite equal time subdivision has
uniformly C¹-close adjacent lifted circles.  The estimates hold for every
real phase, not merely phases in the chosen fundamental interval. -/
theorem exists_uniformC1_equisubdivision
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧
      ∀ k : ℕ, k < m → ∀ u : ℝ,
        ‖T.lift ((k : ℝ) / (m : ℝ)) u -
            T.lift (((k + 1 : ℕ) : ℝ) / (m : ℝ)) u‖ < ε ∧
        ‖deriv (T.lift ((k : ℝ) / (m : ℝ))) u -
            deriv (T.lift (((k + 1 : ℕ) : ℝ) / (m : ℝ))) u‖ < ε := by
  let K : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have huniform : UniformContinuousOn
      (c1Jet (V := V) (h2 := h2) (O := O) (T := T)) K :=
    hK.uniformContinuousOn_of_continuous
      (continuous_c1Jet (V := V) (h2 := h2) (O := O) T).continuousOn
  obtain ⟨δ, hδ, hnear⟩ :=
    Metric.uniformContinuousOn_iff.mp huniform ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  refine ⟨j + 1, Nat.succ_pos j, ?_⟩
  intro k hk u
  let v : ℝ := Int.fract u
  have hv : v ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  have hmpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hk_le : k ≤ j + 1 := Nat.le_of_lt hk
  have hk_succ_le : k + 1 ≤ j + 1 := by omega
  have htime₀ : (k : ℝ) / ((j + 1 : ℕ) : ℝ) ∈
      Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hmpos).2 (by exact_mod_cast hk_le)
  have htime₁ : ((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ∈
      Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hmpos).2 (by exact_mod_cast hk_succ_le)
  have hstep :
      dist ((k : ℝ) / ((j + 1 : ℕ) : ℝ))
          (((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)) =
        1 / ((j + 1 : ℕ) : ℝ) := by
    rw [Real.dist_eq]
    have hle :
        (k : ℝ) / ((j + 1 : ℕ) : ℝ) ≤
          ((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.le_succ k) hmpos.le
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    field_simp
    norm_num
  have hdist :
      dist
        ((k : ℝ) / ((j + 1 : ℕ) : ℝ), v)
        (((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ), v) < δ := by
    rw [dist_prod_same_right, hstep]
    simpa only [Nat.cast_add, Nat.cast_one] using hj
  have hout := hnear
    ((k : ℝ) / ((j + 1 : ℕ) : ℝ), v) ⟨htime₀, hv⟩
    (((k + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ), v) ⟨htime₁, hv⟩
    hdist
  rw [Prod.dist_eq, max_lt_iff] at hout
  constructor
  · rw [lift_eq_fract (V := V) (h2 := h2) (O := O) T _ u,
      lift_eq_fract (V := V) (h2 := h2) (O := O) T _ u]
    simpa only [c1Jet, dist_eq_norm, Prod.fst] using hout.1
  · change
      ‖D ((k : ℝ) / ((j + 1 : ℕ) : ℝ)) u -
        D (((k + 1 : ℕ) : ℝ) /
          ((j + 1 : ℕ) : ℝ)) u‖ < ε
    rw [phaseDeriv_eq_fract (V := V) (h2 := h2) (O := O) T _ u,
      phaseDeriv_eq_fract (V := V) (h2 := h2) (O := O) T _ u]
    simpa only [c1Jet, dist_eq_norm, Prod.snd] using hout.2


-- @@ L181-181 verbatim
end EmbeddedCircleTrack


-- @@ L183-183 verbatim
end FourierFiniteC1Subdivision

-- @@ L184-184 verbatim
end TamedField

-- @@ L185-185 verbatim
end Submission
