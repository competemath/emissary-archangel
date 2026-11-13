import Mathlib
import Submission.SmoothApprox
import Submission.TubeCollapse


-- @@ L5-18 verbatim
/-!
# An exact smooth approximation for the explicit tube collapse

The general bridge construction first collars a cubical representative and
then replaces it by an abstract smooth approximation.  For the explicit tube
collapse no loss of geometric information is necessary: the affine map
`v ↦ 12v - 6` already realizes the collared representative.  Outside the
middle cube both sides are the south pole, while on the middle cube the two
affine formulae agree exactly.

This file packages that observation as an actual `Approximation`.  It is the
entry point for computing the ledger of a genuine `BridgeData`, rather than a
standalone local tube contract.
-/


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Topology.Homotopy

-- @@ L23-23 verbatim
open scoped Topology unitInterval ContDiff


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
variable {m : ℕ}


-- @@ L29-29 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))


-- @@ L31-35 verbatim
/-- The change of basepoint proof does not alter the represented stable class. -/
theorem tubeThomStableGenLoop_class (k : ℕ) :
    (⟦tubeThomStableGenLoop (m := m) k⟧ : StableSpherePi (m + 2)) =
      tubeThomStableClass k := by
  rfl


-- @@ L37-39 verbatim
/-- The globally smooth affine source map implementing the collar expansion. -/
def tubeApproxAmbient (v : Fin (m + 3) → ℝ) : E :=
  WithLp.toLp 2 fun i => 12 * v i - 6


-- @@ L41-44 verbatim
@[simp] theorem tubeApproxAmbient_apply (v : Fin (m + 3) → ℝ)
    (i : Fin (m + 3)) :
    tubeApproxAmbient (m := m) v i = 12 * v i - 6 :=
  rfl


-- @@ L46-53 verbatim
theorem contDiff_tubeApproxAmbient :
    ContDiff ℝ ∞ (tubeApproxAmbient (m := m)) := by
  have h : tubeApproxAmbient (m := m) = fun v =>
      (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm
        (fun i => 12 * v i - 6) := rfl
  rw [h]
  exact (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm.contDiff.comp <| by
    fun_prop


-- @@ L55-95 verbatim
/-- If one source coordinate lies outside the middle cube, its affine image is
already far outside the active tube. -/
theorem tubeApproxAmbient_off_outer_of_outer_coord
    {v : Fin (m + 3) → ℝ} {j : Fin (m + 3)}
    (hj : v j ≤ 1 / 4 ∨ 3 / 4 ≤ v j) :
    tubeApproxAmbient (m := m) v ∉ tubeRegion (1 / 3) := by
  let x : E := tubeApproxAmbient (m := m) v
  have habs : 3 ≤ |x j| := by
    change 3 ≤ |12 * v j - 6|
    rcases hj with hj | hj
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  have hsq : 9 ≤ x j ^ 2 := by
    nlinarith [sq_abs (x j)]
  have hd : 1 / 9 ≤ tubeDistSq x := by
    by_cases hj0 : j = 0
    · subst j
      have hrsq := rad_sq x
      have hr0 := rad_nonneg x
      have hrad : 3 ≤ rad x := by
        rw [radSq] at hrsq
        nlinarith [sq_nonneg (x 1)]
      have hdist := sq_rad_le_tubeDistSq x
      nlinarith [sq_nonneg (rad x - 1)]
    · by_cases hj1 : j = 1
      · subst j
        have hrsq := rad_sq x
        have hr0 := rad_nonneg x
        have hrad : 3 ≤ rad x := by
          rw [radSq] at hrsq
          nlinarith [sq_nonneg (x 0)]
        have hdist := sq_rad_le_tubeDistSq x
        nlinarith [sq_nonneg (rad x - 1)]
      · have hdist := coordSq_le_tubeDistSq_of_ne x hj0 hj1
        linarith
  intro hin
  change tubeDistSq x < (1 / 3 : ℝ) ^ 2 at hin
  norm_num at hin
  exact (not_lt_of_ge hd) hin


-- @@ L97-99 verbatim
/-- The explicit smooth raw map. -/
def tubeApproxRaw (k : ℕ) (v : Fin (m + 3) → ℝ) : E :=
  tubeThomVec k (tubeApproxAmbient v)


-- @@ L101-103 verbatim
theorem contDiff_tubeApproxRaw (k : ℕ) :
    ContDiff ℝ ∞ (tubeApproxRaw (m := m) k) :=
  (contDiff_tubeThomVec k).comp contDiff_tubeApproxAmbient


-- @@ L105-107 verbatim
theorem norm_tubeApproxRaw (k : ℕ) (v : Fin (m + 3) → ℝ) :
    ‖tubeApproxRaw (m := m) k v‖ = 1 :=
  norm_tubeThomVec k _


-- @@ L109-125 verbatim
/-- On the closed bridge collar the explicit raw map is exactly the canonical
south pole. -/
theorem tubeApproxRaw_eq_southPole_on_collar (k : ℕ)
    {v : Fin (m + 3) → ℝ}
    (hv : v ∈ closedAmbientCollar (Fin (m + 3))) :
    tubeApproxRaw (m := m) k v =
      ((southPole (m + 2) : UnitSphere E) : E) := by
  obtain ⟨j, hj⟩ := hv
  have hj' : v j ≤ 1 / 4 ∨ 3 / 4 ≤ v j := by
    rcases hj with hj | hj
    · exact Or.inl (hj.trans (by norm_num))
    · have h34 : (3 / 4 : ℝ) ≤ 4 / 5 := by norm_num
      exact Or.inr (h34.trans hj)
  rw [tubeApproxRaw,
    tubeThomVec_off_outer k (tubeApproxAmbient_off_outer_of_outer_coord hj')]
  show -eVert (m := m) = -eLast (m + 2)
  rw [eVert_eq_eLast]


-- @@ L127-146 verbatim
/-- On the middle cube, collaring followed by the original `6t-3` expansion is
the same affine map as `12v-6`. -/
theorem cubeToTubeAmbient_collarMap_cubeClamp_eq
    {v : Fin (m + 3) → ℝ}
    (hv : ∀ i, 1 / 4 < v i ∧ v i < 3 / 4) :
    cubeToTubeAmbient (m := m) (collarMap (cubeClamp v)) =
      tubeApproxAmbient v := by
  apply (EuclideanSpace.equiv (Fin (m + 3)) ℝ).injective
  funext i
  have h0 : 0 ≤ v i := by linarith [(hv i).1]
  have h1 : v i ≤ 1 := by linarith [(hv i).2]
  have hc : ((cubeClamp v i : I) : ℝ) = v i := by
    rw [cubeClamp, Set.coe_projIcc, min_eq_right h1, max_eq_right h0]
  have hs0 : 0 ≤ 2 * v i - 1 / 2 := by linarith [(hv i).1]
  have hs1 : 2 * v i - 1 / 2 ≤ 1 := by linarith [(hv i).2]
  change 6 * (((collarMap (cubeClamp v) i : I) : ℝ)) - 3 =
    12 * v i - 6
  rw [collarMap, Set.coe_projIcc, hc, min_eq_right hs1,
    max_eq_right hs0]
  ring


-- @@ L148-178 verbatim
/-- The affine raw map is not merely close to the clamped collared loop: it is
pointwise equal to it. -/
theorem tubeApproxRaw_eq_extended (k : ℕ) (v : Fin (m + 3) → ℝ) :
    tubeApproxRaw (m := m) k v =
      extended (tubeThomStableGenLoop (m := m) k) v := by
  by_cases hv : ∀ i, 1 / 4 < v i ∧ v i < 3 / 4
  · change tubeThomVec k (tubeApproxAmbient v) =
      tubeThomVec k (cubeToTubeAmbient (collarMap (cubeClamp v)))
    rw [cubeToTubeAmbient_collarMap_cubeClamp_eq hv]
  · obtain ⟨j, hj⟩ := Classical.not_forall.mp hv
    have hj' : v j ≤ 1 / 4 ∨ 3 / 4 ≤ v j := by
      by_cases hlo : v j ≤ 1 / 4
      · exact Or.inl hlo
      · by_cases hhi : 3 / 4 ≤ v j
        · exact Or.inr hhi
        · exact False.elim (hj ⟨lt_of_not_ge hlo, lt_of_not_ge hhi⟩)
    have hraw : tubeApproxRaw (m := m) k v =
        ((southPole (m + 2) : UnitSphere E) : E) := by
      rw [tubeApproxRaw,
        tubeThomVec_off_outer k (tubeApproxAmbient_off_outer_of_outer_coord hj')]
      show -eVert (m := m) = -eLast (m + 2)
      rw [eVert_eq_eLast]
    have hcollar : ∃ i, ((cubeClamp v i : I) : ℝ) ≤ 1 / 4 ∨
        3 / 4 ≤ ((cubeClamp v i : I) : ℝ) := by
      refine ⟨j, ?_⟩
      rcases hj' with hj' | hj'
      · exact Or.inl (cubeClamp_coe_le hj')
      · exact Or.inr (le_cubeClamp_coe hj')
    rw [hraw, extended]
    exact congrArg Subtype.val
      (collared_eq_basepoint (tubeThomStableGenLoop (m := m) k) hcollar).symm


-- @@ L180-205 verbatim
/-- The exact explicit `Approximation` used by the tube bridge. -/
def tubeApproximation (k : ℕ) :
    Approximation (tubeThomStableGenLoop (m := m) k) where
  raw := tubeApproxRaw k
  contDiff_raw := contDiff_tubeApproxRaw k
  raw_close := fun v => by
    rw [tubeApproxRaw_eq_extended]
    norm_num
  raw_eq_basepoint_on_collar := fun v hv =>
    tubeApproxRaw_eq_southPole_on_collar k hv
  representative := collared (tubeThomStableGenLoop k)
  representative_coe := by
    intro t
    have hext := extended_coords (tubeThomStableGenLoop (m := m) k) t
    have hraw := tubeApproxRaw_eq_extended (m := m) k
      (fun i => (t i : ℝ))
    calc
      ((collared (tubeThomStableGenLoop (m := m) k) t :
          UnitSphere E) : E) =
          tubeApproxRaw k (fun i => (t i : ℝ)) := by
            exact hext.symm.trans hraw.symm
      _ = ‖tubeApproxRaw k (fun i => (t i : ℝ))‖⁻¹ •
          tubeApproxRaw k (fun i => (t i : ℝ)) := by
            rw [norm_tubeApproxRaw]
            simp
  homotopic := homotopic_collared _


-- @@ L207-207 verbatim
end Submission
