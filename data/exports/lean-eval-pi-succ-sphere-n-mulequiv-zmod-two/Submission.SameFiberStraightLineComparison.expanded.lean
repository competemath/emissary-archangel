import Mathlib
import Submission.NormalizeMoves


-- @@ L4-21 verbatim
/-!
# Exact straight-line comparison of two same-fiber presentations

This file isolates a concrete sufficient condition for the final
post-placement comparison problem.  Two defining maps can be joined by their
literal affine interpolation provided:

* their zero fibers agree;
* their values never form an obtuse pair (so interpolation creates no new
  zero away from the common fiber); and
* their first derivatives agree on the common fiber (so every intermediate
  zero remains regular).

The endpoint is the prescribed target defining map exactly.  Thus this is a
useful terminal adapter after local frame/jet normalization: it identifies the
remaining global obligation as value-direction control away from the fiber,
rather than hiding it in an abstract `DefiningMapHomotopy` field.
-/


-- @@ L23-23 verbatim
set_option autoImplicit false


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Set Function

-- @@ L28-28 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L30-30 verbatim
namespace Submission

-- @@ L31-31 verbatim
namespace SameFiberStraightLineComparison


-- @@ L33-33 verbatim
variable {n : ℕ}


-- @@ L35-35 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L36-36 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L38-44 verbatim
/-- Explicit hypotheses under which affine interpolation is an exact
same-fiber defining-map homotopy. -/
structure Data (X Y : FramedLevelSet n) where
  fiber_eq : Y.fiber = X.fiber
  pairing_nonneg : ∀ x : E, 0 ≤ inner ℝ (X.g x) (Y.g x)
  firstJet_eq : ∀ x ∈ X.fiber,
    fderiv ℝ Y.g x = fderiv ℝ X.g x


-- @@ L46-46 verbatim
namespace Data


-- @@ L48-48 verbatim
variable {X Y : FramedLevelSet n} (D : Data X Y)


-- @@ L50-52 verbatim
/-- Literal affine interpolation between the two prescribed defining maps. -/
def straightMap (_D : Data X Y) (s : ℝ) (x : E) : F :=
  (1 - s) • X.g x + s • Y.g x


-- @@ L54-58 verbatim
theorem straightMap_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × E => D.straightMap p.1 p.2) := by
  exact ((contDiff_const.sub contDiff_fst).smul
      (X.smooth.comp contDiff_snd)).add
    (contDiff_fst.smul (Y.smooth.comp contDiff_snd))


-- @@ L60-62 verbatim
@[simp] theorem straightMap_zero : D.straightMap 0 = X.g := by
  funext x
  simp [straightMap]


-- @@ L64-66 verbatim
@[simp] theorem straightMap_one : D.straightMap 1 = Y.g := by
  funext x
  simp [straightMap]


-- @@ L68-105 verbatim
/-- Nonnegative pointwise pairing prevents the straight segment from passing
through zero away from the common zero fiber. -/
theorem straightMap_fiber_eq (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    {x | D.straightMap s x = 0} = X.fiber := by
  ext x
  constructor
  · intro hx
    change D.straightMap s x = 0 at hx
    by_cases hsend : s = 1
    · subst s
      have hy : Y.g x = 0 := by simpa [straightMap] using hx
      have hmem : x ∈ Y.fiber := hy
      rw [D.fiber_eq] at hmem
      exact hmem
    · have hslt : s < 1 := lt_of_le_of_ne hs1 hsend
      have hinner := congrArg (fun v : F => inner ℝ (X.g x) v) hx
      simp only [straightMap, inner_add_right, real_inner_smul_right,
        inner_zero_right, real_inner_self_eq_norm_sq] at hinner
      have hpair := D.pairing_nonneg x
      have hterm1 : 0 ≤ (1 - s) * ‖X.g x‖ ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg _)
      have hterm2 : 0 ≤ s * inner ℝ (X.g x) (Y.g x) :=
        mul_nonneg hs0 hpair
      have hterm1zero : (1 - s) * ‖X.g x‖ ^ 2 = 0 := by
        linarith
      have hnormsq : ‖X.g x‖ ^ 2 = 0 :=
        (mul_eq_zero.mp hterm1zero).resolve_left
          (sub_ne_zero.mpr (Ne.symm hsend))
      have hnorm : ‖X.g x‖ = 0 := by
        exact sq_eq_zero_iff.mp hnormsq
      exact norm_eq_zero.mp hnorm
  · intro hx
    have hx0 : X.g x = 0 := hx
    have hyMem : x ∈ Y.fiber := by
      rw [D.fiber_eq]
      exact hx
    have hy0 : Y.g x = 0 := hyMem
    simp [straightMap, hx0, hy0]


-- @@ L107-120 verbatim
/-- First-jet agreement makes the derivative of every intermediate map
literally equal to the source derivative on the common fiber. -/
theorem fderiv_straightMap_of_mem_fiber
    (s : ℝ) {x : E} (hx : x ∈ X.fiber) :
    fderiv ℝ (D.straightMap s) x = fderiv ℝ X.g x := by
  change fderiv ℝ ((1 - s) • X.g + s • Y.g) x = fderiv ℝ X.g x
  rw [fderiv_add,
    fderiv_const_smul_field, fderiv_const_smul_field]
  · change (1 - s) • fderiv ℝ X.g x + s • fderiv ℝ Y.g x =
      fderiv ℝ X.g x
    rw [D.firstJet_eq x hx]
    module
  · exact X.smooth.differentiable (by simp) x |>.const_smul _
  · exact Y.smooth.differentiable (by simp) x |>.const_smul _


-- @@ L122-133 verbatim
/-- The affine interpolation is therefore a genuine exact
`DefiningMapHomotopy`, not merely a same-fiber endpoint interface. -/
def homotopy : DefiningMapHomotopy X Y where
  H := D.straightMap
  smooth := D.straightMap_smooth
  H_zero := D.straightMap_zero
  H_one := D.straightMap_one
  fiber_eq := D.straightMap_fiber_eq
  regular := by
    intro s _hs0 _hs1 x hx
    rw [D.fderiv_straightMap_of_mem_fiber s hx]
    exact X.regular x hx


-- @@ L135-135 verbatim
end Data


-- @@ L137-137 verbatim
end SameFiberStraightLineComparison

-- @@ L138-138 verbatim
end Submission
