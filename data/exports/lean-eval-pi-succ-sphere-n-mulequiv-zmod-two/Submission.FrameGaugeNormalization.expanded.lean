import Mathlib
import Submission.AmbientNormalizationPrimitive


-- @@ L4-21 verbatim
/-!
# Smooth gauge changes of a framed defining map

Once an embedded fiber circle has been moved to its standard position, its
normal framing is changed by multiplying the defining equations by a smooth
field of invertible linear maps.  This file proves the analytic step in full.

For a framed defining map `g` and a smooth field `Q(x)` of invertible
continuous linear endomorphisms of the codomain, the gauge transform is

`x ↦ Q(x) (g(x))`.

It has exactly the same zero fiber.  At a point of that fiber, the product-rule
term differentiating `Q` vanishes because `g(x)=0`; hence its derivative is
literally `Q(x) ∘ Dg(x)` and remains surjective.  The same calculation for a
two-parameter field `Q(s,x)` produces a genuine `DefiningMapHomotopy` and can
be fed directly to `SmoothAmbientIsotopy.signedNormalizationCobordism`.
-/


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function

-- @@ L26-26 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L28-28 verbatim
namespace Submission


-- @@ L30-30 verbatim
variable {n : ℕ}


-- @@ L32-32 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L33-33 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L35-35 verbatim
/-! ## The derivative calculation -/


-- @@ L37-48 verbatim
/-- At a zero of `g`, differentiating a varying linear gauge contributes no
product-rule correction. -/
theorem fderiv_gauge_apply_of_eq_zero
    {Q : E → F →L[ℝ] F} {g : E → F}
    (hQ : ContDiff ℝ ∞ Q) (hg : ContDiff ℝ ∞ g)
    {x : E} (hx : g x = 0) :
    fderiv ℝ (fun y => Q y (g y)) x =
      (Q x).comp (fderiv ℝ g x) := by
  rw [fderiv_clm_apply
    (hQ.differentiable (by simp) x)
    (hg.differentiable (by simp) x), hx]
  simp


-- @@ L50-50 verbatim
/-! ## A single gauge transform -/


-- @@ L52-52 verbatim
namespace FramedLevelSet


-- @@ L54-79 verbatim
/-- Multiplication of a framed defining map by a smooth pointwise invertible
linear gauge. -/
def gaugeTransform (X : FramedLevelSet n) (Q : E → F →L[ℝ] F)
    (hQ : ContDiff ℝ ∞ Q) (hQbij : ∀ x, Bijective (Q x)) :
    FramedLevelSet n where
  g x := Q x (X.g x)
  smooth := hQ.clm_apply X.smooth
  fiber_bounded := by
    have hfiber : {x : E | Q x (X.g x) = 0} = X.fiber := by
      ext x
      constructor
      · intro hx
        apply (hQbij x).1
        simpa using hx
      · intro hx
        change X.g x = 0 at hx
        simp [hx]
    rw [hfiber]
    exact X.fiber_bounded
  regular := by
    intro x hx
    have hxg : X.g x = 0 := by
      apply (hQbij x).1
      simpa using hx
    rw [fderiv_gauge_apply_of_eq_zero hQ X.smooth hxg]
    exact (hQbij x).2.comp (X.regular x hxg)


-- @@ L81-85 verbatim
@[simp] theorem gaugeTransform_g (X : FramedLevelSet n)
    (Q : E → F →L[ℝ] F) (hQ : ContDiff ℝ ∞ Q)
    (hQbij : ∀ x, Bijective (Q x)) (x : E) :
    (X.gaugeTransform Q hQ hQbij).g x = Q x (X.g x) :=
  rfl


-- @@ L87-101 verbatim
/-- A pointwise invertible gauge does not move the zero fiber. -/
theorem gaugeTransform_fiber (X : FramedLevelSet n)
    (Q : E → F →L[ℝ] F) (hQ : ContDiff ℝ ∞ Q)
    (hQbij : ∀ x, Bijective (Q x)) :
    (X.gaugeTransform Q hQ hQbij).fiber = X.fiber := by
  ext x
  constructor
  · intro hx
    change Q x (X.g x) = 0 at hx
    apply (hQbij x).1
    simpa using hx
  · intro hx
    change X.g x = 0 at hx
    change Q x (X.g x) = 0
    simp [hx]


-- @@ L103-103 verbatim
end FramedLevelSet


-- @@ L105-105 verbatim
namespace FiberSign


-- @@ L107-113 verbatim
/-- Since a gauge transform has the same fiber, a sign label transports
unchanged. -/
def gaugeTransform {X : FramedLevelSet n} (S : FiberSign X)
    (Q : E → F →L[ℝ] F) (hQ : ContDiff ℝ ∞ Q)
    (hQbij : ∀ x, Bijective (Q x)) :
    FiberSign (X.gaugeTransform Q hQ hQbij) :=
  S.restrict (by rw [FramedLevelSet.gaugeTransform_fiber])


-- @@ L115-119 verbatim
@[simp] theorem gaugeTransform_apply {X : FramedLevelSet n} (S : FiberSign X)
    (Q : E → F →L[ℝ] F) (hQ : ContDiff ℝ ∞ Q)
    (hQbij : ∀ x, Bijective (Q x)) (x : E) :
    S.gaugeTransform Q hQ hQbij x = S x :=
  rfl


-- @@ L121-121 verbatim
end FiberSign


-- @@ L123-123 verbatim
/-! ## A smooth family of gauges -/


-- @@ L125-130 verbatim
/-- Joint smoothness gives smoothness of every fixed-parameter gauge. -/
theorem contDiff_gauge_slice
    {Q : ℝ → E → F →L[ℝ] F}
    (hQ : ContDiff ℝ ∞ (fun p : ℝ × E => Q p.1 p.2)) (s : ℝ) :
    ContDiff ℝ ∞ (Q s) :=
  hQ.comp (contDiff_const.prodMk contDiff_id)


-- @@ L132-132 verbatim
namespace DefiningMapHomotopy


-- @@ L134-166 verbatim
/-- A smooth family of invertible gauges is a common-fiber homotopy of framed
defining maps.  It is the direct formal target of a smooth `SO(n)` frame-loop
homotopy. -/
def ofGauge (X : FramedLevelSet n)
    (Q : ℝ → E → F →L[ℝ] F)
    (hQ : ContDiff ℝ ∞ (fun p : ℝ × E => Q p.1 p.2))
    (hQzero : ∀ x, Q 0 x = ContinuousLinearMap.id ℝ F)
    (hQbij : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, Bijective (Q s x)) :
    DefiningMapHomotopy X
      (X.gaugeTransform (Q 1) (contDiff_gauge_slice hQ 1)
        (fun x => hQbij 1 ⟨zero_le_one, le_rfl⟩ x)) where
  H s x := Q s x (X.g x)
  smooth := hQ.clm_apply (X.smooth.comp contDiff_snd)
  H_zero := by
    funext x
    rw [hQzero x]
    rfl
  H_one := rfl
  fiber_eq := by
    intro s hs0 hs1
    ext x
    constructor
    · intro hx
      apply (hQbij s ⟨hs0, hs1⟩ x).1
      simpa using hx
    · intro hx
      change X.g x = 0 at hx
      simp [hx]
  regular := by
    intro s hs0 hs1 x hx
    rw [fderiv_gauge_apply_of_eq_zero
      (contDiff_gauge_slice hQ s) X.smooth hx]
    exact (hQbij s ⟨hs0, hs1⟩ x).2.comp (X.regular x hx)


-- @@ L168-175 verbatim
@[simp] theorem ofGauge_H (X : FramedLevelSet n)
    (Q : ℝ → E → F →L[ℝ] F)
    (hQ : ContDiff ℝ ∞ (fun p : ℝ × E => Q p.1 p.2))
    (hQzero : ∀ x, Q 0 x = ContinuousLinearMap.id ℝ F)
    (hQbij : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, Bijective (Q s x))
    (s : ℝ) (x : E) :
    (ofGauge X Q hQ hQzero hQbij).H s x = Q s x (X.g x) :=
  rfl


-- @@ L177-189 verbatim
/-- The endpoint sign produced by the gauge homotopy is pointwise the original
sign. -/
theorem ofGauge_restrict_eq_gaugeTransform
    (X : FramedLevelSet n) (S : FiberSign X)
    (Q : ℝ → E → F →L[ℝ] F)
    (hQ : ContDiff ℝ ∞ (fun p : ℝ × E => Q p.1 p.2))
    (hQzero : ∀ x, Q 0 x = ContinuousLinearMap.id ℝ F)
    (hQbij : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, Bijective (Q s x)) :
    S.restrict (ofGauge X Q hQ hQzero hQbij).fiber_subset =
      S.gaugeTransform (Q 1) (contDiff_gauge_slice hQ 1)
        (fun x => hQbij 1 ⟨zero_le_one, le_rfl⟩ x) := by
  cases S
  rfl


-- @@ L191-191 verbatim
end DefiningMapHomotopy


-- @@ L193-193 verbatim
end Submission
