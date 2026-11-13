import Mathlib
import Submission.SOFrameGauge
import Submission.RelativeNormalizationProduct


-- @@ L5-13 verbatim
/-!
# Relative normalization by a smooth special-orthogonal gauge

This file closes the analytic normalization pipeline.  Starting from an actual
ambient isotopy and a smooth `SO(n)`-valued spatial family, it constructs the
endpoint framed presentation, transports the sign, and returns the fully glued
signed normalization cobordism.  If both inputs are stationary over `K`, the
whole glued cobordism is a literal product over `K`.
-/


-- @@ L15-15 verbatim
set_option autoImplicit false


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Set Function

-- @@ L20-20 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L22-22 verbatim
namespace Submission

-- @@ L23-23 verbatim
namespace SORelativeNormalization


-- @@ L25-25 verbatim
variable {n : ℕ}


-- @@ L27-27 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L28-28 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)

-- @@ L29-29 verbatim
local notation "M" => Matrix (Fin n) (Fin n) ℝ


-- @@ L31-40 verbatim
/-- Smoothness of the endpoint gauge obtained by fixing the time parameter at
one. -/
theorem contDiff_endpointGauge
    {R : ℝ → E → SOGroup n}
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j)) :
    ContDiff ℝ ∞ (fun x => SOFrameGauge.toCLM (R 1 x)) := by
  apply SOFrameGauge.contDiff_toCLM
  intro i j
  exact (hR i j).comp (contDiff_const.prodMk contDiff_id)


-- @@ L42-55 verbatim
/-- The endpoint sign after a special-orthogonal gauge is literally the
transported ambient sign function on the unchanged zero fiber. -/
def endpointSign (A : SmoothAmbientIsotopy n) {X : FramedLevelSet n}
    (S : FiberSign X) (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j)) :
    FiberSign ((A.pullback X).gaugeTransform
      (fun x => SOFrameGauge.toCLM (R 1 x))
      (contDiff_endpointGauge hR)
      (fun x => SOFrameGauge.toCLM_bijective (R 1 x))) :=
  (A.pullbackSign S).gaugeTransform
    (fun x => SOFrameGauge.toCLM (R 1 x))
    (contDiff_endpointGauge hR)
    (fun x => SOFrameGauge.toCLM_bijective (R 1 x))


-- @@ L57-63 verbatim
@[simp] theorem endpointSign_apply (A : SmoothAmbientIsotopy n)
    {X : FramedLevelSet n} (S : FiberSign X)
    (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j))
    (x : E) : endpointSign A S R hR x = A.pullbackSign S x :=
  rfl


-- @@ L65-78 verbatim
/-- Actual ambient-plus-`SO(n)`-frame normalization, including the final sign
stage. -/
def signedCobordism (A : SmoothAmbientIsotopy n)
    (X : FramedLevelSet n) (S : FiberSign X)
    (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j))
    (hRzero : ∀ x, R 0 x = 1) :
    SignedFramedLevelCobordism S (endpointSign A S R hR) := by
  let D := SOFrameGauge.homotopy (A.pullback X) R hR hRzero
  exact SmoothAmbientIsotopy.signedNormalizationCobordism A D S
    (endpointSign A S R hR) (by
      intro x hx
      rfl)


-- @@ L80-110 verbatim
/-- If the ambient move fixes `K` and the special-orthogonal gauge equals the
identity there throughout the homotopy, the complete signed normalization is a
literal product over `K`. -/
theorem signedCobordism_productOn
    (A : SmoothAmbientIsotopy n)
    (X : FramedLevelSet n) (S : FiberSign X)
    (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j))
    (hRzero : ∀ x, R 0 x = 1)
    {K : Set E} (hA : A.FixedOn K)
    (hRK : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, R s x = 1) :
    (signedCobordism A X S R hR hRzero).ProductOn K X.g S := by
  let D := SOFrameGauge.homotopy (A.pullback X) R hR hRzero
  have hD : D.FixedOn K X.g := by
    intro s hs x hx
    change SOFrameGauge.toCLM (R s x) ((A.pullback X).g x) = X.g x
    rw [hRK s hs x hx, SOFrameGauge.toCLM_one]
    exact hA.pullback_g_eq X hx
  have hT : ∀ x ∈ K, endpointSign A S R hR x = S x := by
    intro x hx
    rw [endpointSign_apply]
    exact hA.pullbackSign_eq S hx
  apply SmoothAmbientIsotopy.signedNormalizationCobordism_productOn
    (A := A) (D := D) (S := S) (T := endpointSign A S R hR)
    (hpos := by
      intro x hx
      rfl)
  · exact hA
  · exact hD
  · exact hT


-- @@ L112-112 verbatim
end SORelativeNormalization

-- @@ L113-113 verbatim
end Submission
