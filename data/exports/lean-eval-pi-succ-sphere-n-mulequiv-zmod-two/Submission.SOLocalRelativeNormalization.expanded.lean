import Mathlib
import Submission.SOLocalExtension
import Submission.SORelativeNormalization


-- @@ L5-19 verbatim
/-!
# Relative normalization from circle `SO(n)` data

This is the direct adapter between the two previously separate analytic
pieces of component normalization:

* `SOLocalExtension` extends a smooth `SO(n)` homotopy prescribed on the
  standard circle to a gauge supported in its tubular neighborhood;
* `SORelativeNormalization` turns an ambient isotopy and a smooth spatial
  `SO(n)` gauge into an actual signed framed cobordism.

The only geometric input which remains here is the ambient isotopy itself and
the smooth Cartesian representative of the circle homotopy.  In particular,
no already-extended spatial gauge is assumed by the API below.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function

-- @@ L26-26 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L28-28 verbatim
namespace Submission

-- @@ L29-29 verbatim
namespace SOLocalRelativeNormalization


-- @@ L31-31 verbatim
variable {m : ℕ}


-- @@ L33-33 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L34-34 verbatim
local notation "M" => Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ


-- @@ L36-53 verbatim
/-- The endpoint sign produced after first applying the ambient move and then
the tubular extension of the prescribed circle `SO(m+2)` homotopy. -/
def endpointSign (A : SmoothAmbientIsotopy (m + 2))
    {X : FramedLevelSet (m + 2)} (S : FiberSign X)
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2))
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => ((R p.1 p.2 : SOGroup (m + 2)) : M) i j))
    (hRzero : ∀ z, R 0 z = 1) :
    FiberSign ((A.pullback X).gaugeTransform
      (fun x => SOFrameGauge.toCLM
        (SOLocalExtension.extendCircleSOHomotopy R 1 x))
      (SORelativeNormalization.contDiff_endpointGauge
        (SOLocalExtension.contDiff_extendCircleSOHomotopy hR hRzero))
      (fun x => SOFrameGauge.toCLM_bijective
        (SOLocalExtension.extendCircleSOHomotopy R 1 x))) :=
  SORelativeNormalization.endpointSign A S
    (SOLocalExtension.extendCircleSOHomotopy R)
    (SOLocalExtension.contDiff_extendCircleSOHomotopy hR hRzero)


-- @@ L55-68 verbatim
/-- An ambient normalization move together with circle-level `SO(m+2)` data
gives an actual signed framed cobordism.  Spatial extension of the gauge is
constructed internally. -/
def signedCobordism (A : SmoothAmbientIsotopy (m + 2))
    (X : FramedLevelSet (m + 2)) (S : FiberSign X)
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2))
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => ((R p.1 p.2 : SOGroup (m + 2)) : M) i j))
    (hRzero : ∀ z, R 0 z = 1) :
    SignedFramedLevelCobordism S (endpointSign A S R hR hRzero) :=
  SORelativeNormalization.signedCobordism A X S
    (SOLocalExtension.extendCircleSOHomotopy R)
    (SOLocalExtension.contDiff_extendCircleSOHomotopy hR hRzero)
    (SOLocalExtension.extendCircleSOHomotopy_zero R hRzero)


-- @@ L70-92 verbatim
/-- If the ambient move fixes `K` and `K` lies outside the outer circle tube,
then the complete ambient/frame/sign normalization is a literal product on
`K`.  This is the componentwise induction interface needed after an unknotting
move has been constructed in one disjoint ball. -/
theorem signedCobordism_productOn
    (A : SmoothAmbientIsotopy (m + 2))
    (X : FramedLevelSet (m + 2)) (S : FiberSign X)
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2))
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => ((R p.1 p.2 : SOGroup (m + 2)) : M) i j))
    (hRzero : ∀ z, R 0 z = 1)
    {K : Set E} (hA : A.FixedOn K)
    (hK : K ⊆ {x : E | x ∉ tubeRegion (m := m) (1 / 3)}) :
    (signedCobordism A X S R hR hRzero).ProductOn K X.g S := by
  apply SORelativeNormalization.signedCobordism_productOn
    (A := A) (X := X) (S := S)
    (R := SOLocalExtension.extendCircleSOHomotopy R)
    (hR := SOLocalExtension.contDiff_extendCircleSOHomotopy hR hRzero)
    (hRzero := SOLocalExtension.extendCircleSOHomotopy_zero R hRzero)
    hA
  intro s hs x hx
  exact SOLocalExtension.extendCircleSOHomotopy_eq_one_off_outer
    R hRzero s (hK hx)


-- @@ L94-94 verbatim
end SOLocalRelativeNormalization

-- @@ L95-95 verbatim
end Submission
