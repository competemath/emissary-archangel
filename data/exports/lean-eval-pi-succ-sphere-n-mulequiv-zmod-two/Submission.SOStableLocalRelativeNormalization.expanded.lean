import Mathlib
import Submission.SOCartesianRadialExtension
import Submission.SOLocalRelativeNormalization


-- @@ L5-19 verbatim
/-!
# Stable circle classes as actual local frame-normalization cobordisms

`SOCartesianRadialExtension` turns a null stable `SO(r)` loop with a smooth
Cartesian endpoint representative into the jointly smooth family required by
`SOLocalExtension`.  This file packages that output and feeds it directly to
the signed local-normalization cobordism.

Thus, after an ambient move has put one fiber component on the standard
circle, the remaining frame step needs only:

* the desired endpoint gauge loop;
* a smooth Cartesian representative of that loop; and
* the proof that its stable `ZMod 2` class is zero.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function

-- @@ L26-26 verbatim
open scoped unitInterval ContDiff Topology RealInnerProductSpace


-- @@ L28-28 verbatim
namespace Submission


-- @@ L30-41 verbatim
/-- A closed `SO(r)` loop together with a globally smooth Cartesian formula
whose restriction to the unit circle is that loop. -/
structure SmoothCartesianSOLoop (r : ℕ) where
  loop : C(I, SOGroup r)
  closed : loop 0 = loop 1
  cartesian : ℝ × ℝ → SOGroup r
  loop_eq_cartesian : ∀ u : I,
    loop u = cartesian
      (addCircleCartesian (((u : ℝ) : AddCircle (1 : ℝ))))
  cartesian_smooth : ContDiff ℝ ∞
    (fun z : ℝ × ℝ => matrixToEuclidean
      ((cartesian z : SOGroup r) : Matrix (Fin r) (Fin r) ℝ))


-- @@ L43-43 verbatim
namespace SmoothCartesianSOLoop


-- @@ L45-45 verbatim
variable {r : ℕ}


-- @@ L47-53 verbatim
/-- The smooth null-gauge produced from one stable-class-zero Cartesian loop. -/
structure NullGaugeData (L : SmoothCartesianSOLoop r) where
  Q : ℝ → ℝ × ℝ → SOGroup r
  smooth : ∀ i j, ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) =>
    ((Q p.1 p.2 : SOGroup r) : Matrix (Fin r) (Fin r) ℝ) i j
  zero : ∀ z, Q 0 z = 1
  endpoint_circle : ∀ z, z.1 ^ 2 + z.2 ^ 2 = 1 → Q 1 z = L.cartesian z


-- @@ L55-70 verbatim
/-- Stable nullity is sufficient to construct the full jointly smooth gauge.
All approximation and endpoint-relative smoothing are internal. -/
theorem nonempty_nullGaugeData (L : SmoothCartesianSOLoop r)
    (hr : 3 ≤ r)
    (hclass : loopClassZ2 L.loop L.closed = 0) :
    Nonempty L.NullGaugeData := by
  let e : C(I, SOGroup r) := ContinuousMap.const I 1
  have heclosed : e 0 = e 1 := rfl
  have he : ∀ u : I, e u = 1 := fun _ => rfl
  have hclasses : loopClassZ2 e heclosed = loopClassZ2 L.loop L.closed := by
    rw [loopClassZ2_const, hclass]
  obtain ⟨Q, hQ, hQzero, hQone⟩ :=
    exists_contDiff_cartesianSOHomotopy_of_loopClassZ2_eq
      hr heclosed L.closed he hclasses L.cartesian
      L.loop_eq_cartesian L.cartesian_smooth
  exact ⟨⟨Q, hQ, hQzero, hQone⟩⟩


-- @@ L72-72 verbatim
variable {m : ℕ}


-- @@ L74-74 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L75-75 verbatim
local notation "M" => Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ


-- @@ L77-81 verbatim
/-- The ambient field used by local frame normalization. -/
def NullGaugeData.spatialGauge
    {L : SmoothCartesianSOLoop (m + 2)} (D : L.NullGaugeData)
    (s : ℝ) (x : E) : SOGroup (m + 2) :=
  SOLocalExtension.extendCircleSOHomotopy D.Q s x


-- @@ L83-88 verbatim
theorem NullGaugeData.spatialGauge_smooth
    {L : SmoothCartesianSOLoop (m + 2)} (D : L.NullGaugeData) :
    ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E =>
        ((D.spatialGauge p.1 p.2 : SOGroup (m + 2)) : M) i j) :=
  SOLocalExtension.contDiff_extendCircleSOHomotopy D.smooth D.zero


-- @@ L90-93 verbatim
@[simp] theorem NullGaugeData.spatialGauge_zero
    {L : SmoothCartesianSOLoop (m + 2)} (D : L.NullGaugeData)
    (x : E) : D.spatialGauge 0 x = 1 :=
  SOLocalExtension.extendCircleSOHomotopy_zero D.Q D.zero x


-- @@ L95-103 verbatim
/-- On the standard circle, the endpoint field is exactly the prescribed
Cartesian endpoint gauge. -/
@[simp] theorem NullGaugeData.spatialGauge_one_circleAt
    {L : SmoothCartesianSOLoop (m + 2)} (D : L.NullGaugeData) (θ : ℝ) :
    D.spatialGauge 1 (circleAt θ) =
      L.cartesian (Real.cos θ, Real.sin θ) := by
  rw [NullGaugeData.spatialGauge,
    SOLocalExtension.extendCircleSOHomotopy_one_circleAt]
  exact D.endpoint_circle _ (Real.cos_sq_add_sin_sq θ)


-- @@ L105-115 verbatim
/-- Feed the constructed null-gauge into the complete ambient/frame/sign
normalization primitive. -/
def NullGaugeData.signedCobordism
    {L : SmoothCartesianSOLoop (m + 2)} (D : L.NullGaugeData)
    (A : SmoothAmbientIsotopy (m + 2))
    (X : FramedLevelSet (m + 2)) (S : FiberSign X) :
    SignedFramedLevelCobordism S
      (SOLocalRelativeNormalization.endpointSign
        A S D.Q D.smooth D.zero) :=
  SOLocalRelativeNormalization.signedCobordism
    A X S D.Q D.smooth D.zero


-- @@ L117-127 verbatim
/-- If the ambient move fixes a set outside the standard outer tube, the
entire local normalization cobordism is a product there. -/
theorem NullGaugeData.signedCobordism_productOn
    {L : SmoothCartesianSOLoop (m + 2)} (D : L.NullGaugeData)
    (A : SmoothAmbientIsotopy (m + 2))
    (X : FramedLevelSet (m + 2)) (S : FiberSign X)
    {K : Set E} (hA : A.FixedOn K)
    (hK : K ⊆ {x : E | x ∉ tubeRegion (m := m) (1 / 3)}) :
    (D.signedCobordism A X S).ProductOn K X.g S :=
  SOLocalRelativeNormalization.signedCobordism_productOn
    A X S D.Q D.smooth D.zero hA hK


-- @@ L129-129 verbatim
end SmoothCartesianSOLoop


-- @@ L131-131 verbatim
end Submission
