import Mathlib
import Submission.BridgeEndpointCutoff
import Submission.SignedPTCubical


-- @@ L5-14 verbatim
/-!
# The centered signed bridge collapse represents the bridge class

The canonical bridge loop is originally written on the unit cube.  Compactly
supported PT constructions naturally use a large centered cube.  This file
constructs the explicit relative homotopy between those two parametrizations.
It then proves the inverse PT statement needed by the ledger realization: a
signed framed cobordism between two bridge presentations forces their original
homotopy classes to be equal.
-/


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open Set Function Metric Topology.Homotopy

-- @@ L19-19 verbatim
open scoped Topology RealInnerProductSpace ContDiff unitInterval


-- @@ L21-21 verbatim
namespace Submission


-- @@ L23-23 verbatim
variable {n : ℕ}

-- @@ L24-25 verbatim
variable {z : HomotopyGroup (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}


-- @@ L27-27 verbatim
namespace BridgeData


-- @@ L29-29 verbatim
variable (B : BridgeData n z)


-- @@ L31-31 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L32-32 verbatim
local notation "Q" => I^(Fin (n + 1))


-- @@ L34-44 verbatim
/-- The canonical bridge cutoff vanishes on the whole closed ambient collar,
not only on the literal cube boundary. -/
lemma northEndpointPTCutoff_of_mem_closedAmbientCollar {x : E}
    (hx : WithLp.ofLp x ∈ closedAmbientCollar (Fin (n + 1))) :
    B.northEndpointPTCutoff x = 0 := by
  change B.northCutoff x = 0
  rw [northCutoff, northSource, nprep_of_mem_collar B.approx hx]
  apply plateauA_of_le
  show (-eLast n : E) (Fin.last n) ≤ -(1 / 2 : ℝ)
  simp [eLast]
  norm_num


-- @@ L46-51 verbatim
/-- Linear interpolation from the centered box `[-R,R]` to the bridge's unit
cube. -/
def bridgeCubeInterpolation (R : ℝ) (p : I × Q) : E :=
  WithLp.toLp 2 fun i =>
    (1 - (p.1 : ℝ)) * (2 * R * (p.2 i : ℝ) - R) +
      (p.1 : ℝ) * (p.2 i : ℝ)


-- @@ L53-57 verbatim
@[simp] lemma bridgeCubeInterpolation_apply (R : ℝ) (p : I × Q)
    (i : Fin (n + 1)) :
    bridgeCubeInterpolation (n := n) R p i =
      (1 - (p.1 : ℝ)) * (2 * R * (p.2 i : ℝ) - R) +
        (p.1 : ℝ) * (p.2 i : ℝ) := rfl


-- @@ L59-75 verbatim
lemma continuous_bridgeCubeInterpolation (R : ℝ) :
    Continuous (bridgeCubeInterpolation (n := n) R) := by
  have h : bridgeCubeInterpolation (n := n) R = fun p =>
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (fun i =>
        (1 - (p.1 : ℝ)) * (2 * R * (p.2 i : ℝ) - R) +
          (p.1 : ℝ) * (p.2 i : ℝ)) := rfl
  rw [h]
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  have hs : Continuous fun p : I × Q => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have ht : Continuous fun p : I × Q => (p.2 i : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
  exact ((continuous_const.sub hs).mul
    (((continuous_const.mul continuous_const).mul ht).sub continuous_const)).add
      (hs.mul ht)


-- @@ L77-82 verbatim
@[simp] lemma bridgeCubeInterpolation_zero (R : ℝ) (t : Q) :
    bridgeCubeInterpolation (n := n) R (0, t) =
      FiberSign.PTCutoff.centeredCube (n := n) R t := by
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
  funext i
  simp [bridgeCubeInterpolation, FiberSign.PTCutoff.centeredCube]


-- @@ L84-88 verbatim
@[simp] lemma bridgeCubeInterpolation_one (R : ℝ) (t : Q) :
    bridgeCubeInterpolation (n := n) R (1, t) = cubeToBridgeDomain t := by
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
  funext i
  simp [bridgeCubeInterpolation, cubeToBridgeDomain]


-- @@ L90-115 verbatim
/-- During the interpolation every boundary face stays inside the closed
ambient collar. -/
lemma bridgeCubeInterpolation_mem_collar {R : ℝ} (hR : 1 ≤ R)
    (s : I) {t : Q} (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    WithLp.ofLp (bridgeCubeInterpolation (n := n) R (s, t)) ∈
      closedAmbientCollar (Fin (n + 1)) := by
  obtain ⟨i, hi | hi⟩ := ht
  · refine ⟨i, Or.inl ?_⟩
    change (1 - (s : ℝ)) * (2 * R * (t i : ℝ) - R) +
      (s : ℝ) * (t i : ℝ) ≤ 1 / 5
    rw [hi, Set.Icc.coe_zero]
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hR0 : 0 ≤ R := le_trans (by norm_num) hR
    have hmul : 0 ≤ (1 - (s : ℝ)) * R :=
      mul_nonneg (sub_nonneg.mpr hs1) hR0
    nlinarith
  · refine ⟨i, Or.inr ?_⟩
    change (4 / 5 : ℝ) ≤
      (1 - (s : ℝ)) * (2 * R * (t i : ℝ) - R) +
        (s : ℝ) * (t i : ℝ)
    rw [hi, Set.Icc.coe_one]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hmul : (1 - (s : ℝ)) * 1 ≤ (1 - (s : ℝ)) * R :=
      mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr hs1)
    nlinarith


-- @@ L117-121 verbatim
lemma northEndpointPTCutoff_interpolation_boundary {R : ℝ} (hR : 1 ≤ R)
    (s : I) {t : Q} (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    B.northEndpointPTCutoff (bridgeCubeInterpolation (n := n) R (s, t)) = 0 :=
  B.northEndpointPTCutoff_of_mem_closedAmbientCollar
    (bridgeCubeInterpolation_mem_collar (n := n) hR s ht)


-- @@ L123-161 verbatim
/-- Relative homotopy from the large centered canonical PT loop to the original
unit-cube bridge loop. -/
def centeredLoopToBridgeLoopHomotopy (R : ℝ) (hR0 : 0 ≤ R) (hR : 1 ≤ R)
    (hsupp : FiberSign.PTCutoff.VanishesOutside B.fiberSign
      B.northEndpointPTCutoff R) :
    ContinuousMap.HomotopyRel
      (FiberSign.PTCutoff.centeredLoop B.fiberSign B.northEndpointPTCutoff R
        hR0 hsupp).1
      B.northEndpointPTCutoffLoop.1 (Cube.boundary (Fin (n + 1))) where
  toFun st := FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff
    (bridgeCubeInterpolation (n := n) R st)
  continuous_toFun :=
    (map_continuous
      (FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff)).comp
      (continuous_bridgeCubeInterpolation (n := n) R)
  map_zero_left t := by
    change FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff
      (bridgeCubeInterpolation (n := n) R (0, t)) =
      FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff
        (FiberSign.PTCutoff.centeredCube (n := n) R t)
    rw [bridgeCubeInterpolation_zero]
  map_one_left t := by
    change FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff
      (bridgeCubeInterpolation (n := n) R (1, t)) =
      FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff
        (cubeToBridgeDomain t)
    rw [bridgeCubeInterpolation_one]
  prop' s t ht := by
    change FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff
      (bridgeCubeInterpolation (n := n) R (s, t)) =
      FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff
        (FiberSign.PTCutoff.centeredCube (n := n) R t)
    rw [FiberSign.PTCutoff.sphereMap_of_zero B.fiberSign
      B.northEndpointPTCutoff
        (B.northEndpointPTCutoff_interpolation_boundary hR s ht)]
    exact (FiberSign.PTCutoff.sphereMap_of_zero B.fiberSign
      B.northEndpointPTCutoff
        (FiberSign.PTCutoff.centeredCube_boundary_zero B.fiberSign
          B.northEndpointPTCutoff hR0 hsupp ht)).symm


-- @@ L163-171 verbatim
theorem centeredLoop_homotopic_northEndpointPTCutoffLoop
    (R : ℝ) (hR0 : 0 ≤ R) (hR : 1 ≤ R)
    (hsupp : FiberSign.PTCutoff.VanishesOutside B.fiberSign
      B.northEndpointPTCutoff R) :
    GenLoop.Homotopic
      (FiberSign.PTCutoff.centeredLoop B.fiberSign B.northEndpointPTCutoff R
        hR0 hsupp)
      B.northEndpointPTCutoffLoop :=
  ⟨B.centeredLoopToBridgeLoopHomotopy R hR0 hR hsupp⟩


-- @@ L173-186 verbatim
/-- Every sufficiently large centered canonical bridge loop still represents
the bridge's original class. -/
theorem centeredLoop_class_eq (R : ℝ) (hR0 : 0 ≤ R) (hR : 1 ≤ R)
    (hsupp : FiberSign.PTCutoff.VanishesOutside B.fiberSign
      B.northEndpointPTCutoff R) :
    (⟦FiberSign.PTCutoff.centeredLoop B.fiberSign B.northEndpointPTCutoff R
        hR0 hsupp⟧ :
      HomotopyGroup (Fin (n + 1)) (UnitSphere E) (southPole n)) = z := by
  calc
    ⟦FiberSign.PTCutoff.centeredLoop B.fiberSign B.northEndpointPTCutoff R
        hR0 hsupp⟧ = ⟦B.northEndpointPTCutoffLoop⟧ :=
      Quotient.sound
        (B.centeredLoop_homotopic_northEndpointPTCutoffLoop R hR0 hR hsupp)
    _ = z := B.northEndpointPTCutoffLoop_class_eq


-- @@ L188-188 verbatim
end BridgeData


-- @@ L190-212 verbatim
/-- **Inverse signed PT for bridges.**  A signed framed level cobordism between
two bridge presentations identifies their original stable sphere classes. -/
theorem BridgeData.eq_of_signedCobordism
    {z z' : HomotopyGroup (Fin (n + 1))
      (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}
    (B : BridgeData n z) (B' : BridgeData n z')
    (C : SignedFramedLevelCobordism B.fiberSign B'.fiberSign) : z = z' := by
  obtain ⟨χ⟩ :=
    SignedFramedLevelCobordism.SignedSlabCutoff.nonempty C
  obtain ⟨R, hR, hR1, h₀, h₁, hhom⟩ :=
    SignedFramedLevelCobordism.SignedSlabCutoff.exists_endpointCutoffHomotopy
      C χ B.northEndpointPTCutoff B'.northEndpointPTCutoff
  have hz := B.centeredLoop_class_eq R hR.le hR1 h₀
  have hz' := B'.centeredLoop_class_eq R hR.le hR1 h₁
  have hclasses :
      (⟦FiberSign.PTCutoff.centeredLoop B.fiberSign
          B.northEndpointPTCutoff R hR.le h₀⟧ :
        HomotopyGroup (Fin (n + 1))
          (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)) =
      ⟦FiberSign.PTCutoff.centeredLoop B'.fiberSign
          B'.northEndpointPTCutoff R hR.le h₁⟧ :=
    Quotient.sound hhom
  exact hz.symm.trans (hclasses.trans hz')


-- @@ L214-214 verbatim
end Submission
