/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentState
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedResidualEquation


-- @@ L12-14 verbatim
/-! Both actual initialized packet branches produce the same recursive
physical state. Their residual and parity proofs are supplied by their
source formulas, not additional hypotheses about the new solution. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerParentPacketFrames.SmoothState


-- @@ L23-25 verbatim
open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderDriftCorrection EulerGraphInvariantFlow EulerPacketTerminalDatum
  EulerPacketProfileRecursion EulerSpatialCutoffs


-- @@ L27-33 verbatim
variable {A : Parent} (S : SmoothState A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (hSym : ∀ x, -x ∈ support ↔ x ∈ support)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ support) (α : ℝ)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)


-- @@ L35-56 verbatim
/-- Forward child, constructed using `S.packetChild`. -/
def forwardChild
    (Q : Budget period A.T_pos
      (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm J support hSupport)
        rfl δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk))
    (G : EulerPhysicalGraphFlowBounds.Data period A.T)
    (hG : G.A =
 Q.liftedPacketCoefficient period
      (forwardInitializedNormalizedField (A.meanData H) (A.transverseData m hm J support hSupport)
        rfl δ hδ ξ hs α N k))
    (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
    (labels : LabelData (A.child G k m hgraph nextEll hnext hnext1)) :
    SmoothState (A.child G k m hgraph nextEll hnext hnext1) :=
  S.packetChild m hm J support hSupport Q
    (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support
        hSupport)
      rfl δ hδ ξ hs α (A.sourceAgreement m hm J support hSupport H) N hN k hk)
    (forwardInitializedNormalizedField (A.meanData H) (A.transverseData m hm J support hSupport)
      rfl δ hδ ξ hs α N k) rfl
    (S.odd.forwardCorrectionParity H m hm J support hSupport hSym δ hδ ξ hs α N hN k hk)
    G hG k (mul_inv_cancel₀ (by linarith : k ≠ 0)) hgraph nextEll hnext hnext1 labels


-- @@ L58-81 verbatim
/-- Joined child, constructed using `S.packetChild`. -/
def joinedChild (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)
    (Q : Budget period A.T_pos
      (initializedCorrectionData (A.meanData H) (A.transverseData m hm J support hSupport)
        rfl τ hτ hτT (A.historyOn H m hm J support hSupport τ hτ hτT) δ hδ ξ hs α
        (A.sourceAgreement m hm J support hSupport H) N hN k hk))
    (G : EulerPhysicalGraphFlowBounds.Data period A.T)
    (hG : G.A =
 Q.liftedPacketCoefficient period
      (initializedNormalizedField (A.meanData H) (A.transverseData m hm J support hSupport)
        rfl τ hτ hτT (A.historyOn H m hm J support hSupport τ hτ hτT) δ hδ ξ hs α N k))
    (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
    (labels : LabelData (A.child G k m hgraph nextEll hnext hnext1)) :
    SmoothState (A.child G k m hgraph nextEll hnext hnext1) :=
  S.packetChild m hm J support hSupport Q
    (initializedApproximationResidual (A.meanData H) (A.transverseData m hm J support hSupport)
      rfl τ hτ hτT (A.historyOn H m hm J support hSupport τ hτ hτT) δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk)
    (initializedNormalizedField (A.meanData H) (A.transverseData m hm J support hSupport)
      rfl τ hτ hτT (A.historyOn H m hm J support hSupport τ hτ hτT) δ hδ ξ hs α N k) rfl
    (S.odd.joinedCorrectionParity H m hm J support hSupport hSym δ hδ ξ hs α
      τ hτ hτT N hN k hk)
    G hG k (mul_inv_cancel₀ (by linarith : k ≠ 0)) hgraph nextEll hnext hnext1 labels


-- @@ L83-83 verbatim
end EulerParentPacketFrames.SmoothState
