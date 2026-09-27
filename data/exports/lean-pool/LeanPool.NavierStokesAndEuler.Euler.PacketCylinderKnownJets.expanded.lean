/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderSpatialJet


-- @@ L11-11 verbatim
/-! Literal known-grade jet data are reconstructed from only the genuine prefix fields. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerPacketCylinderField


-- @@ L20-20 verbatim
open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion


-- @@ L22-29 verbatim
/-- Prefix fields data, collecting `high`, `mean`, `corrector`. -/
structure PrefixFields (P T : ℝ) [Fact (0 < P)] (p : ℕ) (a : ℕ → Profile) where
  /-- High-frequency field of `PrefixFields`, of type `∀ i, i < p → Field P T (a i).high`. -/
  high : ∀ i, i < p → Field P T (a i).high
  /-- Mean field of `PrefixFields`, of type `∀ i, i < p → Field P T (a i).mean`. -/
  mean : ∀ i, i < p → Field P T (a i).mean
  /-- Correction field of `PrefixFields`, of type `∀ i, i < p → Field P T (a i).corrector`. -/
  corrector : ∀ i, i < p → Field P T (a i).corrector


-- @@ L31-31 verbatim
variable {P T : ℝ} [Fact (0 < P)] {p : ℕ} {a : ℕ → Profile}


-- @@ L33-56 verbatim
/-- No grade at or above p is used to obtain the spatial part of the known jets. -/
def PrefixFields.knownJet (F : PrefixFields P T p a) (O : Operators) (hp : 1 ≤ p) (i : ℕ) :
    SpatialJetField P T (fun z => knownJets O p a z i) := by
  classical
  by_cases hi : i < p
  · by_cases hz : i = 0
    · refine (SpatialJetField.zero P T).congr ?_
      intro t x θ
      simp [knownJets,history,velocityJet,hz,show 0 < p by omega]
    · let G := ((SpatialJetField.ofField O.interval (F.high i hi)).add
        (SpatialJetField.ofField O.interval (F.mean i hi))).add
        (SpatialJetField.ofField O.interval (F.corrector (i-1) (by omega)))
      refine G.congr ?_
      intro t x θ
      simp only [knownJets,history,hi,ite_true,velocityJet,hz,ite_false]
      rfl
  · by_cases he : i = p
    · refine (SpatialJetField.ofField O.interval (F.corrector (p-1) (by omega))).congr ?_
      intro t x θ
      simp [knownJets,history,he]
    · refine (SpatialJetField.zero P T).congr ?_
      intro t x θ
      simp only [knownJets,history,hi,ite_false,he]
      rfl


-- @@ L58-58 verbatim
end EulerPacketCylinderField
