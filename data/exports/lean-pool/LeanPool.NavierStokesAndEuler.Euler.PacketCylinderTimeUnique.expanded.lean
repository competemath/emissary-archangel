/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique


-- @@ L12-12 verbatim
/-! Genuine time-derivative witnesses are unique, including at both endpoints. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace EulerPacketCylinderField.TimeDerivative


-- @@ L19-19 verbatim
open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketPointJets


-- @@ L21-23 verbatim
variable {P T : ℝ} [Fact (0 < P)] {hT : 0 < T}
  {raw raw₁ raw₂ : VectorField} {G H : Field P T raw}
  {G₁ : Field P T raw₁} {H₁ : Field P T raw₂}


-- @@ L25-27 verbatim
theorem raw_eq (hG : TimeDerivative hT.le G G₁) (hH : TimeDerivative hT.le H H₁)
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) : raw₁ (t,(x,θ)) = raw₂ (t,(x,θ)) :=
  (G.slicedJet_temporal hT G₁ hG t x θ).symm.trans (H.slicedJet_temporal hT H₁ hH t x θ)


-- @@ L29-30 verbatim
theorem path_eq (hG : TimeDerivative hT.le G G₁) (hH : TimeDerivative hT.le H H₁) :
    G₁.path = H₁.path := G₁.path_eq_of_raw_eq H₁ (fun t x θ => (raw_eq (hT := hT) hG hH t x θ).symm)


-- @@ L32-32 verbatim
end EulerPacketCylinderField.TimeDerivative
