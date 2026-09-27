/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderForcingParity
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTimeParity
import LeanPool.NavierStokesAndEuler.Euler.PacketSlicedAssembly


-- @@ L14-14 verbatim
/-! Joint parity carried by the actual profile fields and their true time derivatives. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerPacketCylinderField


-- @@ L23-23 verbatim
open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion


-- @@ L25-33 verbatim
/-- Profile parity data, collecting `high`, `mean`, `corrector`, `pressure`, `highPressure`,
`meanPressure`. -/
structure ProfileParity (T : ℝ) (a : Profile) : Prop where
  high : JointOdd T a.high
  mean : JointOdd T a.mean
  corrector : JointOdd T a.corrector
  pressure : JointOdd T (pressureGradient a.highPressure)
  highPressure : ∀ (t : Icc (0 : ℝ) T) x θ, a.highPressure (t,(-x,-θ)) = a.highPressure (t,(x,θ))
  meanPressure : ∀ (t : Icc (0 : ℝ) T) x θ, a.meanPressure (t,(-x,-θ)) = a.meanPressure (t,(x,θ))


-- @@ L35-35 verbatim
namespace ProfileParity


-- @@ L37-47 verbatim
theorem zero (T : ℝ) : ProfileParity T (0 : Profile) where
  high := JointOdd.zero T
  mean := JointOdd.zero T
  corrector := JointOdd.zero T
  pressure := by
    intro t x θ
    change pressureGradient (0 : ScalarField) (t,(-x,-θ)) =
      -pressureGradient (0 : ScalarField) (t,(x,θ))
    simp [pressureGradient,pressureJet_zero]
  highPressure _ _ _ := rfl
  meanPressure _ _ _ := rfl


-- @@ L49-53 verbatim
theorem prefixOdd {T : ℝ} {p : ℕ} {a : ℕ → Profile}
    (H : ∀ i, i < p → ProfileParity T (a i)) : PrefixOdd T p a where
  high i hi := (H i hi).high
  mean i hi := (H i hi).mean
  corrector i hi := (H i hi).corrector


-- @@ L55-58 verbatim
theorem changeTime {T T' : ℝ} {a : Profile} (H : ProfileParity T a) (h : T = T') :
    ProfileParity T' a := by
  subst T'
  exact H


-- @@ L60-61 verbatim
variable {P T : ℝ} [Fact (0 < P)] {S : Set Space} {a : Profile}
  (hT : 0 < T) (G : ProfileRegularity P T hT.le S a) (H : ProfileParity T a)


-- @@ L63-63 verbatim
include H


-- @@ L65-66 verbatim
theorem highDerivative_odd : JointOdd T G.highT :=
  G.high.timeDerivative_odd G.highDerivative hT G.high_time H.high


-- @@ L68-69 verbatim
theorem meanDerivative_odd : JointOdd T G.meanT :=
  G.mean.timeDerivative_odd G.meanDerivative hT G.mean_time H.mean


-- @@ L71-72 verbatim
theorem correctorDerivative_odd : JointOdd T G.correctorT :=
  G.corrector.timeDerivative_odd G.correctorDerivative hT G.corrector_time H.corrector


-- @@ L74-74 verbatim
end ProfileParity


-- @@ L76-79 verbatim
theorem JointOdd.changeTime {T T' : ℝ} {raw : VectorField} (H : JointOdd T raw) (h : T = T') :
    JointOdd T' raw := by
  subst T'
  exact H


-- @@ L81-81 verbatim
end EulerPacketCylinderField
