/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra


-- @@ L12-12 verbatim
/-! A raw cylinder field determines its actual continuous L² path uniquely. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L21-22 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerPacketProfileRecursion


-- @@ L24-24 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}


-- @@ L26-34 verbatim
theorem path_eq_of_same_raw (G H : Field P T raw) : G.path = H.path := by
  apply ContinuousMap.ext
  intro t
  apply Lp.ext
  filter_upwards [pointField_ae P G.path G.orbit t,pointField_ae P H.path H.orbit t] with z hg hh
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective z.2
  have he := (G.raw_eq t z.1 θ).symm.trans (H.raw_eq t z.1 θ)
  rw [hθ] at he
  exact hg.trans (he.trans hh.symm)


-- @@ L36-39 verbatim
theorem path_eq_of_raw_eq (G : Field P T raw) (H : Field P T raw')
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw' (t, (x, θ)) = raw (t, (x, θ))) :
    G.path = H.path :=
  (G.congr he).path_eq_of_same_raw H


-- @@ L41-41 verbatim
end EulerPacketCylinderField.Field
