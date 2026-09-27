/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketGradeAbsorption


-- @@ L12-12 verbatim
/-! A single spare shift absorbs every fixed linear-operator amplitude at the same radius. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace EulerGevrey


-- @@ L19-24 verbatim
theorem amplitude_absorbed (A R : ℝ) (hA : 0 ≤ A) (hAR : A ≤ R) (d n : ℕ) :
    A*majorant R d n ≤ majorant R (d+1) n := by
  have hcount : 1 ≤ (d+1)^2 := by
    simpa only [one_pow] using Nat.pow_le_pow_left (by omega : 1 ≤ d+1) 2
  have h := finite_cost_absorbed A R hA hAR 1 (d+1) n (by omega) hcount
  simpa only [Nat.cast_one,mul_one,Nat.add_sub_cancel] using h


-- @@ L26-26 verbatim
end EulerGevrey


-- @@ L28-28 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L30-30 verbatim
open EulerGevrey EulerPacketProfileRecursion


-- @@ L32-33 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  {q d e : ℕ} {R A : ℝ}


-- @@ L35-38 verbatim
theorem WordBound.absorb_amplitude (hG : G.WordBound q R A d) (hA : 0 ≤ A) (hAR : A ≤ R) :
    G.WordBound q R 1 (d+1) := by
  intro n
  simpa only [one_mul] using (hG n).trans (amplitude_absorbed A R hA hAR d n)


-- @@ L40-42 verbatim
theorem WordBound.absorb_amplitude_to (hG : G.WordBound q R A d)
    (hR : 1 ≤ R) (hA : 0 ≤ A) (hAR : A ≤ R) (hde : d + 1 ≤ e) : G.WordBound q R 1 e :=
  (hG.absorb_amplitude hA hAR).mono_shift hR zero_le_one hde


-- @@ L44-44 verbatim
end EulerPacketCylinderField.Field
