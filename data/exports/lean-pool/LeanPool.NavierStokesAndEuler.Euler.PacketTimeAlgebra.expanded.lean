/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul


-- @@ L14-14 verbatim
/-! Genuine within-interval time derivatives commute with the finite packet algebra. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerPacketCylinderField.TimeDerivative


-- @@ L23-23 verbatim
open Set Finset EulerPacketProfileRecursion EulerVolterraConvolution


-- @@ L25-28 verbatim
variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T}
  {raw raw' next next' : VectorField}
  {G : Field P T raw} {G' : Field P T raw'}
  {H : Field P T next} {H' : Field P T next'}


-- @@ L30-32 verbatim
theorem zero : TimeDerivative hT (Field.zero P T) (Field.zero P T) := by
  intro t
  exact hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (0 : EulerLiftedGradientSpace.LiftL2 P)


-- @@ L34-37 verbatim
theorem add (hG : TimeDerivative hT G G') (hH : TimeDerivative hT H H') :
    TimeDerivative hT (G.add H) (G'.add H') := by
  intro t
  exact (hG t).add (hH t)


-- @@ L39-42 verbatim
theorem smul (hG : TimeDerivative hT G G') (c : ℝ) :
    TimeDerivative hT (G.smul c) (G'.smul c) := by
  intro t
  exact (hG t).const_smul c


-- @@ L44-53 verbatim
theorem finsetSum {ι : Type*} (s : Finset ι) (f f' : ι → VectorField)
    (G : ∀ i, Field P T (f i)) (G' : ∀ i, Field P T (f' i))
    (hG : ∀ i ∈ s, TimeDerivative hT (G i) (G' i)) :
    TimeDerivative hT (Field.finsetSum s f G) (Field.finsetSum s f' G') := by
  intro t
  have h := HasDerivWithinAt.fun_sum (u := s) (fun i hi => hG i hi t)
  change HasDerivWithinAt (fun r => (∑ i ∈ s, (G i).path) (projIcc 0 T hT r))
    ((∑ i ∈ s, (G' i).path) t) (Icc (0 : ℝ) T) t
  simp only [ContinuousMap.sum_apply]
  exact h


-- @@ L55-59 verbatim
theorem of_path_eq (hG : TimeDerivative hT G G')
    (h : H.path = G.path) (h' : H'.path = G'.path) : TimeDerivative hT H H' := by
  unfold TimeDerivative
  rw [h,h']
  exact hG


-- @@ L61-61 verbatim
end EulerPacketCylinderField.TimeDerivative
