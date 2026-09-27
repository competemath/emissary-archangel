/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeSupport
import LeanPool.NavierStokesAndEuler.Euler.PacketTimeAlgebra


-- @@ L14-14 verbatim
/-! Actual path and time-derivative witnesses for finite coefficient assembly. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerPacketCylinderField


-- @@ L23-23 verbatim
open Set Finset EulerPacketPointJets EulerPacketProfileRecursion EulerFiniteGrades


-- @@ L25-25 verbatim
variable {P T : ℝ} [Fact (0 < P)]


-- @@ L27-27 verbatim
namespace Field


-- @@ L29-34 verbatim
/-- Truncate family as an element of `Field P T (truncate M f n)`. -/
def truncateFamily (M : ℕ) (f : ℕ → VectorField)
    (G : ∀ i, i ≤ M → Field P T (f i)) (n : ℕ) : Field P T (truncate M f n) := by
  by_cases hn : n ≤ M
  · exact (G n hn).congr (fun _ _ _ => by rw [truncate_of_le M n f hn])
  · exact (Field.zero P T).congr (fun _ _ _ => by rw [truncate_of_gt M n f (by omega)])


-- @@ L36-41 verbatim
/-- Assemble family used in packet finite field algebra. -/
def assembleFamily (M : ℕ) (f c : ℕ → VectorField)
    (G : ∀ i, i ≤ M → Field P T (f i)) (H : ∀ i, i ≤ M → Field P T (c i)) :
    (n : ℕ) → Field P T (assemble M f c n)
  | 0 => (truncateFamily M f G 0).congr (fun _ _ _ => by simp only [assemble,shiftUp,add_zero])
  | n+1 => (truncateFamily M f G (n+1)).add (truncateFamily M c H n)


-- @@ L43-47 verbatim
/-- Evaluate family as an element of `Field P T (fieldSum M κ f)`. -/
def evaluateFamily (M : ℕ) (κ : ℝ) (f : ℕ → VectorField) (G : ∀ i, Field P T (f i)) :
    Field P T (fieldSum M κ f) :=
  (Field.finsetSum (range (M+1)) (fun i => κ^i • f i) (fun i => (G i).smul (κ^i))).congr
    (fun _ _ _ => by simp only [fieldSum,evaluate,Finset.sum_apply,Pi.smul_apply])


-- @@ L49-49 verbatim
end Field


-- @@ L51-51 verbatim
namespace TimeDerivative


-- @@ L53-53 verbatim
variable {hT : 0 ≤ T}


-- @@ L55-63 verbatim
theorem truncateFamily (M : ℕ) (f f' : ℕ → VectorField)
    (G : ∀ i, i ≤ M → Field P T (f i)) (G' : ∀ i, i ≤ M → Field P T (f' i))
    (hG : ∀ i (hi : i ≤ M), TimeDerivative hT (G i hi) (G' i hi)) (n : ℕ) :
    TimeDerivative hT (Field.truncateFamily M f G n) (Field.truncateFamily M f' G' n) := by
  by_cases hn : n ≤ M
  · simp only [Field.truncateFamily,dite_eq_left hn]
    exact hG n hn
  · simp only [Field.truncateFamily,dite_eq_right hn]
    exact zero


-- @@ L65-74 verbatim
theorem assembleFamily (M : ℕ) (f f' c c' : ℕ → VectorField)
    (G : ∀ i, i ≤ M → Field P T (f i)) (G' : ∀ i, i ≤ M → Field P T (f' i))
    (H : ∀ i, i ≤ M → Field P T (c i)) (H' : ∀ i, i ≤ M → Field P T (c' i))
    (hG : ∀ i (hi : i ≤ M), TimeDerivative hT (G i hi) (G' i hi))
    (hH : ∀ i (hi : i ≤ M), TimeDerivative hT (H i hi) (H' i hi)) (n : ℕ) :
    TimeDerivative hT (Field.assembleFamily M f c G H n) (Field.assembleFamily M f' c' G' H' n) :=
        by
  cases n with
  | zero => exact truncateFamily M f f' G G' hG 0
  | succ n => exact (truncateFamily M f f' G G' hG (n+1)).add (truncateFamily M c c' H H' hH n)


-- @@ L76-81 verbatim
theorem evaluateFamily (M : ℕ) (κ : ℝ) (f f' : ℕ → VectorField)
    (G : ∀ i, Field P T (f i)) (G' : ∀ i, Field P T (f' i))
    (hG : ∀ i, TimeDerivative hT (G i) (G' i)) :
    TimeDerivative hT (Field.evaluateFamily M κ f G) (Field.evaluateFamily M κ f' G') :=
  finsetSum (range (M+1)) (fun i => κ^i • f i) (fun i => κ^i • f' i)
    (fun i => (G i).smul (κ^i)) (fun i => (G' i).smul (κ^i)) (fun i _ => (hG i).smul (κ^i))


-- @@ L83-83 verbatim
end TimeDerivative

-- @@ L84-84 verbatim
end EulerPacketCylinderField
