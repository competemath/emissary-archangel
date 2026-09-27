/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L11-13 verbatim
/-!
# LeanPool.RlTheoryInLean.Probability.Kernel.Basic
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open MeasureTheory MeasureTheory.Measure ProbabilityTheory.Kernel ProbabilityTheory

-- @@ L18-18 verbatim
open Finset Bornology NNReal ENNReal Preorder Filter


-- @@ L20-20 verbatim
namespace ProbabilityTheory.Kernel


-- @@ L22-22 verbatim
variable {α β γ : Type*}

-- @@ L23-23 verbatim
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]


-- @@ L25-28 verbatim
/-- Iterates of a homogeneous transition kernel. -/
noncomputable def iter (κ : Kernel α α) : ℕ → Kernel α α
| 0       => Kernel.id
| (n + 1) => ((iter κ) n).comp κ


-- @@ L30-36 verbatim
instance (n : ℕ) (κ : Kernel α α) [IsMarkovKernel κ] :
  IsMarkovKernel (κ.iter n) := by
  induction n with
  | zero => simp only [iter]
            infer_instance
  | succ n ih => simp only [iter]
                 infer_instance


-- @@ L38-45 verbatim
lemma iter_comm (κ : Kernel α α) (n : ℕ) :
  κ ∘ₖ κ.iter n = κ.iter n ∘ₖ κ := by
  induction n with
  | zero => simp [iter, Kernel.id_comp]
  | succ n ih =>
    simp only [iter]
    conv_rhs => rw [← ih]
    simp [comp_assoc]


-- @@ L47-56 verbatim
lemma iter_comp (κ : Kernel α α) (m n : ℕ) :
  (κ.iter m).comp (κ.iter n) = κ.iter (m + n) := by
  induction m with
  | zero => simp [iter, Kernel.id_comp]
  | succ m ih =>
    have : m + 1 + n = (m + n) + 1 := by omega
    rw [this, iter, iter, ← ih]
    simp only [comp_assoc]
    apply congrArg
    simp [iter_comm]


-- @@ L58-58 verbatim
end ProbabilityTheory.Kernel
