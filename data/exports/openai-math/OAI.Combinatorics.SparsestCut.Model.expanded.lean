import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open scoped BigOperators


-- @@ L7-7 verbatim
namespace UniformSparsestCut


-- @@ L9-13 verbatim
structure Capacity (n : ℕ) where
  cap : Fin n → Fin n → ℝ
  nonneg : ∀ i j, 0 ≤ cap i j
  symm : ∀ i j, cap i j = cap j i
  diagonal : ∀ i, cap i i = 0


-- @@ L15-16 verbatim
def pairSum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then f i j else 0


-- @@ L18-20 verbatim
noncomputable def cutRatio {n : ℕ} (C : Capacity n) (B : Finset (Fin n)) : ℝ :=
  (∑ i ∈ B, ∑ j ∈ Bᶜ, C.cap i j) /
    ((B.card : ℝ) * ((n : ℝ) - (B.card : ℝ)))


-- @@ L22-23 verbatim
noncomputable def OPT {n : ℕ} (C : Capacity n) : ℝ :=
  sInf {r | ∃ B : Finset (Fin n), B.Nonempty ∧ B ≠ Finset.univ ∧ r = cutRatio C B}


-- @@ L25-27 verbatim
def NegativeType {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop :=
  (∃ x : Fin n → EuclideanSpace ℝ (Fin n), ∀ i j, d i j = ‖x i - x j‖ ^ 2) ∧
  ∀ i j k, d i k ≤ d i j + d j k


-- @@ L29-30 verbatim
def Feasible {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop :=
  NegativeType d ∧ pairSum d = 1


-- @@ L32-34 verbatim
noncomputable def glValue {n : ℕ} (C : Capacity n) : ℝ :=
  sInf {r | ∃ d : Fin n → Fin n → ℝ, Feasible d ∧
    r = pairSum (fun i j => C.cap i j * d i j)}


-- @@ L36-36 verbatim
end UniformSparsestCut


-- @@ L38-38 verbatim
end OAI
