/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.Distillation


-- @@ L8-33 verbatim
/-!
# Model Distillation Verification Example

This file demonstrates **verified model distillation** using LeanCert's
interval arithmetic infrastructure.

## The Scenario

In AI deployment, we often need to:
1. Train a large "Teacher" model for accuracy
2. Compress it into a smaller "Student" model for efficiency
3. **Verify** that the Student behaves similarly to the Teacher

LeanCert can formally prove that |Teacher(x) - Student(x)| ≤ ε for ALL inputs
in a domain - not just sampled points, but a mathematical guarantee.

## Example Networks

We define two simple 2→2→1 networks and verify their outputs differ by at most
ε = 3 on the input domain [0, 1]².

## Main Results

* `distillationCheck_passes` - The computable check returns true
* `distillation_certificate` - Formal proof of bounded difference
-/


-- @@ L35-35 verbatim
namespace LeanCert.Examples.ML.Distillation


-- @@ L37-37 verbatim
open LeanCert.Core

-- @@ L38-38 verbatim
open LeanCert.ML

-- @@ L39-39 verbatim
open LeanCert.ML.Distillation

-- @@ L40-40 verbatim
open LeanCert.Engine.IntervalVector


-- @@ L42-42 verbatim
/-! ### Network Definitions -/


-- @@ L44-47 verbatim
/-- Layer 1: 2 inputs → 2 outputs -/
def layer1 : Layer where
  weights := [[1, 1], [1, 0]]
  bias := [0, 0]


-- @@ L49-52 verbatim
/-- Layer 2: 2 inputs → 1 output -/
def layer2 : Layer where
  weights := [[1, 1]]
  bias := [0]


-- @@ L54-56 verbatim
/-- The Teacher network -/
def teacherNet : SequentialNet where
  layers := [layer1, layer2]


-- @@ L58-60 verbatim
/-- The Student network -/
def studentNet : SequentialNet where
  layers := [layer1, layer2]


-- @@ L62-62 verbatim
/-! ### Well-formedness Proofs -/


-- @@ L64-67 verbatim
theorem layer1_wf : layer1.WellFormed := by
  constructor
  · intro row hrow; simp only [layer1, Layer.inputDim] at hrow ⊢; fin_cases hrow <;> rfl
  · rfl


-- @@ L69-72 verbatim
theorem layer2_wf : layer2.WellFormed := by
  constructor
  · intro row hrow; simp only [layer2, Layer.inputDim] at hrow ⊢; fin_cases hrow; rfl
  · rfl


-- @@ L74-76 verbatim
theorem teacherNet_wf : teacherNet.WellFormed 2 := by
  simp only [SequentialNet.WellFormed, teacherNet, SequentialNet.LayersWellFormed]
  exact ⟨layer1_wf, rfl, layer2_wf, rfl, trivial⟩


-- @@ L78-80 verbatim
theorem studentNet_wf : studentNet.WellFormed 2 := by
  simp only [SequentialNet.WellFormed, studentNet, SequentialNet.LayersWellFormed]
  exact ⟨layer1_wf, rfl, layer2_wf, rfl, trivial⟩


-- @@ L82-82 verbatim
/-! ### Input Domain -/


-- @@ L84-86 verbatim
/-- Create an interval from rational bounds -/
def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := -53) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec


-- @@ L88-90 verbatim
/-- Input domain: [0, 1]² -/
def inputDomain : IntervalVector :=
  [mkInterval 0 1, mkInterval 0 1]


-- @@ L92-92 verbatim
/-! ### Equivalence Check -/


-- @@ L94-95 verbatim
/-- Tolerance for distillation verification -/
def epsilon : ℚ := 3


-- @@ L97-99 verbatim
/-- The computable certificate -/
def distillationCheck : Bool :=
  checkEquivalence teacherNet studentNet inputDomain epsilon (-53)


-- @@ L101-102 verbatim
/-- The check passes! This is verified by computation. -/
theorem distillationCheck_passes : distillationCheck = true := by native_decide


-- @@ L104-104 verbatim
/-! ### Helper Lemmas -/


-- @@ L106-113 verbatim
/-- Membership in mkInterval -/
theorem mem_mkInterval {x : ℝ} {lo hi : ℚ} (hle : lo ≤ hi)
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    x ∈ mkInterval lo hi hle prec := by
  unfold mkInterval
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  simp only [IntervalRat.mem_def]
  exact hx


-- @@ L115-115 verbatim
/-! ### The Distillation Certificate -/


-- @@ L117-154 verbatim
/-- For ANY inputs (x, y) in [0, 1]², Teacher and Student outputs differ by at most ε = 3. -/
theorem distillation_certificate (x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    (SequentialNet.forwardInterval teacherNet inputDomain (-53)).length =
    (SequentialNet.forwardInterval studentNet inputDomain (-53)).length ∧
    ∀ i (hi_t : i < (SequentialNet.forwardInterval teacherNet inputDomain (-53)).length)
        (hi_s : i < (SequentialNet.forwardInterval studentNet inputDomain (-53)).length),
      |(SequentialNet.forwardReal teacherNet [x, y])[i]'(by
          simp only [SequentialNet.forwardReal]
          simp only [SequentialNet.forwardInterval] at hi_t hi_s
          have h := SequentialNet.forwardLength_aux teacherNet.layers [x, y] inputDomain
              (by rfl) teacherNet_wf (-53)
          have hlen : (List.foldl (fun acc l => l.forwardInterval acc (-53)) inputDomain teacherNet.layers).length = 1 := by native_decide
          omega) -
       (SequentialNet.forwardReal studentNet [x, y])[i]'(by
          simp only [SequentialNet.forwardReal]
          simp only [SequentialNet.forwardInterval] at hi_t hi_s
          have h := SequentialNet.forwardLength_aux studentNet.layers [x, y] inputDomain
              (by rfl) studentNet_wf (-53)
          have hlen : (List.foldl (fun acc l => l.forwardInterval acc (-53)) inputDomain studentNet.layers).length = 1 := by native_decide
          omega)| ≤ (epsilon : ℝ) := by
  -- Build domain membership
  have hdom : [x, y].length = inputDomain.length := rfl
  have hmem : ∀ i (hi : i < inputDomain.length), [x, y][i]'(hdom ▸ hi) ∈ inputDomain[i]'hi := by
    intro i hi
    match i with
    | 0 =>
      simp only [inputDomain, List.getElem_cons_zero]
      exact mem_mkInterval (by norm_num) ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩ (-53)
    | 1 =>
      simp only [inputDomain, List.getElem_cons_succ, List.getElem_cons_zero]
      exact mem_mkInterval (by norm_num) ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩ (-53)
    | n + 2 =>
      simp only [inputDomain, List.length_cons, List.length_nil] at hi
      omega
  -- Apply the golden theorem
  exact verify_equivalence teacherNet studentNet inputDomain epsilon (-53)
    [x, y] (by norm_num) teacherNet_wf studentNet_wf hdom hmem distillationCheck_passes


-- @@ L156-169 verbatim
/-! ### Interpretation

The theorem `distillation_certificate` proves that for ANY (x, y) ∈ [0, 1]²:
  |Teacher(x,y) - Student(x,y)| ≤ 3

This bound arises from interval arithmetic conservatism: the analysis computes
bounds on Teacher and Student outputs independently, then subtracts them.

## Applications

- **Deployment Safety**: Verify compressed models before deployment
- **Regulatory Compliance**: Provide machine-checked certificates
- **CI/CD Integration**: Automatically verify model equivalence in pipelines
-/


-- @@ L171-171 verbatim
end LeanCert.Examples.ML.Distillation
