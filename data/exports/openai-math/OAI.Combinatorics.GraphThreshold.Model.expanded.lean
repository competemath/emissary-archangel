import Mathlib.Data.Fintype.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Analysis.SpecialFunctions.Log.Basic


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
universe u


-- @@ L13-13 verbatim
namespace LeanBlast.SecondKahnKalai


-- @@ L15-17 verbatim
def bernoulliWeight {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (W : Finset X) : ℝ :=
  ∏ x, if x ∈ W then p else 1 - p


-- @@ L19-21 verbatim
def bernoulliExpectation {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (f : Finset X → ℝ) : ℝ :=
  ∑ W, bernoulliWeight p W * f W


-- @@ L23-26 verbatim
def bernoulliProbability {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (P : Finset X → Prop) : ℝ := by
  classical
  exact ∑ W, if P W then bernoulliWeight p W else 0


-- @@ L28-29 verbatim
/-- The unordered non-loop edges of the complete graph on `n` vertices. -/
abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬e.IsDiag}


-- @@ L31-33 verbatim
/-- A set of edges, interpreted as an ordinary graph on all `n` vertices. -/
def graphOfEdges {n : ℕ} (W : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Subtype.val '' (W : Set (Edge n)))


-- @@ L35-36 verbatim
/-- The number of unordered edges, each counted once. -/
def edgeCount {V : Type u} (H : SimpleGraph V) : ℕ := Nat.card H.edgeSet


-- @@ L38-41 verbatim
/-- Expected number of actual unlabelled non-induced copies in `G(n,p)`. -/
def expectedCopies {V : Type u} (n : ℕ) (p : ℝ) (H : SimpleGraph V) : ℝ :=
  bernoulliExpectation p (fun W : Finset (Edge n) =>
    ((graphOfEdges W).copyCount H : ℝ))


-- @@ L43-47 verbatim
/-- Probability that `G(n,p)` contains at least one non-induced copy. -/
def containmentProbability {V : Type u} (n : ℕ) (p : ℝ)
    (H : SimpleGraph V) : ℝ :=
  bernoulliProbability p (fun W : Finset (Edge n) =>
    0 < (graphOfEdges W).copyCount H)


-- @@ L49-50 verbatim
def criticalThreshold {V : Type u} (n : ℕ) (H : SimpleGraph V) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ (1 / 2 : ℝ) ≤ containmentProbability n p H}


-- @@ L52-54 verbatim
def expectationThreshold {V : Type u} (n : ℕ) (H : SimpleGraph V) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧
    ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe}


-- @@ L56-56 verbatim
def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2


-- @@ L58-63 verbatim
def SecondKahnKalaiBounds {V : Type u} (n : ℕ) (H : SimpleGraph V) : Prop :=
  criticalThreshold n H ≤
      min 1 (2048 * Real.exp 50 * expectationThreshold n H *
        (1 + logTwo (edgeCount H : ℝ))) ∧
    criticalThreshold n H ≤
      6144 * Real.exp 50 * expectationThreshold n H * logTwo (n : ℝ)


-- @@ L65-65 verbatim
end LeanBlast.SecondKahnKalai


-- @@ L67-67 verbatim
end


-- @@ L69-69 verbatim
end OAI
