/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Hierarchy


-- @@ L8-40 verbatim
/-!
# Completeness without a class: the degree of a problem

Every completeness result of this library measures a problem against a class
*defined by a logic*. The same machinery supports a second, orthogonal notion,
at almost no cost: completeness for the degree of a fixed *problem*, with no
logic anywhere. “GI-complete” – complete for the degree of Graph Isomorphism
(`DescriptiveComplexity.DigraphIso`) – is the standard example, and the reason
this file exists.

`DescriptiveComplexity.ComplexityClass.below Q₀` is the downward closure of a
fixed relational problem `Q₀` under ordered first-order reductions, as a bona
fide `DescriptiveComplexity.ComplexityClass`: membership is “reduces to `Q₀`”,
closed under reductions by transitivity, and hardness is the same cofinal
hardness (`DescriptiveComplexity.CofinalHard`) every other class of the library
uses – it is parameterized by an arbitrary membership predicate, so nothing has
to be reproved. `(below Q₀).Complete P` then unfolds to “`P` is `Q₀`-complete”,
and `DescriptiveComplexity.ComplexityClass.complete_below_iff` states it in the
form one uses: `P` reduces to `Q₀` and `Q₀` reduces back to `P`.

Two sanity checks come with the construction:

* the class only depends on the *degree* of `Q₀`, not on `Q₀` itself
  (`DescriptiveComplexity.ComplexityClass.below_congr`);
* a class with a complete problem *is* the degree of that problem
  (`DescriptiveComplexity.ComplexityClass.eq_below_of_complete`), so “`Q₀`-hardness is
  `𝒞`-hardness” stops being folklore. The statement takes the class's own
  hardness-is-cofinal-hardness equation as a hypothesis, which is `Iff.rfl` for
  every class built by `DescriptiveComplexity.ComplexityClass.ofMem`, and the
  non-relativized reduction as its other hypothesis: a class's own hardness
  discharge delivers one, while `DescriptiveComplexity.cofinalHard_iff` on its
  own yields only the relativized `≤ʳᶠᵒ[≤]`.
-/


-- @@ L42-42 verbatim
namespace DescriptiveComplexity


-- @@ L44-44 verbatim
open FirstOrder


-- @@ L46-46 verbatim
open Language


-- @@ L48-48 verbatim
/-! ### Cofinal hardness only depends on the membership predicate -/


-- @@ L50-59 verbatim
/-- Cofinal hardness is congruent in its membership predicate: two collections
with the same problems have the same hard problems. This is what makes the
degree construction below independent of the *presentation* of a class. -/
theorem CofinalHard.congr_mem
    {Mem₁ Mem₂ : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    (h : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q : DecisionProblem L₀), Mem₁ Q ↔ Mem₂ Q)
    {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    CofinalHard Mem₁ P ↔ CofinalHard Mem₂ P :=
  ⟨fun hP _ _ S hS _ _ Q hQ => hP S hS Q ((h Q).mpr hQ),
    fun hP _ _ S hS _ _ Q hQ => hP S hS Q ((h Q).mp hQ)⟩


-- @@ L61-61 verbatim
/-! ### The degree of a problem -/


-- @@ L63-63 verbatim
namespace ComplexityClass


-- @@ L65-65 verbatim
variable {L₀ : Language.{0, 0}} [L₀.IsRelational]


-- @@ L67-80 verbatim
/-- **The degree of a problem**: the problems that (ordered) first-order reduce
to `Q₀`, as a complexity class. Membership is closed under reductions by
transitivity of reductions, and hardness is cofinal hardness for that
membership, exactly as in the logically defined classes.

`(below Q₀).Complete P` is then literally “`P` is `Q₀`-complete”; see
`DescriptiveComplexity.ComplexityClass.complete_below_iff`. -/
noncomputable def below (Q₀ : DecisionProblem L₀) : ComplexityClass :=
  .ofMem (fun P => Nonempty (P ≤ᶠᵒ[≤] Q₀))
    (fun f h => h.map fun g => f.trans_ordered g)
    (fun f h => h.map fun g => f.trans g)
    (fun hfin =>
      ⟨fun h => h.map fun g => g.congrSource hfin,
        fun h => h.map fun g => g.congrSource fun A _ _ => (hfin A).symm⟩)


-- @@ L82-82 verbatim
variable {L : Language.{0, 0}} [L.IsRelational] {Q₀ : DecisionProblem L₀}


-- @@ L84-87 verbatim
@[simp]
theorem mem_below_iff (P : DecisionProblem L) :
    P ∈ below Q₀ ↔ Nonempty (P ≤ᶠᵒ[≤] Q₀) :=
  Iff.rfl


-- @@ L89-96 verbatim
/-- Hardness for a degree, spelled out: everything reducing to `Q₀` reduces to
`P`. (An instance of `DescriptiveComplexity.cofinalHard_iff`, whose relativized
conclusion `≤ʳᶠᵒ[≤]` is what cofinal hardness yields in general.) -/
theorem hard_below_iff (P : DecisionProblem L) :
    (below Q₀).Hard P ↔
      ∀ {L' : Language.{0, 0}} [L'.IsRelational] (Q : DecisionProblem L'),
        Nonempty (Q ≤ᶠᵒ[≤] Q₀) → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P


-- @@ L98-100 verbatim
/-- A problem belongs to its own degree. -/
theorem mem_below_self (Q₀ : DecisionProblem L₀) : Q₀ ∈ below Q₀ :=
  ⟨(FOReduction.refl Q₀).toOrdered⟩


-- @@ L102-105 verbatim
/-- A problem is hard for its own degree: everything reducing to it reduces to
it. -/
theorem hard_below_self (Q₀ : DecisionProblem L₀) : (below Q₀).Hard Q₀ :=
  (hard_below_iff Q₀).mpr fun _ h => ⟨h.some.toRel⟩


-- @@ L107-112 verbatim
/-- **A problem is complete for its own degree** – the statement that makes
`below` the right construction.
Registered in the Lax archive as
[`Lax604544.DegreeOfAProblem.below_complete_self`](https://laxarchive.org/lax-604544/Lax604544.DegreeOfAProblem.html#s-Lax604544.DegreeOfAProblem.below_complete_self). -/
theorem below_complete_self (Q₀ : DecisionProblem L₀) : (below Q₀).Complete Q₀ :=
  ⟨mem_below_self Q₀, hard_below_self Q₀⟩


-- @@ L114-124 verbatim
/-- **`Q₀`-completeness is mutual reducibility**: `P` is complete for the degree
of `Q₀` exactly when `P` reduces to `Q₀` and `Q₀` reduces back to `P`. The
backward reduction is the relativized `≤ʳᶠᵒ[≤]`, which is what hardness
delivers and what a spanning problem needs.
Registered in the Lax archive as
[`Lax604544.DegreeOfAProblem.complete_below_iff`](https://laxarchive.org/lax-604544/Lax604544.DegreeOfAProblem.html#s-Lax604544.DegreeOfAProblem.complete_below_iff). -/
theorem complete_below_iff (P : DecisionProblem L) :
    (below Q₀).Complete P ↔ Nonempty (P ≤ᶠᵒ[≤] Q₀) ∧ Nonempty (Q₀ ≤ʳᶠᵒ[≤] P) := by
  refine ⟨fun h => ⟨h.mem, (hard_below_iff P).mp h.hard Q₀ (mem_below_self Q₀)⟩,
    fun ⟨hmem, hhard⟩ => ⟨hmem, (hard_below_iff P).mpr fun Q hQ => ?_⟩⟩
  exact ⟨hQ.some.toRel.trans hhard.some⟩


-- @@ L126-136 verbatim
/-- The degree only depends on the *degree*: mutually reducible problems have
the same downward closure.
Registered in the Lax archive as
[`Lax604544.DegreeOfAProblem.below_congr`](https://laxarchive.org/lax-604544/Lax604544.DegreeOfAProblem.html#s-Lax604544.DegreeOfAProblem.below_congr). -/
theorem below_congr {L₁ : Language.{0, 0}} [L₁.IsRelational] {Q₁ : DecisionProblem L₁}
    (h₀ : Nonempty (Q₀ ≤ᶠᵒ[≤] Q₁)) (h₁ : Nonempty (Q₁ ≤ᶠᵒ[≤] Q₀)) :
    below Q₀ = below Q₁ := by
  have hMem : ∀ {L' : Language.{0, 0}} [L'.IsRelational] (P : DecisionProblem L'),
      (below Q₀).Mem P ↔ (below Q₁).Mem P := fun P =>
    ⟨fun h => ⟨h.some.trans h₀.some⟩, fun h => ⟨h.some.trans h₁.some⟩⟩
  exact ext hMem fun P => CofinalHard.congr_mem hMem P


-- @@ L138-159 verbatim
/-- **A class with a complete problem is that problem's degree**: `𝒞 = below Q₀`
whenever `Q₀` is `𝒞`-complete in the strong sense that every member of `𝒞`
reduces to it by a *non-relativized* ordered reduction – which is what a class's
own hardness discharge (`DescriptiveComplexity.sat_hard_of_sigmaSODefinable` and
its siblings) produces.

The last hypothesis says that `𝒞` reads hardness as cofinal hardness for its own
members; it is `fun _ => Iff.rfl` for every class built by
`DescriptiveComplexity.ComplexityClass.ofMem`, hence for every logically defined
class of this library. -/
theorem eq_below_of_complete {C : ComplexityClass} (Q₀ : DecisionProblem L₀) (hmem : Q₀ ∈ C)
    (hred : ∀ {L' : Language.{0, 0}} [L'.IsRelational] (P : DecisionProblem L'),
      P ∈ C → Nonempty (P ≤ᶠᵒ[≤] Q₀))
    (hhard : ∀ {L' : Language.{0, 0}} [L'.IsRelational] (P : DecisionProblem L'),
      C.Hard P ↔ CofinalHard C.Mem P) :
    C = below Q₀ := by
  have hMem : ∀ {L' : Language.{0, 0}} [L'.IsRelational] (P : DecisionProblem L'),
      C.Mem P ↔ (below Q₀).Mem P := fun P =>
    ⟨fun h => hred P h, fun h => C.mem_of_orderedReduction h.some hmem⟩
  refine ext hMem fun P => ?_
  rw [hhard P]
  exact CofinalHard.congr_mem hMem P


-- @@ L161-161 verbatim
end ComplexityClass


-- @@ L163-163 verbatim
end DescriptiveComplexity
