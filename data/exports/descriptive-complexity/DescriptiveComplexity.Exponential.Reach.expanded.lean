/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Copies
import DescriptiveComplexity.Exponential.Class
import DescriptiveComplexity.ImmermanSzelepcsenyi
import DescriptiveComplexity.PSpace


-- @@ L11-39 verbatim
/-!
# An SO(TC) walk is reachability on an exponential expansion

The construction that connects the exponential classes to the polynomial ones:
**an `DescriptiveComplexity.SOTCSpec` is the graph REACH reads on the expansion
whose points are its states**. Compare the two definitions, which are the same
sentence up to the name of the universe:

```
SOTCSpec.Accepts A = ∃ ρ σ, spec.IsSrc ρ ∧ spec.IsTgt σ ∧ Relation.ReflTransGen spec.Step ρ σ
Reachable       M = ∃ s t, SGSource s   ∧ SGTarget t   ∧ Relation.ReflTransGen SGEdge     s t
```

So the expansion `DescriptiveComplexity.SOTCSpec.toExp` takes `Tag := Unit`, no
domain restriction, the block of the specification, and the vocabulary of
graphs with marked sources and targets, defining the edge symbol by the
transition sentence and the two marks by the endpoint sentences. Its points are
the states (`DescriptiveComplexity.SOTCSpec.toExpEquiv`) and REACH holds of it
exactly when the walk accepts
(`DescriptiveComplexity.SOTCSpec.reachable_toExp_iff`).

Since REACH is in every class from NL up, this gives at once

* `PSPACE ⊆ NL.exp` and `PSPACE ⊆ PTIME.exp = EXPTIME`,

the inclusion that starts the tower above PSPACE. Read on the definitions the
second one is **SO(TC) ⊆ SO(LFP)** – a transitive closure is a least fixed
point – which is the second-order shadow of `NL ⊆ PTIME`.
-/


-- @@ L41-41 verbatim
namespace DescriptiveComplexity


-- @@ L43-43 verbatim
open FirstOrder


-- @@ L45-45 verbatim
open Language Structure


-- @@ L47-47 verbatim
namespace SOTCSpec


-- @@ L49-49 verbatim
variable {L : Language.{0, 0}} (spec : SOTCSpec L)


-- @@ L51-51 verbatim
/-! ### The expansion of a specification -/


-- @@ L53-70 verbatim
/-- **The expansion whose points are the states of the walk**: no tags, no
domain restriction, and the three sentences of the specification defining the
three symbols of the vocabulary of marked graphs. -/
def toExp : ExpExpansion L where
  Tag := Unit
  B := spec.B
  E := Language.stGraph
  dom _ := ⊤
  relSentence {n} r _ :=
    match n, r with
    | _, .edge => (spec.B.twoLHom (L.sum Language.order)).onSentence spec.step
    | _, .source => (spec.B.oneLHom (L.sum Language.order)).onSentence spec.src
    | _, .target => (spec.B.oneLHom (L.sum Language.order)).onSentence spec.tgt
  dom_nonempty := by
    intro A _ _ _ _
    refine ⟨(), spec.B.botAssign A, ?_⟩
    let := spec.B.structure₁ (L := L.sum Language.order) (spec.B.botAssign A)
    exact Formula.realize_top.mpr trivial


-- @@ L72-72 verbatim
variable (A : Type) [L.Structure A] [LinearOrder A]


-- @@ L74-79 verbatim
/-- The expanded structure of `DescriptiveComplexity.SOTCSpec.toExp`, at the
vocabulary of marked graphs – equal to the expansion's own by definition, but
not syntactically, so instance search has to be handed it. -/
@[instance_reducible]
def toExpStructure : Language.stGraph.Structure (spec.toExp.Map A) :=
  spec.toExp.mapStructure A


-- @@ L81-85 verbatim
/-- The domain of `DescriptiveComplexity.SOTCSpec.toExp` is the whole space of
tagged assignments: its domain sentence is `⊤`. -/
theorem domHolds_toExp (p : spec.toExp.Point A) : ExpExpansion.DomHolds p := by
  let := spec.toExp.B.structure₁ (L := L.sum Language.order) p.2
  exact Formula.realize_top.mpr trivial


-- @@ L87-92 verbatim
/-- **The points of the expansion are the states of the walk.** -/
def toExpEquiv : spec.toExp.Map A ≃ spec.State A where
  toFun x := x.1.2
  invFun ρ := ⟨((), ρ), spec.domHolds_toExp A ((), ρ)⟩
  left_inv _ := ExpExpansion.map_ext rfl rfl
  right_inv _ := rfl


-- @@ L94-94 verbatim
/-! ### The three symbols -/


-- @@ L96-96 verbatim
variable {A}


-- @@ L98-103 verbatim
/-- **The edge symbol is the transition sentence.** -/
theorem sgEdge_toExp (x y : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    SGEdge x y ↔ spec.Step x.1.2 y.1.2 :=
  SOBlock.realize_twoLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x, y] : Fin 2 → spec.toExp.Map A) i).1.2) spec.step


-- @@ L105-110 verbatim
/-- **The marked sources are the starting states.** -/
theorem sgSource_toExp (x : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    SGSource x ↔ spec.IsSrc x.1.2 :=
  SOBlock.realize_oneLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x] : Fin 1 → spec.toExp.Map A) i).1.2) spec.src


-- @@ L112-117 verbatim
/-- **The marked targets are the accepting states.** -/
theorem sgTarget_toExp (x : spec.toExp.Map A) :
    letI := spec.toExpStructure A
    SGTarget x ↔ spec.IsTgt x.1.2 :=
  SOBlock.realize_oneLHom (L := L.sum Language.order) spec.B
    (fun i => ((![x] : Fin 1 → spec.toExp.Map A) i).1.2) spec.tgt


-- @@ L119-119 verbatim
/-! ### Acceptance is reachability -/


-- @@ L121-128 verbatim
private theorem reach_of_reflTransGen :
    letI := spec.toExpStructure A
    ∀ {s t : spec.toExp.Map A}, Relation.ReflTransGen SGEdge s t → spec.Reach s.1.2 t.1.2 := by
  let := spec.toExpStructure A
  intro s t h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ((spec.sgEdge_toExp _ _).mp hbc)


-- @@ L130-138 verbatim
private theorem reflTransGen_of_reach :
    letI := spec.toExpStructure A
    ∀ {ρ σ : spec.State A}, spec.Reach ρ σ →
      Relation.ReflTransGen SGEdge ((spec.toExpEquiv A).symm ρ) ((spec.toExpEquiv A).symm σ) := by
  let := spec.toExpStructure A
  intro ρ σ h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ((spec.sgEdge_toExp _ _).mpr hbc)


-- @@ L140-140 verbatim
variable (A)


-- @@ L142-154 verbatim
/-- **The walk accepts exactly when REACH holds of the expansion.** -/
theorem reachable_toExp_iff :
    letI := spec.toExpStructure A
    Reachable (spec.toExp.Map A) ↔ spec.Accepts A := by
  let := spec.toExpStructure A
  constructor
  · rintro ⟨s, t, hs, ht, hpath⟩
    exact ⟨s.1.2, t.1.2, (spec.sgSource_toExp s).mp hs, (spec.sgTarget_toExp t).mp ht,
      spec.reach_of_reflTransGen hpath⟩
  · rintro ⟨ρ, σ, hρ, hσ, hreach⟩
    exact ⟨(spec.toExpEquiv A).symm ρ, (spec.toExpEquiv A).symm σ,
      (spec.sgSource_toExp _).mpr hρ, (spec.sgTarget_toExp _).mpr hσ,
      spec.reflTransGen_of_reach hreach⟩


-- @@ L156-156 verbatim
end SOTCSpec


-- @@ L158-158 verbatim
/-! ### Polynomial space sits inside every exponential class above NL -/


-- @@ L160-160 verbatim
variable {L : Language.{0, 0}} [L.IsRelational]


-- @@ L162-172 verbatim
/-- **An SO(TC) definable problem is definable over an expanded universe by
REACH**: the walk is the graph the expansion draws, so any class containing
REACH contains the problem one exponential up. -/
theorem SOTCDefinable.expDefinable {C : ComplexityClass} (hreach : REACH ∈ C)
    {P : DecisionProblem L} (h : SOTCDefinable P) : ExpDefinable C P := by
  obtain ⟨spec, hspec⟩ := h
  let hinst : ∀ (A : Type) [L.Structure A] [LinearOrder A],
      Language.stGraph.Structure (spec.toExp.Map A) := fun A => spec.toExpStructure A
  refine ⟨spec.toExp, REACH, hreach, ?_⟩
  intro A _ _ _ _
  exact (hspec A).trans (spec.reachable_toExp_iff A).symm


-- @@ L174-180 verbatim
/-- **`PSPACE ⊆ NL.exp`**: polynomial space is nondeterministic logarithmic
space read one exponential up. This is the inclusion of the succinctness
theorem at the level where the library independently knows the answer, and so
the check that `DescriptiveComplexity.ComplexityClass.exp` computes the
intended class. -/
theorem PSPACE_subset_NL_exp : PSPACE ⊆ NL.exp :=
  fun _ _ P h => SOTCDefinable.expDefinable reach_mem_NL ((mem_PSPACE_iff P).mp h)


-- @@ L182-186 verbatim
/-- **`PSPACE ⊆ PTIME.exp`**, i.e., `PSPACE ⊆ EXPTIME` once the class is named
(`DescriptiveComplexity.PSPACE_subset_EXPTIME`). Read on the definitions it is
**SO(TC) ⊆ SO(LFP)**, the second-order shadow of `NL ⊆ PTIME`. -/
theorem PSPACE_subset_PTIME_exp : PSPACE ⊆ PTIME.exp :=
  fun _ _ P h => SOTCDefinable.expDefinable reach_mem_PTIME ((mem_PSPACE_iff P).mp h)


-- @@ L188-188 verbatim
end DescriptiveComplexity
