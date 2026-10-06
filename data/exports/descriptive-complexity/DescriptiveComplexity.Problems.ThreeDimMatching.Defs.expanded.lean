/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Vocabulary
import DescriptiveComplexity.Interpretation


-- @@ L9-32 verbatim
/-!
# 3-dimensional matching: definition

3-DIMENSIONAL MATCHING ([Karp 1972][karp1972reducibility]): given three
marked classes and a set of triples, one element from each class, is there a
set of triples covering every marked element **exactly once**?

The vocabulary `FirstOrder.Language.tripleSys` carries three unary marks
`xEl`, `yEl`, `zEl` and one ternary relation `trip`. A yes-instance is one
admitting a *matching* (`DescriptiveComplexity.IsMatchingOn`): a sub-relation of
`trip`, inside the three classes, that covers each marked element exactly
once. Nothing asks the three classes to be disjoint or to exhaust the
universe: elements outside them ride along, and the reduction of
`DescriptiveComplexity.Problems.ThreeDimMatching.Hardness` produces disjoint ones
anyway.

Perfect matchings force the three classes to have the same size, which is why
the problem is the tripartite form of Exact Cover with sets of size three, and
why it is the natural source of the exact-cover family.
-/

/- The language of triple systems lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/

-- @@ L33-33 verbatim
namespace FirstOrder


-- @@ L35-35 verbatim
namespace Language


-- @@ L37-47 verbatim
/-- The relational language of triple systems: three marked classes and a
ternary relation. -/
fo_language tripleSys with ts where
  /-- `xEl a`: `a` belongs to the first class. -/
  xEl : 1
  /-- `yEl a`: `a` belongs to the second class. -/
  yEl : 1
  /-- `zEl a`: `a` belongs to the third class. -/
  zEl : 1
  /-- `trip a b c`: `(a, b, c)` is one of the available triples. -/
  trip : 3


-- @@ L49-49 verbatim
end Language


-- @@ L51-51 verbatim
end FirstOrder


-- @@ L53-53 verbatim
namespace DescriptiveComplexity


-- @@ L55-55 verbatim
open FirstOrder


-- @@ L57-57 verbatim
open Language Structure


-- @@ L59-59 verbatim
/-! ### The shorthands of the vocabulary -/


-- @@ L61-61 verbatim
section Shorthands


-- @@ L63-63 verbatim
variable {A : Type} [Language.tripleSys.Structure A]


-- @@ L65-65 verbatim
fo_predicates Language.tripleSys ts


-- @@ L67-67 verbatim
end Shorthands


-- @@ L69-69 verbatim
/-! ### Matchings -/


-- @@ L71-71 verbatim
section Matching


-- @@ L73-73 verbatim
variable {A : Type}


-- @@ L75-83 verbatim
/-- A **matching**: a set of triples, taken from `T` and lying in the three
classes, covering every marked element exactly once. -/
def IsMatchingOn (X Y Z : A → Prop) (T : A → A → A → Prop) (M : A → A → A → Prop) : Prop :=
  (∀ x y z, M x y z → T x y z ∧ X x ∧ Y y ∧ Z z) ∧
    (∀ x, X x → ∃ y z, M x y z) ∧ (∀ y, Y y → ∃ x z, M x y z) ∧
    (∀ z, Z z → ∃ x y, M x y z) ∧
    (∀ x y z y' z', M x y z → M x y' z' → y = y' ∧ z = z') ∧
    (∀ x y z x' z', M x y z → M x' y z' → x = x' ∧ z = z') ∧
    ∀ x y z x' y', M x y z → M x' y' z → x = x' ∧ y = y'


-- @@ L85-85 verbatim
end Matching


-- @@ L87-87 verbatim
/-! ### The problem -/


-- @@ L89-89 verbatim
section Problem


-- @@ L91-91 verbatim
variable (A : Type) [Language.tripleSys.Structure A]


-- @@ L93-97 verbatim
/-- A triple system is a yes-instance when some subset of its triples covers
each marked element exactly once. -/
def HasThreeDimMatching : Prop :=
  Finite A ∧ ∃ M : A → A → A → Prop,
    IsMatchingOn (TSXEl (A := A)) TSYEl TSZEl TSTrip M


-- @@ L99-99 verbatim
end Problem


-- @@ L101-101 verbatim
section Iso


-- @@ L103-103 verbatim
variable {A B : Type} [Language.tripleSys.Structure A] [Language.tripleSys.Structure B]


-- @@ L105-134 verbatim
private theorem hasThreeDimMatching_of_iso (e : A ≃[Language.tripleSys] B)
    (h : HasThreeDimMatching A) : HasThreeDimMatching B := by
  obtain ⟨hfin, M, hsub, hx, hy, hz, hux, huy, huz⟩ := h
  have hX : ∀ a : A, TSXEl a ↔ TSXEl (e a) := fun a => relMap_equiv₁ e tsXEl a
  have hY : ∀ a : A, TSYEl a ↔ TSYEl (e a) := fun a => relMap_equiv₁ e tsYEl a
  have hZ : ∀ a : A, TSZEl a ↔ TSZEl (e a) := fun a => relMap_equiv₁ e tsZEl a
  have hT : ∀ a b c : A, TSTrip a b c ↔ TSTrip (e a) (e b) (e c) := fun a b c =>
    relMap_equiv₃ e tsTrip a b c
  refine ⟨e.toEquiv.finite_iff.mp hfin,
    fun x y z => M (e.symm x) (e.symm y) (e.symm z), fun x y z hm => ?_, fun x hx' => ?_,
    fun y hy' => ?_, fun z hz' => ?_, fun x y z y' z' h₁ h₂ => ?_,
    fun x y z x' z' h₁ h₂ => ?_, fun x y z x' y' h₁ h₂ => ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hsub _ _ _ hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using (hT _ _ _).mp h₁
    · simpa using (hX _).mp h₂
    · simpa using (hY _).mp h₃
    · simpa using (hZ _).mp h₄
  · obtain ⟨y, z, hyz⟩ := hx (e.symm x) ((hX _).mpr (by simpa using hx'))
    exact ⟨e y, e z, by simpa using hyz⟩
  · obtain ⟨x, z, hxz⟩ := hy (e.symm y) ((hY _).mpr (by simpa using hy'))
    exact ⟨e x, e z, by simpa using hxz⟩
  · obtain ⟨x, y, hxy⟩ := hz (e.symm z) ((hZ _).mpr (by simpa using hz'))
    exact ⟨e x, e y, by simpa using hxy⟩
  · obtain ⟨h₃, h₄⟩ := hux _ _ _ _ _ h₁ h₂
    exact ⟨by simpa using congrArg e h₃, by simpa using congrArg e h₄⟩
  · obtain ⟨h₃, h₄⟩ := huy _ _ _ _ _ h₁ h₂
    exact ⟨by simpa using congrArg e h₃, by simpa using congrArg e h₄⟩
  · obtain ⟨h₃, h₄⟩ := huz _ _ _ _ _ h₁ h₂
    exact ⟨by simpa using congrArg e h₃, by simpa using congrArg e h₄⟩


-- @@ L136-139 verbatim
/-- Having a 3-dimensional matching is isomorphism-invariant. -/
theorem hasThreeDimMatching_iso (e : A ≃[Language.tripleSys] B) :
    HasThreeDimMatching A ↔ HasThreeDimMatching B :=
  ⟨hasThreeDimMatching_of_iso e, hasThreeDimMatching_of_iso e.symm⟩


-- @@ L141-141 verbatim
end Iso


-- @@ L143-147 verbatim
/-- 3-DIMENSIONAL MATCHING, as a problem on triple systems: do some of the
triples cover every marked element exactly once? -/
def ThreeDimMatching : DecisionProblem Language.tripleSys where
  Holds := fun A inst => @HasThreeDimMatching A inst
  iso_invariant := fun e => hasThreeDimMatching_iso e


-- @@ L149-149 verbatim
end DescriptiveComplexity
