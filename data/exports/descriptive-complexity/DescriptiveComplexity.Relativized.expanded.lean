/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Ordered


-- @@ L8-40 verbatim
/-!
# Relativized first-order interpretations (definable target universes)

An `DescriptiveComplexity.FOInterpretation` fixes the target universe to all of
`Tag × A^dim`. That is convenient for *subset*-style problems – a yes-witness
lives on part of the universe and junk elements sit isolated and unused – but
it cannot target a **spanning** problem such as HAMILTON CIRCUIT, where a
yes-witness (a tour) must visit *every* universe element: junk points with no
valid incident edges make every interpreted instance a no-instance.

The textbook remedy ([Immerman 1999][immerman1999descriptive]) is a **domain
formula**: the target universe is a *definable subset* of `Tag × A^dim`. This
file adds it as a layer *on top of* `FOInterpretation`, so that no existing
interpretation, reduction or problem file changes:

* `DescriptiveComplexity.RelFOInterpretation` extends `FOInterpretation` with a
  `domFormula : Tag → L.Formula (Fin dim)`;
* `DescriptiveComplexity.RelFOInterpretation.MapRel` is the interpreted structure carried by
  the subtype `{x : Tag × A^dim // domFormula holds of x}`;
* `DescriptiveComplexity.RelOrderedFOReduction` (notation `≤ʳᶠᵒ[≤]`) is the ordered reduction
  through such an interpretation, carrying the extra obligation
  `dom_nonempty` – a definable domain can be empty on a nonempty structure, so
  `Nonempty Tag` does not by itself guarantee a nonempty output;
* `DescriptiveComplexity.OrderedFOReduction.toRel` embeds an ordinary ordered reduction as a
  relativized one with `domFormula := ⊤`, the transparency of the whole-universe
  case being an isomorphism (`DescriptiveComplexity.FOInterpretation.toRelLEquiv`) rather than
  a definitional equality.

This is the hardness-side machinery of relativized reductions; it is what a
hardness proof for a spanning problem needs. Membership closure under
relativized reductions lives in `DescriptiveComplexity.FixedPointStepRel`, and is
not needed when membership is a direct second-order sentence.
-/


-- @@ L42-42 verbatim
namespace DescriptiveComplexity


-- @@ L44-44 verbatim
open FirstOrder


-- @@ L46-46 verbatim
open Language Structure


-- @@ L48-48 verbatim
variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}


-- @@ L50-58 verbatim
/-- A *relativized* tagged first-order interpretation: an ordinary
interpretation together with, for each tag, a **domain formula** on the `dim`
coordinates. The target universe is cut down to the tagged tuples whose
coordinates satisfy their tag's domain formula. -/
structure RelFOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ)
    extends FOInterpretation L L' Tag dim where
  /-- The domain formula of each tag: a tagged tuple `(t, ā)` belongs to the
  target universe iff `domFormula t` holds of `ā`. -/
  domFormula : Tag → L.Formula (Fin dim)


-- @@ L60-60 verbatim
namespace RelFOInterpretation


-- @@ L62-62 verbatim
variable (I : RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]


-- @@ L64-70 verbatim
/-- The universe of the relativized interpretation in `A`: the tagged tuples
whose coordinates satisfy their tag's domain formula. A subtype (not a `def`
of a product) so that the definable restriction is real; the `L'`-structure on
it reads its relations through `Subtype.val`, exactly as `FOInterpretation.Map`
does. -/
protected def MapRel : Type :=
  {x : Tag × (Fin dim → A) // (I.domFormula x.1).Realize x.2}


-- @@ L72-75 verbatim
/-- The `L'`-structure interpreted on the definable subset. -/
instance mapRelStructure [L'.IsRelational] : L'.Structure (I.MapRel A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1.1).Realize fun p => (xs p.1).1.2 p.2


-- @@ L77-79 verbatim
theorem relMap_mapRel [L'.IsRelational] {n : ℕ} (R : L'.Relations n) (xs : Fin n → I.MapRel A) :
    RelMap R xs ↔ (I.relFormula R fun i => (xs i).1.1).Realize fun p => (xs p.1).1.2 p.2 :=
  Iff.rfl


-- @@ L81-84 verbatim
/-- The relativized universe of a finite structure over finite tags is
finite. -/
theorem mapRel_finite [Finite Tag] [Finite A] : Finite (I.MapRel A) :=
  Subtype.finite


-- @@ L86-86 verbatim
end RelFOInterpretation


-- @@ L88-88 verbatim
/-! ### Functoriality on isomorphisms -/


-- @@ L90-90 verbatim
namespace RelFOInterpretation


-- @@ L92-93 verbatim
variable [L'.IsRelational] (I : RelFOInterpretation L L' Tag dim)
  {M N : Type} [L.Structure M] [L.Structure N]


-- @@ L95-108 verbatim
/-- Relativized interpretations are functorial on `L`-isomorphisms: the domain
formula is an `L`-formula, so its truth transports, and the induced map of
subtypes is an `L'`-isomorphism. -/
def mapRelLEquiv (e : M ≃[L] N) : I.MapRel M ≃[L'] I.MapRel N where
  toFun x := ⟨(x.1.1, fun j => e (x.1.2 j)),
    (StrongHomClass.realize_formula e (I.domFormula x.1.1)).mpr x.2⟩
  invFun x := ⟨(x.1.1, fun j => e.symm (x.1.2 j)),
    (StrongHomClass.realize_formula e.symm (I.domFormula x.1.1)).mpr x.2⟩
  left_inv x := Subtype.ext (Prod.ext_iff.mpr ⟨rfl, funext fun j => e.symm_apply_apply (x.1.2 j)⟩)
  right_inv x := Subtype.ext (Prod.ext_iff.mpr ⟨rfl, funext fun j => e.apply_symm_apply (x.1.2 j)⟩)
  map_fun' f := isEmptyElim f
  map_rel' _ _ := by
    rw [RelFOInterpretation.relMap_mapRel, RelFOInterpretation.relMap_mapRel]
    exact StrongHomClass.realize_formula e _


-- @@ L110-110 verbatim
end RelFOInterpretation


-- @@ L112-112 verbatim
/-! ### The whole-universe case is an ordinary interpretation -/


-- @@ L114-118 verbatim
/-- Any interpretation is a relativized one whose domain formula is `⊤`: the
target universe is all of `Tag × A^dim`, as before. -/
def FOInterpretation.toRel (I : FOInterpretation L L' Tag dim) :
    RelFOInterpretation L L' Tag dim :=
  { toFOInterpretation := I, domFormula := fun _ => ⊤ }


-- @@ L120-130 verbatim
/-- The transparency of the `⊤` domain: the relativized universe of `I.toRel`
is `L'`-isomorphic to the ordinary universe of `I`. (Not a definitional
equality – a subtype over `⊤` is not literally the product.) -/
def FOInterpretation.toRelLEquiv [L'.IsRelational] (I : FOInterpretation L L' Tag dim)
    (A : Type) [L.Structure A] : I.Map A ≃[L'] I.toRel.MapRel A where
  toFun a := ⟨a, Formula.realize_top.mpr trivial⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_fun' f := isEmptyElim f
  map_rel' _ _ := Iff.rfl


-- @@ L132-132 verbatim
/-! ### Relativized ordered reductions -/


-- @@ L134-156 verbatim
/-- An *ordered* first-order reduction through a **relativized**
interpretation: like `DescriptiveComplexity.OrderedFOReduction`, but the target universe is
the definable subset carved out by the domain formula. The `Nonempty Tag`
field of the ordinary reduction is replaced by `dom_nonempty`, since a
definable domain may be empty even when the tags and the input are not. -/
structure RelOrderedFOReduction [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L) (Q : DecisionProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : RelFOInterpretation (L.sum Language.order) L' Tag dim
  /-- The definable domain is inhabited: some tagged tuple satisfies its tag's
  domain formula. The relativized counterpart of `Nonempty Tag`, which does not
  suffice once the domain is cut out by a formula. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (w : Fin dim → A), (toRelInterpretation.domFormula t).Realize w
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toRelInterpretation.MapRel A)


-- @@ L158-159 verbatim
@[inherit_doc]
scoped notation:50 P:51 " ≤ʳᶠᵒ[≤] " Q:51 => RelOrderedFOReduction P Q


-- @@ L161-161 verbatim
namespace RelOrderedFOReduction


-- @@ L163-163 verbatim
variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}


-- @@ L165-170 verbatim
/-- The relativized universe of the output of a reduction is nonempty on
nonempty finite ordered inputs. -/
theorem mapRel_nonempty (f : P ≤ʳᶠᵒ[≤] Q) (A : Type) [L.Structure A] [LinearOrder A]
    [Finite A] [Nonempty A] : Nonempty (f.toRelInterpretation.MapRel A) :=
  let ⟨t, w, h⟩ := f.dom_nonempty A
  ⟨⟨(t, w), h⟩⟩


-- @@ L172-172 verbatim
end RelOrderedFOReduction


-- @@ L174-186 verbatim
/-- An ordinary ordered FO reduction is a relativized one with `⊤` domain: the
correctness is transported across `DescriptiveComplexity.FOInterpretation.toRelLEquiv`, and the
domain is inhabited by any tag and any constant tuple. -/
def OrderedFOReduction.toRel [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L}
    {Q : DecisionProblem L'} (f : P ≤ᶠᵒ[≤] Q) : P ≤ʳᶠᵒ[≤] Q :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toInterpretation.toRel
    dom_nonempty := fun A => ⟨Classical.arbitrary f.Tag, fun _ => Classical.arbitrary A,
      Formula.realize_top.mpr trivial⟩
    correct := fun A => (f.correct A).trans (Q.iso_invariant (f.toInterpretation.toRelLEquiv A)) }


-- @@ L188-198 verbatim
/-- A relativized reduction can be transported along an agreement of the source
problems on finite structures. -/
def RelOrderedFOReduction.congrSource [L.IsRelational] [L'.IsRelational] {P P' : DecisionProblem L}
    {S : DecisionProblem L'} (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A)
    (g : P ≤ʳᶠᵒ[≤] S) : P' ≤ʳᶠᵒ[≤] S :=
  letI := g.tagFinite
  { Tag := g.Tag
    dim := g.dim
    toRelInterpretation := g.toRelInterpretation
    dom_nonempty := g.dom_nonempty
    correct := fun A => (h A).symm.trans (g.correct A) }


-- @@ L200-200 verbatim
end DescriptiveComplexity
