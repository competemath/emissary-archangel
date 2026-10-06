/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureParam
import DescriptiveComplexity.FixedPointReductionClosure


-- @@ L9-52 verbatim
/-!
# FO(TC) reductions: the logarithmic-space reductions

The reduction notion of `DescriptiveComplexity.NL`: an interpretation whose
defining formulas may consult, besides the input structure, the **reachability
relations of first-order walks** (`DescriptiveComplexity.TCFamily`). It sits
between the two notions already built,

`≤ᶠᵒ[≤]` ⊆ `≤ᵗᶜ` ⊆ `≤ˡᶠᵖ`,

the first inclusion strict (`DescriptiveComplexity.TransitiveClosureReductionStrict`),
and it is what “logarithmic-space reduction” means in a machine-free
development, exactly as `≤ˡᶠᵖ` is what “polynomial-time reduction” means.

## What comes for free, and what does not

A walk is an inflationary induction of a very restricted shape
(`DescriptiveComplexity.TCFamily.inflLimit_toStepDef`), so an FO(TC)
interpretation *is* an FO(LFP) interpretation
(`DescriptiveComplexity.TCInterpretation.toLFP`) and an FO(TC) reduction is an
FO(LFP) reduction (`DescriptiveComplexity.TCReduction.toLFP`). Every closure
theorem of `DescriptiveComplexity.FixedPointReductionClosure` therefore
transfers: PTIME, NP and coNP are closed under `≤ᵗᶜ`, and hardness under
first-order reductions implies hardness under these.

What does not transfer is the closure of NL itself: the membership walk
pulled back through the reduction is a walk whose steps consult walks, and the
route the other classes took is unavailable here – there the induction was
absorbed by a *smaller* class already known to sit inside (PTIME inside NP),
and NL has no smaller class to lean on. What it needs is its own normal form,
a `TC` of a formula containing `TC`s being a single `TC`, and that is proved
as an algebra of walks with two exits (`DescriptiveComplexity.Decider`,
`DescriptiveComplexity.TransitiveClosureDecide` through
`DescriptiveComplexity.TransitiveClosureSentenceDecide`): NL is closed under
`≤ᵗᶜ` (`DescriptiveComplexity.mem_NL_of_tcReduction`, in
`DescriptiveComplexity.TransitiveClosureReductionClosure`).

Transitivity of `≤ᵗᶜ` (`DescriptiveComplexity.TCReduction.trans`, in
`DescriptiveComplexity.TransitiveClosureReductionTrans`) composes two FO(TC)
interpretations by pulling the outer walks back through the inner
interpretation, flattening them with the same deciders, and extending the
inner interpretation to the outer walks' vocabulary. So `≤ᵗᶜ` is a reduction
*order*, with the closure properties of NL and of the classes above it.
-/


-- @@ L54-54 verbatim
namespace DescriptiveComplexity


-- @@ L56-56 verbatim
open FirstOrder


-- @@ L58-58 verbatim
open Language Structure


-- @@ L60-60 verbatim
/-! ### Interpretations that read walks -/


-- @@ L62-73 verbatim
/-- An **FO(TC) interpretation**: a relativized first-order interpretation
whose formulas may read the reachability relations of a finite family of
first-order walks over the base structure.

Over an ordered base (`L := L₀.sum Language.order`) this is Immerman's FO(TC)
reduction, the logical form of a logarithmic-space reduction. -/
structure TCInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) : Type 1 where
  /-- The walks whose reachability relations the formulas may read. -/
  fam : TCFamily L
  /-- The interpretation, over the base vocabulary expanded by the walks'
  relation variables. -/
  toRel : RelFOInterpretation (L.sum fam.block.lang) L' Tag dim


-- @@ L75-75 verbatim
namespace TCInterpretation


-- @@ L77-77 verbatim
variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

-- @@ L78-78 verbatim
variable (I : TCInterpretation L L' Tag dim) (A : Type) [L.Structure A]


-- @@ L80-84 verbatim
/-- The base structure expanded by the reachability relations of the walks –
the structure the interpretation is read over. -/
@[instance_reducible]
def expStructure : (L.sum I.fam.block.lang).Structure A :=
  I.fam.block.structure₁ (L := L) (I.fam.reachAssign A)


-- @@ L86-89 verbatim
/-- The universe of the interpreted structure. -/
protected def Map : Type :=
  letI := I.expStructure A
  I.toRel.MapRel A


-- @@ L91-94 verbatim
/-- The `L'`-structure interpreted in `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) :=
  letI := I.expStructure A
  RelFOInterpretation.mapRelStructure I.toRel A


-- @@ L96-98 verbatim
theorem map_finite [Finite Tag] [Finite A] : Finite (I.Map A) :=
  letI := I.expStructure A
  I.toRel.mapRel_finite A


-- @@ L100-100 verbatim
/-! ### A walk is an induction, so an FO(TC) interpretation is an FO(LFP) one -/


-- @@ L102-108 verbatim
/-- **An FO(TC) interpretation, read as an FO(LFP) interpretation**: the
family's walks become the one induction that computes their reachability
relations (`DescriptiveComplexity.TCFamily.toStepDef`), and the interpretation
is unchanged. -/
noncomputable def toLFP : LFPInterpretation L L' Tag dim where
  ind := I.fam.toStepDef
  toRel := I.toRel


-- @@ L110-110 verbatim
variable {I A}


-- @@ L112-116 verbatim
/-- The two readings expand the base structure by the same relations: the
value of the induction is the reachability relations. -/
theorem expStructure_toLFP [Finite A] :
    (I.toLFP.expStructure A : (L.sum I.fam.block.lang).Structure A) = I.expStructure A :=
  congrArg (I.fam.block.structure₁ (L := L)) TCFamily.inflLimit_toStepDef


-- @@ L118-129 verbatim
/-- Equal expansions give the same interpreted structure. -/
def mapEquivOfEq [L'.IsRelational] {inst₁ inst₂ : (L.sum I.fam.block.lang).Structure A}
    (h : inst₁ = inst₂) :
    @Language.Equiv L'
      (@RelFOInterpretation.MapRel _ _ _ _ I.toRel A inst₁)
      (@RelFOInterpretation.MapRel _ _ _ _ I.toRel A inst₂)
      (@RelFOInterpretation.mapRelStructure _ _ _ _ I.toRel A inst₁ _)
      (@RelFOInterpretation.mapRelStructure _ _ _ _ I.toRel A inst₂ _) := by
  subst h
  exact { toEquiv := Equiv.refl _
          map_fun' := fun f => isEmptyElim f
          map_rel' := fun R x => Iff.rfl }


-- @@ L131-135 verbatim
/-- **The FO(LFP) reading interprets the same structure**: the identity map on
tagged tuples is an isomorphism. -/
noncomputable def toLFPLEquiv [L'.IsRelational] [Finite A] :
    (I.toLFP).Map A ≃[L'] I.Map A :=
  mapEquivOfEq (I := I) (A := A) expStructure_toLFP


-- @@ L137-137 verbatim
end TCInterpretation


-- @@ L139-139 verbatim
/-! ### FO(TC) reductions -/


-- @@ L141-141 verbatim
variable {L L' : Language.{0, 0}}


-- @@ L143-164 verbatim
/-- An **FO(TC) reduction** from `P` to `Q` – a logarithmic-space reduction, in
the logical form of [Immerman 1999][immerman1999descriptive]: an FO(TC)
interpretation over the ordered expansion of the source vocabulary, mapping
yes-instances exactly to yes-instances, for every finite linear order on the
input. -/
structure TCReduction [L.IsRelational] [L'.IsRelational] (P : DecisionProblem L)
    (Q : DecisionProblem L') : Type 1 where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying FO(TC) interpretation, over the ordered expansion. -/
  toInterpretation : TCInterpretation (L.sum Language.order) L' Tag dim
  /-- The interpreted structure is nonempty on nonempty finite ordered
  inputs. -/
  map_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    Nonempty (toInterpretation.Map A)
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)


-- @@ L166-167 verbatim
@[inherit_doc]
scoped notation:50 P:51 " ≤ᵗᶜ " Q:51 => TCReduction P Q


-- @@ L169-169 verbatim
/-! ### Every FO(TC) reduction is an FO(LFP) reduction -/


-- @@ L171-171 verbatim
section ToLFP


-- @@ L173-173 verbatim
variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}


-- @@ L175-187 verbatim
/-- **An FO(TC) reduction is an FO(LFP) reduction**: reachability is an
inflationary induction. Every closure property of `≤ˡᶠᵖ` transfers along
this. -/
noncomputable def TCReduction.toLFP (f : P ≤ᵗᶜ Q) : P ≤ˡᶠᵖ Q :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation.toLFP
    map_nonempty := fun A _ _ _ _ =>
      (f.map_nonempty A).map (TCInterpretation.toLFPLEquiv (I := f.toInterpretation)).symm
    correct := fun A _ _ _ _ =>
      (f.correct A).trans
        (Q.iso_invariant (TCInterpretation.toLFPLEquiv (I := f.toInterpretation))).symm }


-- @@ L189-189 verbatim
end ToLFP


-- @@ L191-191 verbatim
/-! ### Every first-order reduction is an FO(TC) reduction -/


-- @@ L193-193 verbatim
section OfFO


-- @@ L195-195 verbatim
variable {Tag : Type} {dim : ℕ} [L'.IsRelational]


-- @@ L197-201 verbatim
/-- The empty family of walks: no relation variables, so the expansion is the
structure itself. -/
def TCFamily.empty (L : Language.{0, 0}) : TCFamily L where
  Ix := Empty
  spec := fun i => i.elim


-- @@ L203-207 verbatim
/-- A relativized interpretation, read as an FO(TC) interpretation whose
formulas ignore the walks it is given. -/
def RelFOInterpretation.toTCFam (J : RelFOInterpretation L L' Tag dim) (F : TCFamily L) :
    TCInterpretation L L' Tag dim :=
  ⟨F, J.liftSource LHom.sumInl⟩


-- @@ L209-216 verbatim
/-- An interpretation that ignores its walks produces exactly the structure of
the relativized interpretation it lifts, whatever the walks are: the expansion
interprets the base symbols as the base structure does. -/
def RelFOInterpretation.toTCFamLEquiv (J : RelFOInterpretation L L' Tag dim) (F : TCFamily L)
    (A : Type) [instA : L.Structure A] : (J.toTCFam F).Map A ≃[L'] J.MapRel A :=
  letI := (J.toTCFam F).expStructure A
  J.liftSourceLEquiv LHom.sumInl (inst₀ := instA)
    (inst₁ := (J.toTCFam F).expStructure A) ⟨fun _ _ => rfl, fun _ _ => rfl⟩


-- @@ L218-222 verbatim
/-- A relativized interpretation, read as an FO(TC) interpretation that
consults no walk. -/
def RelFOInterpretation.toTC (J : RelFOInterpretation L L' Tag dim) :
    TCInterpretation L L' Tag dim :=
  J.toTCFam (TCFamily.empty L)


-- @@ L224-228 verbatim
/-- The FO(TC) interpretation with no walks produces exactly the structure of
the relativized interpretation it lifts. -/
def RelFOInterpretation.toTCLEquiv (J : RelFOInterpretation L L' Tag dim) (A : Type)
    [L.Structure A] : J.toTC.Map A ≃[L'] J.MapRel A :=
  J.toTCFamLEquiv (TCFamily.empty L) A


-- @@ L230-230 verbatim
end OfFO


-- @@ L232-232 verbatim
section Embed


-- @@ L234-234 verbatim
variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}


-- @@ L236-246 verbatim
/-- **A relativized ordered FO reduction is an FO(TC) reduction**, consulting
no walk. -/
def RelOrderedFOReduction.toTC (f : P ≤ʳᶠᵒ[≤] Q) : P ≤ᵗᶜ Q :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toRelInterpretation.toTC
    map_nonempty := fun A _ _ _ _ =>
      (f.mapRel_nonempty A).map (f.toRelInterpretation.toTCLEquiv A).symm
    correct := fun A _ _ _ _ =>
      (f.correct A).trans (Q.iso_invariant (f.toRelInterpretation.toTCLEquiv A)).symm }


-- @@ L248-250 verbatim
/-- **An ordered FO reduction is an FO(TC) reduction.** -/
def OrderedFOReduction.toTC (f : P ≤ᶠᵒ[≤] Q) : P ≤ᵗᶜ Q :=
  f.toRel.toTC


-- @@ L252-254 verbatim
/-- **An FO reduction is an FO(TC) reduction.** -/
noncomputable def FOReduction.toTC (f : P ≤ᶠᵒ Q) : P ≤ᵗᶜ Q :=
  f.toOrdered.toRel.toTC


-- @@ L256-256 verbatim
end Embed


-- @@ L258-258 verbatim
/-! ### The classes above NL are closed under FO(TC) reductions -/


-- @@ L260-260 verbatim
section Closure


-- @@ L262-262 verbatim
variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}


-- @@ L264-266 verbatim
/-- **PTIME is closed under FO(TC) reductions.** -/
theorem mem_PTIME_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ PTIME) : P ∈ PTIME :=
  mem_PTIME_of_lfpReduction f.toLFP h


-- @@ L268-270 verbatim
/-- **NP is closed under FO(TC) reductions.** -/
theorem mem_NP_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ NP) : P ∈ NP :=
  mem_NP_of_lfpReduction f.toLFP h


-- @@ L272-274 verbatim
/-- **coNP is closed under FO(TC) reductions.** -/
theorem mem_coNP_of_tcReduction (f : P ≤ᵗᶜ Q) (h : Q ∈ coNP) : P ∈ coNP :=
  mem_coNP_of_lfpReduction f.toLFP h


-- @@ L276-276 verbatim
end Closure


-- @@ L278-278 verbatim
end DescriptiveComplexity
