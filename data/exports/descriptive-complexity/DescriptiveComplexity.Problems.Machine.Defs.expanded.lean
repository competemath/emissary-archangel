/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Machines
import DescriptiveComplexity.Interpretation


-- @@ L9-55 verbatim
/-!
# Machine acceptance as a decision problem

The vocabulary of the machine bridge, and the problem the bridge is about: a
nondeterministic Turing machine is *data in an instance*, and

> does this machine accept its input within as many steps as there are
> positions?

is `DescriptiveComplexity.NTMAccept`, an ordinary iso-invariant problem of the catalog.
The semantics it reads is `DescriptiveComplexity.TMData`, defined without a vocabulary
in `DescriptiveComplexity.Machines`.

## The vocabulary

`FirstOrder.Language.turing` carries, following design decision (a) of the
plan, **no relation of arity above two**: a transition is an *element* `τ` of
the universe with four binary attributes `tsrc`/`tread`/`tdst`/`twrite` and a
unary mark `right`, rather than a single 5-ary symbol. An
`FOInterpretation` supplies one defining formula per tuple of tags, so a 5-ary
symbol would mean `|Tag|⁵` formula cases; keeping every symbol binary keeps the
reductions of stages 3 and 4 in the regime the rest of the catalog lives in.

Positions are both tape cells and time steps (design decision (b)), so the
budget of `DescriptiveComplexity.TMData.Accepts` is unary by construction and no
arithmetic is needed anywhere.

## Well-formedness

Being a linear order is not automatic for a relation symbol, so – exactly as
`DescriptiveComplexity.IsLinOrd` for Knapsack, and `WidthAtMostThree` for 3SAT – it is
folded into the yes-instances, together with the other promises of
`DescriptiveComplexity.TMData.WellFormed`. All of them are first-order, so the `Σ₁`
kernel of the membership proof can check them.

## Why there are no state and symbol sorts

The vocabulary marks positions (`posn`) and transitions (`tr`) and nothing else.
Sorts of states and of symbols are omitted because nothing in the semantics or
in the membership proof reads them: a junk element is harmless as a state, since
it is reachable only through a transition, and a reduction controls which
elements it marks accepting. Should a construction want them, adding a unary
symbol is a local change to this file and to the well-formedness predicate.
-/

/- The language of machine instances lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order`. -/

-- @@ L56-56 verbatim
namespace FirstOrder


-- @@ L58-58 verbatim
namespace Language


-- @@ L60-86 verbatim
/-- Relation symbols of machine instances. -/
inductive turingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a tape cell, and equally a time step. -/
  | posn : turingRel 1
  /-- `tr τ`: `τ` is a transition. -/
  | tr : turingRel 1
  /-- `start q`: `q` is a start state. -/
  | start : turingRel 1
  /-- `acc q`: `q` is an accepting state. -/
  | acc : turingRel 1
  /-- `blank a`: `a` is the blank symbol. -/
  | blank : turingRel 1
  /-- `right τ`: the transition `τ` moves the head right. -/
  | right : turingRel 1
  /-- `le p q`: the linear order along which the head moves. -/
  | le : turingRel 2
  /-- `tsrc τ q`: `τ` applies in the state `q`. -/
  | tsrc : turingRel 2
  /-- `tread τ a`: `τ` applies when reading the symbol `a`. -/
  | tread : turingRel 2
  /-- `tdst τ q`: `τ` moves to the state `q`. -/
  | tdst : turingRel 2
  /-- `twrite τ a`: `τ` writes the symbol `a`. -/
  | twrite : turingRel 2
  /-- `inp p a`: the cell `p` initially holds the symbol `a`. -/
  | inp : turingRel 2
  deriving DecidableEq


-- @@ L88-93 verbatim
/-- The relational language of machine instances: positions with their order,
transitions with their attributes, the distinguished states and symbol, and the
initial tape. -/
protected def turing : Language :=
  ⟨fun _ => Empty, turingRel⟩
  deriving IsRelational


-- @@ L95-96 verbatim
/-- The position symbol. -/
abbrev tmPosn : Language.turing.Relations 1 := .posn


-- @@ L98-99 verbatim
/-- The transition symbol. -/
abbrev tmTr : Language.turing.Relations 1 := .tr


-- @@ L101-102 verbatim
/-- The start-state symbol. -/
abbrev tmStart : Language.turing.Relations 1 := .start


-- @@ L104-105 verbatim
/-- The accepting-state symbol. -/
abbrev tmAcc : Language.turing.Relations 1 := .acc


-- @@ L107-108 verbatim
/-- The blank symbol. -/
abbrev tmBlank : Language.turing.Relations 1 := .blank


-- @@ L110-111 verbatim
/-- The move-right symbol. -/
abbrev tmRight : Language.turing.Relations 1 := .right


-- @@ L113-114 verbatim
/-- The order symbol. -/
abbrev tmLe : Language.turing.Relations 2 := .le


-- @@ L116-117 verbatim
/-- The transition-source symbol. -/
abbrev tmSrc : Language.turing.Relations 2 := .tsrc


-- @@ L119-120 verbatim
/-- The transition-read symbol. -/
abbrev tmRead : Language.turing.Relations 2 := .tread


-- @@ L122-123 verbatim
/-- The transition-destination symbol. -/
abbrev tmDst : Language.turing.Relations 2 := .tdst


-- @@ L125-126 verbatim
/-- The transition-write symbol. -/
abbrev tmWrite : Language.turing.Relations 2 := .twrite


-- @@ L128-129 verbatim
/-- The input symbol. -/
abbrev tmInp : Language.turing.Relations 2 := .inp


-- @@ L131-131 verbatim
end Language


-- @@ L133-133 verbatim
end FirstOrder


-- @@ L135-135 verbatim
namespace DescriptiveComplexity


-- @@ L137-137 verbatim
open FirstOrder


-- @@ L139-139 verbatim
open Language Structure


-- @@ L141-141 verbatim
/-! ### The shorthands of the vocabulary -/


-- @@ L143-143 verbatim
section Shorthands


-- @@ L145-145 verbatim
variable {A : Type} [Language.turing.Structure A]


-- @@ L147-148 verbatim
/-- Being a position. -/
def TMPosn (a : A) : Prop := RelMap tmPosn ![a]


-- @@ L150-151 verbatim
/-- Being a transition. -/
def TMTr (a : A) : Prop := RelMap tmTr ![a]


-- @@ L153-154 verbatim
/-- Being a start state. -/
def TMStart (a : A) : Prop := RelMap tmStart ![a]


-- @@ L156-157 verbatim
/-- Being an accepting state. -/
def TMAcc (a : A) : Prop := RelMap tmAcc ![a]


-- @@ L159-160 verbatim
/-- Being the blank symbol. -/
def TMBlank (a : A) : Prop := RelMap tmBlank ![a]


-- @@ L162-163 verbatim
/-- Moving the head right. -/
def TMRight (a : A) : Prop := RelMap tmRight ![a]


-- @@ L165-166 verbatim
/-- The order on positions. -/
def TMLe (a b : A) : Prop := RelMap tmLe ![a, b]


-- @@ L168-169 verbatim
/-- The state a transition applies in. -/
def TMSrc (a b : A) : Prop := RelMap tmSrc ![a, b]


-- @@ L171-172 verbatim
/-- The symbol a transition reads. -/
def TMRead (a b : A) : Prop := RelMap tmRead ![a, b]


-- @@ L174-175 verbatim
/-- The state a transition moves to. -/
def TMDst (a b : A) : Prop := RelMap tmDst ![a, b]


-- @@ L177-178 verbatim
/-- The symbol a transition writes. -/
def TMWrite (a b : A) : Prop := RelMap tmWrite ![a, b]


-- @@ L180-181 verbatim
/-- The initial contents of a cell. -/
def TMInp (a b : A) : Prop := RelMap tmInp ![a, b]


-- @@ L183-196 verbatim
/-- The machine an instance describes. -/
def tmData (A : Type) [Language.turing.Structure A] : TMData A where
  Posn := TMPosn
  Le := TMLe
  Tr := TMTr
  Start := TMStart
  Acc := TMAcc
  Blank := TMBlank
  Right := TMRight
  Src := TMSrc
  Read := TMRead
  Dst := TMDst
  Write := TMWrite
  Inp := TMInp


-- @@ L198-198 verbatim
end Shorthands


-- @@ L200-200 verbatim
/-! ### The problem -/


-- @@ L202-202 verbatim
section Problem


-- @@ L204-204 verbatim
variable {A B : Type} [Language.turing.Structure A] [Language.turing.Structure B]


-- @@ L206-224 verbatim
/-- **An isomorphism makes the two machines agree.** Every symbol of the
vocabulary transports, which is all `DescriptiveComplexity.TMData.Agree` asks for. -/
theorem agree_of_equiv (e : A ≃[Language.turing] B) :
    (tmData B).Agree e.symm.toEquiv (tmData A) := by
  have h1 : ∀ (r : Language.turing.Relations 1) (b : B),
      (RelMap r ![b] : Prop) ↔ RelMap r ![(e.symm b : A)] := fun r b => by
    have h := relMap_equiv₁ e r (e.symm b)
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b] at h
    exact h.symm
  have h2 : ∀ (r : Language.turing.Relations 2) (b b' : B),
      (RelMap r ![b, b'] : Prop) ↔ RelMap r ![(e.symm b : A), (e.symm b' : A)] := fun r b b' => by
    have h := relMap_equiv₂ e r (e.symm b) (e.symm b')
    rw [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b,
      show (e (e.symm b') : B) = b' from e.toEquiv.apply_symm_apply b'] at h
    exact h.symm
  exact ⟨fun b => h1 tmPosn b, fun b b' => h2 tmLe b b', fun b => h1 tmTr b,
    fun b => h1 tmStart b, fun b => h1 tmAcc b, fun b => h1 tmBlank b, fun b => h1 tmRight b,
    fun b b' => h2 tmSrc b b', fun b b' => h2 tmRead b b', fun b b' => h2 tmDst b b',
    fun b b' => h2 tmWrite b b', fun b b' => h2 tmInp b b'⟩


-- @@ L226-234 verbatim
/-- **Machine acceptance.** Does the machine described by the instance accept
its input within as many steps as there are positions? The well-formedness
promises of `DescriptiveComplexity.TMData.WellFormed` are folded into the
yes-instances. -/
def NTMAccept : DecisionProblem Language.turing where
  Holds := fun A inst => @TMData.WellFormed A (tmData A) ∧ @TMData.Accepts A (tmData A)
  iso_invariant := fun {A B} _ _ e => by
    have h := agree_of_equiv e
    exact (and_congr h.wellFormed h.accepts).symm


-- @@ L236-246 verbatim
/-- **Deterministic machine acceptance.** The same question with the extra
promise `DescriptiveComplexity.TMData.Deterministic` folded into the yes-instances,
exactly as the Horn condition is folded into `DescriptiveComplexity.HORNSAT`: the
table is functional, so the run is unique – the shape a least fixed point can
compute, which is what puts this problem in PTIME. -/
def DTMAccept : DecisionProblem Language.turing where
  Holds := fun A inst => @TMData.WellFormed A (tmData A) ∧
    @TMData.Deterministic A (tmData A) ∧ @TMData.Accepts A (tmData A)
  iso_invariant := fun {A B} _ _ e => by
    have h := agree_of_equiv e
    exact (and_congr h.wellFormed (and_congr h.deterministic h.accepts)).symm


-- @@ L248-258 verbatim
/-- **Machine acceptance in bounded space**: the same question as
`DescriptiveComplexity.NTMAccept` with the step bound dropped. Nothing else
changes – the tape is indexed by the positions, so the space a machine may use
is bounded by construction and a reduction of dimension `d` buys `nᵈ` cells
exactly as it buys `nᵈ` steps – but a run may now visit exponentially many
configurations, so acceptance is reachability in the configuration graph. -/
def NTMAcceptSpace : DecisionProblem Language.turing where
  Holds := fun A inst => @TMData.WellFormed A (tmData A) ∧ @TMData.AcceptsSpace A (tmData A)
  iso_invariant := fun {A B} _ _ e => by
    have h := agree_of_equiv e
    exact (and_congr h.wellFormed h.acceptsSpace).symm


-- @@ L260-269 verbatim
/-- **Deterministic machine acceptance in bounded space**, with determinism
folded into the yes-instances as in `DescriptiveComplexity.DTMAccept`. That this
problem and `DescriptiveComplexity.NTMAcceptSpace` are complete for the same class
is the content of `PSPACE = NPSPACE`. -/
def DTMAcceptSpace : DecisionProblem Language.turing where
  Holds := fun A inst => @TMData.WellFormed A (tmData A) ∧
    @TMData.Deterministic A (tmData A) ∧ @TMData.AcceptsSpace A (tmData A)
  iso_invariant := fun {A B} _ _ e => by
    have h := agree_of_equiv e
    exact (and_congr h.wellFormed (and_congr h.deterministic h.acceptsSpace)).symm


-- @@ L271-271 verbatim
end Problem


-- @@ L273-273 verbatim
end DescriptiveComplexity
