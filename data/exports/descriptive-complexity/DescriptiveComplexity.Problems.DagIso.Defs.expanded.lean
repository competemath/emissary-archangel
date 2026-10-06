/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Vocabulary
import DescriptiveComplexity.Problems.DigraphIso
import DescriptiveComplexity.Problems.Feedback.Defs


-- @@ L10-49 verbatim
/-!
# DAG Isomorphism: vocabulary and semantics

DAG ISOMORPHISM: are the two directed acyclic graphs of the instance
isomorphic? This file fixes the vocabulary and the yes-instance predicate; the
two halves of GI-completeness live in
`DescriptiveComplexity.Problems.DagIso.ToDigraphIso` and
`DescriptiveComplexity.Problems.DagIso.FromDigraphIso`.

## Why the instances carry a topological order

Acyclicity is **not first-order definable**, so a problem whose yes-instances
are “both sides acyclic *and* isomorphic” could not be reduced back to
`DescriptiveComplexity.DigraphIso`: the reduction would have to decide acyclicity
first-order, and no first-order interpretation can (a directed cycle is a
reachability question). A classical polynomial-time reduction simply tests
acyclicity and maps a cyclic instance to a fixed no-instance; an FO reduction,
computable in AC⁰, cannot.

The instances therefore *carry* their acyclicity witness: besides the two arc
relations, each side has a relation asked to be a strict partial order
containing its arcs (`DescriptiveComplexity.TopoOn`) – a topological order of
the DAG, in the partial-order form, which is exactly what
`DescriptiveComplexity.acyclicRel_iff_exists_order` certifies acyclicity by.
Being a strict partial order containing the arcs is first-order, so a reduction
*can* test it, and the well-formed instances are precisely the pairs of DAGs
(`DescriptiveComplexity.acyclicOn_iff_exists_topoOn`: a finite relation admits
such a witness exactly when it is acyclic). The witness is data of the
instance, not of the problem: the isomorphism asked for by
`DescriptiveComplexity.HasDagIso` relates the *arcs* only and may ignore the two
orders entirely, so this is DAG isomorphism and not isomorphism of ordered
DAGs.

This is the same “junk is ignorable” discipline as everywhere in the catalog,
one level up: elements outside both marks are junk, and instances whose order
relation is not a witness are no-instances.
-/

/- The language of two-DAG structures lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.twoGraphs`. -/

-- @@ L50-50 verbatim
namespace FirstOrder


-- @@ L52-52 verbatim
namespace Language


-- @@ L54-69 verbatim
/-- The relational language of two directed acyclic graphs: two arc relations
sharing a universe, each with its own vertex mark and its own topological
order. -/
fo_language twoDags with td where
  /-- `patV a`: `a` is a vertex of the pattern DAG. -/
  patV : 1
  /-- `hostV a`: `a` is a vertex of the host DAG. -/
  hostV : 1
  /-- `patArc a b`: there is an arc of the pattern DAG from `a` to `b`. -/
  patArc : 2
  /-- `hostArc a b`: there is an arc of the host DAG from `a` to `b`. -/
  hostArc : 2
  /-- `patLt a b`: `a` precedes `b` in the pattern's topological order. -/
  patLt : 2
  /-- `hostLt a b`: `a` precedes `b` in the host's topological order. -/
  hostLt : 2


-- @@ L71-71 verbatim
end Language


-- @@ L73-73 verbatim
end FirstOrder


-- @@ L75-75 verbatim
namespace DescriptiveComplexity


-- @@ L77-77 verbatim
open FirstOrder


-- @@ L79-79 verbatim
open Language Structure


-- @@ L81-81 verbatim
/-! ### The acyclicity witness -/


-- @@ L83-83 verbatim
section Topo


-- @@ L85-85 verbatim
variable {A : Type}


-- @@ L87-94 verbatim
/-- `Lt` is a topological order for the arcs `Arc` on the marked set `V`: a
strict partial order (on `V`) containing the arcs. Its existence is exactly the
acyclicity of the arcs (`DescriptiveComplexity.acyclicOn_iff_exists_topoOn`),
and it is first-order checkable, which acyclicity itself is not. -/
def TopoOn (V : A → Prop) (Lt Arc : A → A → Prop) : Prop :=
  (∀ x, V x → ¬Lt x x) ∧
    (∀ x y z, V x → V y → V z → Lt x y → Lt y z → Lt x z) ∧
    ∀ x y, V x → V y → Arc x y → Lt x y


-- @@ L96-96 verbatim
variable {B : Type}


-- @@ L98-114 verbatim
/-- `TopoOn` transports along an equivalence commuting with the three
predicates. -/
theorem TopoOn.of_equiv (u : B ≃ A) {VB : B → Prop} {LtB ArcB : B → B → Prop}
    {VA : A → Prop} {LtA ArcA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hLt : ∀ b b', LtB b b' ↔ LtA (u b) (u b'))
    (hArc : ∀ b b', ArcB b b' ↔ ArcA (u b) (u b'))
    (h : TopoOn VB LtB ArcB) : TopoOn VA LtA ArcA := by
  obtain ⟨hirr, htrans, hmono⟩ := h
  refine ⟨fun x hx hlt => ?_, fun x y z hx hy hz h₁ h₂ => ?_, fun x y hx hy harc => ?_⟩
  · exact hirr (u.symm x) ((hV _).mpr (by simpa using hx)) ((hLt _ _).mpr (by simpa using hlt))
  · have := htrans (u.symm x) (u.symm y) (u.symm z) ((hV _).mpr (by simpa using hx))
      ((hV _).mpr (by simpa using hy)) ((hV _).mpr (by simpa using hz))
      ((hLt _ _).mpr (by simpa using h₁)) ((hLt _ _).mpr (by simpa using h₂))
    simpa using (hLt (u.symm x) (u.symm z)).mp this
  · have := hmono (u.symm x) (u.symm y) ((hV _).mpr (by simpa using hx))
      ((hV _).mpr (by simpa using hy)) ((hArc _ _).mpr (by simpa using harc))
    simpa using (hLt (u.symm x) (u.symm y)).mp this


-- @@ L116-124 verbatim
/-- `TopoOn` transports along an equivalence, iff version. -/
theorem TopoOn.equiv_iff (u : B ≃ A) {VB : B → Prop} {LtB ArcB : B → B → Prop}
    {VA : A → Prop} {LtA ArcA : A → A → Prop}
    (hV : ∀ b, VB b ↔ VA (u b)) (hLt : ∀ b b', LtB b b' ↔ LtA (u b) (u b'))
    (hArc : ∀ b b', ArcB b b' ↔ ArcA (u b) (u b')) :
    TopoOn VB LtB ArcB ↔ TopoOn VA LtA ArcA :=
  ⟨TopoOn.of_equiv u hV hLt hArc,
    TopoOn.of_equiv u.symm (fun a => by rw [hV]; simp) (fun a a' => by rw [hLt]; simp)
      fun a a' => by rw [hArc]; simp⟩


-- @@ L126-147 verbatim
/-- **The well-formed instances are exactly the DAGs**: the arcs of a marked
set admit a topological order precisely when they are acyclic on it. Left to
right a cycle would give `Lt x x`; right to left the transitive closure is the
order (`DescriptiveComplexity.acyclicRel_iff_exists_order`, on the subtype of
marked elements).

This is why carrying the witness costs no generality: every DAG is a
yes-instance-shaped instance, and no other structure is. -/
theorem acyclicOn_iff_exists_topoOn (V : A → Prop) (Arc : A → A → Prop) :
    AcyclicRel (fun x y : {x : A // V x} => Arc x.1 y.1) ↔
      ∃ Lt : A → A → Prop, TopoOn V Lt Arc := by
  constructor
  · intro hac
    obtain ⟨Lt, htrans, hirr, hmono⟩ := (acyclicRel_iff_exists_order _).mp hac
    exact ⟨fun x y => ∃ (hx : V x) (hy : V y), Lt ⟨x, hx⟩ ⟨y, hy⟩,
      fun x _ ⟨hx₁, _, hlt⟩ => hirr ⟨x, hx₁⟩ hlt,
      fun x _ z hx _ hz ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => ⟨hx, hz, htrans _ _ _ h₁ h₂⟩,
      fun x y hx hy harc => ⟨hx, hy, hmono ⟨x, hx⟩ ⟨y, hy⟩ harc⟩⟩
  · rintro ⟨Lt, hirr, htrans, hmono⟩
    refine (acyclicRel_iff_exists_order _).mpr
      ⟨fun x y => Lt x.1 y.1, fun x y z h₁ h₂ => htrans _ _ _ x.2 y.2 z.2 h₁ h₂,
        fun x => hirr x.1 x.2, fun a b h => hmono _ _ a.2 b.2 h⟩


-- @@ L149-149 verbatim
end Topo


-- @@ L151-151 verbatim
/-! ### The problem -/


-- @@ L153-153 verbatim
section Shorthands


-- @@ L155-155 verbatim
variable {A : Type} [Language.twoDags.Structure A]


-- @@ L157-157 verbatim
fo_predicates Language.twoDags td


-- @@ L159-159 verbatim
end Shorthands


-- @@ L161-161 verbatim
section Problem


-- @@ L163-163 verbatim
variable (A : Type) [Language.twoDags.Structure A]


-- @@ L165-172 verbatim
/-- Both sides are well-formed – each order relation is a topological order of
its arcs, so both marked arc relations are acyclic – and the two DAGs are
isomorphic. The isomorphism relates the arcs only: the two orders are the
instance's acyclicity witnesses, not part of the structure being matched. -/
def HasDagIso : Prop :=
  Finite A ∧ TopoOn (TDPatV (A := A)) TDPatLt TDPatArc ∧
    TopoOn (TDHostV (A := A)) TDHostLt TDHostArc ∧
    RelIsoOn (TDPatV (A := A)) TDHostV TDPatArc TDHostArc


-- @@ L174-174 verbatim
end Problem


-- @@ L176-176 verbatim
section Iso


-- @@ L178-178 verbatim
variable {A B : Type} [Language.twoDags.Structure A] [Language.twoDags.Structure B]


-- @@ L180-194 verbatim
/-- The DAG-isomorphism property is isomorphism-invariant.
Registered in the Lax archive as
[`Lax604544.IsomorphismInvariance.hasDagIso_iso`](https://laxarchive.org/lax-604544/Lax604544.IsomorphismInvariance.html#s-Lax604544.IsomorphismInvariance.hasDagIso_iso). -/
theorem hasDagIso_iso (e : A ≃[Language.twoDags] B) :
    HasDagIso A ↔ HasDagIso B :=
  and_congr e.toEquiv.finite_iff
    (and_congr
      (TopoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tdPatV a)
        (fun a b => relMap_equiv₂ e tdPatLt a b) fun a b => relMap_equiv₂ e tdPatArc a b)
      (and_congr
        (TopoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tdHostV a)
          (fun a b => relMap_equiv₂ e tdHostLt a b) fun a b => relMap_equiv₂ e tdHostArc a b)
        (RelIsoOn.equiv_iff e.toEquiv (fun a => relMap_equiv₁ e tdPatV a)
          (fun a => relMap_equiv₁ e tdHostV a) (fun a b => relMap_equiv₂ e tdPatArc a b)
          fun a b => relMap_equiv₂ e tdHostArc a b)))


-- @@ L196-196 verbatim
end Iso


-- @@ L198-204 verbatim
/-- DAG ISOMORPHISM, as a problem on two-DAG structures: are the two marked
DAGs isomorphic? Well-formedness – each side's order relation being a
topological order of its arcs – is part of the yes-condition, and is
first-order, unlike acyclicity itself. -/
def DagIso : DecisionProblem Language.twoDags where
  Holds := fun A inst => @HasDagIso A inst
  iso_invariant := fun e => hasDagIso_iso e


-- @@ L206-206 verbatim
end DescriptiveComplexity
