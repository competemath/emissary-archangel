/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Hamilton.Defs
import DescriptiveComplexity.Problems.CliqueFamily.Defs
import DescriptiveComplexity.Relativized
import DescriptiveComplexity.OrderWalk


-- @@ L12-42 verbatim
/-!
# The Vertex Cover → Hamilton Circuit gadget interpretation

This file defines the relativized ordered first-order interpretation
`DescriptiveComplexity.hamInterp` that reduces VERTEX COVER (on marked graphs) to
(undirected) HAMILTON CIRCUIT (on digraphs read symmetrically), the classical
twelve-vertex cover-testing-gadget reduction of [Karp 1972][karp1972reducibility],
read in the tagged framework.

The output graph `hamInterp.MapRel A` has these vertices (all carried by a pair
of input vertices, `dim = 2`, cut down by a **domain formula** – hence a
*relativized* interpretation, `DescriptiveComplexity.RelFOInterpretation`):

* **gadget vertices** `⟨g i, (a, b)⟩` for `i : Fin 6` (tags `g0 … g5`), one per
  ordered pair `(a, b)` of adjacent distinct input vertices. The twelve vertices
  over the unordered edge `{u, v}` are `(u, v, 0..5)` (the `u`-side) and
  `(v, u, 0..5)` (the `v`-side): the *side* is which endpoint owns the tuple.
* **selector vertices** `⟨sel, (m, m)⟩`, one per *marked* input vertex `m`; they
  form a self-looped clique and attach to the ends of every vertex's chain.
* one **hub** vertex `⟨hub, (min, min)⟩`, present only for the degenerate input
  with no edges and no marks (where the output would otherwise be empty); it is
  a self-looped isolated vertex, so it is a one-element Hamilton circuit, which
  matches the (vacuous) yes-instance.

The gadget's edges force, in any Hamilton circuit, one of exactly three
traversals of `{u, v}`: through the `u`-side, through the `v`-side, or both –
never neither. So each edge is *covered*, and the number of vertices whose
chains are traversed – the cover – is at most the number of selectors, the
marked set. This file only builds the interpretation and characterizes its
adjacency; the two directions of correctness are in `Forward` and `Reverse`.
-/


-- @@ L44-44 verbatim
namespace DescriptiveComplexity


-- @@ L46-46 verbatim
open FirstOrder


-- @@ L48-48 verbatim
open Language Structure BoundedFormula


-- @@ L50-52 verbatim
/-- The ordered expansion of the marked-graph vocabulary, the source language of
the reduction. -/
abbrev hamL : Language := Language.markedGraph.sum Language.order


-- @@ L54-55 verbatim
/-- The adjacency symbol over the ordered expansion of marked graphs. -/
abbrev hAdjSym : hamL.Relations 2 := Sum.inl mgAdj


-- @@ L57-58 verbatim
/-- The mark symbol over the ordered expansion of marked graphs. -/
abbrev hMarkedSym : hamL.Relations 1 := Sum.inl mgMarked


-- @@ L60-60 verbatim
/-! ### Edge and neighbor-order formulas -/


-- @@ L62-62 verbatim
section Formulas


-- @@ L64-64 verbatim
variable {α : Type}


-- @@ L66-69 verbatim
/-- Symmetric adjacency: an arc in either direction. -/
private noncomputable def adjOrF (s t : α) : hamL.Formula α :=
  Relations.formula₂ hAdjSym (Term.var s) (Term.var t) ⊔
    Relations.formula₂ hAdjSym (Term.var t) (Term.var s)


-- @@ L71-74 verbatim
/-- The two variables name an (undirected) edge: adjacent in some direction,
and distinct. -/
private noncomputable def edgeF (s t : α) : hamL.Formula α :=
  adjOrF s t ⊓ ∼(Term.equal (Term.var s) (Term.var t))


-- @@ L76-78 expanded
/-- `b` is the least neighbor of `a`: it is `≤` every neighbor of `a`. -/
private noncomputable def minNbrF (a b : α) : hamL.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    ((edgeF (Sum.inl a) (Sum.inr 0)).imp (leF (Sum.inl b) (Sum.inr 0)))


-- @@ L80-82 expanded
/-- `b` is the greatest neighbor of `a`. -/
private noncomputable def maxNbrF (a b : α) : hamL.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    ((edgeF (Sum.inl a) (Sum.inr 0)).imp (leF (Sum.inr 0) (Sum.inl b)))


-- @@ L84-89 expanded
/-- `c` is the immediate neighbor-successor of `b` in `a`'s neighbor list: `c`
is a neighbor of `a`, `b < c`, and no neighbor of `a` lies strictly between
`b` and `c`. -/
private noncomputable def succNbrF (a b c : α) : hamL.Formula α :=
  edgeF a c ⊓ ltF b c ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((edgeF (Sum.inl a) (Sum.inr 0)).imp
        (leF (Sum.inr 0) (Sum.inl b) ⊔ leF (Sum.inl c) (Sum.inr 0)))


-- @@ L91-91 verbatim
end Formulas


-- @@ L93-93 verbatim
/-! ### Edge predicate on the input -/


-- @@ L95-95 verbatim
section EdgePred


-- @@ L97-97 verbatim
variable {A : Type} [Language.markedGraph.Structure A]


-- @@ L99-101 verbatim
/-- The undirected edge relation on the input: adjacent in some direction, and
distinct. -/
def HEdge (a b : A) : Prop := (MGAdj a b ∨ MGAdj b a) ∧ a ≠ b


-- @@ L103-104 verbatim
theorem hEdge_symm {a b : A} (h : HEdge a b) : HEdge b a :=
  ⟨h.1.symm, fun he => h.2 he.symm⟩


-- @@ L106-106 verbatim
end EdgePred


-- @@ L108-108 verbatim
/-! ### Realization of the edge and neighbor formulas -/


-- @@ L110-110 verbatim
section Realize


-- @@ L112-112 verbatim
variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A] {α : Type} (v : α → A)


-- @@ L114-118 verbatim
@[simp]
theorem realize_adjOrF (s t : α) :
    (adjOrF s t).Realize v ↔ MGAdj (v s) (v t) ∨ MGAdj (v t) (v s) := by
  rw [adjOrF, Formula.realize_sup, Formula.realize_rel₂, Formula.realize_rel₂]
  simp [MGAdj]


-- @@ L120-124 verbatim
@[simp]
theorem realize_edgeF (s t : α) :
    (edgeF s t).Realize v ↔ HEdge (v s) (v t) := by
  rw [edgeF, Formula.realize_inf, Formula.realize_not, Formula.realize_equal, realize_adjOrF]
  rfl


-- @@ L126-131 verbatim
theorem realize_minNbrF (a b : α) :
    (minNbrF a b).Realize v ↔ ∀ d : A, HEdge (v a) d → v b ≤ d := by
  rw [minNbrF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, realize_edgeF, realize_leF,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h d => h (fun _ => d), fun h i => h (i 0)⟩


-- @@ L133-138 verbatim
theorem realize_maxNbrF (a b : α) :
    (maxNbrF a b).Realize v ↔ ∀ d : A, HEdge (v a) d → d ≤ v b := by
  rw [maxNbrF]
  simp only [Formula.realize_iAlls, Formula.realize_imp, realize_edgeF, realize_leF,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h d => h (fun _ => d), fun h i => h (i 0)⟩


-- @@ L140-147 verbatim
theorem realize_succNbrF (a b c : α) :
    (succNbrF a b c).Realize v ↔ HEdge (v a) (v c) ∧ v b < v c ∧
      ∀ d : A, HEdge (v a) d → d ≤ v b ∨ v c ≤ d := by
  rw [succNbrF]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_sup,
    realize_edgeF, realize_ltF, realize_leF, Sum.elim_inl, Sum.elim_inr, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  exact ⟨fun h d => h (fun _ => d), fun h i => h (i 0)⟩


-- @@ L149-149 verbatim
end Realize


-- @@ L151-151 verbatim
/-! ### The tags and the interpretation -/


-- @@ L153-174 verbatim
/-- The tags of the interpreted structure. Six gadget-node indices (the *side*,
`u` vs `v`, is encoded by which endpoint owns the carrying tuple), one selector,
one degenerate-case hub. Named constructors, not `Fin 8`, so the tag match
inside the defining formulas reduces definitionally in the characterizations. -/
inductive HTag
  /-- Gadget node `0`: the entrance of a side. -/
  | g0
  /-- Gadget node `1`. -/
  | g1
  /-- Gadget node `2`. -/
  | g2
  /-- Gadget node `3`. -/
  | g3
  /-- Gadget node `4`. -/
  | g4
  /-- Gadget node `5`: the exit of a side. -/
  | g5
  /-- A selector, one per marked vertex. -/
  | sel
  /-- The degenerate-case hub. -/
  | hub
  deriving DecidableEq


-- @@ L176-177 verbatim
instance : Fintype HTag :=
  ⟨{.g0, .g1, .g2, .g3, .g4, .g5, .sel, .hub}, fun t => by cases t <;> decide⟩


-- @@ L179-179 verbatim
instance : Inhabited HTag := ⟨.sel⟩


-- @@ L181-183 expanded
/-- Two tuples are equal, coordinatewise. -/
private noncomputable def hEqTupF : hamL.Formula (Fin 2 × Fin 2) :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0))
      (FirstOrder.Language.Term.var (1, 0)) ⊓
    FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 1))
      (FirstOrder.Language.Term.var (1, 1))


-- @@ L185-187 expanded
/-- The second tuple is the first swapped. -/
private noncomputable def hSwapTupF : hamL.Formula (Fin 2 × Fin 2) :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0))
      (FirstOrder.Language.Term.var (1, 1)) ⊓
    FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 1))
      (FirstOrder.Language.Term.var (1, 0))


-- @@ L189-192 expanded
/-- The chain edge from an exit `⟨g5, (a, b)⟩` to the next entrance
`⟨g0, (a, c)⟩`: same owner, and `c` the neighbor-successor of `b`. -/
private noncomputable def hChain50F : hamL.Formula (Fin 2 × Fin 2) :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0))
      (FirstOrder.Language.Term.var (1, 0)) ⊓
    succNbrF (0, 0) (0, 1) (1, 1)


-- @@ L194-196 expanded
/-- The chain edge the other way, from `⟨g0, (a, c)⟩` to `⟨g5, (a, b)⟩`. -/
private noncomputable def hChain05F : hamL.Formula (Fin 2 × Fin 2) :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (0, 0))
      (FirstOrder.Language.Term.var (1, 0)) ⊓
    succNbrF (0, 0) (1, 1) (0, 1)


-- @@ L198-200 expanded
/-- No vertex is marked. -/
private noncomputable def noMarksF : hamL.Formula (Fin 2) :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    (FirstOrder.Language.BoundedFormula.not
      (FirstOrder.Language.Relations.formula₁ hMarkedSym
        (FirstOrder.Language.Term.var (Sum.inr 0))))


-- @@ L202-204 expanded
/-- No two vertices form an edge. -/
private noncomputable def noEdgesF : hamL.Formula (Fin 2) :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    (FirstOrder.Language.BoundedFormula.not (edgeF (Sum.inr 0) (Sum.inr 1)))


-- @@ L206-232 verbatim
/-- **The reduction of Vertex Cover into Hamilton Circuit**: the twelve-vertex
cover-testing gadget of each edge, chained along every vertex's neighbor list,
with the marked vertices as selectors. -/
noncomputable def hamInterp : RelFOInterpretation hamL Language.digraph HTag 2 where
  toFOInterpretation :=
    { relFormula := fun {n} R =>
        match n, R with
        | _, .arc => fun t =>
            match t 0, t 1 with
            | .g0, .g1 => hEqTupF | .g1, .g0 => hEqTupF
            | .g1, .g2 => hEqTupF | .g2, .g1 => hEqTupF
            | .g2, .g3 => hEqTupF | .g3, .g2 => hEqTupF
            | .g3, .g4 => hEqTupF | .g4, .g3 => hEqTupF
            | .g4, .g5 => hEqTupF | .g5, .g4 => hEqTupF
            | .g0, .g2 => hSwapTupF | .g2, .g0 => hSwapTupF
            | .g3, .g5 => hSwapTupF | .g5, .g3 => hSwapTupF
            | .g5, .g0 => hChain50F | .g0, .g5 => hChain05F
            | .sel, .g0 => minNbrF (1, 0) (1, 1) | .g0, .sel => minNbrF (0, 0) (0, 1)
            | .sel, .g5 => maxNbrF (1, 0) (1, 1) | .g5, .sel => maxNbrF (0, 0) (0, 1)
            | .sel, .sel => ⊤
            | .hub, .hub => ⊤
            | _, _ => ⊥ }
  domFormula := fun t =>
    match t with
    | .sel => Term.equal (Term.var 0) (Term.var 1) ⊓ Relations.formula₁ hMarkedSym (Term.var 0)
    | .hub => Term.equal (Term.var 0) (Term.var 1) ⊓ minF 0 ⊓ noMarksF ⊓ noEdgesF
    | _ => edgeF 0 1


-- @@ L234-234 verbatim
/-! ### Realization of the degenerate-case guards -/


-- @@ L236-236 verbatim
section DomRealize


-- @@ L238-238 verbatim
variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A] (w : Fin 2 → A)


-- @@ L240-245 verbatim
theorem realize_noMarksF : (noMarksF).Realize w ↔ ∀ y : A, ¬MGMarked y := by
  rw [noMarksF]
  simp only [Formula.realize_iAlls, Formula.realize_not, Formula.realize_rel₁, Term.realize_var,
    Sum.elim_inr]
  exact ⟨fun h y => by have := h (fun _ => y); simpa [MGMarked] using this,
    fun h i => by simpa [MGMarked] using h (i 0)⟩


-- @@ L247-250 verbatim
theorem realize_noEdgesF : (noEdgesF).Realize w ↔ ∀ y z : A, ¬HEdge y z := by
  rw [noEdgesF]
  simp only [Formula.realize_iAlls, Formula.realize_not, realize_edgeF, Sum.elim_inr]
  exact ⟨fun h y z => h ![y, z], fun h i => h (i 0) (i 1)⟩


-- @@ L252-252 verbatim
end DomRealize


-- @@ L254-254 verbatim
/-! ### The vertices of the interpreted graph -/


-- @@ L256-256 verbatim
section Points


-- @@ L258-258 verbatim
variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]


-- @@ L260-265 verbatim
/-- The domain formula of a gadget tag says the tuple is an edge. -/
theorem dom_gadget (t : HTag) (ht : t ≠ .sel ∧ t ≠ .hub) (w : Fin 2 → A) :
    (hamInterp.domFormula t).Realize w ↔ HEdge (w 0) (w 1) := by
  have : hamInterp.domFormula t = edgeF 0 1 := by
    cases t <;> first | rfl | (exfalso; simp_all)
  rw [this, realize_edgeF]


-- @@ L267-272 verbatim
theorem dom_sel (w : Fin 2 → A) :
    (hamInterp.domFormula .sel).Realize w ↔ w 0 = w 1 ∧ MGMarked (w 0) := by
  change (Term.equal (Term.var 0) (Term.var 1) ⊓
    Relations.formula₁ hMarkedSym (Term.var 0)).Realize w ↔ _
  rw [Formula.realize_inf, Formula.realize_equal, Formula.realize_rel₁]
  simp [MGMarked]


-- @@ L274-280 verbatim
theorem dom_hub (w : Fin 2 → A) :
    (hamInterp.domFormula .hub).Realize w ↔
      w 0 = w 1 ∧ (∀ a : A, w 0 ≤ a) ∧ (∀ y : A, ¬MGMarked y) ∧ ∀ y z : A, ¬HEdge y z := by
  change (Term.equal (Term.var 0) (Term.var 1) ⊓ minF 0 ⊓ noMarksF ⊓ noEdgesF).Realize w ↔ _
  rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_inf, Formula.realize_equal,
    realize_minF, realize_noMarksF, realize_noEdgesF]
  tauto


-- @@ L282-282 verbatim
end Points


-- @@ L284-284 verbatim
/-! ### The adjacency of the interpreted graph -/


-- @@ L286-286 verbatim
section Adjacency


-- @@ L288-288 verbatim
variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]


-- @@ L290-310 verbatim
/-- The intended (symmetric) adjacency of the interpreted graph, on raw tagged
tuples: the ten horizontal gadget edges, the four cross edges, the two chain
edges, the selector–entrance and selector–exit edges, the selector clique and
the hub self-loop. This is exactly what `DescriptiveComplexity.hamInterp` realizes
(`DescriptiveComplexity.dgArc_iff`). -/
def IAdjRaw (p q : HTag × (Fin 2 → A)) : Prop :=
  match p.1, q.1 with
  | .g0, .g1 | .g1, .g0 | .g1, .g2 | .g2, .g1 | .g2, .g3 | .g3, .g2
  | .g3, .g4 | .g4, .g3 | .g4, .g5 | .g5, .g4 => p.2 0 = q.2 0 ∧ p.2 1 = q.2 1
  | .g0, .g2 | .g2, .g0 | .g3, .g5 | .g5, .g3 => p.2 0 = q.2 1 ∧ p.2 1 = q.2 0
  | .g5, .g0 => p.2 0 = q.2 0 ∧ HEdge (p.2 0) (q.2 1) ∧ p.2 1 < q.2 1 ∧
      ∀ d, HEdge (p.2 0) d → d ≤ p.2 1 ∨ q.2 1 ≤ d
  | .g0, .g5 => p.2 0 = q.2 0 ∧ HEdge (p.2 0) (p.2 1) ∧ q.2 1 < p.2 1 ∧
      ∀ d, HEdge (p.2 0) d → d ≤ q.2 1 ∨ p.2 1 ≤ d
  | .sel, .g0 => ∀ d, HEdge (q.2 0) d → q.2 1 ≤ d
  | .g0, .sel => ∀ d, HEdge (p.2 0) d → p.2 1 ≤ d
  | .sel, .g5 => ∀ d, HEdge (q.2 0) d → d ≤ q.2 1
  | .g5, .sel => ∀ d, HEdge (p.2 0) d → d ≤ p.2 1
  | .sel, .sel => True
  | .hub, .hub => True
  | _, _ => False


-- @@ L312-322 verbatim
/-- **The adjacency of the interpreted graph**: `DescriptiveComplexity.hamInterp`
realizes exactly the intended edges `DescriptiveComplexity.IAdjRaw`. -/
theorem dgArc_iff (p q : hamInterp.MapRel A) : DGArc p q ↔ IAdjRaw p.1 q.1 := by
  obtain ⟨⟨t, w⟩, hp⟩ := p
  obtain ⟨⟨t', w'⟩, hq⟩ := q
  change RelMap (M := hamInterp.MapRel A) dgArc ![⟨(t, w), hp⟩, ⟨(t', w'), hq⟩] ↔ _
  rw [RelFOInterpretation.relMap_mapRel]
  cases t <;> cases t' <;>
    simp only [IAdjRaw] <;>
    simp [hamInterp, hEqTupF, hSwapTupF, hChain50F, hChain05F,
      realize_minNbrF, realize_maxNbrF, realize_succNbrF]


-- @@ L324-335 verbatim
/-- The intended adjacency is symmetric: every gadget, chain, selector and hub
edge appears in both directions. -/
theorem iAdjRaw_symm (p q : HTag × (Fin 2 → A)) : IAdjRaw p q ↔ IAdjRaw q p := by
  obtain ⟨t, w⟩ := p
  obtain ⟨t', w'⟩ := q
  cases t <;> cases t' <;> simp only [IAdjRaw] <;>
    first
      | rfl
      | (constructor <;> exact fun h => ⟨h.1.symm, h.2.symm⟩)
      | (constructor <;> exact fun h => ⟨h.2.symm, h.1.symm⟩)
      | (constructor <;> exact fun ⟨h0, h1, h2, h3⟩ =>
          ⟨h0.symm, by rw [← h0]; exact h1, h2, fun d hd => h3 d (by rw [h0]; exact hd)⟩)


-- @@ L337-340 verbatim
/-- `DGArc` on the interpreted graph is symmetric, so the symmetric reading
`DescriptiveComplexity.DGEdge` used by HAMILTON CIRCUIT coincides with it. -/
theorem dgEdge_iff (p q : hamInterp.MapRel A) : DGEdge p q ↔ IAdjRaw p.1 q.1 := by
  rw [DGEdge, dgArc_iff, dgArc_iff, iAdjRaw_symm q.1 p.1, or_self]


-- @@ L342-342 verbatim
end Adjacency


-- @@ L344-344 verbatim
/-! ### The vertices, as named constructors -/


-- @@ L346-346 verbatim
section Constructors


-- @@ L348-348 verbatim
variable {A : Type} [Language.markedGraph.Structure A] [LinearOrder A]


-- @@ L350-352 verbatim
/-- A gadget vertex `⟨t, (a, b)⟩` for a gadget tag `t` over an edge `(a, b)`. -/
def gPt (t : HTag) (ht : t ≠ .sel ∧ t ≠ .hub) {a b : A} (h : HEdge a b) : hamInterp.MapRel A :=
  ⟨(t, ![a, b]), (dom_gadget t ht ![a, b]).mpr (by simpa using h)⟩


-- @@ L354-356 verbatim
/-- A selector vertex, one per marked input vertex. -/
def selPt {m : A} (h : MGMarked m) : hamInterp.MapRel A :=
  ⟨(.sel, ![m, m]), (dom_sel ![m, m]).mpr ⟨rfl, by simpa using h⟩⟩


-- @@ L358-361 verbatim
/-- The degenerate-case hub vertex. -/
def hubPt {m : A} (hmin : ∀ a : A, m ≤ a) (hnm : ∀ y : A, ¬MGMarked y)
    (hne : ∀ y z : A, ¬HEdge y z) : hamInterp.MapRel A :=
  ⟨(.hub, ![m, m]), (dom_hub ![m, m]).mpr ⟨rfl, by simpa using hmin, hnm, hne⟩⟩


-- @@ L363-363 verbatim
@[simp] theorem gPt_tag (t : HTag) (ht) {a b : A} (h : HEdge a b) : (gPt t ht h).1.1 = t := rfl

-- @@ L364-364 verbatim
@[simp] theorem gPt_fst (t : HTag) (ht) {a b : A} (h : HEdge a b) : (gPt t ht h).1.2 0 = a := rfl

-- @@ L365-365 verbatim
@[simp] theorem gPt_snd (t : HTag) (ht) {a b : A} (h : HEdge a b) : (gPt t ht h).1.2 1 = b := rfl

-- @@ L366-366 verbatim
@[simp] theorem selPt_tag {m : A} (h : MGMarked m) : (selPt h).1.1 = HTag.sel := rfl

-- @@ L367-367 verbatim
@[simp] theorem selPt_fst {m : A} (h : MGMarked m) : (selPt h).1.2 0 = m := rfl


-- @@ L369-397 verbatim
/-- Every vertex of the interpreted graph is a gadget vertex, a selector, or the
hub. -/
theorem point_cases (p : hamInterp.MapRel A) :
    (∃ (t : HTag) (ht : t ≠ .sel ∧ t ≠ .hub) (h : HEdge (p.1.2 0) (p.1.2 1)),
        p = gPt t ht h) ∨
      (∃ h : MGMarked (p.1.2 0), p.1.2 0 = p.1.2 1 ∧ p = selPt h) ∨
      p.1.1 = HTag.hub := by
  obtain ⟨⟨t, w⟩, hd⟩ := p
  have hw : w = ![w 0, w 1] := by
    funext i; fin_cases i <;> rfl
  have gad : ∀ (s : HTag) (hs : s ≠ .sel ∧ s ≠ .hub)
      (hd' : (hamInterp.domFormula s).Realize w),
      (∃ (t' : HTag) (ht' : t' ≠ .sel ∧ t' ≠ .hub) (h : HEdge (w 0) (w 1)),
        (⟨(s, w), hd'⟩ : hamInterp.MapRel A) = gPt t' ht' h) := fun s hs hd' =>
    ⟨s, hs, (dom_gadget s hs w).mp hd',
      Subtype.ext (show ((s, w) : HTag × (Fin 2 → A)) = (s, ![w 0, w 1]) by
        rw [Prod.ext_iff]; exact ⟨rfl, hw⟩)⟩
  cases t
  case sel =>
    obtain ⟨heq, hm⟩ := (dom_sel w).mp hd
    refine Or.inr (Or.inl ⟨by simpa using hm, heq, ?_⟩)
    apply Subtype.ext
    simp only [selPt]
    rw [Prod.ext_iff]
    refine ⟨rfl, ?_⟩
    funext i
    fin_cases i <;> simp [heq]
  case hub => exact Or.inr (Or.inr rfl)
  all_goals (dsimp only at hd; exact Or.inl (gad _ ⟨by decide, by decide⟩ hd))


-- @@ L399-399 verbatim
end Constructors


-- @@ L401-401 verbatim
end DescriptiveComplexity
