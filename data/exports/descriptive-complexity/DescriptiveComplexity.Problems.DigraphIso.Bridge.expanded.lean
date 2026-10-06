/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.DigraphIso
import DescriptiveComplexity.GadgetDouble
import DescriptiveComplexity.Degree


-- @@ L11-29 verbatim
/-!
# Digraph Isomorphism is the generic isomorphism problem of the graph vocabulary

`DescriptiveComplexity.DigraphIso` was stated over the hand-rolled
`FirstOrder.Language.twoGraphs` before the generic
`FirstOrder.Language.twoCopies` existed. The two vocabularies are the same up
to renaming – `patV`/`patE` against the pattern mark and the pattern copy of
`adj` – and this file proves the problems are FO-interreducible, in both
directions, by the interpretation that renames the symbols.

The payoff is
`DescriptiveComplexity.below_digraphIso_eq_below_twoCopiesIso`: the degree of
`DescriptiveComplexity.DigraphIso` *is* the degree of
`DescriptiveComplexity.TwoCopiesIso FirstOrder.Language.graph`, and hence the
GI degree. A problem stated over `twoCopies` – as every entry added from here
on is meant to be – therefore reaches the degree through
`DescriptiveComplexity.isoReflecting_fo_reduction` and this bridge, with no
further vocabulary bookkeeping.
-/


-- @@ L31-31 verbatim
namespace DescriptiveComplexity


-- @@ L33-33 verbatim
open FirstOrder


-- @@ L35-35 verbatim
open Language Structure


-- @@ L37-37 verbatim
namespace DigraphBridge


-- @@ L39-39 verbatim
/-! ### Renaming the hand-rolled vocabulary to the generic one -/


-- @@ L41-49 expanded
/-- The interpretation renaming `twoGraphs` to `twoCopies graph`: one tag, one
dimension, each symbol to its counterpart. -/
def toTC : FOInterpretation Language.twoGraphs (Language.twoCopies Language.graph) Unit 1 where
  relFormula {n}
    R :=
    match n, R with
    | _, .patMark => fun _ =>
      FirstOrder.Language.Relations.formula₁ tgPatV (FirstOrder.Language.Term.var (0, 0))
    | _, .hostMark => fun _ =>
      FirstOrder.Language.Relations.formula₁ tgHostV (FirstOrder.Language.Term.var (0, 0))
    | _, .pat .adj => fun _ =>
      FirstOrder.Language.Relations.formula₂ tgPatE (FirstOrder.Language.Term.var (0, 0))
        (FirstOrder.Language.Term.var (1, 0))
    | _, .host .adj => fun _ =>
      FirstOrder.Language.Relations.formula₂ tgHostE (FirstOrder.Language.Term.var (0, 0))
        (FirstOrder.Language.Term.var (1, 0))


-- @@ L51-58 expanded
/-- The interpretation renaming `twoCopies graph` back to `twoGraphs`. -/
def ofTC : FOInterpretation (Language.twoCopies Language.graph) Language.twoGraphs Unit 1 where
  relFormula {n}
    R :=
    match n, R with
    | _, .patV => fun _ =>
      FirstOrder.Language.Relations.formula₁ (tcPatMark Language.graph)
        (FirstOrder.Language.Term.var (0, 0))
    | _, .hostV => fun _ =>
      FirstOrder.Language.Relations.formula₁ (tcHostMark Language.graph)
        (FirstOrder.Language.Term.var (0, 0))
    | _, .patE => fun _ =>
      FirstOrder.Language.Relations.formula₂ (tcPat Language.adj)
        (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))
    | _, .hostE => fun _ =>
      FirstOrder.Language.Relations.formula₂ (tcHost Language.adj)
        (FirstOrder.Language.Term.var (0, 0)) (FirstOrder.Language.Term.var (1, 0))


-- @@ L60-60 verbatim
/-! ### The one-dimensional universe -/


-- @@ L62-62 verbatim
section Points


-- @@ L64-64 verbatim
variable {A : Type}


-- @@ L66-67 verbatim
/-- The unique copy of an element, going to the generic vocabulary. -/
def toPt (v : A) : toTC.Map A := ((), fun _ => v)


-- @@ L69-70 verbatim
/-- The unique copy of an element, coming back. -/
def ofPt (v : A) : ofTC.Map A := ((), fun _ => v)


-- @@ L72-77 verbatim
/-- The image universe is a copy of the original. -/
def toEquivMap : toTC.Map A ≃ A where
  toFun p := p.2 0
  invFun := toPt
  left_inv p := Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg p.2 (Subsingleton.elim 0 i)⟩
  right_inv _ := rfl


-- @@ L79-84 verbatim
/-- The image universe is a copy of the original, coming back. -/
def ofEquivMap : ofTC.Map A ≃ A where
  toFun p := p.2 0
  invFun := ofPt
  left_inv p := Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg p.2 (Subsingleton.elim 0 i)⟩
  right_inv _ := rfl


-- @@ L86-86 verbatim
end Points


-- @@ L88-88 verbatim
/-! ### What the renamings realize -/


-- @@ L90-90 verbatim
section Realize


-- @@ L92-92 verbatim
variable {A : Type} [Language.twoGraphs.Structure A]


-- @@ L94-97 verbatim
theorem toTC_patMark (p : toTC.Map A) :
    TCPatMark (L₁ := Language.graph) p ↔ TGPatV (p.2 0) := by
  rw [TCPatMark, FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₁, TGPatV]


-- @@ L99-102 verbatim
theorem toTC_hostMark (p : toTC.Map A) :
    TCHostMark (L₁ := Language.graph) p ↔ TGHostV (p.2 0) := by
  rw [TCHostMark, FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₁, TGHostV]


-- @@ L104-107 verbatim
theorem toTC_patAdj (p q : toTC.Map A) :
    RelMap (tcPat Language.adj) ![p, q] ↔ TGPatE (p.2 0) (q.2 0) := by
  rw [FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₂, TGPatE]


-- @@ L109-112 verbatim
theorem toTC_hostAdj (p q : toTC.Map A) :
    RelMap (tcHost Language.adj) ![p, q] ↔ TGHostE (p.2 0) (q.2 0) := by
  rw [FOInterpretation.relMap_map]
  simp [toTC, Formula.realize_rel₂, TGHostE]


-- @@ L114-114 verbatim
end Realize


-- @@ L116-116 verbatim
section RealizeBack


-- @@ L118-118 verbatim
variable {A : Type} [(Language.twoCopies Language.graph).Structure A]


-- @@ L120-123 verbatim
theorem ofTC_patV (p : ofTC.Map A) :
    TGPatV p ↔ TCPatMark (L₁ := Language.graph) (p.2 0) := by
  rw [TGPatV, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₁, TCPatMark]


-- @@ L125-128 verbatim
theorem ofTC_hostV (p : ofTC.Map A) :
    TGHostV p ↔ TCHostMark (L₁ := Language.graph) (p.2 0) := by
  rw [TGHostV, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₁, TCHostMark]


-- @@ L130-133 verbatim
theorem ofTC_patE (p q : ofTC.Map A) :
    TGPatE p q ↔ RelMap (tcPat Language.adj) ![p.2 0, q.2 0] := by
  rw [TGPatE, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₂]


-- @@ L135-138 verbatim
theorem ofTC_hostE (p q : ofTC.Map A) :
    TGHostE p q ↔ RelMap (tcHost Language.adj) ![p.2 0, q.2 0] := by
  rw [TGHostE, FOInterpretation.relMap_map]
  simp [ofTC, Formula.realize_rel₂]


-- @@ L140-140 verbatim
end RealizeBack


-- @@ L142-142 verbatim
/-! ### The generic side condition, as a relation isomorphism -/


-- @@ L144-144 verbatim
section Generic


-- @@ L146-146 verbatim
variable {B : Type} [(Language.twoCopies Language.graph).Structure B]


-- @@ L148-149 verbatim
/-- The pattern relation of a `twoCopies graph`-structure. -/
def TCPatAdj (x y : B) : Prop := RelMap (tcPat Language.adj) ![x, y]


-- @@ L151-152 verbatim
/-- The host relation of a `twoCopies graph`-structure. -/
def TCHostAdj (x y : B) : Prop := RelMap (tcHost Language.adj) ![x, y]


-- @@ L154-161 verbatim
/-- The pattern side's adjacency, read on the ambient structure. -/
theorem patSide_relMap (a b : {x : B // TCPatMark (L₁ := Language.graph) x}) :
    RelMap (L := Language.graph) Language.adj ![a, b] ↔ TCPatAdj a.1 b.1 := by
  change RelMap (tcPat Language.adj)
    (fun i => ((![a, b] : Fin 2 → {x : B // TCPatMark (L₁ := Language.graph) x}) i).1) ↔ _
  rw [show (fun i => ((![a, b] : Fin 2 → {x : B // TCPatMark (L₁ := Language.graph) x}) i).1)
      = ![a.1, b.1] by funext i; fin_cases i <;> rfl]
  exact Iff.rfl


-- @@ L163-170 verbatim
/-- The host side's adjacency, read on the ambient structure. -/
theorem hostSide_relMap (a b : {x : B // TCHostMark (L₁ := Language.graph) x}) :
    RelMap (L := Language.graph) Language.adj ![a, b] ↔ TCHostAdj a.1 b.1 := by
  change RelMap (tcHost Language.adj)
    (fun i => ((![a, b] : Fin 2 → {x : B // TCHostMark (L₁ := Language.graph) x}) i).1) ↔ _
  rw [show (fun i => ((![a, b] : Fin 2 → {x : B // TCHostMark (L₁ := Language.graph) x}) i).1)
      = ![a.1, b.1] by funext i; fin_cases i <;> rfl]
  exact Iff.rfl


-- @@ L172-197 verbatim
/-- **The generic isomorphism condition is the concrete one**: an isomorphism
of the two sides, over the graph vocabulary, is a bijection of the two marks
preserving the two relations. Stated through
`DescriptiveComplexity.relIsoOn_iff_equiv`, whose right-hand side mentions no
structure, so the two presentations of a side never have to be identified as
instances. -/
theorem nonempty_tcSideEquiv_iff_relIsoOn :
    Nonempty (TCSideEquiv (L₁ := Language.graph) B) ↔
      RelIsoOn (TCPatMark (L₁ := Language.graph)) (TCHostMark (L₁ := Language.graph))
        (TCPatAdj (B := B)) TCHostAdj := by
  rw [relIsoOn_iff_equiv]
  constructor
  · rintro ⟨e⟩
    refine ⟨e.toEquiv, fun x y => ?_⟩
    have h := e.map_rel' Language.adj ![x, y]
    rw [show (e.toFun ∘ ![x, y]) = ![e.toEquiv x, e.toEquiv y] by
      funext i; fin_cases i <;> rfl, hostSide_relMap, patSide_relMap] at h
    exact h.symm
  · rintro ⟨e, hedge⟩
    refine ⟨{ toEquiv := e, map_fun' := fun f => isEmptyElim f, map_rel' := ?_ }⟩
    intro n r x
    cases r
    rw [show x = ![x 0, x 1] by funext i; fin_cases i <;> rfl]
    rw [show (e.toFun ∘ ![x 0, x 1]) = ![e.toFun (x 0), e.toFun (x 1)] by
      funext i; fin_cases i <;> rfl, hostSide_relMap, patSide_relMap]
    exact (hedge (x 0) (x 1)).symm


-- @@ L199-199 verbatim
end Generic


-- @@ L201-201 verbatim
/-! ### Correctness of the two renamings -/


-- @@ L203-203 verbatim
section Correctness


-- @@ L205-218 verbatim
/-- Going to the generic vocabulary preserves the answer. -/
theorem toTC_correct (A : Type) [Language.twoGraphs.Structure A] [Finite A] :
    DigraphIso.Holds A ↔ (TwoCopiesIso Language.graph).Holds (toTC.Map A) := by
  have hrel : RelIsoOn (TCPatMark (L₁ := Language.graph)) TCHostMark
      (TCPatAdj (B := toTC.Map A)) TCHostAdj ↔
      RelIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE :=
    RelIsoOn.equiv_iff toEquivMap (fun p => toTC_patMark p) (fun p => toTC_hostMark p)
      (fun p q => toTC_patAdj p q) fun p q => toTC_hostAdj p q
  constructor
  · rintro ⟨-, h⟩
    exact ⟨toTC.map_finite A,
      (nonempty_tcSideEquiv_iff_relIsoOn).mpr (hrel.mpr h)⟩
  · rintro ⟨-, h⟩
    exact ⟨‹Finite A›, hrel.mp ((nonempty_tcSideEquiv_iff_relIsoOn).mp h)⟩


-- @@ L220-231 verbatim
/-- Coming back preserves the answer. -/
theorem ofTC_correct (A : Type) [(Language.twoCopies Language.graph).Structure A] [Finite A] :
    (TwoCopiesIso Language.graph).Holds A ↔ DigraphIso.Holds (ofTC.Map A) := by
  have hrel : RelIsoOn (TGPatV (A := ofTC.Map A)) TGHostV TGPatE TGHostE ↔
      RelIsoOn (TCPatMark (L₁ := Language.graph)) TCHostMark (TCPatAdj (B := A)) TCHostAdj :=
    RelIsoOn.equiv_iff ofEquivMap (fun p => ofTC_patV p) (fun p => ofTC_hostV p)
      (fun p q => ofTC_patE p q) fun p q => ofTC_hostE p q
  constructor
  · rintro ⟨-, h⟩
    exact ⟨ofTC.map_finite A, hrel.mpr ((nonempty_tcSideEquiv_iff_relIsoOn).mp h)⟩
  · rintro ⟨-, h⟩
    exact ⟨‹Finite A›, (nonempty_tcSideEquiv_iff_relIsoOn).mpr (hrel.mp h)⟩


-- @@ L233-233 verbatim
end Correctness


-- @@ L235-235 verbatim
end DigraphBridge


-- @@ L237-237 verbatim
/-! ### The two reductions, and the degree -/


-- @@ L239-245 verbatim
/-- **Digraph Isomorphism reduces to the generic isomorphism problem** of the
graph vocabulary, by renaming the symbols. -/
def digraphIso_fo_reduction_twoCopiesIso : DigraphIso ≤ᶠᵒ TwoCopiesIso Language.graph where
  Tag := Unit
  dim := 1
  toInterpretation := DigraphBridge.toTC
  correct A _ _ _ := DigraphBridge.toTC_correct A


-- @@ L247-252 verbatim
/-- And back. -/
def twoCopiesIso_fo_reduction_digraphIso : TwoCopiesIso Language.graph ≤ᶠᵒ DigraphIso where
  Tag := Unit
  dim := 1
  toInterpretation := DigraphBridge.ofTC
  correct A _ _ _ := DigraphBridge.ofTC_correct A


-- @@ L254-262 verbatim
/-- **Digraph Isomorphism and the generic isomorphism problem of the graph
vocabulary have the same degree.** A problem stated over `twoCopies` reaches the
GI degree through this equality, so
`DescriptiveComplexity.isoReflecting_fo_reduction` – a gadget on single
structures – is all a new entry needs. -/
theorem below_digraphIso_eq_below_twoCopiesIso :
    ComplexityClass.below DigraphIso = ComplexityClass.below (TwoCopiesIso Language.graph) :=
  ComplexityClass.below_congr ⟨digraphIso_fo_reduction_twoCopiesIso.toOrdered⟩
    ⟨twoCopiesIso_fo_reduction_digraphIso.toOrdered⟩


-- @@ L264-264 verbatim
end DescriptiveComplexity
