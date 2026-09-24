/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Lens.Distributivity


-- @@ L10-16 verbatim
/-!
# Examples for the left-distributivity laws of substitution

Regression tests instantiating the substitution-distributivity equivalences at
small concrete polynomials, and the guardrail witnessing that substitution does
*not* right-distribute over products (Spivak–Niu, Ex. 6.56).
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
universe u


-- @@ L22-22 verbatim
namespace PFunctor


-- @@ L24-24 verbatim
/-! ## Instantiating the distributivity equivalences -/


-- @@ L26-27 verbatim
/-- **Prop. 6.47 / (6.48)** (library `sumCompDistrib`) at `(y + 1) ◃ y`. -/
example := Lens.Equiv.sumCompDistrib (P := (y : PFunctor.{0, 0})) (Q := y) (R := 1)


-- @@ L29-30 verbatim
/-- **(6.50)** (library `sigmaCompDistrib`) at a `Bool`-indexed family of `y`s. -/
example := Lens.sigmaCompDistrib (P := (y : PFunctor.{0, 0})) (F := fun _ : Bool => y)


-- @@ L32-33 verbatim
/-- **(6.51)** at a `Bool`-indexed product of `y`s. -/
example := Lens.Equiv.piCompDistrib (P := (y : PFunctor.{0, 0})) (F := fun _ : Bool => y)


-- @@ L35-38 verbatim
/-- The indexed-product distributivity equivalence round-trips positions. -/
example (x : ((pi (fun _ : Bool => y.{0, 0})) ◃ y).A) :
    Lens.Equiv.piCompDistrib.invLens.toFunA
      (Lens.Equiv.piCompDistrib.toLens.toFunA x) = x := rfl


-- @@ L40-41 verbatim
/-- **(6.49)** at `y * y ◃ y`. -/
example := Lens.Equiv.prodCompDistrib (P := (y : PFunctor.{0, 0})) (Q := y) (R := y)


-- @@ L43-44 verbatim
/-- **(6.49)** at `(y + 1) * y ◃ 1`. -/
example := Lens.Equiv.prodCompDistrib (P := (y + 1 : PFunctor.{0, 0})) (Q := y) (R := 1)


-- @@ L46-47 verbatim
/-- **Ex. 6.55** at `C Bool * y ◃ y`. -/
example := Lens.Equiv.scalarCompDistrib (A := Bool) (p := (y : PFunctor.{0, 0})) (q := y)


-- @@ L49-49 verbatim
/-! ## The monomial hom-set equivalence -/


-- @@ L51-53 verbatim
/-- A lens out of a monomial round-trips through `A → p(B)`. -/
example {A B : Type} {p : PFunctor.{0, 0}} (l : Lens (A y^ B) p) :
    Lens.homMonomialEquiv.symm (Lens.homMonomialEquiv l) = l := rfl


-- @@ L55-57 verbatim
/-- A function `A → p(B)` round-trips through the lens. -/
example {A B : Type} {p : PFunctor.{0, 0}} (g : A → p.Obj B) :
    Lens.homMonomialEquiv (Lens.homMonomialEquiv.symm g) = g := rfl


-- @@ L59-62 verbatim
/-- The identity lens on `Bool y^ Unit` becomes `a ↦ ⟨a, id⟩`. -/
example :
    Lens.homMonomialEquiv (Lens.id (Bool y^ Unit))
      = (fun a => ⟨a, id⟩ : Bool → (Bool y^ Unit).Obj Unit) := rfl


-- @@ L64-68 verbatim
/-! ## Ex. 6.56: substitution does not right-distribute over products

With `p = y + 1`, `q = 1`, `r = 0`, the polynomial `p ◃ (q * r)` has a single
position while `(p ◃ q) * (p ◃ r)` has two, so the two sides cannot be
equivalent — substitution only distributes over products on the *left*. -/


-- @@ L70-84 verbatim
/-- The left-hand `p ◃ (q * r)` has at most one position. -/
theorem right_distrib_lhs_subsingleton :
    Subsingleton (((y + 1 : PFunctor.{0, 0}) ◃ ((1 : PFunctor.{0, 0}) * 0)).A) := by
  constructor
  rintro ⟨a, f⟩ ⟨a', f'⟩
  have hE : IsEmpty (((1 : PFunctor.{0, 0}) * 0).A) :=
    inferInstanceAs (IsEmpty (PUnit × PEmpty))
  match a, f with
  | Sum.inl _, f => exact (hE.false (f PUnit.unit)).elim
  | Sum.inr _, f =>
    match a', f' with
    | Sum.inl _, f' => exact (hE.false (f' PUnit.unit)).elim
    | Sum.inr _, f' =>
      have : f = f' := funext (fun e => e.elim)
      subst this; rfl


-- @@ L86-94 verbatim
/-- The right-hand `(p ◃ q) * (p ◃ r)` has at least two positions. -/
theorem right_distrib_rhs_nontrivial :
    Nontrivial ((((y + 1 : PFunctor.{0, 0}) ◃ 1) * ((y + 1 : PFunctor.{0, 0}) ◃ 0)).A) := by
  refine ⟨⟨⟨Sum.inl PUnit.unit, fun _ => PUnit.unit⟩, ⟨Sum.inr PUnit.unit, PEmpty.elim⟩⟩,
          ⟨⟨Sum.inr PUnit.unit, PEmpty.elim⟩, ⟨Sum.inr PUnit.unit, PEmpty.elim⟩⟩, ?_⟩
  intro h
  have h2 : (Sum.inl PUnit.unit : PUnit ⊕ PUnit) = Sum.inr PUnit.unit :=
    congrArg (fun z => z.1.1) h
  exact absurd h2 (by decide)


-- @@ L96-104 verbatim
/-- Consequently there is no bijection between the two position types, so no
lens-equivalence right-distributes substitution over the product. -/
example :
    IsEmpty ((((y + 1 : PFunctor.{0, 0}) ◃ ((1 : PFunctor.{0, 0}) * 0)).A) ≃
      ((((y + 1 : PFunctor.{0, 0}) ◃ 1) * ((y + 1 : PFunctor.{0, 0}) ◃ 0)).A)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨x, y, hxy⟩ := right_distrib_rhs_nontrivial.exists_pair_ne
  exact hxy (e.symm.injective
    (@Subsingleton.elim _ right_distrib_lhs_subsingleton (e.symm x) (e.symm y)))


-- @@ L106-106 verbatim
end PFunctor
