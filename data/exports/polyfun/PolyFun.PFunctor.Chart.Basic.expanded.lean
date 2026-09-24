/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.Equiv.Basic
import Batteries.Tactic.Lint


-- @@ L12-56 verbatim
/-!
# Charts between polynomial functors

A `Chart P Q` is a pair `(toFunA, toFunB)` where

* `toFunA : P.A → Q.A` is a forward map on positions, and
* `toFunB : ∀ a, P.B a → Q.B (toFunA a)` is a forward map on directions.

While **lenses** make `Poly` into a 2-category whose categorical product is
`*` (positions ×, directions Σ), **charts** make `Poly` into a different
category that is isomorphic to the arrow category `Set^→` (squares
`B → A → B' → A'`). A consequence is that the chart category has a
*different* monoidal structure from the lens category.

## Comparison with `Lens`

|              | Lens                                     | Chart                            |
|--------------|------------------------------------------|----------------------------------|
| Coproduct    | `+`                                      | `+` (same)                       |
| Product      | `*` (positions ×, directions ⊕)          | `⊗` (positions ×, directions ×)  |
| Terminal     | `1` (positions = 1, no directions)       | `y = y` (positions = 1, dir = 1) |
| Composition  | `compMap` is natural                     | `compMap` is **not** natural     |
| Sigma        | `sigmaExists`, `sigmaMap`                | `sigmaExists`, `sigmaMap`        |
| Pi           | `piForall`, `piMap`                      | only `piMap`                     |

The operations missing from charts (`compMap`, `piForall`, projections from
`*`, `sigmaForall`) all require contravariance and so are intrinsically
lens-side. What charts do have, they have cleanly: `+` is the coproduct
with `inl`/`inr`/`sumPair`, and `⊗` is the categorical product with
`fst`/`snd`/`tensorPair`.

## Layout

This file mirrors `PolyFun/PFunctor/Lens/Basic.lean` for ease of
cross-reference. Each section header that overlaps with `Lens` is named
identically; the chart-specific sections (`Tensor` for the categorical
product, `Prod` for the polynomial product) are documented inline.

## Downstream consumers

`Interface.Hom`, `Interface.Hom.mapPacket`, and the boundary-side composition
operators are intentionally thin wrappers around this file. New downstream
operators on packet/index transport (e.g. parallel composition, sum routing)
should be defined as wrappers, not re-implemented.
-/


-- @@ L58-58 verbatim
@[expose] public section


-- @@ L60-60 verbatim
universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆


-- @@ L62-62 verbatim
namespace PFunctor


-- @@ L64-64 verbatim
namespace Chart


-- @@ L66-78 verbatim
@[ext (iff := false)]
theorem ext {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (c₁ c₂ : Chart P Q)
    (h₁ : ∀ a, c₁.toFunA a = c₂.toFunA a) (h₂ : ∀ a, c₁.toFunB a = (h₁ a) ▸ c₂.toFunB a) :
    c₁ = c₂ := by
  rcases c₁ with ⟨toFunA₁, toFunB₁⟩
  rcases c₂ with ⟨toFunA₂, toFunB₂⟩
  have h : toFunA₁ = toFunA₂ := funext h₁
  subst h
  have hB : toFunB₁ = toFunB₂ := by
    funext a
    simpa using h₂ a
  subst hB
  rfl


-- @@ L80-80 verbatim
/-! ### Identity and composition -/


-- @@ L82-83 expanded
/-- The identity chart -/
protected def id (P : PFunctor.{uA, uB}) : Chart P P :=
  Chart.mk id fun _ => id


-- @@ L85-89 verbatim
/-- Composition of charts -/
def comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (c' : Chart Q R) (c : Chart P Q) : Chart P R where
  toFunA := c'.toFunA ∘ c.toFunA
  toFunB := fun i => c'.toFunB (c.toFunA i) ∘ c.toFunB i


-- @@ L91-92 verbatim
/-- Infix notation for chart composition `c' ∘c c` -/
infixl:75 " ∘c " => comp


-- @@ L94-96 verbatim
/-- Diagrammatic composition of charts: `c ⨟ c'` applies `c` first and `c'`
second, the book's left-to-right composition order, so `c ⨟ c' = c' ∘c c`. -/
notation:75 c:75 " ⨟ " c':76 => Chart.comp c' c


-- @@ L98-100 expanded
@[simp]
theorem id_comp {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Chart P Q) :
    comp (Chart.id Q) f = f :=
  rfl


-- @@ L102-104 expanded
@[simp]
theorem comp_id {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (f : Chart P Q) :
    comp f (Chart.id P) = f :=
  rfl


-- @@ L106-108 expanded
theorem comp_assoc {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {S : PFunctor.{uA₄, uB₄}} (c : Chart R S) (c' : Chart Q R) (c'' : Chart P Q) :
    comp (comp c c') c'' = comp c (comp c' c'') :=
  rfl


-- @@ L110-110 verbatim
/-! ### Equivalences -/


-- @@ L112-121 verbatim
/-- An equivalence between two polynomial functors `P` and `Q`, using charts.
    This corresponds to an isomorphism in the category `PFunctor` with `Chart` morphisms. -/
@[ext]
protected structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward chart of the equivalence, from `P` to `Q`. -/
  toChart : Chart P Q
  /-- The backward chart of the equivalence, from `Q` to `P`. -/
  invChart : Chart Q P
  left_inv : comp invChart toChart = Chart.id P := by simp
  right_inv : comp toChart invChart = Chart.id Q := by simp


-- @@ L123-124 verbatim
/-- Infix notation for chart equivalence `P ≃c Q` -/
infix:50 " ≃c " => Chart.Equiv


-- @@ L126-126 verbatim
namespace Equiv


-- @@ L128-131 expanded
/-- The identity equivalence on `P`, built from the identity chart in both directions. -/
@[refl]
def refl (P : PFunctor.{uA, uB}) : Chart.Equiv P P :=
  ⟨Chart.id P, Chart.id P, rfl, rfl⟩


-- @@ L133-136 expanded
/-- The inverse equivalence, swapping the forward and backward charts of `e`. -/
@[symm]
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : Chart.Equiv P Q) :
    Chart.Equiv Q P :=
  ⟨e.invChart, e.toChart, e.right_inv, e.left_inv⟩


-- @@ L138-150 expanded
/-- The composite equivalence `P ≃c R` obtained by chaining `e₁ : P ≃c Q` and `e₂ : Q ≃c R`. -/
@[trans]
def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (e₁ : Chart.Equiv P Q) (e₂ : Chart.Equiv Q R) : Chart.Equiv P R :=
  ⟨comp e₂.toChart e₁.toChart, comp e₁.invChart e₂.invChart,
    by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.left_inv, e₂.left_inv], by
    rw [comp_assoc]
    rw (occs := [2]) [← comp_assoc]
    simp [e₁.right_inv, e₂.right_inv]⟩


-- @@ L152-152 verbatim
end Equiv


-- @@ L154-154 verbatim
/-! ### Initial and terminal -/


-- @@ L156-158 expanded
/-- The (unique) initial chart from the zero functor to any functor `P`. -/
def initial {P : PFunctor.{uA, uB}} : Chart 0 P :=
  Chart.mk PEmpty.elim fun _ => PEmpty.elim


-- @@ L160-166 expanded
/-- The (unique) terminal chart from any functor `P` to `y = y`.

`y` is the terminal object of the chart category — a single position with a
single direction — corresponding to the identity arrow `1 → 1` in `Set^→`.
This differs from the lens-side terminal `1` (positions `1`, no directions). -/
def terminal {P : PFunctor.{uA, uB}} : Chart P y :=
  Chart.mk (fun _ => PUnit.unit) (fun _ _ => PUnit.unit)


-- @@ L168-168 verbatim
alias fromZero := initial

-- @@ L169-169 verbatim
alias toOne := terminal


-- @@ L171-176 verbatim
/-! ### Coproduct (`+`)

`+` is the coproduct in the chart category (as it is in the lens category).
The two inclusions `inl`/`inr` plus the copairing `sumPair` realise the
universal property of `+`. The parallel-sum `sumMap` is then a derived
construction. -/


-- @@ L178-181 expanded
/-- Left injection chart `inl : P → P + Q`. -/
def inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Chart.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q) :=
  Chart.mk Sum.inl fun _ => id


-- @@ L183-186 expanded
/-- Right injection chart `inr : Q → P + Q`. -/
def inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    Chart.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q) :=
  Chart.mk Sum.inr fun _ => id


-- @@ L188-194 expanded
/-- Copairing of charts `[c₁, c₂]c : P + Q → R`. -/
def sumPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB₃}}
    (c₁ : Chart P R) (c₂ : Chart Q R) : Chart.{max uA₁ uA₂, uB, uA₃, uB₃} (P + Q) R :=
  Chart.mk (Sum.elim c₁.toFunA c₂.toFunA) fun
    | .inl pa => c₁.toFunB pa
    | .inr qa => c₂.toFunB qa


-- @@ L196-202 expanded
/-- Parallel application of charts for coproduct `c₁ ⊎c c₂ : P + Q → R + W`. -/
def sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₃}} (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.{max uA₁ uA₂, uB₁, max uA₃ uA₄, uB₃} (P + Q) (R + W) :=
  Chart.mk (Sum.map c₁.toFunA c₂.toFunA) fun
    | .inl pa => c₁.toFunB pa
    | .inr qa => c₂.toFunB qa


-- @@ L204-208 verbatim
/-! ### Tensor (`⊗`) — the chart category's binary product

`⊗` is the **categorical** binary product in the chart category, with
projections `fst`/`snd` and pairing `tensorPair`. (For lenses, the
categorical product is `*`, not `⊗`.) -/


-- @@ L210-213 expanded
/-- Projection chart `fst : P ⊗ Q → P`. -/
def fst {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, uA₁, uB₁} (P ⊗ Q) P :=
  Chart.mk Prod.fst (fun _ => Prod.fst)


-- @@ L215-218 expanded
/-- Projection chart `snd : P ⊗ Q → Q`. -/
def snd {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, uA₂, uB₂} (P ⊗ Q) Q :=
  Chart.mk Prod.snd (fun _ => Prod.snd)


-- @@ L220-225 expanded
/-- Pairing of charts `⟨c₁, c₂⟩c : P → Q ⊗ R`. -/
def tensorPair {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (c₁ : Chart P Q) (c₂ : Chart P R) : Chart.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q ⊗ R) :=
  Chart.mk (fun pa => (c₁.toFunA pa, c₂.toFunA pa))
    (fun pa pb => (c₁.toFunB pa pb, c₂.toFunB pa pb))


-- @@ L227-232 expanded
/-- Parallel application of charts for tensor `c₁ ⊗c c₂ : P ⊗ Q → R ⊗ W`. -/
def tensorMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P ⊗ Q) (R ⊗ W) :=
  Chart.mk (Prod.map c₁.toFunA c₂.toFunA) fun (pa, qa) => Prod.map (c₁.toFunB pa) (c₂.toFunB qa)


-- @@ L234-241 verbatim
/-! ### Polynomial product (`*`) — *not* the chart categorical product

The polynomial product `*` is **not** the categorical product in the chart
category: there is no natural chart `P * Q → P` because the source has
direction type `P.B a₁ ⊕ Q.B a₂` and we cannot project a `Q.B a₂` to a
`P.B a₁`. We provide only the parallel-map operation.

For categorical projections / pairing, use `⊗` instead. -/


-- @@ L243-248 expanded
/-- Parallel application of charts for polynomial product `c₁ ×c c₂ : P * Q → R * W`. -/
def prodMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    {W : PFunctor.{uA₄, uB₄}} (c₁ : Chart P R) (c₂ : Chart Q W) :
    Chart.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P * Q) (R * W) :=
  Chart.mk (Prod.map c₁.toFunA c₂.toFunA) fun (pa, qa) => Sum.map (c₁.toFunB pa) (c₂.toFunB qa)


-- @@ L250-255 verbatim
/-! ### Indexed colimits and limits

The chart category has Sigma-eliminations (`sigmaExists`/`sigmaMap`) but
only the parametric Pi-map (`piMap`); `piForall` is intrinsically a
lens-side construction because it requires "choosing an index" in the
chart direction, which has no canonical choice in `Set^→`. -/


-- @@ L257-262 expanded
/-- Dependent copairing of charts over `sigma`: `(Σ i, F i) → R`. -/
def sigmaExists {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}}
    (c : ∀ i, Chart (F i) R) : Chart (sigma F) R :=
  Chart.mk (fun ⟨i, fa⟩ => (c i).toFunA fa) (fun ⟨i, fa⟩ => (c i).toFunB fa)


-- @@ L264-269 expanded
/-- Pointwise mapping of charts over `sigma`. -/
def sigmaMap {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    (c : ∀ i, Chart (F i) (G i)) : Chart (sigma F) (sigma G) :=
  Chart.mk (fun ⟨i, fa⟩ => ⟨i, (c i).toFunA fa⟩) (fun ⟨i, fa⟩ => (c i).toFunB fa)


-- @@ L271-276 expanded
/-- Pointwise mapping of charts over `pi`. -/
def piMap {I : Type v} {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    (c : ∀ i, Chart (F i) (G i)) : Chart (pi F) (pi G) :=
  Chart.mk (fun fa i => (c i).toFunA (fa i)) (fun fa ⟨i, fb⟩ => ⟨i, (c i).toFunB (fa i) fb⟩)


-- @@ L278-283 verbatim
/-! ### Action on indices

A chart `φ : P → Q` acts on `Idx P = Σ a : P.A, P.B a` by sending
`⟨a, b⟩ ↦ ⟨φ.toFunA a, φ.toFunB a b⟩`. This is the underlying function on
positions; `Trace.mapChart` (in `PolyFun.PFunctor.Trace`) uses it to push
event traces along charts. -/


-- @@ L285-285 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}


-- @@ L287-289 verbatim
/-- Push an `Idx P` along a chart `P → Q` to an `Idx Q`. -/
def mapIdx (φ : Chart P Q) (i : Idx P) : Idx Q :=
  ⟨φ.toFunA i.1, φ.toFunB i.1 i.2⟩


-- @@ L291-291 verbatim
@[simp] theorem mapIdx_id (i : Idx P) : mapIdx (Chart.id P) i = i := rfl


-- @@ L293-294 expanded
@[simp]
theorem mapIdx_comp (g : Chart Q R) (f : Chart P Q) (i : Idx P) :
    mapIdx (comp g f) i = mapIdx g (mapIdx f i) :=
  rfl


-- @@ L296-296 verbatim
/-! ### Special charts -/


-- @@ L298-307 verbatim
set_option linter.checkUnivs false in
/-- The type of charts from a polynomial functor `P` to `y`.

A chart `P → y` is equivalent to a function `(a : P.A) → P.B a → PUnit`,
i.e. a boundary valuation that picks out a single direction at every
position. Analogous to `Lens.enclose`. -/
-- `Chart.enclose`'s two universe pairs are the independent domain (`uA`/`uB`) and
-- codomain (`uA₁`/`uB₁`) position/direction universes, kept independent.
def enclose (P : PFunctor.{uA, uB}) : Type max uA uA₁ uB uB₁ :=
  Chart P y.{uA₁, uB₁}


-- @@ L309-309 verbatim
/-! ### Notations for binary operations -/


-- @@ L311-311 verbatim
@[inherit_doc] infixl:75 " ⊎c " => sumMap

-- @@ L312-312 verbatim
@[inherit_doc] infixl:75 " ⊗c " => tensorMap

-- @@ L313-313 verbatim
@[inherit_doc] infixl:75 " ×c " => prodMap

-- @@ L314-315 verbatim
/-- Notation for the copairing `sumPair c₁ c₂` of two charts out of a sum. -/
notation "[" c₁ "," c₂ "]c" => sumPair c₁ c₂

-- @@ L316-317 verbatim
/-- Notation for the pairing `tensorPair c₁ c₂` of two charts into a tensor. -/
notation "⟨" c₁ "," c₂ "⟩c" => tensorPair c₁ c₂


-- @@ L319-319 verbatim
/-! ### Coproduct coherence -/


-- @@ L321-321 verbatim
section Sum


-- @@ L323-324 verbatim
variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
  {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}} {S : PFunctor.{uA₅, uB₅}}


-- @@ L326-328 expanded
@[simp]
theorem sumMap_comp_inl (c₁ : Chart P R) (c₂ : Chart Q W) :
    (comp (sumMap c₁ c₂) Chart.inl) = (comp Chart.inl c₁) :=
  rfl


-- @@ L330-332 expanded
@[simp]
theorem sumMap_comp_inr (c₁ : Chart P R) (c₂ : Chart Q W) :
    (comp (sumMap c₁ c₂) Chart.inr) = (comp Chart.inr c₂) :=
  rfl


-- @@ L334-337 expanded
theorem sumPair_comp_sumMap (c₁ : Chart P R) (c₂ : Chart Q W) (f : Chart R S) (g : Chart W S) :
    comp (Chart.sumPair f g) (sumMap c₁ c₂) = Chart.sumPair (comp f c₁) (comp g c₂) := by
  ext a <;> rcases a with a | a <;> rfl


-- @@ L339-341 expanded
@[simp]
theorem sumPair_comp_inl (f : Chart P R) (g : Chart Q R) : comp (Chart.sumPair f g) Chart.inl = f :=
  rfl


-- @@ L343-345 expanded
@[simp]
theorem sumPair_comp_inr (f : Chart P R) (g : Chart Q R) : comp (Chart.sumPair f g) Chart.inr = g :=
  rfl


-- @@ L347-349 expanded
theorem comp_inl_inr (h : Chart.{max uA₁ uA₂, uB, uA₃, uB₃} (P + Q) R) :
    Chart.sumPair (comp h Chart.inl) (comp h Chart.inr) = h := by ext a <;> rcases a <;> rfl


-- @@ L351-354 verbatim
@[simp]
theorem sumMap_id :
    Chart.sumMap (Chart.id P) (Chart.id Q) = Chart.id.{max uA₁ uA₂, uB} (P + Q) := by
  ext a <;> rcases a <;> rfl


-- @@ L356-359 verbatim
@[simp]
theorem sumPair_inl_inr :
    Chart.sumPair Chart.inl Chart.inr = Chart.id.{max uA₁ uA₂, uB} (P + Q) := by
  ext a <;> rcases a <;> rfl


-- @@ L361-365 expanded
theorem sumMap_comp_sumMap {S : PFunctor.{uA₅, uB₅}} {T : PFunctor.{uA₆, uB₅}} (c₁ : Chart P R)
    (c₂ : Chart Q W) (c₁' : Chart R S) (c₂' : Chart W T) :
    comp (sumMap c₁' c₂') (sumMap c₁ c₂) = sumMap (comp c₁' c₁) (comp c₂' c₂) := by
  ext a <;> rcases a <;> rfl


-- @@ L367-367 verbatim
namespace Equiv


-- @@ L369-375 verbatim
/-- Commutativity of coproduct -/
def sumComm (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    Chart.Equiv.{max uA₁ uA₂, uB, max uA₁ uA₂, uB} (P + Q) (Q + P) where
  toChart := Chart.sumPair Chart.inr Chart.inl
  invChart := Chart.sumPair Chart.inr Chart.inl
  left_inv := by ext a <;> rcases a with a | a <;> rfl
  right_inv := by ext a <;> rcases a with a | a <;> rfl


-- @@ L377-377 verbatim
variable {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}


-- @@ L379-381 verbatim
@[simp]
theorem sumComm_symm :
    (sumComm P Q).symm = sumComm Q P := rfl


-- @@ L383-399 expanded
/-- Associativity of coproduct -/
def sumAssoc : Chart.Equiv.{max uA₁ uA₂ uA₃, uB, max uA₁ uA₂ uA₃, uB} ((P + Q) + R) (P + (Q + R))
    where
  toChart :=
    Chart.sumPair (Chart.sumPair Chart.inl (comp Chart.inr Chart.inl)) (comp Chart.inr Chart.inr)
  invChart :=
    Chart.sumPair (comp Chart.inl Chart.inl) (Chart.sumPair (comp Chart.inl Chart.inr) Chart.inr)
  left_inv := by ext a <;> rcases a with (a | a) | a <;> rfl
  right_inv := by ext a <;> rcases a with a | (a | a) <;> rfl


-- @@ L401-408 verbatim
/-- Coproduct with `0` is identity (right) -/
def sumZero :
    Chart.Equiv.{max uA uA₁, uB, uA₁, uB} (P + (0 : PFunctor.{uA, uB})) P where
  toChart := Chart.sumPair (Chart.id P) Chart.initial
  invChart := Chart.inl
  left_inv := by
    ext a <;> rcases a with a | a <;> first | rfl | exact PEmpty.elim a
  right_inv := by ext <;> rfl


-- @@ L410-417 verbatim
/-- Coproduct with `0` is identity (left) -/
def zeroSum :
    Chart.Equiv.{max uA uA₁, uB, uA₁, uB} ((0 : PFunctor.{uA, uB}) + P) P where
  toChart := Chart.sumPair Chart.initial (Chart.id P)
  invChart := Chart.inr
  left_inv := by
    ext a <;> rcases a with a | a <;> first | rfl | exact PEmpty.elim a
  right_inv := by ext <;> rfl


-- @@ L419-429 expanded
/-- Coproduct preserves equivalences: `P ≃c P' → Q ≃c Q' → P + Q ≃c P' + Q'`. -/
def sumCongr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} {P' : PFunctor.{uA₃, uB}}
    {Q' : PFunctor.{uA₄, uB}} (e₁ : Chart.Equiv P P') (e₂ : Chart.Equiv Q Q') :
    Chart.Equiv.{max uA₁ uA₂, uB, max uA₃ uA₄, uB} (P + Q) (P' + Q')
    where
  toChart := sumMap e₁.toChart e₂.toChart
  invChart := sumMap e₁.invChart e₂.invChart
  left_inv := by rw [Chart.sumMap_comp_sumMap, e₁.left_inv, e₂.left_inv, Chart.sumMap_id]
  right_inv := by rw [Chart.sumMap_comp_sumMap, e₁.right_inv, e₂.right_inv, Chart.sumMap_id]


-- @@ L431-431 verbatim
end Equiv


-- @@ L433-433 verbatim
end Sum


-- @@ L435-435 verbatim
/-! ### Tensor coherence -/


-- @@ L437-437 verbatim
section Tensor


-- @@ L439-440 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {W : PFunctor.{uA₄, uB₄}} {S : PFunctor.{uA₅, uB₅}}


-- @@ L442-444 expanded
@[simp]
theorem fst_comp_tensorMap (c₁ : Chart P R) (c₂ : Chart Q W) :
    comp Chart.fst (tensorMap c₁ c₂) = comp c₁ Chart.fst :=
  rfl


-- @@ L446-448 expanded
@[simp]
theorem snd_comp_tensorMap (c₁ : Chart P R) (c₂ : Chart Q W) :
    comp Chart.snd (tensorMap c₁ c₂) = comp c₂ Chart.snd :=
  rfl


-- @@ L450-452 expanded
theorem tensorMap_comp_tensorPair (c₁ : Chart Q W) (c₂ : Chart R S) (f : Chart P Q)
    (g : Chart P R) :
    comp (tensorMap c₁ c₂) (Chart.tensorPair f g) = Chart.tensorPair (comp c₁ f) (comp c₂ g) :=
  rfl


-- @@ L454-456 expanded
@[simp]
theorem fst_comp_tensorPair (f : Chart P Q) (g : Chart P R) :
    comp Chart.fst (Chart.tensorPair f g) = f :=
  rfl


-- @@ L458-460 expanded
@[simp]
theorem snd_comp_tensorPair (f : Chart P Q) (g : Chart P R) :
    comp Chart.snd (Chart.tensorPair f g) = g :=
  rfl


-- @@ L462-463 expanded
theorem comp_fst_snd (h : Chart.{uA₁, uB₁, max uA₂ uA₃, max uB₂ uB₃} P (Q ⊗ R)) :
    Chart.tensorPair (comp Chart.fst h) (comp Chart.snd h) = h :=
  rfl


-- @@ L465-466 expanded
@[simp]
theorem tensorMap_id : tensorMap (Chart.id P) (Chart.id Q) = Chart.id (P ⊗ Q) :=
  rfl


-- @@ L468-471 expanded
theorem tensorMap_comp {P' : PFunctor.{uA₅, uB₅}} {Q' : PFunctor.{uA₆, uB₆}} (c₁ : Chart P P')
    (c₂ : Chart Q Q') (c₁' : Chart P' R) (c₂' : Chart Q' W) :
    tensorMap (comp c₁' c₁) (comp c₂' c₂) = comp (tensorMap c₁' c₂') (tensorMap c₁ c₂) :=
  rfl


-- @@ L473-476 expanded
theorem tensorMap_comp_tensorMap {P' : PFunctor.{uA₅, uB₅}} {Q' : PFunctor.{uA₆, uB₆}}
    (c₁ : Chart P R) (c₂ : Chart Q W) (c₁' : Chart R P') (c₂' : Chart W Q') :
    comp (tensorMap c₁' c₂') (tensorMap c₁ c₂) = tensorMap (comp c₁' c₁) (comp c₂' c₂) :=
  rfl


-- @@ L478-480 verbatim
@[simp]
theorem tensorPair_fst_snd : Chart.tensorPair Chart.fst Chart.snd =
    Chart.id.{max uA₁ uA₂, max uB₁ uB₂} (P ⊗ Q) := rfl


-- @@ L482-482 verbatim
namespace Equiv


-- @@ L484-489 expanded
/-- Commutativity of tensor product -/
def tensorComm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) : Chart.Equiv (P ⊗ Q) (Q ⊗ P)
    where
  toChart := Chart.mk Prod.swap (fun _ => Prod.swap)
  invChart := Chart.mk Prod.swap (fun _ => Prod.swap)
  left_inv := rfl
  right_inv := rfl


-- @@ L491-492 verbatim
@[simp]
theorem tensorComm_symm : (tensorComm P Q).symm = tensorComm Q P := rfl


-- @@ L494-501 expanded
/-- Associativity of tensor product -/
def tensorAssoc : Chart.Equiv ((P ⊗ Q) ⊗ R) (P ⊗ (Q ⊗ R))
    where
  toChart :=
    Chart.mk (_root_.Equiv.prodAssoc _ _ _).toFun (fun _ => (_root_.Equiv.prodAssoc _ _ _).toFun)
  invChart :=
    Chart.mk (_root_.Equiv.prodAssoc _ _ _).invFun (fun _ => (_root_.Equiv.prodAssoc _ _ _).invFun)
  left_inv := rfl
  right_inv := rfl


-- @@ L503-508 expanded
/-- Tensor product with `y` is identity (right) -/
def tensorY : Chart.Equiv (P ⊗ y) P
    where
  toChart := Chart.mk Prod.fst (fun _ => Prod.fst)
  invChart := Chart.mk (fun p => (p, PUnit.unit)) (fun _ b => (b, PUnit.unit))
  left_inv := rfl
  right_inv := rfl


-- @@ L510-515 expanded
/-- Tensor product with `y` is identity (left) -/
def yTensor : Chart.Equiv (y ⊗ P) P
    where
  toChart := Chart.mk Prod.snd (fun _ => Prod.snd)
  invChart := Chart.mk (fun p => (PUnit.unit, p)) (fun _ b => (PUnit.unit, b))
  left_inv := rfl
  right_inv := rfl


-- @@ L517-517 verbatim
@[deprecated (since := "2026-08-17")] alias tensorX := tensorY

-- @@ L518-518 verbatim
@[deprecated (since := "2026-08-17")] alias xTensor := yTensor


-- @@ L520-525 expanded
/-- Tensor product with `0` is zero (left) -/
def zeroTensor : Chart.Equiv (0 ⊗ P) 0
    where
  toChart := Chart.mk (fun a => PEmpty.elim a.1) fun a => PEmpty.elim a.1
  invChart := Chart.mk PEmpty.elim fun a => PEmpty.elim a
  left_inv := by ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by ext a <;> exact PEmpty.elim a


-- @@ L527-532 expanded
/-- Tensor product with `0` is zero (right) -/
def tensorZero : Chart.Equiv (P ⊗ 0) 0
    where
  toChart := Chart.mk (fun a => PEmpty.elim a.2) fun a => PEmpty.elim a.2
  invChart := Chart.mk PEmpty.elim fun a => PEmpty.elim a
  left_inv := by ext ⟨_, b⟩ <;> exact PEmpty.elim b
  right_inv := by ext a <;> exact PEmpty.elim a


-- @@ L534-547 expanded
/-- Tensor product preserves equivalences: `P ≃c P' → Q ≃c Q' → P ⊗ Q ≃c P' ⊗ Q'`. -/
def tensorCongr {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {P' : PFunctor.{uA₃, uB₃}}
    {Q' : PFunctor.{uA₄, uB₄}} (e₁ : Chart.Equiv P P') (e₂ : Chart.Equiv Q Q') :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P ⊗ Q) (P' ⊗ Q')
    where
  toChart := tensorMap e₁.toChart e₂.toChart
  invChart := tensorMap e₁.invChart e₂.invChart
  left_inv := by rw [Chart.tensorMap_comp_tensorMap, e₁.left_inv, e₂.left_inv, Chart.tensorMap_id]
  right_inv := by
    rw [Chart.tensorMap_comp_tensorMap, e₁.right_inv, e₂.right_inv, Chart.tensorMap_id]


-- @@ L549-560 expanded
/-- Left distributivity of tensor product over coproduct.

`P ⊗ (Q + R) ≃c (P ⊗ Q) + (P ⊗ R)`. -/
def tensorSumDistrib {P : PFunctor.{uA₁, uB₁}} {Q R : PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂} (P ⊗ (Q + R))
      ((P ⊗ Q) + (P ⊗ R))
    where
  toChart :=
    Chart.mk (fun (p, qr) => qr.map (p, ·) (p, ·))
      (fun
        | ⟨_, .inl _⟩ | ⟨_, .inr _⟩ => id)
  invChart :=
    Chart.mk (Sum.elim (Prod.map id Sum.inl) (Prod.map id Sum.inr))
      (fun
        | .inl _ | .inr _ => id)
  left_inv := by ext ⟨_, qr⟩ <;> cases qr <;> rfl
  right_inv := by ext pqpr <;> cases pqpr <;> rfl


-- @@ L562-573 expanded
/-- Right distributivity of tensor product over coproduct.

`(Q + R) ⊗ P ≃c (Q ⊗ P) + (R ⊗ P)`. -/
def sumTensorDistrib {P : PFunctor.{uA₁, uB₁}} {Q R : PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂} ((Q + R) ⊗ P)
      ((Q ⊗ P) + (R ⊗ P))
    where
  toChart :=
    Chart.mk (fun (qr, p) => qr.map (·, p) (·, p))
      (fun
        | ⟨.inl _, _⟩ | ⟨.inr _, _⟩ => id)
  invChart :=
    Chart.mk (Sum.elim (Prod.map Sum.inl id) (Prod.map Sum.inr id))
      (fun
        | .inl _ | .inr _ => id)
  left_inv := by ext ⟨qr, _⟩ <;> cases qr <;> rfl
  right_inv := by ext qprp <;> cases qprp <;> rfl


-- @@ L575-575 verbatim
end Equiv


-- @@ L577-577 verbatim
end Tensor


-- @@ L579-584 verbatim
/-! ### Polynomial-product coherence

Even though `*` is *not* the categorical product in the chart category, it
is still a functor and admits coherent equivalences (commutativity,
associativity, units, zeros, congruence, distributivity over `+`). These
mirror the `PFunctor.Equiv.prod*` lemmas. -/


-- @@ L586-586 verbatim
section Prod


-- @@ L588-589 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
  {W : PFunctor.{uA₄, uB₄}}


-- @@ L591-596 expanded
@[simp]
theorem prodMap_id :
    prodMap (Chart.id P) (Chart.id Q) = Chart.id.{max uA₁ uA₂, max uB₁ uB₂} (P * Q) :=
  by
  ext _ x
  · rfl
  · cases x <;> rfl


-- @@ L598-603 expanded
theorem prodMap_comp_prodMap {S : PFunctor.{uA₅, uB₅}} {T : PFunctor.{uA₆, uB₆}} (c₁ : Chart P R)
    (c₂ : Chart Q W) (c₁' : Chart R S) (c₂' : Chart W T) :
    comp (prodMap c₁' c₂') (prodMap c₁ c₂) = prodMap (comp c₁' c₁) (comp c₂' c₂) :=
  by
  refine Chart.ext _ _ ?_ ?_
  · intro _; rfl
  · intro _; funext psum; rcases psum <;> rfl


-- @@ L605-605 verbatim
namespace Equiv


-- @@ L607-618 expanded
/-- Polynomial-product preserves equivalences: `P ≃c P' → Q ≃c Q' → P * Q ≃c P' * Q'`. -/
def prodCongr {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {P' : PFunctor.{uA₃, uB₃}}
    {Q' : PFunctor.{uA₄, uB₄}} (e₁ : Chart.Equiv P P') (e₂ : Chart.Equiv Q Q') :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₃ uA₄, max uB₃ uB₄} (P * Q) (P' * Q')
    where
  toChart := prodMap e₁.toChart e₂.toChart
  invChart := prodMap e₁.invChart e₂.invChart
  left_inv := by rw [Chart.prodMap_comp_prodMap, e₁.left_inv, e₂.left_inv, Chart.prodMap_id]
  right_inv := by rw [Chart.prodMap_comp_prodMap, e₁.right_inv, e₂.right_inv, Chart.prodMap_id]


-- @@ L620-632 expanded
/-- Commutativity of the polynomial product. -/
def prodComm (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂} (P * Q) (Q * P)
    where
  toChart := Chart.mk Prod.swap fun _ => Sum.swap
  invChart := Chart.mk Prod.swap fun _ => Sum.swap
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext d; rcases d <;> rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext d; rcases d <;> rfl


-- @@ L634-653 expanded
/-- Associativity of the polynomial product. -/
def prodAssoc :
    Chart.Equiv.{max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃, max uA₁ uA₂ uA₃, max uB₁ uB₂ uB₃} ((P * Q) * R)
      (P * (Q * R))
    where
  toChart :=
    Chart.mk (_root_.Equiv.prodAssoc _ _ _).toFun (fun _ => (_root_.Equiv.sumAssoc _ _ _).toFun)
  invChart :=
    Chart.mk (_root_.Equiv.prodAssoc _ _ _).invFun (fun _ => (_root_.Equiv.sumAssoc _ _ _).invFun)
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext d; rcases d with d | d
      · rcases d with d | d <;> rfl
      · rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext d; rcases d with d | d
      · rfl
      · rcases d with d | d <;> rfl


-- @@ L655-660 expanded
/-- Polynomial-product with `0` is `0` (right). -/
def prodZero : Chart.Equiv (P * 0) 0
    where
  toChart := Chart.mk (fun a => PEmpty.elim a.2) fun a => PEmpty.elim a.2
  invChart := Chart.mk PEmpty.elim fun a => PEmpty.elim a
  left_inv := by ext ⟨_, b⟩ <;> exact PEmpty.elim b
  right_inv := by ext a <;> exact PEmpty.elim a


-- @@ L662-667 expanded
/-- Polynomial-product with `0` is `0` (left). -/
def zeroProd : Chart.Equiv (0 * P) 0
    where
  toChart := Chart.mk (fun a => PEmpty.elim a.1) fun a => PEmpty.elim a.1
  invChart := Chart.mk PEmpty.elim fun a => PEmpty.elim a
  left_inv := by ext ⟨a, _⟩ <;> exact PEmpty.elim a
  right_inv := by ext a <;> exact PEmpty.elim a


-- @@ L669-680 expanded
/-- Left distributivity of polynomial product over coproduct.

`P * (Q + R) ≃c (P * Q) + (P * R)`. -/
def prodSumDistrib {P : PFunctor.{uA₁, uB₁}} {Q R : PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂} (P * (Q + R))
      ((P * Q) + (P * R))
    where
  toChart :=
    Chart.mk (fun (p, qr) => qr.map (p, ·) (p, ·))
      (fun
        | ⟨_, .inl _⟩ | ⟨_, .inr _⟩ => id)
  invChart :=
    Chart.mk (Sum.elim (Prod.map id Sum.inl) (Prod.map id Sum.inr))
      (fun
        | .inl _ | .inr _ => id)
  left_inv := by ext ⟨_, qr⟩ <;> cases qr <;> rfl
  right_inv := by ext pqpr <;> cases pqpr <;> rfl


-- @@ L682-693 expanded
/-- Right distributivity of polynomial product over coproduct.

`(Q + R) * P ≃c (Q * P) + (R * P)`. -/
def sumProdDistrib {P : PFunctor.{uA₁, uB₁}} {Q R : PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂, max uB₁ uB₂, max uA₁ uA₂, max uB₁ uB₂} ((Q + R) * P)
      ((Q * P) + (R * P))
    where
  toChart :=
    Chart.mk (fun (qr, p) => qr.map (·, p) (·, p))
      (fun
        | ⟨.inl _, _⟩ | ⟨.inr _, _⟩ => id)
  invChart :=
    Chart.mk (Sum.elim (Prod.map Sum.inl id) (Prod.map Sum.inr id))
      (fun
        | .inl _ | .inr _ => id)
  left_inv := by ext ⟨qr, _⟩ <;> cases qr <;> rfl
  right_inv := by ext qprp <;> cases qprp <;> rfl


-- @@ L695-695 verbatim
end Equiv


-- @@ L697-697 verbatim
end Prod


-- @@ L699-699 verbatim
/-! ### ULift -/


-- @@ L701-701 verbatim
namespace Equiv


-- @@ L703-708 expanded
/-- ULift equivalence for charts. -/
def ulift {P : PFunctor.{uA, uB}} : Chart.Equiv P.ulift P
    where
  toChart := Chart.mk (fun a => ULift.down a) (fun _ b => ULift.down b)
  invChart := Chart.mk (fun a => ULift.up a) (fun _ b => ULift.up b)
  left_inv := rfl
  right_inv := rfl


-- @@ L710-710 verbatim
end Equiv


-- @@ L712-712 verbatim
end Chart


-- @@ L714-714 verbatim
namespace Equiv


-- @@ L716-716 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}


-- @@ L718-721 verbatim
/-- Convert an equivalence between two polynomial functors `P` and `Q` to a chart. -/
def toChart (e : P ≃ₚ Q) : Chart P Q where
  toFunA := e.equivA
  toFunB := fun a => e.equivB a


-- @@ L723-733 verbatim
/-! ### Bridge `PFunctor.Equiv → Chart.Equiv`

Every polynomial-functor equivalence yields a chart equivalence: the forward
chart uses `e.equivA` / `e.equivB`, and the inverse chart uses their symmetric
counterparts. The proofs of `left_inv` / `right_inv` need the cast
machinery from `forward_equivB_roundtrip` / `reverse_equivB_roundtrip` because
`e.symm.equivA (e.equivA a)` and `a` are only propositionally equal.

This is the chart analogue of `Equiv.toLensEquiv` and is the standard way to
derive sigma / distributivity equivalences from their `PFunctor.Equiv`
counterparts. -/


-- @@ L735-740 verbatim
private theorem eqRec_id_apply_codomain
    {α : Sort*} {β : α → Sort*} {a₀ a₁ : α}
    (h : a₀ = a₁) (x : β a₀) :
    Eq.rec (motive := fun x _ => β a₀ → β x) id h x =
      _root_.cast (congrArg β h) x := by
  subst h; rfl


-- @@ L742-749 expanded
@[simp]
theorem symm_toChart_comp_toChart (e : P ≃ₚ Q) : comp e.symm.toChart e.toChart = Chart.id P :=
  by
  refine Chart.ext _ _ (fun a => e.equivA.symm_apply_apply a) (fun a => ?_)
  funext b
  simp only [Chart.comp, Chart.id, toChart, Function.comp_apply]
  rw [forward_equivB_roundtrip]
  exact (eqRec_id_apply_codomain (e.equivA.symm_apply_apply a).symm b).symm


-- @@ L751-759 expanded
@[simp]
theorem toChart_comp_symm_toChart (e : P ≃ₚ Q) : comp e.toChart e.symm.toChart = Chart.id Q :=
  by
  refine Chart.ext _ _ (fun a => e.equivA.apply_symm_apply a) (fun a => ?_)
  funext b
  simp only [Chart.comp, Chart.id, toChart, Function.comp_apply]
  change e.equivB (e.equivA.symm a) (e.symm.equivB a b) = _
  rw [reverse_equivB_roundtrip]
  exact (eqRec_id_apply_codomain (e.equivA.apply_symm_apply a).symm b).symm


-- @@ L761-770 expanded
/-- Convert an equivalence between two polynomial functors to a chart equivalence.

Chart-side analogue of `Equiv.toLensEquiv`. Together with `Chart.Equiv.refl`,
`symm`, and `trans`, this establishes a faithful functor
`PFunctor.Equiv → Chart.Equiv`. -/
def toChartEquiv (e : P ≃ₚ Q) : Chart.Equiv P Q
    where
  toChart := e.toChart
  invChart := e.symm.toChart
  left_inv := symm_toChart_comp_toChart e
  right_inv := toChart_comp_symm_toChart e


-- @@ L772-772 verbatim
end Equiv


-- @@ L774-778 verbatim
/-! ### Sigma equivalences

These are derived from `PFunctor.Equiv.toChartEquiv` applied to the
corresponding `PFunctor.Equiv` constructions. They mirror the
`PFunctor.Lens.Equiv.sigma*` family. -/


-- @@ L780-780 verbatim
namespace Chart.Equiv


-- @@ L782-782 verbatim
variable {I : Type v}


-- @@ L784-786 expanded
/-- Sigma of an empty family is the zero functor. -/
def sigmaEmpty [IsEmpty I] {F : I → PFunctor.{uA, uB}} : Chart.Equiv (sigma F) 0 :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.emptySigma (F := F))


-- @@ L788-794 expanded
/-- Sigma of a `PUnit`-indexed family is equivalent to the functor itself
    (up to `ulift`). -/
def sigmaUnit {F : PUnit → PFunctor.{uA, uB}} : Chart.Equiv (sigma F) (F PUnit.unit).ulift :=
  PFunctor.Equiv.toChartEquiv
    (PFunctor.Equiv.trans (PFunctor.Equiv.punitSigma (F := F))
      (PFunctor.Equiv.uliftEquiv (P := F PUnit.unit)))


-- @@ L796-802 expanded
/-- Sigma of a unique-indexed family is equivalent to the default fiber
    (up to `ulift`). -/
def sigmaOfUnique [Unique I] {F : I → PFunctor.{uA, uB}} :
    Chart.Equiv (sigma F) (F default).ulift :=
  PFunctor.Equiv.toChartEquiv
    (PFunctor.Equiv.trans (PFunctor.Equiv.uniqueSigma (F := F))
      (PFunctor.Equiv.uliftEquiv (P := F default)))


-- @@ L804-808 verbatim
/-- Left distributivity of polynomial product over sigma. -/
def prodSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂ v, max uB₁ uB₂, max uA₁ uA₂ v, max uB₁ uB₂}
      (P * sigma F) (sigma (fun i => (P * F i : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}))) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.prodSigmaDistrib (P := P) (F := F))


-- @@ L810-814 verbatim
/-- Right distributivity of polynomial product over sigma. -/
def sigmaProdDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Chart.Equiv.{max uA₁ uA₂ v, max uB₁ uB₂, max uA₁ uA₂ v, max uB₁ uB₂}
      (sigma F * P) (sigma (fun i => (F i * P : PFunctor.{max uA₁ uA₂, max uB₁ uB₂}))) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.sigmaProdDistrib (P := P) (F := F))


-- @@ L816-819 expanded
/-- Left distributivity of tensor product over sigma. -/
def tensorSigmaDistrib {P : PFunctor.{uA₁, uB₁}} {F : I → PFunctor.{uA₂, uB₂}} :
    Chart.Equiv (P ⊗ sigma F) (sigma (fun i => P ⊗ F i)) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.tensorSigmaDistrib (P := P) (F := F))


-- @@ L821-824 expanded
/-- Right distributivity of tensor product over sigma. -/
def sigmaTensorDistrib {P : PFunctor.{uA₂, uB₂}} {F : I → PFunctor.{uA₁, uB₁}} :
    Chart.Equiv (sigma F ⊗ P) (sigma (fun i => F i ⊗ P)) :=
  PFunctor.Equiv.toChartEquiv (PFunctor.Equiv.sigmaTensorDistrib (F := F) (P := P))


-- @@ L826-830 verbatim
/-! ### Pi equivalences

`piMap` lives in the operations section, but unlike lenses, charts admit
no `piForall` (Pi-elimination requires direction-contravariance). What we
get cleanly here is `piUnit` and `piZero`. -/


-- @@ L832-843 expanded
/-- Pi over a `PUnit`-indexed family is equivalent to the functor itself. -/
def piUnit {P : PFunctor.{uA, uB}} : Chart.Equiv (pi (fun (_ : PUnit) => P)) P
    where
  toChart := Chart.mk (fun f => f PUnit.unit) (fun _ s => s.2)
  invChart := Chart.mk (fun pa _ => pa) (fun _ pb => ⟨PUnit.unit, pb⟩)
  left_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro f; funext u; cases u; rfl
    · intro f; funext ⟨u, pb⟩; cases u; rfl
  right_inv := by
    refine Chart.ext _ _ ?_ ?_
    · intro _; rfl
    · intro _; funext _; rfl


-- @@ L845-863 expanded
/-- Pi of a family of zero functors over an inhabited type is the zero functor. -/
def piZero [Inhabited I] {F : I → PFunctor.{uA, uB}} (F_zero : ∀ i, F i = 0) :
    Chart.Equiv (pi F) 0 :=
  by
  have : IsEmpty (pi F).A := by
    refine ⟨fun f => ?_⟩
    have hf : (F default).A := f default
    rw [F_zero (default : I)] at hf
    exact hf.elim
  refine
    { toChart := Chart.mk isEmptyElim fun a => isEmptyElim a
      invChart := Chart.mk PEmpty.elim fun a => PEmpty.elim a
      left_inv := by
        refine Chart.ext _ _ ?_ ?_
        · intro a; exact isEmptyElim a
        · intro a; exact isEmptyElim a
      right_inv := by
        refine Chart.ext _ _ ?_ ?_
        · intro a; exact PEmpty.elim a
        · intro a; exact PEmpty.elim a }


-- @@ L865-865 verbatim
end Chart.Equiv


-- @@ L867-867 verbatim
end PFunctor
