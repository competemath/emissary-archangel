/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Util.Notation3


-- @@ L11-18 verbatim
/-!
  # Polynomial Functors, Lens, and Charts

  This file defines polynomial functors, lenses, and charts. The goal is to provide basic
  definitions, with their properties and categories defined in later files.

dt: this file is getting long and should maybe be split up more.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄ uA₅ uB₅ uA₆ uB₆ vA vB


-- @@ L24-24 verbatim
namespace PFunctor


-- @@ L26-26 verbatim
section Basic


-- @@ L28-31 verbatim
/-- The zero polynomial functor, defined as `A = PEmpty` and `B _ = PEmpty`, is the identity with
  respect to sum (up to equivalence) -/
instance instZeroPFunctor : Zero PFunctor.{uA, uB} where
  zero := ⟨PEmpty, fun _ => PEmpty⟩


-- @@ L33-36 verbatim
/-- The unit polynomial functor, defined as `A = PUnit` and `B _ = PEmpty`, is the identity with
  respect to product (up to equivalence) -/
instance instOnePFunctor : One PFunctor.{uA, uB} where
  one := ⟨PUnit, fun _ => PEmpty⟩


-- @@ L38-42 verbatim
/-- The variable (or identity) polynomial functor `y`, with a single position and a single
direction. Under the Yoneda reading `y = y^ PUnit` is the representable on a point; it is the
unit for both composition `◃` and the tensor product `⊗` (up to equivalence). -/
def y : PFunctor.{uA, uB} :=
  ⟨PUnit, fun _ => PUnit⟩


-- @@ L44-45 verbatim
/-- Deprecated compatibility name for the variable polynomial. -/
@[deprecated (since := "2026-08-17")] alias X := y


-- @@ L47-47 verbatim
instance : IsEmpty (A 0) := inferInstanceAs (IsEmpty PEmpty)

-- @@ L48-48 verbatim
instance instUniqueAOfNatOne : Unique (A 1) := inferInstanceAs (Unique PUnit)

-- @@ L49-49 verbatim
instance : Unique y.A := inferInstanceAs (Unique PUnit)


-- @@ L51-54 verbatim
/-- The monomial functor `A y^ B` has `A` as its head type and the constant
  family `B_a = B` as the child type for each each shape `a : A` . -/
def monomial (A : Type uA) (B : Type uB) : PFunctor.{uA, uB} :=
  ⟨A, fun _ => B⟩


-- @@ L56-56 verbatim
@[inherit_doc] scoped[PFunctor] 
-- @@ L56-56 verbatim
infixr:82 " y^ " => monomial


-- @@ L58-62 verbatim
/-- Parse-only compatibility spelling of the monomial `A y^ B`.

Kept in this foundational module so direct importers of `PFunctor.Basic` or
`PFunctor.Lens.Basic` continue to elaborate while migrating to `y^`. -/
scoped syntax:82 term:83 " X^ " term:82 : term


-- @@ L64-65 verbatim
scoped macro_rules
  | `($A X^ $B) => `(PFunctor.monomial $A $B)


-- @@ L67-70 verbatim
/-- The constant polynomial functor `A y^ PEmpty` -/
@[reducible]
def C (A : Type uA) : PFunctor.{uA, uB} :=
  A y^ PEmpty


-- @@ L72-74 verbatim
/-- The linear polynomial functor `A y^ PUnit` -/
def linear (A : Type uA) : PFunctor.{uA, uB} :=
  A y^ PUnit


-- @@ L76-84 verbatim
/-- The self monomial polynomial functor `S y^ S`.

The body spells out the monomial rather than using `S y^ S` so that the
head and child types are projections of an explicit structure literal at
every transparency level; the mate-object equations in the dynamical
layers rewrite through this carrier during implicit-transparency checks. -/
@[reducible]
def selfMonomial (S : Type uA) : PFunctor.{uA, uA} :=
  { A := S, B := fun _ => S }


-- @@ L86-88 verbatim
/-- The pure power polynomial functor `y^ B`, the representable on the type `B`. -/
def purePower (B : Type uB) : PFunctor.{uA, uB} :=
  PUnit y^ B


-- @@ L90-91 verbatim
/-- A polynomial functor is representable if it is equivalent to `y^ A` for some type `A`. -/
alias representable := purePower


-- @@ L93-93 verbatim
@[inherit_doc purePower] scoped[PFunctor] 
-- @@ L93-93 verbatim
notation:100 "y^" B:100 => purePower B


-- @@ L95-104 verbatim
/-- The **universe polynomial functor** `Σ (T : Type u), y^ T`: positions are types,
and the directions at a position `T` are its elements. Its extension `univ.Obj S` is
`Σ (T : Type u), T → S`, so a dynamical system over `univ` is a transition system that
exposes at each state the type of its currently enabled events; see `PFunctor.DynSystem`.

Reducible so that a direction type `univ.B T` unfolds to `T` during elaboration and
instance search, keeping transitions over `univ` as ergonomic as bare functions. -/
@[reducible]
def univ : PFunctor.{u + 1, u} :=
  ⟨Type u, fun T => T⟩


-- @@ L106-106 verbatim
section Coprod

-- @@ L107-107 verbatim
instance {a} : IsEmpty (B 1 a) := inferInstanceAs (IsEmpty PEmpty)

-- @@ L108-108 verbatim
instance {α} (a : α) : IsEmpty (B (C α) a) := inferInstanceAs (IsEmpty PEmpty)

-- @@ L109-109 verbatim
instance {a} : Unique (B y a) := inferInstanceAs (Unique PUnit)

-- @@ L110-110 verbatim
instance {α} (a : α) : Unique (B (linear α) a) := inferInstanceAs (Unique PUnit)

-- @@ L111-111 verbatim
instance {β} : Unique (A (purePower β)) := inferInstanceAs (Unique PUnit)


-- @@ L113-113 verbatim
@[simp] lemma C_empty : C PEmpty = 0 := rfl

-- @@ L114-114 verbatim
@[simp] lemma C_unit : C PUnit = 1 := rfl


-- @@ L116-116 verbatim
@[simp] lemma C_A (A : Type u) : (C A).A = A := rfl

-- @@ L117-117 verbatim
@[simp] lemma C_B (A : Type u) (a : (C A).A) : (C A).B a = PEmpty := rfl


-- @@ L119-119 verbatim
@[simp] lemma y_A : y.A = PUnit := rfl

-- @@ L120-120 verbatim
@[simp] lemma y_B (a : y.A) : y.B a = PUnit := rfl


-- @@ L122-122 verbatim
@[deprecated (since := "2026-08-17")] alias X_A := y_A

-- @@ L123-123 verbatim
@[deprecated (since := "2026-08-17")] alias X_B := y_B


-- @@ L125-125 verbatim
@[simp] lemma linear_A (A : Type u) : (linear A).A = A := rfl

-- @@ L126-126 verbatim
@[simp] lemma linear_B (A : Type u) (a : (linear A).A) : (linear A).B a = PUnit := rfl


-- @@ L128-128 verbatim
@[simp] lemma selfMonomial_A (S : Type u) : (selfMonomial S).A = S := rfl

-- @@ L129-129 verbatim
@[simp] lemma selfMonomial_B (S : Type u) (a : (selfMonomial S).A) : (selfMonomial S).B a = S := rfl

-- @@ L130-130 verbatim
@[simp] lemma selfMonomial_unit : selfMonomial PUnit = y := rfl


-- @@ L132-132 verbatim
@[simp] lemma purePower_A (B : Type u) : (purePower B).A = PUnit := rfl

-- @@ L133-133 verbatim
@[simp] lemma purePower_B (B : Type u) (a : (purePower B).A) : (purePower B).B a = B := rfl

-- @@ L134-134 verbatim
@[simp] lemma purePower_unit : purePower PUnit = y := rfl


-- @@ L136-137 verbatim
@[simp] lemma univ_A : univ.{u}.A = Type u := rfl
lemma univ_B (T : Type u) : univ.{u}.B T = T := rfl


-- @@ L139-139 verbatim
section Sum


-- @@ L141-149 verbatim
/-- The sum (coproduct) of two polynomial functors `P` and `Q`, written as `P + Q`.

Defined as the sum of the head types and the dependent sum recursor for the child types. The
recursor is written directly so that nested coproduct directions normalize at implicit
transparency.

Note: requires the `B` universe levels to be the same. -/
abbrev sum (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) : PFunctor.{max uA₁ uA₂, uB} :=
  ⟨P.A ⊕ Q.A, @Sum.rec P.A Q.A (fun _ => Type uB) P.B Q.B⟩


-- @@ L151-153 verbatim
@[simp]
lemma sum_A (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    (sum P Q).A = (P.A ⊕ Q.A) := rfl


-- @@ L155-157 verbatim
@[simp]
lemma sum_B_inl (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : P.A) :
    (sum P Q).B (.inl a) = P.B a := rfl


-- @@ L159-161 verbatim
@[simp]
lemma sum_B_inr (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) (a : Q.A) :
    (sum P Q).B (.inr a) = Q.B a := rfl


-- @@ L163-166 verbatim
/-- Addition of polynomial functors, defined as the sum construction. -/
@[reducible] instance instHAddPFunctor :
    HAdd PFunctor.{uA₁, uB} PFunctor.{uA₂, uB} PFunctor.{max uA₁ uA₂, uB} where
  hAdd := sum


-- @@ L168-175 verbatim
@[reducible] instance instAddPFunctor : Add PFunctor.{uA, uB} where
  add := sum

lemma add_def (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    P + Q = ⟨P.A ⊕ Q.A, @Sum.rec P.A Q.A (fun _ => Type uB) P.B Q.B⟩ := rfl

-- alias coprodUnit := zero
alias coprod := sum


-- @@ L177-179 verbatim
/-- The generalized sum (sigma type) of an indexed family of polynomial functors. -/
def sigma {I : Type v} (F : I → PFunctor.{uA, uB}) : PFunctor.{max uA v, uB} :=
  ⟨Σ i, (F i).A, fun ⟨i, a⟩ => (F i).B a⟩


-- @@ L181-182 verbatim
/-- `Σₚ i, F i` is the indexed sum `PFunctor.sigma F` of a family of polynomial functors. -/
scoped notation3 "Σₚ "(...)", "F:60:(
-- @@ L182-182 verbatim
scoped f => PFunctor.sigma f) => F


-- @@ L184-184 verbatim
end Sum


-- @@ L186-186 verbatim
section Prod


-- @@ L188-193 verbatim
/-- The product of two polynomial functors `P` and `Q`, written as `P * Q`.

Defined as the product of the head types and the sum of the child types. -/
def prod (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 ⊕ Q.B ab.2⟩


-- @@ L195-198 verbatim
/-- Multiplication of polynomial functors, defined as the product construction. -/
instance instHMulPFunctor :
    HMul PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{max uA₁ uA₂, max uB₁ uB₂} where
  hMul := prod


-- @@ L200-201 verbatim
instance instMulPFunctor : Mul PFunctor.{uA, uB} where
  mul := prod


-- @@ L203-205 verbatim
/-- The generalized product (pi type) of an indexed family of polynomial functors. -/
def pi {I : Type v} (F : I → PFunctor.{uA, uB}) : PFunctor.{max uA v, max uB v} :=
  ⟨(i : I) → (F i).A, fun f => Σ i, (F i).B (f i)⟩


-- @@ L207-208 verbatim
/-- `Πₚ i, F i` is the indexed product `PFunctor.pi F` of a family of polynomial functors. -/
scoped notation3 "Πₚ "(...)", "F:60:(
-- @@ L208-208 verbatim
scoped f => PFunctor.pi f) => F


-- @@ L210-210 verbatim
end Prod


-- @@ L212-212 verbatim
section Tensor


-- @@ L214-219 verbatim
/-- The tensor (also called parallel or Dirichlet) product of two polynomial functors `P` and `Q`.

Defined as the product of the head types and the product of the child types. -/
def tensor (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} :=
  ⟨P.A × Q.A, fun ab => P.B ab.1 × Q.B ab.2⟩


-- @@ L221-222 verbatim
/-- Infix notation for tensor product `P ⊗ Q` -/
scoped[PFunctor] 
-- @@ L222-222 verbatim
infixl:70 " ⊗ " => tensor


-- @@ L224-225 verbatim
/-- The unit for the tensor product, the variable `y` -/
alias tensorUnit := y


-- @@ L227-227 verbatim
end Tensor


-- @@ L229-229 verbatim
section Comp


-- @@ L231-232 verbatim
/-- Infix notation for `PFunctor.comp P Q` -/
scoped[PFunctor] 
-- @@ L232-232 verbatim
infixl:80 " ◃ " => PFunctor.comp


-- @@ L234-235 verbatim
/-- The unit for composition, the variable `y` -/
alias compUnit := y


-- @@ L237-241 verbatim
/-- The composition power `P ◃^ n`, the `n`-fold composite `P ◃ P ◃ ... ◃ P`. -/
@[simp]
def compNth (P : PFunctor.{uA, uB}) : Nat → PFunctor.{max uA uB, uB}
  | 0 => y
  | Nat.succ n => P ◃ compNth P n


-- @@ L243-243 verbatim
@[inherit_doc] scoped[PFunctor] 
-- @@ L243-243 verbatim
infixl:85 " ◃^ " => compNth


-- @@ L245-248 verbatim
/-- Compatibility instance for the former `p ^ n` composition-power spelling.
The canonical notation is `p ◃^ n`. -/
instance instNatPowPFunctor : NatPow PFunctor.{max uA uB, uB} where
  pow := compNth


-- @@ L250-250 verbatim
end Comp


-- @@ L252-252 verbatim
section ULift


-- @@ L254-256 verbatim
/-- Lift a polynomial functor `P` to a pair of larger universes. -/
protected def ulift (P : PFunctor.{uA, uB}) : PFunctor.{max uA vA, max uB vB} :=
  ⟨ULift P.A, fun a => ULift (P.B (ULift.down a))⟩


-- @@ L258-258 verbatim
end ULift


-- @@ L260-262 verbatim
/-- Exponential of polynomial functors `P ^ Q` -/
def exp (P Q : PFunctor.{uA, uB}) : PFunctor.{max uA uB, max uA uB} :=
  pi (fun a => P ◃ (y + C (Q.B a)))


-- @@ L264-266 verbatim
instance instHPowPFunctor :
    HPow PFunctor.{uA, uB} PFunctor.{uA, uB} PFunctor.{max uA uB, max uA uB} where
  hPow := exp


-- @@ L268-268 verbatim
section Fintype


-- @@ L270-273 verbatim
/-- A polynomial functor is finitely branching if each of its branches is a finite type. -/
protected class Fintype (P : PFunctor.{uA, uB}) where
  /-- The direction type over each position `a` is a finite type. -/
  fintypeB : ∀ a, Fintype (P.B a)


-- @@ L275-279 verbatim
instance {P : PFunctor.{uA, uB}} [inst : P.Fintype] : PFunctor.Fintype (PFunctor.ulift P) where
  fintypeB := fun a => by
    unfold PFunctor.ulift
    have : Fintype (P.B (ULift.down a)) := inst.fintypeB (ULift.down a)
    infer_instance


-- @@ L281-283 verbatim
@[simp]
instance {P : PFunctor.{uA, uB}} [inst : P.Fintype] : ∀ a, Fintype (P.B a) :=
  fun a => inst.fintypeB a


-- @@ L285-286 verbatim
instance : PFunctor.Fintype 0 where
  fintypeB _ := Fintype.instPEmpty


-- @@ L288-289 verbatim
instance : PFunctor.Fintype 1 where
  fintypeB _ := Fintype.instPEmpty


-- @@ L291-291 verbatim
end Fintype


-- @@ L293-293 verbatim
section Inhabited


-- @@ L295-298 verbatim
/-- A polynomial functor is pointwise inhabited if each of its branches is an inhabited type. -/
protected class Inhabited (P : PFunctor.{uA, uB}) where
  /-- The direction type over each position `a` is inhabited. -/
  inhabitedB : ∀ a, Inhabited (P.B a)


-- @@ L300-305 verbatim
instance {P : PFunctor.{uA, uB}} [inst : P.Inhabited] :
    PFunctor.Inhabited (PFunctor.ulift P) where
  inhabitedB := fun a => by
    unfold PFunctor.ulift
    have : Inhabited (P.B (ULift.down a)) := inst.inhabitedB (ULift.down a)
    infer_instance


-- @@ L307-309 verbatim
@[simp]
instance {P : PFunctor.{uA, uB}} [inst : P.Inhabited] : ∀ a, Inhabited (P.B a) :=
  fun a => inst.inhabitedB a


-- @@ L311-311 verbatim
end Inhabited


-- @@ L313-313 verbatim
section DecidableEq


-- @@ L315-321 verbatim
/-- A polynomial functor has decidable equality if its position type and each of its
direction types have decidable equality. -/
protected class DecidableEq (P : PFunctor.{uA, uB}) where
  /-- The position type `P.A` has decidable equality. -/
  decidableEqA : DecidableEq P.A
  /-- The direction type over each position `a` has decidable equality. -/
  decidableEqB : ∀ a, DecidableEq (P.B a)


-- @@ L323-324 verbatim
instance {P : PFunctor.{uA, uB}} [inst : P.DecidableEq] : DecidableEq P.A :=
  inst.decidableEqA


-- @@ L326-327 verbatim
instance {P : PFunctor.{uA, uB}} [inst : P.DecidableEq] (a : P.A) :
    DecidableEq (P.B a) := inst.decidableEqB a


-- @@ L329-337 verbatim
@[simp]
instance {P : PFunctor.{uA, uB}} [inst : P.DecidableEq] :
    PFunctor.DecidableEq (PFunctor.ulift P) where
  decidableEqA := by
    unfold PFunctor.ulift
    infer_instance
  decidableEqB := fun a => by
    unfold PFunctor.ulift
    infer_instance


-- @@ L339-341 verbatim
instance : PFunctor.DecidableEq 0 where
  decidableEqA := inferInstanceAs (DecidableEq PEmpty)
  decidableEqB _ := inferInstanceAs (DecidableEq PEmpty)


-- @@ L343-345 verbatim
instance : PFunctor.DecidableEq 1 where
  decidableEqA := inferInstanceAs (DecidableEq PUnit)
  decidableEqB _ := inferInstanceAs (DecidableEq PEmpty)


-- @@ L347-347 verbatim
end DecidableEq


-- @@ L349-349 verbatim
section ofConst


-- @@ L351-354 verbatim
/-- PFunctor where the output type is constant over an arbitrary input type. -/
def ofConst (A : Type uA) (B : Type uB) : PFunctor.{uA, uB} where
  A := A
  B _ := B


-- @@ L356-356 verbatim
variable (A : Type uA) (B : Type uB)


-- @@ L358-359 verbatim
instance [hB : Fintype B] : (ofConst A B).Fintype where
  fintypeB _ := inferInstanceAs (Fintype B)


-- @@ L361-363 verbatim
instance [DecidableEq A] [DecidableEq B] : (ofConst A B).DecidableEq where
  decidableEqA := inferInstanceAs (DecidableEq A)
  decidableEqB _ := inferInstanceAs (DecidableEq B)


-- @@ L365-366 verbatim
instance [Inhabited B] : (ofConst A B).Inhabited where
  inhabitedB _ := inferInstanceAs (Inhabited B)


-- @@ L368-368 verbatim
end ofConst

-- @@ L369-374 verbatim
/-- An equivalence between two polynomial functors `P` and `Q`, written `P ≃ₚ Q`, is given by an
equivalence of the `A` types and an equivalence between the `B` types for each `a : A`. -/
@[ext]
protected structure Equiv (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- An equivalence between the `A` types -/
  equivA : P.A ≃ Q.A
  
-- @@ L375-376 verbatim
/-- An equivalence between the `B` types for each `a : A` -/
  equivB : ∀ a, P.B a ≃ Q.B (equivA a)


-- @@ L378-378 verbatim
@[inherit_doc] scoped[PFunctor] 
-- @@ L378-378 verbatim
infixl:25 " ≃ₚ " => PFunctor.Equiv


-- @@ L380-380 verbatim
namespace Equiv


-- @@ L382-382 verbatim
variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}}


-- @@ L384-387 verbatim
/-- The identity equivalence between a polynomial functor `P` and itself. -/
def refl (P : PFunctor.{uA, uB}) : P ≃ₚ P where
  equivA := _root_.Equiv.refl P.A
  equivB := fun a => _root_.Equiv.refl (P.B a)


-- @@ L389-394 verbatim
/-- The inverse of an equivalence between polynomial functors. -/
def symm {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (E : P ≃ₚ Q) : Q ≃ₚ P where
  equivA := E.equivA.symm
  equivB := fun a =>
    (Equiv.cast (congrArg Q.B ((Equiv.symm_apply_eq E.equivA).mp rfl))).trans
      (E.equivB (E.equivA.symm a)).symm


-- @@ L396-400 verbatim
/-- The composition of two equivalences between polynomial functors. -/
def trans {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}
    (E : P ≃ₚ Q) (F : Q ≃ₚ R) : P ≃ₚ R where
  equivA := E.equivA.trans F.equivA
  equivB := fun a => (E.equivB a).trans (F.equivB (E.equivA a))


-- @@ L402-406 verbatim
/-- Equivalence between two polynomial functors `P` and `Q` that are equal. -/
def cast {P Q : PFunctor.{uA, uB}} (hA : P.A = Q.A) (hB : ∀ a, P.B a = Q.B (cast hA a)) :
    P ≃ₚ Q where
  equivA := _root_.Equiv.cast hA
  equivB := fun a => _root_.Equiv.cast (hB a)


-- @@ L408-411 verbatim
@[simp]
theorem symm_comp_self {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} (e : P ≃ₚ Q) :
    e.symm.equivA ∘ e.equivA = id := by
  simp [Equiv.symm]


-- @@ L413-418 verbatim
/-- Rewrite a dependent `Eq.rec` with identity to a cast on the argument. -/
lemma eqRec_id_apply {α : Sort u} {β : α → Sort v}
    {a1 a0 : α} (h : a1 = a0) (x : β a0) :
    Eq.rec (motive := fun y _ => β y → β a1) id h x = _root_.cast (congrArg β h).symm x := by
  cases h
  rfl


-- @@ L420-427 verbatim
/-- Cast-normalization helper for `equivB` under equal `equivA` images. -/
lemma equivB_symm_apply_of_eq (e : P ≃ₚ Q) {a a' : P.A} (ha : e.equivA a = e.equivA a')
    (b : P.B a') :
    (e.equivB a).symm ((_root_.Equiv.cast (congrArg Q.B ha)).symm ((e.equivB a') b)) =
      _root_.cast (congrArg P.B (e.equivA.injective ha).symm) b := by
  have ha' : a = a' := e.equivA.injective ha
  cases ha'
  simp


-- @@ L429-434 verbatim
/-- Cast-normalization helper for `symm.equivB` under equal `symm.equivA` images. -/
lemma symm_equivB_symm_apply_of_eq (e : P ≃ₚ Q) {a a' : Q.A}
    (ha : e.symm.equivA a = e.symm.equivA a') (b : Q.B a') :
    (e.symm.equivB a).symm ((_root_.Equiv.cast (congrArg P.B ha)).symm ((e.symm.equivB a') b)) =
      _root_.cast (congrArg Q.B (e.symm.equivA.injective ha).symm) b := by
  simpa using equivB_symm_apply_of_eq (e := e.symm) (a := a) (a' := a') (ha := ha) (b := b)


-- @@ L436-445 verbatim
/-- Specialized cast-normalization for `e` followed by `e.symm`. -/
lemma equivB_symm_apply (e : P ≃ₚ Q) (a : P.A) (b : P.B (e.equivA.symm (e.equivA a))) :
    (e.equivB a).symm ((e.symm.equivB (e.equivA a)).symm b) =
      _root_.cast (congrArg P.B (e.equivA.symm_apply_apply a)) b := by
  have hEqA : e.equivA a = e.equivA (e.equivA.symm (e.equivA a)) := by
    simp
  simp only [PFunctor.Equiv.symm]
  exact equivB_symm_apply_of_eq (e := e)
    (a := a) (a' := e.equivA.symm (e.equivA a))
    (ha := hEqA) (b := b)


-- @@ L447-456 verbatim
/-- Specialized cast-normalization for `e.symm` followed by `e`. -/
lemma symm_equivB_symm_apply (e : P ≃ₚ Q) (a : Q.A) (b : Q.B (e.equivA (e.equivA.symm a))) :
    (e.symm.equivB a).symm ((e.equivB (e.equivA.symm a)).symm b) =
      _root_.cast (congrArg Q.B (e.equivA.apply_symm_apply a)) b := by
  change ((_root_.Equiv.cast (congrArg Q.B ((_root_.Equiv.symm_apply_eq e.equivA).mp rfl))).symm
      ((e.equivB (e.equivA.symm a)) ((e.equivB (e.equivA.symm a)).symm b))) = _
  rw [_root_.Equiv.apply_symm_apply (e.equivB (e.equivA.symm a)) b]
  change _root_.cast (congrArg Q.B ((_root_.Equiv.symm_apply_eq e.equivA).mp rfl)).symm b =
    _root_.cast (congrArg Q.B (e.equivA.apply_symm_apply a)) b
  simp


-- @@ L458-467 verbatim
/-- Forward roundtrip: applying `equivB` then `symm.equivB` gives a cast. -/
lemma forward_equivB_roundtrip (e : P ≃ₚ Q) (a : P.A) (b : P.B a) :
    e.symm.equivB (e.equivA a) (e.equivB a b) =
      _root_.cast (congrArg P.B (e.equivA.symm_apply_apply a).symm) b := by
  change (((_root_.Equiv.cast _).trans
    (e.equivB (e.equivA.symm (e.equivA a))).symm) (e.equivB a b)) = _
  simp only [_root_.Equiv.trans_apply]
  exact equivB_symm_apply_of_eq e
    (a := e.equivA.symm (e.equivA a)) (a' := a)
    (ha := e.equivA.apply_symm_apply _) (b := b)


-- @@ L469-478 verbatim
/-- Reverse roundtrip: applying `symm.equivB` then `equivB` gives a cast. -/
lemma reverse_equivB_roundtrip (e : P ≃ₚ Q) (a : Q.A)
    (b : Q.B a) :
    e.equivB (e.equivA.symm a) (e.symm.equivB a b) =
      _root_.cast
        (congrArg Q.B (e.equivA.apply_symm_apply a).symm) b := by
  change ((e.equivB (e.equivA.symm a)))
    (((_root_.Equiv.cast _).trans
      (e.equivB (e.equivA.symm a)).symm) b) = _
  simp [_root_.Equiv.trans_apply]


-- @@ L480-480 verbatim
end Equiv


-- @@ L482-490 verbatim
/-- A **lens** between two polynomial functors `P` and `Q` is a pair of a function:
- `toFunA : P.A → Q.A`
- `toFunB : ∀ a, Q.B (toFunA a) → P.B a` -/
structure Lens (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward map on positions, sending each position of `P` to a position of `Q`. -/
  toFunA : P.A → Q.A
  /-- The backward map on directions, pulling a direction of `Q` at `toFunA a` back to a
  direction of `P` at `a`. -/
  toFunB : ∀ a, Q.B (toFunA a) → P.B a


-- @@ L492-493 verbatim
/-- Infix notation for constructing a lens `toFunA ⇆ toFunB` -/
infixr:25 " ⇆ " => Lens.mk


-- @@ L495-503 verbatim
/-- A chart between two polynomial functors `P` and `Q` is a pair of a function:
- `toFunA : P.A → Q.A`
- `toFunB : ∀ a, P.B a → Q.B (toFunA a)` -/
structure Chart (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) where
  /-- The forward map on positions, sending each position of `P` to a position of `Q`. -/
  toFunA : P.A → Q.A
  /-- The forward map on directions, pushing a direction of `P` at `a` to a direction of `Q`
  at `toFunA a`. -/
  toFunB : ∀ a, P.B a → Q.B (toFunA a)


-- @@ L505-506 verbatim
/-- Infix notation for constructing a chart `toFunA ⇉ toFunB` -/
infixr:25 " ⇉ " => Chart.mk


-- @@ L508-508 verbatim
section Lemmas


-- @@ L510-510 verbatim
@[ext (iff := false)]

-- @@ L511-516 verbatim
theorem ext {P Q : PFunctor.{uA, uB}} (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) : P = Q := by
  cases P; cases Q; simp only [mk.injEq] at h h' ⊢; subst h;
  simp_all only [heq_eq_eq, true_and]; funext; exact h' _

lemma y_eq_linear_pUnit : y = linear PUnit := rfl
lemma y_eq_purePower_pUnit : y = purePower PUnit := rfl


-- @@ L518-518 verbatim
@[deprecated (since := "2026-08-17")] alias X_eq_linear_pUnit := y_eq_linear_pUnit

-- @@ L519-519 verbatim
@[deprecated (since := "2026-08-17")] alias X_eq_purePower_pUnit := y_eq_purePower_pUnit


-- @@ L521-521 verbatim
section ULift


-- @@ L523-523 verbatim
variable {P : PFunctor.{uA, uB}}


-- @@ L525-526 verbatim
@[simp]
theorem ulift_A : (P.ulift).A = ULift P.A := rfl


-- @@ L528-529 verbatim
@[simp]
theorem ulift_B {a : P.A} : (P.ulift).B (ULift.up a) = ULift (P.B a) := rfl


-- @@ L531-531 verbatim
end ULift


-- @@ L533-533 verbatim
end Lemmas


-- @@ L535-535 verbatim
end Coprod

-- @@ L536-536 verbatim
end Basic

-- @@ L537-537 verbatim
end PFunctor
