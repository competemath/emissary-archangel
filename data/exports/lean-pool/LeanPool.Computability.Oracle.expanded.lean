/-
Copyright (c) 2026 Tanner Duve, Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Mathlib.Computability.Partrec


-- @@ L10-39 verbatim
/-!
# Oracle Computability

This file defines a model of oracle computability using partial recursive functions. It extends
the notion of `Nat.Partrec` by allowing access to a set of oracle functions.

## Main Definitions

* `RecursiveIn O f`:
  A partial function `f : ℕ →. ℕ` is recursive in a set of oracles `O ⊆ ℕ →. ℕ` if it can be
  constructed from constants, basic operations, and functions in `O` using pairing, composition,
  primitive recursion, and μ-recursion.
* `liftPrim`: Encodes a function `α →. σ` as a function `ℕ →. ℕ` using `Primcodable`.
* `RecursiveIn'`, `RecursiveIn₂`, `ComputableIn`, `ComputableIn₂`:
  Versions of `RecursiveIn` for functions between `Primcodable` types.

## Implementation Notes

The encoding/decoding mechanism relies on `Primcodable`. The definition of `RecursiveIn` mimics
the inductive structure of `Nat.Partrec`.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers*, Vol. I.

## Tags

Computability, Oracle, Recursion, Primitive Recursion
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
open Primrec Nat.Partrec Part Encodable


-- @@ L45-45 verbatim
namespace Computability


-- @@ L47-47 verbatim
variable {f g h : ℕ →. ℕ}


-- @@ L49-72 verbatim
/--
The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O fun _ => 0
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O fun n => (Nat.unpair n).1
  | right : RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : ∀ g ∈ O, RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
      RecursiveIn O fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)


-- @@ L74-88 verbatim
/-- The primitive recursive functions `ℕ → ℕ` relative to a set of oracles `O`. -/
inductive PrimrecIn (O : Set (ℕ → ℕ)) : (ℕ → ℕ) → Prop
  | zero : PrimrecIn O fun _ => 0
  | succ : PrimrecIn O Nat.succ
  | left : PrimrecIn O fun n => n.unpair.1
  | right : PrimrecIn O fun n => n.unpair.2
  | oracle : ∀ g ∈ O, PrimrecIn O g
  | pair {f g : ℕ → ℕ} :
      PrimrecIn O f → PrimrecIn O g → PrimrecIn O fun n => Nat.pair (f n) (g n)
  | comp {f g : ℕ → ℕ} : PrimrecIn O f → PrimrecIn O g → PrimrecIn O fun n => f (g n)
  | prec {f g : ℕ → ℕ} :
      PrimrecIn O f →
        PrimrecIn O g →
          PrimrecIn O
            (Nat.unpaired fun z n => n.rec (f z) fun y IH => g <| Nat.pair z <| Nat.pair y IH)


-- @@ L90-92 verbatim
/-- Encodes a partial function `α →. σ` as a partial function `ℕ →. ℕ` using `Primcodable`. -/
def liftPrim {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) : ℕ →. ℕ :=
  fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode


-- @@ L94-96 verbatim
/-- Encodes a total function `α → σ` as a function `ℕ → ℕ` using `Primcodable`. -/
def liftPrimrec {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) : ℕ → ℕ :=
  fun n => (decode (α := α) n).map (fun a => encode (f a)) |>.getD 0


-- @@ L98-100 verbatim
/-- A partial function between `Primcodable` types is recursive in `O` if its lift is. -/
def RecursiveIn' {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α →. σ) : Prop :=
  RecursiveIn O (liftPrim f)


-- @@ L102-104 verbatim
/-- Relative primitive recursion between primcodable types -/
def PrimrecIn' {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ → ℕ)) (f : α → σ) : Prop :=
  PrimrecIn O (liftPrimrec f)


-- @@ L106-109 verbatim
/-- A binary partial function is recursive in `O` if the curried form is. -/
def RecursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β →. σ) : Prop :=
  RecursiveIn' O (fun p : α × β => f p.1 p.2)


-- @@ L111-113 verbatim
/-- A total function is computable in `O` if its constant lift is recursive in `O`. -/
def ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α → σ) : Prop :=
  RecursiveIn' O (fun a => Part.some (f a))


-- @@ L115-118 verbatim
/-- A binary total function is computable in `O`. -/
def ComputableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β → σ) : Prop :=
  ComputableIn O (fun p : α × β => f p.1 p.2)


-- @@ L120-122 verbatim
theorem RecursiveIn.of_eq {f g : ℕ →. ℕ} (hf : RecursiveIn O f) (H : ∀ n, f n = g n) :
    RecursiveIn O g :=
  (funext H : f = g) ▸ hf


-- @@ L124-126 verbatim
theorem RecursiveIn.of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : RecursiveIn O f)
    (H : ∀ n, g n ∈ f n) : RecursiveIn O g :=
  hf.of_eq fun n => eq_some_iff.2 (H n)

-- @@ L127-136 verbatim
/--
If a function is partial recursive, then it is recursive in every partial function.
-/
lemma recursiveIn_of_partrec (pF : Nat.Partrec f) : RecursiveIn O f := by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih


-- @@ L138-144 verbatim
/--
If a function is computable, then it is computable in every oracle.
-/
theorem computableIn_of_computable {f : α → β} [Primcodable α]
[Primcodable β]
(hf : Computable f) : ComputableIn O f :=
  recursiveIn_of_partrec hf


-- @@ L146-147 verbatim
theorem RecursiveIn.of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
RecursiveIn O (fun n => f n) := recursiveIn_of_partrec (Nat.Partrec.of_primrec hf)


-- @@ L149-151 verbatim
theorem computableIn_of_primrec {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} (hf : Primrec f) (O : Set (ℕ →. ℕ)) :
    ComputableIn O f := computableIn_of_computable (Primrec.to_comp hf)


-- @@ L153-156 verbatim
theorem computableIn₂_of_primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Primrec₂ f) (O : Set (ℕ →. ℕ)) :
    ComputableIn₂ O f :=
  computableIn_of_primrec hf O


-- @@ L158-160 verbatim
protected theorem ComputableIn.recursiveIn' {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : ComputableIn O f) :
    RecursiveIn' O (fun a => Part.some (f a)) := hf


-- @@ L162-164 verbatim
protected theorem ComputableIn₂.recursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : ComputableIn₂ O f) :
    RecursiveIn₂ O fun a => (f a : β →. σ) := hf


-- @@ L166-167 verbatim
protected theorem RecursiveIn.some : RecursiveIn O some :=
  RecursiveIn.of_primrec Nat.Primrec.id


-- @@ L169-173 verbatim
theorem RecursiveIn.none : RecursiveIn O (fun _ => none) :=
  (RecursiveIn.of_primrec (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by
      obtain ⟨_, hn, -⟩ := Nat.rfind_dom.1 h
      simp at hn


-- @@ L175-175 verbatim
variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}

-- @@ L176-176 verbatim
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]


-- @@ L178-179 verbatim
theorem const_in (O : Set (ℕ →. ℕ)) (s : σ) : ComputableIn O (fun _ : α => s) :=
  computableIn_of_primrec (Primrec.const s) O


-- @@ L181-182 verbatim
theorem id_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@id α) :=
  computableIn_of_primrec Primrec.id O


-- @@ L184-185 verbatim
theorem fst_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.fst α β) :=
  computableIn_of_primrec Primrec.fst O


-- @@ L187-188 verbatim
theorem snd_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.snd α β) :=
  computableIn_of_primrec Primrec.snd O


-- @@ L190-191 verbatim
theorem unpair_in (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.unpair :=
  computableIn_of_primrec Primrec.unpair O


-- @@ L193-194 verbatim
theorem succ_in (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.succ :=
  computableIn_of_primrec Primrec.succ O


-- @@ L196-197 verbatim
theorem sumInl_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inl α β) :=
  computableIn_of_primrec Primrec.sumInl O


-- @@ L199-200 verbatim
theorem sumInr_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inr α β) :=
  computableIn_of_primrec Primrec.sumInr O


-- @@ L202-214 verbatim
/--
If a function is recursive in the constant zero function,
then it is partial recursive.
-/
lemma RecursiveIn.partrec_of_zero (fRecInZero : RecursiveIn {fun _ => Part.some 0} f) :
    Nat.Partrec f := by
  induction fRecInZero with
  | zero | succ | left | right => constructor
  | oracle g hg => rw [hg]; exact Nat.Partrec.zero
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih


-- @@ L216-228 verbatim
/--
If a function is partial recursive in the constant none function,
then it is partial recursive.
-/
lemma RecursiveIn.partrec_of_none (fRecInNone : RecursiveIn {fun _ => Part.none} f) :
    Nat.Partrec f := by
  induction fRecInNone with
  | zero | succ | left | right => constructor
  | oracle g hg => rw [hg]; exact Nat.Partrec.none
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih


-- @@ L230-235 verbatim
/--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_forall_recursiveIn : Nat.Partrec f ↔ ∀ g, RecursiveIn {g} f:=
  ⟨fun hf _ ↦ recursiveIn_of_partrec hf, (· _ |>.partrec_of_zero)⟩


-- @@ L237-249 verbatim
@[simp]
lemma recursiveIn_empty_iff_partrec : RecursiveIn {} f ↔ Nat.Partrec f := by
  constructor
  · intro hf
    induction hf with
    | zero | succ | left | right => constructor
    | oracle g hg => cases hg
    | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
    | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
    | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
    | rfind _ ih => exact .rfind ih
  · intro hf
    exact recursiveIn_of_partrec (O := ({} : Set (ℕ →. ℕ))) hf


-- @@ L251-260 verbatim
theorem recursiveIn_mono {O₁ O₂ : Set (ℕ →. ℕ)} (hsub : O₁ ⊆ O₂) {g : ℕ →. ℕ} :
      RecursiveIn O₁ g → RecursiveIn O₂ g := by
  intro hg
  induction hg with
  | zero | succ | left | right => constructor
  | oracle g hg => exact RecursiveIn.oracle g (hsub hg)
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih


-- @@ L262-270 verbatim
theorem RecursiveIn_subst {O O' : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} (hf : RecursiveIn O f)
    (hO : ∀ g, g ∈ O → RecursiveIn O' g) : RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf


-- @@ L272-272 verbatim
end Computability
