/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Classes.Slice
public import ArkLib.Data.Fin.Tuple.Defs
public import ArkLib.Data.Fin.Basic
public import Mathlib.Tactic.FinCases


-- @@ L13-39 verbatim
/-!
# Slice notation instances for Fin tuples

This file provides instances of the generic slice type classes (`SliceLT`, `SliceGE`, `Slice`)
for Fin tuples, enabling Python-like slice notation:
- `v⟦:m⟧` takes the first `m` elements
- `v⟦m:⟧` drops the first `m` elements
- `v⟦m₁:m₂⟧` takes elements from index `m₁` to `m₂ - 1`

The instances work for both homogeneous (`Fin n → α`) and heterogeneous (`(i : Fin n) → α i`)
Fin tuples, delegating to the existing `Fin.take` and `Fin.drop` operations.

Each notation also supports manual proof syntax with `'h`:
- `v⟦:m⟧'h` for explicit proof in take operations
- `v⟦m:⟧'h` for explicit proof in drop operations
- `v⟦m₁:m₂⟧'⟨h₁, h₂⟩` for explicit proofs in range operations

## Examples

```lean
variable (v : Fin 10 → ℕ)

#check v⟦:5⟧   -- Takes first 5 elements: Fin 5 → ℕ
#check v⟦3:⟧   -- Drops first 3 elements: Fin 7 → ℕ
#check v⟦2:8⟧  -- Elements 2 through 7: Fin 6 → ℕ
```
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
universe u v v' w


-- @@ L45-45 verbatim
/-! ## Instances for Fin tuples -/


-- @@ L47-47 verbatim
namespace Fin


-- @@ L49-53 verbatim
instance {n : ℕ} {α : Fin n → Type*} : SliceLT ((i : Fin n) → α i) ℕ
    (fun _ stop => stop ≤ n)
    (fun _ stop h => (i : Fin stop) → α (i.castLE h))
    where
  sliceLT := fun v stop h => take stop h v


-- @@ L55-60 verbatim
instance {n : ℕ} {α : Fin n → Type*} : SliceGE ((i : Fin n) → α i) ℕ
    (fun _ start => start ≤ n)
    (fun _ start h =>
      (i : Fin (n - start)) → α (Fin.cast (Nat.sub_add_cancel h) (i.addNat start)))
    where
  sliceGE := fun v start h => drop start h v


-- @@ L62-68 verbatim
instance {n : ℕ} {α : Fin n → Type*} : Slice ((i : Fin n) → α i) ℕ ℕ
    (fun _ start stop => start ≤ stop ∧ stop ≤ n)
    (fun _ start stop h =>
      (i : Fin (stop - start)) →
        α (castLE h.2 (Fin.cast (Nat.sub_add_cancel h.1) (i.addNat start))))
    where
  slice := fun v start stop h => Fin.drop start h.1 (Fin.take stop h.2 v)


-- @@ L70-70 verbatim
end Fin


-- @@ L72-72 verbatim
section Examples


-- @@ L74-74 verbatim
open Fin


-- @@ L76-78 verbatim
/-!
## Examples showing the Python-like slice notation works correctly
-/


-- @@ L80-80 verbatim
variable {n : ℕ} (hn5 : 5 ≤ n) (hn10 : 10 ≤ n) (v : Fin n → ℕ)


-- @@ L82-82 expanded
example : SliceLT.sliceLT v 3 (by get_elem_tactic) = Fin.take 3 (by omega) v :=
  rfl


-- @@ L83-83 expanded
example : SliceGE.sliceGE v 2 (by get_elem_tactic) = Fin.drop 2 (by omega) v :=
  rfl


-- @@ L84-86 expanded
example :
    Slice.slice v 1 4 (by get_elem_tactic) = Fin.drop 1 (by omega) (Fin.take 4 (by omega) v) :=
  rfl


-- @@ L87-87 expanded
example (h₂ : 4 ≤ n) :
    Slice.slice v 1 4 (by get_elem_tactic) = Fin.drop 1 (by omega) (Fin.take 4 h₂ v) :=
  rfl


-- @@ L88-88 expanded
example (h : 3 ≤ n) : SliceLT.sliceLT v 3 h = Fin.take 3 h v :=
  rfl


-- @@ L89-91 expanded
example (h : 2 ≤ n) : SliceGE.sliceGE v 2 h = Fin.drop 2 h v :=
  rfl


-- @@ L92-93 expanded
example : SliceLT.sliceLT (![0, 1, 2, 3, 4] : Fin 5 → ℕ) 3 (by get_elem_tactic) = ![0, 1, 2] := by
  ext i; fin_cases i <;> simp [SliceLT.sliceLT]


-- @@ L95-96 expanded
example : SliceGE.sliceGE (![0, 1, 2, 3, 4] : Fin 5 → ℕ) 2 (by get_elem_tactic) = ![2, 3, 4] := by
  ext i; fin_cases i <;> simp [SliceGE.sliceGE, drop]


-- @@ L98-101 expanded
example : Slice.slice (![0, 1, 2, 3, 4] : Fin 5 → ℕ) 1 4 (by get_elem_tactic) = ![1, 2, 3] := by
  ext i;
  fin_cases i <;>
    simp [Fin.drop, Fin.take, Slice.slice]
      -- Heterogeneous type examples


-- @@ L102-102 verbatim
variable {α : Fin n → Type*} (hv : (i : Fin n) → α i)


-- @@ L104-104 expanded
example (h : 3 ≤ n) : SliceLT.sliceLT hv 3 h = Fin.take 3 h hv :=
  rfl


-- @@ L105-105 expanded
example (h : 2 ≤ n) : SliceGE.sliceGE hv 2 h = Fin.drop 2 h hv :=
  rfl


-- @@ L106-108 expanded
example (h₂ : 4 ≤ n) :
    Slice.slice hv 1 4 (by get_elem_tactic) = Fin.drop 1 (by omega) (Fin.take 4 h₂ hv) :=
  rfl


-- @@ L109-112 expanded
example :
    Slice.slice
        (Slice.slice (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 10 → ℕ) 2 8 (by get_elem_tactic)) 1 4
        (by get_elem_tactic) =
      ![3, 4, 5] :=
  by ext i;
  fin_cases i <;>
    simp [Fin.drop, Fin.take, Slice.slice]
      -- Edge cases


-- @@ L113-114 expanded
example : SliceLT.sliceLT (![0, 1, 2] : Fin 3 → ℕ) 0 (by get_elem_tactic) = ![] := by ext i;
  exact Fin.elim0 i


-- @@ L116-121 expanded
example : SliceGE.sliceGE (![0, 1, 2] : Fin 3 → ℕ) 3 (by get_elem_tactic) = ![] :=
  by
  ext i
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd] at i
  exact Fin.elim0 i


-- @@ L122-122 verbatim
variable (w : Fin 20 → ℕ)


-- @@ L124-124 expanded
example : SliceLT.sliceLT w 5 (by get_elem_tactic) = Fin.take 5 (by omega : 5 ≤ 20) w :=
  rfl


-- @@ L125-125 expanded
example : SliceGE.sliceGE w 15 (by get_elem_tactic) = Fin.drop 15 (by omega : 15 ≤ 20) w :=
  rfl


-- @@ L126-126 expanded
example :
    Slice.slice w 3 18 (by get_elem_tactic) = Fin.drop 3 (by omega) (Fin.take 18 (by omega) w) :=
  rfl


-- @@ L128-128 expanded
example : Slice.slice w 2 4 (by get_elem_tactic) = ![w 2, w 3] := by ext i;
  fin_cases i <;> simp [drop, take, Slice.slice]


-- @@ L130-130 verbatim
end Examples


-- @@ L132-209 verbatim
/-!
## Comprehensive Tuple Notation System with Better Definitional Equality

This file provides a unified notation system for Fin-indexed tuples with better definitional
equality through pattern matching. The system supports homogeneous vectors, heterogeneous tuples,
dependent tuples, and functorial operations, all with consistent notation patterns.

### Vector and Tuple Construction Notation:

**Homogeneous Vectors** (all elements have the same type):
- `!v[a, b, c]` - basic homogeneous vector
- `!v⟨α⟩[a, b, c]` - with explicit type ascription

**Heterogeneous Tuples** (elements can have different types):
- `!h[a, b, c]` - basic heterogeneous tuple (uses `hcons`)
- `!h⟨α⟩[a, b, c]` - heterogeneous tuple with type vector ascription
- `!h⦃F⦄[a, b, c]` - functorial with explicit unary functor F but implicit type vector
- `!h⦃F⦄⟨α⟩[a, b, c]` - functorial with unary functor F and type vector α
- `!h⦃F⦄⟨α₁⟩⟨α₂⟩[a, b, c]` - functorial with binary functor F and type vectors α₁ and α₂

**Dependent Tuples** (with explicit motive specification):
- `!d[a, b, c]` - basic dependent tuple (uses `dcons`)
- `!d⟨motive⟩[a, b, c]` - with explicit motive

### Infix Operations:

**Cons Operations** (prepend element):
- `a ::ᵛ v` - homogeneous cons
- `a ::ᵛ⟨α⟩ v` - homogeneous cons with explicit type ascription
- `a ::ʰ t` - heterogeneous cons
- `a ::ʰ⟨α; β⟩ t` - heterogeneous cons with explicit type ascription
- `a ::ʰ⦃F⦄ t` - functorial cons (unary) with type besides `F` inferred
- `a ::ʰ⦃F⦄⟨α; β⟩ t` - functorial cons (unary) with explicit type ascription
- `a ::ʰ⦃F⦄⟨α₁; β₁⟩⟨α₂; β₂⟩ t` - functorial cons (binary) with explicit type ascription
- `a ::ᵈ t` - dependent cons
- `a ::ᵈ⟨motive⟩ t` - dependent cons with explicit motive

**Concat Operations** (append element):
- `v :+ᵛ a` - homogeneous concat
- `v :+ᵛ⟨α⟩ a` - homogeneous concat with explicit type ascription
- `t :+ʰ a` - heterogeneous concat
- `t :+ʰ⟨α; β⟩ a` - heterogeneous concat with explicit type ascription
- `t :+ʰ⦃F⦄ a` - functorial concat (unary) with type besides `F` inferred
- `t :+ʰ⦃F⦄⟨α; β⟩ a` - functorial concat (unary)
- `t :+ʰ⦃F⦄⟨α₁; β₁⟩⟨α₂; β₂⟩ a` - functorial concat (binary)
- `t :+ᵈ a` - dependent concat
- `t :+ᵈ⟨motive⟩ a` - dependent concat with explicit motive

**Append Operations** (concatenate two tuples):
- `u ++ᵛ v` - homogeneous append
- `u ++ᵛ⟨α⟩ v` - homogeneous append with explicit type ascription
- `u ++ʰ v` - heterogeneous append
- `u ++ʰ⟨α; β⟩ v` - heterogeneous append with explicit type ascription
- `u ++ʰ⦃F⦄ v` - functorial append (unary) with type besides `F` inferred
- `u ++ʰ⦃F⦄⟨α; β⟩ v` - functorial append (unary)
- `u ++ʰ⦃F⦄⟨α₁; β₁⟩⟨α₂; β₂⟩ v` - functorial append (binary)
- `u ++ᵈ v` - dependent append
- `u ++ᵈ⟨motive⟩ v` - dependent append with explicit motive

### Design Principles:

1. **Better Definitional Equality**: All operations use pattern matching instead of `cases`,
   `addCases`, or conditional statements for superior computational behavior.

2. **Unified `h` Superscript**: All heterogeneous and functorial operations use the `h`
   superscript with explicit type ascriptions when needed.

3. **Semicolon Separators**: Functorial operations use `α; β` syntax to clearly distinguish
   the two type arguments required for functor application.

4. **Consistent Type Ascriptions**: Explicit type information uses `⟨...⟩` brackets throughout.

5. **Unexpander Conflict Resolution**: Each construction function (`hcons`, `dcons`, etc.)
   has its own dedicated notation to prevent pretty-printing ambiguities.

This system replaces Mathlib's `Matrix.vecCons`/`Matrix.vecEmpty` approach with our custom
functions that provide better definitional equality and a more comprehensive type hierarchy.
-/


-- @@ L211-213 verbatim
namespace Fin

-- Infix notation for cons operations, similar to Vector.cons

-- @@ L214-217 verbatim
@[inherit_doc]
infixr:67 " ::ᵛ " => Fin.vcons

-- Infix notation for concat operations, following Scala convention

-- @@ L218-219 verbatim
@[inherit_doc]
infixl:65 " :+ᵛ " => Fin.vconcat


-- @@ L221-222 verbatim
/-- `::ᵛ⟨α⟩` notation for homogeneous cons with explicit element type. -/
syntax:67 term:68 " ::ᵛ⟨" term "⟩ " term:67 : term


-- @@ L224-225 verbatim
/-- `:+ᵛ⟨α⟩` notation for homogeneous concat with explicit element type. -/
syntax:65 term:66 " :+ᵛ⟨" term "⟩ " term:65 : term


-- @@ L227-228 verbatim
/-- `++ᵛ⟨α⟩` notation for homogeneous append with explicit element type. -/
syntax:65 term:66 " ++ᵛ⟨" term "⟩ " term:65 : term


-- @@ L230-231 expanded
macro_rules
  | `(Fin.vcons (α := $α:term) $a:term $v:term) => `(Fin.vcons (α := $α) $a $v)


-- @@ L233-234 expanded
macro_rules
  | `(Fin.vconcat (α := $α:term) $v:term $a:term) => `(Fin.vconcat (α := $α) $v $a)


-- @@ L236-237 expanded
macro_rules
  | `(Fin.vappend (α := $α:term) $u:term $v:term) => `(Fin.vappend (α := $α) $u $v)


-- @@ L239-241 verbatim
/-- `!v[...]` notation constructs a vector using our custom functions.
Uses `!v[...]` to distinguish from standard `![]`. -/
syntax (name := finVecNotation) "!v[" term,* "]" : term


-- @@ L243-245 verbatim
/-- `!v⟨α⟩[...]` notation constructs a vector with explicit type ascription.
Uses angle brackets to specify the element type, then square brackets for values. -/
syntax (name := finVecNotationWithType) "!v⟨" term "⟩[" term,* "]" : term


-- @@ L247-250 unexpanded
macro_rules
  | `(!v[$term:term, $terms:term,*]) => `((Fin.vcons $term !v[$terms,*]))
  | `(!v[$term:term]) => `((Fin.vcons $term !v[]))
  | `(!v[]) => `(Fin.vempty)


-- @@ L252-255 unexpanded
macro_rules
  | `(!v⟨$α⟩[$term:term, $terms:term,*]) => `(Fin.vcons (α := $α) $term !v⟨$α⟩[$terms,*])
  | `(!v⟨$α⟩[$term:term]) => `(Fin.vcons (α := $α) $term !v⟨$α⟩[])
  | `(!v⟨$α⟩[]) => `((Fin.vempty : Fin 0 → $α))


-- @@ L257-263 unexpanded
/-- Unexpander for the `!v[x, y, ...]` notation. -/
@[app_unexpander Fin.vcons]
meta def vconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !v[$term2, $terms,*]) => `(!v[$term, $term2, $terms,*])
  | `($_ $term !v[$term2]) => `(!v[$term, $term2])
  | `($_ $term !v[]) => `(!v[$term])
  | _ => throw ()


-- @@ L265-269 unexpanded
/-- Unexpander for the `!v[]` notation. -/
@[app_unexpander Fin.vempty]
meta def vemptyUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(!v[])
  | _ => throw ()


-- @@ L271-272 verbatim
@[inherit_doc]
infixr:67 " ::ʰ " => Fin.hcons


-- @@ L274-275 verbatim
@[inherit_doc]
infixl:65 " :+ʰ " => Fin.hconcat


-- @@ L277-278 verbatim
/-- `::ʰ⟨α; β⟩` notation for hcons with explicit type ascriptions -/
syntax:67 term:68 " ::ʰ⟨" term "; " term "⟩ " term:67 : term


-- @@ L280-281 verbatim
/-- `:+ʰ⟨α; β⟩` notation for hconcat with explicit type ascriptions -/
syntax:65 term:66 " :+ʰ⟨" term "; " term "⟩ " term:65 : term


-- @@ L283-284 verbatim
/-- Functorial cons with explicit functor but inferred type families: `::ʰ⦃F⦄`. -/
syntax:67 term:68 " ::ʰ⦃" term "⦄ " term:67 : term


-- @@ L286-287 verbatim
/-- Functorial cons (unary) with explicit types: `::ʰ⦃F⦄⟨α; β⟩`. -/
syntax:67 term:68 " ::ʰ⦃" term "⦄⟨" term "; " term "⟩ " term:67 : term


-- @@ L289-290 verbatim
/-- Functorial cons (binary) with explicit types: `::ʰ⦃F⦄⟨α₁; β₁⟩⟨α₂; β₂⟩`. -/
syntax:67 term:68 " ::ʰ⦃" term "⦄⟨" term "; " term "⟩⟨" term "; " term "⟩ " term:67 : term


-- @@ L292-293 verbatim
@[inherit_doc]
infixr:67 " ::ᵈ " => Fin.dcons


-- @@ L295-296 verbatim
@[inherit_doc]
infixl:65 " :+ᵈ " => Fin.dconcat


-- @@ L298-299 verbatim
/-- `::ᵈ⟨motive⟩` notation for dcons with explicit motive specification -/
syntax:67 term:68 " ::ᵈ⟨" term "⟩ " term:67 : term


-- @@ L301-302 verbatim
/-- `:+ᵈ⟨motive⟩` notation for dconcat with explicit motive specification -/
syntax:65 term:66 " :+ᵈ⟨" term "⟩ " term:65 : term


-- @@ L304-306 verbatim
/-- `!h[...]` notation constructs a heterogeneous tuple using hcons.
For automatic type inference without explicit motive. -/
syntax (name := finHeterogeneousNotation) "!h[" term,* "]" : term


-- @@ L308-310 verbatim
/-- `!h⟨α⟩[...]` notation constructs a heterogeneous tuple with explicit type vector ascription.
Uses angle brackets to specify the type vector, then square brackets for values. -/
syntax (name := finHeterogeneousNotationWithTypeVec) "!h⟨" term "⟩[" term,* "]" : term


-- @@ L312-313 verbatim
/-- `!h⦃F⦄[...]` functorial heterogeneous tuple with explicit functor and implicit type vectors. -/
syntax (name := finFunctorialHeterogeneousNotationShorthand) "!h⦃" term "⦄[" term,* "]" : term


-- @@ L315-317 verbatim
/-- `!d[...]` notation constructs a dependent tuple using our custom dependent functions.
Uses `!d[...]` for dependent tuples with explicit motives. -/
syntax (name := finDependentNotation) "!d[" term,* "]" : term


-- @@ L319-321 verbatim
/-- `!d⟨motive⟩[...]` notation constructs a dependent tuple with explicit motive specification.
Uses angle brackets to specify the motive, then square brackets for values. -/
syntax (name := finDependentNotationWithmotive) "!d⟨" term "⟩[" term,* "]" : term


-- @@ L323-326 unexpanded
macro_rules
  | `(!h[$term:term, $terms:term,*]) => `(Fin.hcons $term !h[$terms,*])
  | `(!h[$term:term]) => `(Fin.hcons $term !h[])
  | `(!h[]) => `((Fin.dempty))


-- @@ L328-332 unexpanded
macro_rules
  | `(!h⟨$typeVec⟩[$term:term, $terms:term,*]) =>
      `(($term : $typeVec 0) ::ʰ !h⟨fun i => $typeVec (Fin.succ i)⟩[$terms,*])
  | `(!h⟨$typeVec⟩[$term:term]) => `(($term : $typeVec 0) ::ʰ !h⟨fun i => $typeVec (Fin.succ i)⟩[])
  | `(!h⟨$typeVec⟩[]) => `((Fin.dempty : (i : Fin 0) → $typeVec i))


-- @@ L334-334 verbatim
/-! Functorial heterogeneous tuple constructors with explicit type vectors -/


-- @@ L336-338 verbatim
/-- Unary functorial: `!h⦃F⦄⟨α⟩[...]` where `α : Fin n → Sort _`. -/
syntax (name := finFunctorialHeterogeneousNotation)
  "!h⦃" term "⦄⟨" term "⟩[" term,* "]" : term


-- @@ L340-342 verbatim
/-- Binary functorial: `!h⦃F⦄⟨α₁⟩⟨α₂⟩[...]` where `α₁, α₂ : Fin n → Sort _`. -/
syntax (name := finFunctorialBinaryHeterogeneousNotation)
  "!h⦃" term "⦄⟨" term "⟩⟨" term "⟩[" term,* "]" : term


-- @@ L344-351 unexpanded
macro_rules
  | `(!h⦃$F⦄⟨$α:term⟩[$x:term, $xs:term,*]) =>
    `(Fin.fcons (F := $F) (α := $α 0) (β := fun i => $α (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α (Fin.succ i)⟩[$xs,*])
  | `(!h⦃$F⦄⟨$α:term⟩[$x:term]) =>
    `(Fin.fcons (F := $F) (α := $α 0) (β := fun i => $α (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α (Fin.succ i)⟩[])
  | `(!h⦃$F⦄⟨$α:term⟩[]) => `((Fin.dempty : (i : Fin 0) → $F ($α i)))


-- @@ L353-365 unexpanded
macro_rules
  | `(!h⦃$F⦄⟨$α₁:term⟩⟨$α₂:term⟩[$x:term, $xs:term,*]) =>
    `(Fin.fcons₂ (F := $F)
        (α₁ := $α₁ 0) (β₁ := fun i => $α₁ (Fin.succ i))
        (α₂ := $α₂ 0) (β₂ := fun i => $α₂ (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α₁ (Fin.succ i)⟩⟨fun i => $α₂ (Fin.succ i)⟩[$xs,*])
  | `(!h⦃$F⦄⟨$α₁:term⟩⟨$α₂:term⟩[$x:term]) =>
    `(Fin.fcons₂ (F := $F)
        (α₁ := $α₁ 0) (β₁ := fun i => $α₁ (Fin.succ i))
        (α₂ := $α₂ 0) (β₂ := fun i => $α₂ (Fin.succ i))
        $x !h⦃$F⦄⟨fun i => $α₁ (Fin.succ i)⟩⟨fun i => $α₂ (Fin.succ i)⟩[])
  | `(!h⦃$F⦄⟨$α₁:term⟩⟨$α₂:term⟩[]) =>
    `((Fin.dempty : (i : Fin 0) → $F ($α₁ i) ($α₂ i)))


-- @@ L367-372 unexpanded
@[app_unexpander Fin.fcons]
meta def fconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a !h⦃$F⦄⟨$α⟩[$b, $bs,*]) => `(!h⦃$F⦄⟨$α⟩[$a, $b, $bs,*])
  | `($_ $a !h⦃$F⦄⟨$α⟩[$b]) => `(!h⦃$F⦄⟨$α⟩[$a, $b])
  | `($_ $a !h⦃$F⦄⟨$α⟩[]) => `(!h⦃$F⦄⟨$α⟩[$a])
  | _ => throw ()


-- @@ L374-379 unexpanded
@[app_unexpander Fin.fcons₂]
meta def fcons₂Unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a !h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$b, $bs,*]) => `(!h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$a, $b, $bs,*])
  | `($_ $a !h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$b]) => `(!h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$a, $b])
  | `($_ $a !h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[]) => `(!h⦃$F⦄⟨$α₁⟩⟨$α₂⟩[$a])
  | _ => throw ()


-- @@ L381-384 unexpanded
macro_rules
  | `(!h⦃$F⦄[$term:term, $terms:term,*]) => `(Fin.fcons (F := $F) $term !h⦃$F⦄[$terms,*])
  | `(!h⦃$F⦄[$term:term]) => `(Fin.fcons (F := $F) $term !h⦃$F⦄[])
  | `(!h⦃$F⦄[]) => `((Fin.dempty : (i : Fin 0) → $F (_ i)))


-- @@ L386-389 unexpanded
macro_rules
  | `(!d[$term:term, $terms:term,*]) => `(Fin.dcons $term !d[$terms,*])
  | `(!d[$term:term]) => `(Fin.dcons $term !d[])
  | `(!d[]) => `(Fin.dempty)


-- @@ L391-395 unexpanded
macro_rules
  | `(!d⟨$motive⟩[$term:term, $terms:term,*]) =>
      `((Fin.dcons (motive := $motive) $term !d⟨fun i => $motive (Fin.succ i)⟩[$terms,*]))
  | `(!d⟨$motive⟩[$term:term]) => `((Fin.dcons (motive := $motive) $term !d[]))
  | `(!d⟨$motive⟩[]) => `((Fin.dempty : (i : Fin 0) → $motive i))


-- @@ L397-398 expanded
macro_rules
  | `(Fin.dcons (motive := $motive:term) $a:term $b:term) => `(Fin.dcons (motive := $motive) $a $b)


-- @@ L400-401 expanded
macro_rules
  | `(Fin.dconcat (motive := $motive:term) $a:term $b:term) =>
    `(Fin.dconcat (motive := $motive) $a $b)


-- @@ L403-404 expanded
macro_rules
  | `(Fin.hcons (α := $α:term) (β := $β:term) $a:term $b:term) =>
    `(Fin.hcons (α := $α) (β := $β) $a $b)


-- @@ L406-411 expanded
macro_rules
  | `(Fin.fcons (F := $F:term) $a:term $b:term) => `(Fin.fcons (F := $F) $a $b)
  | `(Fin.fcons (F := $F:term) (α := $α:term) (β := $β:term) $a:term $b:term) =>
    `(Fin.fcons (F := $F) (α := $α) (β := $β) $a $b)
  |
  `(Fin.fcons₂ (F := $F:term) (α₁ := $α₁:term) (β₁ := $β₁:term) (α₂ := $α₂:term) (β₂ := $β₂:term)
        $a:term $b:term) =>
    `(Fin.fcons₂ (F := $F) (α₁ := $α₁) (β₁ := $β₁) (α₂ := $α₂) (β₂ := $β₂) $a $b)


-- @@ L413-414 expanded
macro_rules
  | `(Fin.hconcat (α := $α:term) (β := $β:term) $a:term $b:term) =>
    `(Fin.hconcat (α := $α) (β := $β) $a $b)


-- @@ L416-416 verbatim
/-! Functorial concat infix forms to match documentation -/

-- @@ L417-417 verbatim
syntax:65 term:66 " :+ʰ⦃" term "⦄ " term:65 : term

-- @@ L418-418 verbatim
syntax:65 term:66 " :+ʰ⦃" term "⦄⟨" term "; " term "⟩ " term:65 : term

-- @@ L419-419 verbatim
syntax:65 term:66 " :+ʰ⦃" term "⦄⟨" term "; " term "⟩⟨" term "; " term "⟩ " term:65 : term


-- @@ L421-426 expanded
macro_rules
  | `(Fin.fconcat (F := $F:term) $u:term $a:term) => `(Fin.fconcat (F := $F) $u $a)
  | `(Fin.fconcat (F := $F:term) (α := $α:term) (β := $β:term) $u:term $a:term) =>
    `(Fin.fconcat (F := $F) (α := $α) (β := $β) $u $a)
  |
  `(Fin.fconcat₂ (F := $F:term) (α₁ := $α₁:term) (β₁ := $β₁:term) (α₂ := $α₂:term) (β₂ := $β₂:term)
        $u:term $a:term) =>
    `(Fin.fconcat₂ (F := $F) (α₁ := $α₁) (β₁ := $β₁) (α₂ := $α₂) (β₂ := $β₂) $u $a)


-- @@ L428-434 unexpanded
/-- Unexpander for the `!h[x, y, ...]` notation using hcons. -/
@[app_unexpander Fin.hcons]
meta def hconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !h[$term2, $terms,*]) => `(!h[$term, $term2, $terms,*])
  | `($_ $term !h[$term2]) => `(!h[$term, $term2])
  | `($_ $term !h[]) => `(!h[$term])
  | _ => throw ()


-- @@ L436-440 unexpanded
/-- Unexpander for the `!h[]` and `!d[]` notation. -/
@[app_unexpander Fin.dempty]
meta def demptyUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(!h[])
  | _ => throw ()


-- @@ L442-448 unexpanded
/-- Unexpander for the `!d[x, y, ...]` notation using dcons with explicit motive. -/
@[app_unexpander Fin.dcons]
meta def dconsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !d[$term2, $terms,*]) => `(!d[$term, $term2, $terms,*])
  | `($_ $term !d[$term2]) => `(!d[$term, $term2])
  | `($_ $term !d[]) => `(!d[$term])
  | _ => throw ()


-- @@ L450-452 verbatim
end Fin

-- Custom append notation with type ascriptions


-- @@ L454-455 verbatim
/-- Homogeneous vector append notation `++ᵛ` -/
infixl:65 " ++ᵛ " => Fin.vappend


-- @@ L457-458 verbatim
/-- Dependent append notation `++ᵈ` -/
infixl:65 " ++ᵈ " => Fin.dappend


-- @@ L460-461 verbatim
/-- Heterogeneous append notation `++ʰ` -/
infixl:65 " ++ʰ " => Fin.happend


-- @@ L463-464 verbatim
/-- Heterogeneous append with explicit type ascriptions: `++ʰ⟨α; β⟩` -/
syntax:65 term:66 " ++ʰ⟨" term "; " term "⟩ " term:65 : term


-- @@ L466-467 verbatim
/-- Dependent append with explicit motive: `++ᵈ⟨motive⟩` -/
syntax:65 term:66 " ++ᵈ⟨" term "⟩ " term:65 : term


-- @@ L469-470 verbatim
/-- Functorial heterogeneous append with explicit functor but inferred types: `++ʰ⦃F⦄`. -/
syntax:65 term:66 " ++ʰ⦃" term "⦄ " term:65 : term


-- @@ L472-473 verbatim
/-- Functorial heterogeneous append with unary functor: `++ʰ⦃F⦄⟨α; β⟩` -/
syntax:65 term:66 " ++ʰ⦃" term "⦄⟨" term "; " term "⟩ " term:65 : term


-- @@ L475-476 verbatim
/-- Functorial heterogeneous append with binary functor: `++ʰ⦃F⦄⟨α₁; β₁⟩⟨α₂; β₂⟩` -/
syntax:65 term:66 " ++ʰ⦃" term "⦄⟨" term "; " term "⟩⟨" term "; " term "⟩ " term:65 : term


-- @@ L478-479 expanded
macro_rules
  | `(Fin.dappend (motive := $motive:term) $a:term $b:term) =>
    `(Fin.dappend (motive := $motive) $a $b)


-- @@ L481-483 expanded
macro_rules
  | `(Fin.happend (α := fun i => $α:term) (β := fun i => $β:term) $a:term $b:term) =>
    `(Fin.happend (α := fun i => $α) (β := fun i => $β) $a $b)


-- @@ L485-486 expanded
macro_rules
  | `(Fin.fappend (F := $F:term) $a:term $b:term) => `(Fin.fappend (F := $F) $a $b)


-- @@ L488-490 expanded
macro_rules
  | `(Fin.fappend (F := $F:term) (α := $α:term) (β := $β:term) $a:term $b:term) =>
    `(Fin.fappend (F := $F) (α := $α) (β := $β) $a $b)


-- @@ L492-496 expanded
macro_rules
  |
  `(Fin.fappend₂ (F := $F:term) (α₁ := $α₁:term) (β₁ := $β₁:term) (α₂ := $α₂:term) (β₂ := $β₂:term)
        $a:term $b:term) =>
    `(Fin.fappend₂ (F := $F) (α₁ := $α₁) (β₁ := $β₁) (α₂ := $α₂) (β₂ := $β₂) $a $b)
      -- End of core notation definitions


-- @@ L498-500 verbatim
section Examples

-- Basic homogeneous vectors work fine

-- @@ L501-503 expanded
example :
    (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) =
      Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty)) :=
  rfl


-- @@ L504-510 expanded
example :
    Fin.vcons (α := ℕ) 1 (Fin.vcons (α := ℕ) 2 (Fin.vcons (α := ℕ) 3 (Fin.vempty : Fin 0 → ℕ))) =
      ((Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) : Fin 3 → ℕ) :=
  rfl


-- @@ L511-511 expanded
def Mymotive : Fin 3 → Type :=
  (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty)))


-- @@ L513-517 expanded
example :
    (Fin.dcons (motive := Mymotive) (1 : ℕ)
        (Fin.dcons (motive := fun i => Mymotive (Fin.succ i)) (true : Bool)
          (Fin.dcons (motive := fun i => (fun i => Mymotive (Fin.succ i)) (Fin.succ i))
            ("hello" : String) Fin.dempty))) =
      (Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) (Fin.dcons ("hello" : String) Fin.dempty)) :
        (i : Fin 3) → Mymotive i) :=
  rfl


-- @@ L518-518 expanded
example :
    Fin.vappend (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)))) :=
  rfl


-- @@ L519-519 expanded
example :
    Fin.vcons (0 : ℕ) (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) =
      (Fin.vcons 0 (Fin.vcons 1 (Fin.vcons 2 Fin.vempty))) :=
  rfl


-- @@ L520-522 expanded
example :
    Fin.vconcat (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) (3 : ℕ) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L523-526 expanded
example :
    Fin.hcons (1 : ℕ) (Fin.dempty : (i : Fin 0) → Fin.vempty i) =
      (Fin.hcons (1 : ℕ) (Fin.dempty) : (i : Fin 1) → (Fin.vcons ℕ Fin.vempty) i) :=
  rfl


-- @@ L527-530 expanded
example :
    Fin.hcons (1 : ℕ) (Fin.hcons (true : Bool) (Fin.hcons ("hello" : String) (Fin.dempty))) =
      Fin.hcons 1
        (Fin.hcons true (Fin.hcons (α := String) (β := Fin.vempty) "hello" (Fin.dempty))) :=
  rfl


-- @@ L531-531 expanded
def MyTypeVec : Fin 3 → Type :=
  (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty)))


-- @@ L533-536 expanded
example :
    (Fin.dcons (motive := MyTypeVec) (1 : ℕ)
        (Fin.dcons (motive := fun i => MyTypeVec (Fin.succ i)) true
          (Fin.dcons (motive := fun i => (fun i => MyTypeVec (Fin.succ i)) (Fin.succ i)) "hello"
            Fin.dempty))) =
      (Fin.hcons 1 (Fin.hcons true (Fin.hcons "hello" (Fin.dempty))) : (i : Fin 3) → MyTypeVec i) :=
  rfl


-- @@ L537-539 expanded
example : (Fin.dempty : (i : Fin 0) → Fin.vempty i) = (Fin.dempty : (i : Fin 0) → Fin.vempty i) :=
  rfl


-- @@ L540-543 expanded
example :
    (Fin.dcons (motive := (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty)))) (1 : ℕ)
        (Fin.dcons (motive := fun i =>
          (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) (Fin.succ i)) (true : Bool)
          (Fin.dcons (motive := fun i =>
            (fun i => (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) (Fin.succ i))
              (Fin.succ i))
            ("hello" : String) Fin.dempty))) =
      Fin.dcons (1 : ℕ) (Fin.dcons true (Fin.dcons "hello" Fin.dempty)) :=
  rfl


-- @@ L544-548 expanded
example :
    let motive : Fin 2 → Type := fun i => if i = 0 then ℕ else Bool
    (Fin.dcons (motive := motive) (1 : ℕ)
        (Fin.dcons (motive := fun i => motive (Fin.succ i)) (true : Bool) Fin.dempty)) =
      (Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) Fin.dempty) : (i : Fin 2) → motive i) :=
  rfl


-- @@ L549-551 verbatim
section FinVecConsTests

-- Basic cons operation

-- @@ L552-554 expanded
example :
    Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty)) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L555-557 expanded
example :
    Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty)) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L558-560 expanded
example :
    Fin.vcons 0 (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) =
      (Fin.vcons 0 (Fin.vcons 1 (Fin.vcons 2 Fin.vempty))) :=
  rfl


-- @@ L561-564 expanded
example :
    let v : Fin 2 → ℕ := (Fin.vcons 1 (Fin.vcons 2 Fin.vempty))
    Fin.vcons 0 v = (Fin.vcons 0 (Fin.vcons 1 (Fin.vcons 2 Fin.vempty))) :=
  rfl


-- @@ L565-565 expanded
example : Fin.vcons 42 Fin.vempty = (Fin.vcons 42 Fin.vempty) :=
  rfl


-- @@ L567-569 verbatim
end FinVecConsTests

-- Test FinVec.concat (:+ᵛ) notation

-- @@ L570-572 verbatim
section FinVecConcatTests

-- Basic concat operation

-- @@ L573-575 expanded
example :
    Fin.vconcat (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) 3 =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L576-578 expanded
example :
    Fin.vconcat (Fin.vconcat (Fin.vcons 1 Fin.vempty) 2) 3 =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L579-581 expanded
example :
    Fin.vconcat (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) 3 =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L582-585 expanded
example :
    let v : Fin 2 → ℕ := (Fin.vcons 1 (Fin.vcons 2 Fin.vempty))
    Fin.vconcat v 3 = (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L586-588 expanded
example : Fin.vconcat Fin.vempty 42 = (Fin.vcons 42 Fin.vempty) :=
  rfl


-- @@ L589-589 expanded
example :
    Fin.vcons 0 (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) =
        (Fin.vcons 0 (Fin.vcons 1 (Fin.vcons 2 Fin.vempty))) ∧
      Fin.vconcat (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) 3 =
        (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  ⟨rfl, rfl⟩


-- @@ L591-593 verbatim
end FinVecConcatTests

-- Test FinTuple.cons (::ʰ) notation

-- @@ L594-596 verbatim
section FinTupleConsTests

-- Basic heterogeneous cons

-- @@ L597-599 expanded
example :
    Fin.hcons (1 : ℕ) (Fin.hcons (α := Bool) (β := Fin.vempty) (true : Bool) (Fin.dempty)) =
      Fin.hcons (1 : ℕ) (Fin.hcons (true : Bool) (Fin.dempty)) :=
  rfl


-- @@ L600-603 expanded
example :
    Fin.hcons (1 : ℕ)
        (Fin.hcons (true : Bool)
          (Fin.hcons (α := _) (β := Fin.vempty) ("hello" : String) (Fin.dempty))) =
      Fin.hcons (1 : ℕ) (Fin.hcons (true : Bool) (Fin.hcons ("hello" : String) (Fin.dempty))) :=
  rfl


-- @@ L604-607 expanded
example :
    Fin.hcons (α := ℕ) (β := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (0 : ℕ)
        (Fin.hcons (1 : ℕ) (Fin.hcons (true : Bool) (Fin.dempty))) =
      Fin.hcons (0 : ℕ) (Fin.hcons (1 : ℕ) (Fin.hcons (true : Bool) (Fin.dempty))) :=
  rfl


-- @@ L608-611 expanded
example :
    Fin.hcons (α := ℕ) (β := Fin.vempty) (42 : ℕ) (Fin.dempty) = Fin.hcons (42 : ℕ) (Fin.dempty) :=
  rfl


-- @@ L612-614 expanded
example :
    let t1 : (i : Fin 2) → (Fin.vcons Bool (Fin.vcons String Fin.vempty)) i :=
      Fin.hcons (true : Bool) (Fin.hcons ("test" : String) (Fin.dempty))
    let result := Fin.hcons (1 : ℕ) t1
    result =
      Fin.hcons (1 : ℕ) (Fin.hcons (true : Bool) (Fin.hcons ("test" : String) (Fin.dempty))) :=
  rfl


-- @@ L616-618 verbatim
end FinTupleConsTests

-- Test FinTuple.concat (:+ʰ) notation

-- @@ L619-621 verbatim
section FinTupleConcatTests

-- Basic heterogeneous concat

-- @@ L622-629 expanded
example :
    Fin.hconcat (α := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (β := String)
        (Fin.hcons (1 : ℕ) (Fin.hcons (true : Bool) (Fin.dempty))) ("hello" : String) =
      Fin.hcons ((1 : ℕ) : (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) 0)
        (Fin.hcons
          ((true : Bool) :
            (fun i => (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) (Fin.succ i)) 0)
          (Fin.hcons
            (("hello" : String) :
              (fun i =>
                  (fun i =>
                      (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) (Fin.succ i))
                    (Fin.succ i))
                0)
            (Fin.dempty :
              (i : Fin 0) →
                (fun i =>
                    (fun i =>
                        (fun i =>
                            (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty)))
                              (Fin.succ i))
                          (Fin.succ i))
                      (Fin.succ i))
                  i))) :=
  rfl


-- @@ L630-633 expanded
example :
    Fin.hconcat (α := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (β := String)
        (Fin.hcons (1 : ℕ) (Fin.hcons (true : Bool) (Fin.dempty))) ("test" : String) =
      Fin.hcons ((1 : ℕ) : (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) 0)
        (Fin.hcons
          ((true : Bool) :
            (fun i => (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) (Fin.succ i)) 0)
          (Fin.hcons
            (("test" : String) :
              (fun i =>
                  (fun i =>
                      (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) (Fin.succ i))
                    (Fin.succ i))
                0)
            (Fin.dempty :
              (i : Fin 0) →
                (fun i =>
                    (fun i =>
                        (fun i =>
                            (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty)))
                              (Fin.succ i))
                          (Fin.succ i))
                      (Fin.succ i))
                  i))) :=
  rfl


-- @@ L634-637 expanded
example :
    Fin.hconcat (Fin.dempty : (i : Fin 0) → Fin.vempty i) (42 : ℕ) =
      Fin.hcons ((42 : ℕ) : (Fin.vcons ℕ Fin.vempty) 0)
        (Fin.dempty : (i : Fin 0) → (fun i => (Fin.vcons ℕ Fin.vempty) (Fin.succ i)) i) :=
  rfl


-- @@ L638-641 expanded
example :
    Fin.hcons (0 : ℕ)
          (Fin.hcons ((1 : ℕ) : (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) 0)
            (Fin.hcons
              ((true : Bool) : (fun i => (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) (Fin.succ i)) 0)
              (Fin.dempty :
                (i : Fin 0) →
                  (fun i =>
                      (fun i => (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) (Fin.succ i))
                        (Fin.succ i))
                    i))) =
        Fin.hcons ((0 : ℕ) : (Fin.vcons ℕ (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) 0)
          (Fin.hcons
            ((1 : ℕ) :
              (fun i => (Fin.vcons ℕ (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (Fin.succ i)) 0)
            (Fin.hcons
              ((true : Bool) :
                (fun i =>
                    (fun i => (Fin.vcons ℕ (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (Fin.succ i))
                      (Fin.succ i))
                  0)
              (Fin.dempty :
                (i : Fin 0) →
                  (fun i =>
                      (fun i =>
                          (fun i =>
                              (Fin.vcons ℕ (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (Fin.succ i))
                            (Fin.succ i))
                        (Fin.succ i))
                    i))) ∧
      Fin.hconcat
          (Fin.hcons ((1 : ℕ) : (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) 0)
            (Fin.hcons
              ((true : Bool) : (fun i => (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) (Fin.succ i)) 0)
              (Fin.dempty :
                (i : Fin 0) →
                  (fun i =>
                      (fun i => (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) (Fin.succ i))
                        (Fin.succ i))
                    i)))
          ("end" : String) =
        Fin.hcons ((1 : ℕ) : (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) 0)
          (Fin.hcons
            ((true : Bool) :
              (fun i => (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) (Fin.succ i))
                0)
            (Fin.hcons
              (("end" : String) :
                (fun i =>
                    (fun i =>
                        (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty))) (Fin.succ i))
                      (Fin.succ i))
                  0)
              (Fin.dempty :
                (i : Fin 0) →
                  (fun i =>
                      (fun i =>
                          (fun i =>
                              (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty)))
                                (Fin.succ i))
                            (Fin.succ i))
                        (Fin.succ i))
                    i))) :=
  ⟨rfl, rfl⟩


-- @@ L643-645 verbatim
end FinTupleConcatTests

-- Test dependent cons (::ᵈ) notation

-- @@ L646-651 verbatim
section FinDependentConsTests

/- Note: The dependent cons notation ::ᵈ requires explicit typing in most cases.
   These examples show the intended usage but are commented due to type inference issues. -/

-- Working example with explicit motive annotation

-- @@ L652-655 expanded
example :
    let motive : Fin 1 → Type := fun _ => ℕ
    Fin.dcons (42 : ℕ) Fin.dempty = (Fin.dcons (motive := motive) (42 : ℕ) Fin.dempty) :=
  rfl


-- @@ L656-660 expanded
example :
    let motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))
    Fin.dcons (motive := motive) (1 : ℕ) (Fin.dcons (true : Bool) Fin.dempty) =
      (Fin.dcons (motive := motive) (1 : ℕ)
        (Fin.dcons (motive := fun i => motive (Fin.succ i)) (true : Bool) Fin.dempty)) :=
  rfl


-- @@ L661-662 expanded
example :
    let motive : Fin 1 → Type := fun _ => ℕ
    Fin.dcons (motive := motive) (42 : ℕ) Fin.dempty =
      (Fin.dcons (motive := motive) (42 : ℕ) Fin.dempty) :=
  rfl


-- @@ L664-666 verbatim
end FinDependentConsTests

-- Test dependent concat (:+ᵈ) notation

-- @@ L667-672 verbatim
section FinDependentConcatTests

/- Note: The dependent concat notation :+ᵈ requires explicit typing in most cases.
   These examples show the intended usage with explicit motive annotation. -/

-- Simple case with explicit type annotation

-- @@ L673-676 expanded
example :
    Fin.dconcat (Fin.dempty : (i : Fin 0) → ℕ) (42 : ℕ) =
      (Fin.dcons (42 : ℕ) Fin.dempty : (i : Fin 1) → ℕ) :=
  rfl


-- @@ L677-680 expanded
example :
    Fin.dconcat (Fin.dcons (1 : ℕ) Fin.dempty : (i : Fin 1) → ℕ) (2 : ℕ) =
      (Fin.dcons (1 : ℕ) (Fin.dcons (2 : ℕ) Fin.dempty) : (i : Fin 2) → ℕ) :=
  rfl


-- @@ L681-683 expanded
example :
    let motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))
    Fin.dconcat (motive := motive) (Fin.dcons (motive := motive ∘ Fin.castSucc) (1 : ℕ) Fin.dempty)
        (true : Bool) =
      (Fin.dcons (motive := motive) (1 : ℕ)
        (Fin.dcons (motive := fun i => motive (Fin.succ i)) (true : Bool) Fin.dempty)) :=
  rfl


-- @@ L685-687 verbatim
end FinDependentConcatTests

-- Test interaction between all notations

-- @@ L688-690 verbatim
section MixedTests

-- FinVec used as type vector for FinTuple

-- @@ L691-694 expanded
example :
    let _typeVec := Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)
    (Fin.dcons (motive := _typeVec) (1 : ℕ)
        (Fin.dcons (motive := fun i => _typeVec (Fin.succ i)) true Fin.dempty)) =
      Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) Fin.dempty) :=
  rfl


-- @@ L695-703 expanded
example :
    let _types := Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)
    let values := Fin.hcons 1 (Fin.hcons true Fin.dempty)
    values =
      ((Fin.dcons (motive := _types) (1 : ℕ)
          (Fin.dcons (motive := fun i => _types (Fin.succ i)) true Fin.dempty)) :
        (i : Fin 2) → _types i) :=
  rfl


-- @@ L704-706 expanded
example :
    let motive := (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String Fin.vempty)))
    ((Fin.dcons (motive := motive) (1 : ℕ)
          (Fin.dcons (motive := fun i => motive (Fin.succ i)) true
            (Fin.dcons (motive := fun i => (fun i => motive (Fin.succ i)) (Fin.succ i)) "hello"
              Fin.dempty))) :
        (i : Fin 3) → motive i) =
      (Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) (Fin.dcons ("hello" : String) Fin.dempty)) :
        (i : Fin 3) → motive i) :=
  rfl


-- @@ L708-708 verbatim
end MixedTests


-- @@ L710-712 expanded
example :
    Fin.vappend (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)))) :=
  rfl


-- @@ L713-713 expanded
example :
    Fin.vappend (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) (Fin.vempty : Fin 0 → ℕ) =
      (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) :=
  rfl


-- @@ L714-716 expanded
example :
    Fin.vappend (Fin.vempty : Fin 0 → ℕ) (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) =
      (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) :=
  rfl


-- @@ L717-719 expanded
example :
    Fin.vappend (Fin.vappend (Fin.vcons 1 Fin.vempty) (Fin.vcons 2 Fin.vempty))
        (Fin.vcons 3 Fin.vempty) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L720-722 expanded
example :
    Fin.vappend (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)))) :=
  rfl


-- @@ L723-730 expanded
example :
    Fin.vappend (Fin.vcons true (Fin.vcons false Fin.vempty)) (Fin.vcons true Fin.vempty) =
      (Fin.vcons true (Fin.vcons false (Fin.vcons true Fin.vempty))) :=
  rfl


-- @@ L731-733 expanded
example :
    Fin.dappend (motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (Fin.dcons (1 : ℕ) Fin.dempty)
        (Fin.dcons true Fin.dempty) =
      (Fin.dcons (motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (1 : ℕ)
        (Fin.dcons (motive := fun i => (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) (Fin.succ i)) true
          Fin.dempty)) :=
  rfl


-- @@ L734-770 expanded
example :
    Fin.dappend (motive :=
        Fin.vappend (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))
          (Fin.vcons String (Fin.vcons Float Fin.vempty)))
        (Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) Fin.dempty))
        (Fin.dcons ("hello" : String) (Fin.dcons (3.14 : Float) Fin.dempty)) =
      Fin.dcons (1 : ℕ)
        (Fin.dcons (true : Bool)
          (Fin.dcons ("hello" : String) (Fin.dcons (3.14 : Float) Fin.dempty))) :=
  rfl


-- @@ L771-776 expanded
example :
    let motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))
    let d1 : (i : Fin 1) → motive (Fin.castAdd 1 i) := Fin.dcons (1 : ℕ) Fin.dempty
    let d2 : (i : Fin 1) → motive (Fin.natAdd 1 i) := Fin.dcons (true : Bool) Fin.dempty
    Fin.dappend d1 d2 =
      (Fin.dcons (motive := motive) (1 : ℕ)
        (Fin.dcons (motive := fun i => motive (Fin.succ i)) (true : Bool) Fin.dempty)) :=
  rfl


-- @@ L777-783 expanded
example :
    let motive : Fin 4 → Type :=
      (Fin.vcons ℕ (Fin.vcons Bool (Fin.vcons String (Fin.vcons Float Fin.vempty))))
    let d1 : (i : Fin 2) → motive (Fin.castAdd 2 i) :=
      Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) Fin.dempty)
    let d2 : (i : Fin 2) → motive (Fin.natAdd 2 i) :=
      Fin.dcons ("hello" : String) (Fin.dcons (3.14 : Float) Fin.dempty)
    Fin.dappend (n := 2) d1 d2 =
      (Fin.dcons (motive := motive) (1 : ℕ)
        (Fin.dcons (motive := fun i => motive (Fin.succ i)) (true : Bool)
          (Fin.dcons (motive := fun i => (fun i => motive (Fin.succ i)) (Fin.succ i))
            ("hello" : String)
            (Fin.dcons (motive := fun i =>
              (fun i => (fun i => motive (Fin.succ i)) (Fin.succ i)) (Fin.succ i)) (3.14 : Float)
              Fin.dempty)))) :=
  rfl


-- @@ L784-807 expanded
example :
    let motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))
    let d1 : (i : Fin 2) → motive (Fin.castAdd 0 i) :=
      Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) Fin.dempty)
    let d2 : (i : Fin 0) → motive (Fin.natAdd 2 i) := Fin.dempty
    Fin.dappend (n := 0) d1 d2 =
      (Fin.dcons (motive := motive) (1 : ℕ)
        (Fin.dcons (motive := fun i => motive (Fin.succ i)) (true : Bool) Fin.dempty)) :=
  rfl


-- @@ L808-820 expanded
example :
    let motive1 : Fin 2 → Type := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))
    let motive2 : Fin 2 → Type := (Fin.vcons String (Fin.vcons Float Fin.vempty))
    let combined_motive : Fin 4 → Type := Fin.vappend motive1 motive2
    let d1 : (i : Fin 2) → combined_motive (Fin.castAdd 2 i) :=
      Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) Fin.dempty)
    let d2 : (i : Fin 2) → combined_motive (Fin.natAdd 2 i) :=
      Fin.dcons ("hello" : String) (Fin.dcons (3.14 : Float) Fin.dempty)
    Fin.dappend (n := 2) d1 d2 =
      (let rhs : (i : Fin 4) → combined_motive i :=
        Fin.dcons (1 : ℕ)
          (Fin.dcons (true : Bool)
            (Fin.dcons ("hello" : String) (Fin.dcons (3.14 : Float) Fin.dempty)))
      rhs) :=
  by ext i;
  fin_cases i <;>
    rfl
      -- Append with different constructions


-- @@ L821-829 expanded
example :
    (Fin.vappend (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) (Fin.vcons 3 Fin.vempty)) =
        (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) ∧
      (Fin.dappend (Fin.dcons (1 : ℕ) Fin.dempty) (Fin.dcons (true : Bool) Fin.dempty) =
          (Fin.dcons (motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (1 : ℕ)
            (Fin.dcons (motive := fun i => (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) (Fin.succ i))
              (true : Bool) Fin.dempty))) ∧
        (let motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))
        let d1 : (i : Fin 1) → motive (Fin.castAdd 1 i) := Fin.dcons (1 : ℕ) Fin.dempty
        let d2 : (i : Fin 1) → motive (Fin.natAdd 1 i) := Fin.dcons (true : Bool) Fin.dempty
        Fin.dappend (n := 1) d1 d2 =
          (Fin.dcons (motive := motive) (1 : ℕ)
            (Fin.dcons (motive := fun i => motive (Fin.succ i)) (true : Bool) Fin.dempty))) :=
  ⟨rfl, rfl, rfl⟩
    -- Test the new notation


-- @@ L830-832 verbatim
section NewNotationTests

-- These should work with rfl!

-- @@ L833-833 expanded
example : Fin.vcons 1 (Fin.vcons 2 Fin.vempty) = (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) :=
  rfl


-- @@ L835-835 expanded
example :
    Fin.tail (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) =
      (Fin.vcons 2 (Fin.vcons 3 Fin.vempty)) :=
  rfl


-- @@ L837-837 expanded
example :
    Fin.vconcat (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) 3 =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L839-841 expanded
example :
    Fin.vappend (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)))) :=
  rfl


-- @@ L842-842 expanded
example :
    Fin.dcons 1 (Fin.dcons 2 Fin.dempty) =
      (Fin.dcons (motive := fun _ => ℕ) 1
        (Fin.dcons (motive := fun i => (fun _ => ℕ) (Fin.succ i)) 2 Fin.dempty)) :=
  rfl


-- @@ L844-846 expanded
example :
    Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) Fin.dempty) =
      (Fin.dcons (motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (1 : ℕ)
        (Fin.dcons (motive := fun i => (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) (Fin.succ i))
          (true : Bool) Fin.dempty)) :=
  rfl


-- @@ L847-850 expanded
example :
    let motive := (Fin.vcons ℕ Fin.vempty)
    Fin.dcons (motive := motive) (1 : ℕ) Fin.dempty =
      (Fin.dcons (motive := motive) (1 : ℕ) Fin.dempty) :=
  rfl


-- @@ L851-853 expanded
example :
    let motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))
    Fin.dconcat (motive := motive) (Fin.dcons (motive := motive ∘ Fin.castSucc) (1 : ℕ) Fin.dempty)
        (true : Bool) =
      (Fin.dcons (motive := motive) (1 : ℕ)
        (Fin.dcons (motive := fun i => motive (Fin.succ i)) (true : Bool) Fin.dempty)) :=
  rfl


-- @@ L855-858 expanded
example :
    Fin.vappend (Fin.vcons (true, Nat) Fin.vempty)
        (Fin.vappend (Fin.vempty : Fin 0 → Bool × Type)
          (Fin.vappend (Fin.vcons (false, Int) Fin.vempty) (Fin.vempty : Fin 0 → Bool × Type))) =
      (Fin.vcons (true, Nat) (Fin.vcons (false, Int) Fin.vempty)) :=
  rfl


-- @@ L860-863 expanded
example :
    Fin.vappend (Fin.vappend (Fin.vcons (true, Nat) Fin.vempty) (Fin.vcons (false, Int) Fin.vempty))
        (Fin.vcons (false, Int) Fin.vempty) =
      (Fin.vcons (true, Nat) (Fin.vcons (false, Int) (Fin.vcons (false, Int) Fin.vempty))) :=
  rfl


-- @@ L864-867 expanded
example :
    Fin.vappend
        (Fin.take 2 (by omega) (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)))))
        (Fin.drop 2 (by omega) (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty))))) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)))) :=
  rfl


-- @@ L868-870 expanded
example :
    Fin.tail
        (Fin.vappend (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty)))
          (Fin.vcons 4 Fin.vempty)) =
      (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty))) :=
  rfl


-- @@ L871-873 expanded
example :
    Fin.init (Fin.vconcat (Fin.vcons Nat (Fin.vcons Int Fin.vempty)) Bool) =
      (Fin.vcons Nat (Fin.vcons Int Fin.vempty)) :=
  by
  dsimp [Fin.init, Fin.vconcat, Fin.vcons, Fin.vcons]
  ext i; fin_cases i <;> rfl


-- @@ L875-875 expanded
example :
    Fin.vconcat (Fin.init (Fin.vcons Nat (Fin.vcons Int (Fin.vcons Unit Fin.vempty)))) Bool =
      (Fin.vcons Nat (Fin.vcons Int (Fin.vcons Bool Fin.vempty))) :=
  by rfl


-- @@ L877-880 verbatim
example {v : Fin 3 → ℕ} : Fin.vconcat (Fin.init v) (v (Fin.last 2)) = v := by
  ext i; fin_cases i <;> rfl

-- Multiple operations compose cleanly

-- @@ L881-881 expanded
example :
    Fin.tail
        (Fin.vcons 0
          (Fin.vappend (Fin.vcons 1 (Fin.vcons 2 Fin.vempty))
            (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)))) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)))) :=
  rfl


-- @@ L883-886 expanded
/-- Test that our new notation gives the same result as the old one (extensionally) -/
example : (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) = ![1, 2, 3] := by ext i;
  fin_cases i <;>
    rfl
      -- Test that concat notation works with rfl


-- @@ L887-889 expanded
example :
    Fin.vconcat (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) 3 =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L890-892 expanded
example :
    Fin.vappend (Fin.vconcat (Fin.vcons 0 (Fin.vcons 1 Fin.vempty)) 2)
        (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)) =
      (Fin.vcons 0 (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty))))) :=
  rfl


-- @@ L893-896 expanded
example :
    Fin.hconcat
        (Fin.dcons (motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (1 : ℕ)
          (Fin.dcons (motive := fun i => (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) (Fin.succ i))
            (true : Bool) Fin.dempty))
        ("hello" : String) =
      Fin.dcons (1 : ℕ) (Fin.dcons (true : Bool) (Fin.dcons ("hello" : String) Fin.dempty)) :=
  rfl


-- @@ L897-902 expanded
example :
    (Fin.vconcat (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) 3 =
        (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty)))) ∧
      (Fin.hconcat (Fin.dcons (motive := (Fin.vcons ℕ Fin.vempty)) (1 : ℕ) Fin.dempty)
            (true : Bool) =
          (Fin.dcons (motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty))) (1 : ℕ)
            (Fin.dcons (motive := fun i => (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) (Fin.succ i))
              (true : Bool) Fin.dempty))) ∧
        (Fin.hconcat (α := (Fin.vcons ℕ Fin.vempty)) (β := ℕ) (Fin.dcons (1 : ℕ) Fin.dempty)
            (2 : ℕ) =
          (Fin.dcons (motive := (Fin.vcons ℕ (Fin.vcons ℕ Fin.vempty))) (1 : ℕ)
            (Fin.dcons (motive := fun i => (Fin.vcons ℕ (Fin.vcons ℕ Fin.vempty)) (Fin.succ i))
              (2 : ℕ) Fin.dempty))) :=
  ⟨rfl, rfl, rfl⟩
    -- Test dependent vector functions for definitional equality


-- @@ L903-905 verbatim
section DependentVectorTests

-- Test that the ++ᵈ notation is properly defined

-- @@ L906-908 expanded
example :
    Fin.dappend (motive := (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)))
        (Fin.dcons (42 : ℕ) Fin.dempty) (Fin.dcons (true : Bool) Fin.dempty) =
      Fin.dcons (42 : ℕ) (Fin.dcons (true : Bool) Fin.dempty) :=
  rfl


-- @@ L909-909 expanded
example : (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) 0 = ℕ :=
  rfl


-- @@ L911-913 expanded
example : (Fin.vcons ℕ (Fin.vcons Bool Fin.vempty)) 1 = Bool :=
  rfl


-- @@ L914-914 expanded
example : (Fin.vappend (Fin.vcons ℕ Fin.vempty) (Fin.vcons Bool Fin.vempty)) 0 = ℕ :=
  rfl


-- @@ L916-918 expanded
example : (Fin.vappend (Fin.vcons ℕ Fin.vempty) (Fin.vcons Bool Fin.vempty)) 1 = Bool :=
  rfl


-- @@ L919-919 expanded
example : Fin.vconcat (Fin.vcons ℕ Fin.vempty) Bool 0 = ℕ :=
  rfl


-- @@ L921-923 expanded
example : Fin.vconcat (Fin.vcons ℕ Fin.vempty) Bool 1 = Bool :=
  rfl


-- @@ L924-924 expanded
example :
    Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty)) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L926-926 expanded
example :
    Fin.vconcat (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) 3 =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 Fin.vempty))) :=
  rfl


-- @@ L928-930 expanded
example :
    Fin.vappend (Fin.vcons 1 (Fin.vcons 2 Fin.vempty)) (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)) =
      (Fin.vcons 1 (Fin.vcons 2 (Fin.vcons 3 (Fin.vcons 4 Fin.vempty)))) :=
  rfl


-- @@ L931-933 expanded
example :
    Fin.vcons ℕ (Fin.vcons Bool (fun _ : Fin 0 => Empty)) = fun i : Fin 2 =>
      if i = 0 then ℕ else Bool :=
  by ext i; fin_cases i <;> rfl


-- @@ L935-935 verbatim
end DependentVectorTests


-- @@ L937-937 verbatim
end NewNotationTests


-- @@ L939-939 verbatim
end Examples
