import Mathlib.Tactic


-- @@ L3-30 verbatim
/-!
# Analysis I, Section 2.1: The Peano Axioms

This file is a translation of Section 2.1 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing
so.

Main constructions and results of this section:

- Definition of the "Chapter 2" natural numbers, `Chapter2.Nat`,abbreviated as {name}`Nat` within
  the Chapter2 namespace. (In the book, the natural numbers are treated in a purely axiomatic
  fashion, as a type that obeys the Peano axioms; but here we take advantage of Lean's native
  inductive types to explicitly construct a version of the natural numbers that obey those axioms.
  One could also proceed more axiomatically, as is done in Section 3 for set theory: see the
  epilogue to this chapter.)
- Establishment of the Peano axioms for `Chapter2.Nat`.
- Recursive definitions for `Chapter2.Nat`.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" in the next few sections for pedagogical purposes.

-/


-- @@ L32-32 verbatim
namespace Chapter2


-- @@ L34-42 verbatim
/--
  Assumption 2.6 (Existence of natural numbers). Here we use an explicit construction of the
  natural numbers (using an inductive type). For a more axiomatic approach, see the epilogue to
  this chapter.
-/
inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr, DecidableEq  -- this allows `decide` to work on `Nat`


-- @@ L44-45 verbatim
/-- Axiom 2.1 (0 is a natural number) -/
instance Nat.instZero : Zero Nat := ⟨ zero ⟩

-- @@ L46-46 verbatim
#check (0:Nat)


-- @@ L48-49 verbatim
/-- Axiom 2.2 (Successor of a natural number is a natural number) -/
postfix:100 "++" => Nat.succ

-- @@ L50-50 expanded
#check (fun n ↦ Nat.succ n)


-- @@ L53-57 expanded
/-- Definition 2.1.3 (Definition of the numerals 0, 1, 2, etc.). Note: to avoid ambiguity, one may
  need to use explicit casts such as {lean}`(0:Nat)`, {lean}`(1:Nat)`, etc. to refer to this
  chapter's version of the natural numbers.  -/
instance Nat.instOfNat {n : _root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ Nat.succ n) n


-- @@ L59-59 verbatim
instance Nat.instOne : One Nat := ⟨ 1 ⟩

-- @@ L60-60 expanded
lemma Nat.zero_succ : Nat.succ 0 = 1 := by rfl


-- @@ L61-61 verbatim
#check (1:Nat)


-- @@ L63-63 expanded
lemma Nat.one_succ : Nat.succ 1 = 2 := by rfl


-- @@ L64-64 verbatim
#check (2:Nat)


-- @@ L66-67 expanded
/-- Proposition 2.1.4 (3 is a natural number) -/
lemma Nat.two_succ : Nat.succ 2 = 3 := by rfl


-- @@ L68-68 verbatim
#check (3:Nat)


-- @@ L70-76 expanded
/-- Axiom 2.3 (0 is not the successor of any natural number).
  Compare with Lean's {name}`Nat.succ_ne_zero`.
-/
theorem Nat.succ_ne (n : Nat) : Nat.succ n ≠ 0 :=
  by
  by_contra h
  injection h


-- @@ L78-83 expanded
/-- Proposition 2.1.6 (4 is not equal to zero) -/
theorem Nat.four_ne : (4 : Nat) ≠ 0 := by
  -- By definition, 4 = 3++.
  
  change
    Nat.succ 3 ≠
      0
        -- By axiom 2.3, 3++ is not zero.
        
  exact succ_ne _


-- @@ L85-90 expanded
/-- Axiom 2.4 (Different natural numbers have different successors).
  Compare with Mathlib's {name}`Nat.succ_inj`.
-/
theorem Nat.succ_cancel {n m : Nat} (hnm : Nat.succ n = Nat.succ m) : n = m := by injection hnm


-- @@ L92-99 expanded
/-- Axiom 2.4 (Different natural numbers have different successors).
  Compare with Mathlib's {name}`Nat.succ_ne_succ`.
-/
theorem Nat.succ_ne_succ (n m : Nat) : n ≠ m → Nat.succ n ≠ Nat.succ m :=
  by
  intro h
  contrapose! h
  exact succ_cancel h


-- @@ L101-110 expanded
/-- Proposition 2.1.8 (6 is not equal to 2) -/
theorem Nat.six_ne_two : (6 : Nat) ≠ 2 := by
  -- this proof is written to follow the structure of the original text.
  
  by_contra h
  change Nat.succ 5 = Nat.succ 1 at h
  apply succ_cancel at h
  change Nat.succ 4 = Nat.succ 0 at h
  apply succ_cancel at h
  have := four_ne
  contradiction


-- @@ L112-114 verbatim
/-- One can also prove this sort of result by the {tactic}`decide` tactic -/
theorem Nat.six_ne_two' : (6:Nat) ≠ 2 := by
  decide


-- @@ L116-123 expanded
/-- Axiom 2.5 (Principle of mathematical induction). The {tactic}`induction` (or
  {tactic}`induction'`) tactic in Mathlib serves as a substitute for this axiom.  -/
theorem Nat.induction (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (Nat.succ n)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact hind _ ih


-- @@ L125-131 expanded
/-- Recursion. Analogous to the inbuilt Mathlib method {name}`Nat.rec` associated to
  the Mathlib natural numbers
-/
abbrev Nat.recurse (f : Nat → Nat → Nat) (c : Nat) : Nat → Nat := fun n ↦
  match n with
  | 0 => c
  | Nat.succ n => f n (recurse f c n)


-- @@ L133-134 verbatim
/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's {name}`Nat.rec_zero`. -/
theorem Nat.recurse_zero (f: Nat → Nat → Nat) (c: Nat) : Nat.recurse f c 0 = c := by rfl


-- @@ L136-138 expanded
/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's {name}`Nat.rec_add_one`. -/
theorem Nat.recurse_succ (f : Nat → Nat → Nat) (c : Nat) (n : Nat) :
    recurse f c (Nat.succ n) = f n (recurse f c n) := by rfl


-- @@ L140-154 expanded
/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.eq_recurse (f : Nat → Nat → Nat) (c : Nat) (a : Nat → Nat) :
    (a 0 = c ∧ ∀ n, a (Nat.succ n) = f n (a n)) ↔ a = recurse f c :=
  by
  constructor
  . intro
      ⟨h0, hsucc⟩
        -- this proof is written to follow the structure of the original text.
        
    apply funext; apply induction
    . exact h0
    intro n hn
    rw [hsucc n, recurse_succ, hn]
  intro h
  rw [h]
  constructor -- could also use `split_ands` or `and_intros` here
    
  . exact recurse_zero _ _
  exact recurse_succ _ _


-- @@ L157-165 expanded
/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.recurse_uniq (f : Nat → Nat → Nat) (c : Nat) :
    ∃! (a : Nat → Nat), a 0 = c ∧ ∀ n, a (Nat.succ n) = f n (a n) :=
  by
  apply ExistsUnique.intro (recurse f c)
  . constructor -- could also use `split_ands` or `and_intros` here
      
    . exact recurse_zero _ _
    . exact recurse_succ _ _
  intro a
  exact (eq_recurse _ _ a).mp


-- @@ L167-167 verbatim
end Chapter2
