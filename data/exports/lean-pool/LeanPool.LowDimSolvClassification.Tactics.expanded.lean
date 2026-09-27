/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, the LieLean team
-/
module

public meta import Lean.Meta.Tactic.NormCast
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Order.Group.Nat


-- @@ L17-23 verbatim
/-!
# LeanPool.LowDimSolvClassification.Tactics

The reflected Lie expressions retain exposed definitions so the kernel can check proofs
produced by the tactics. The metaprogramming implementation is compiled without exporting
its definition bodies to importing modules.
-/


-- @@ L25-25 verbatim
public section


-- @@ L27-27 verbatim
open Lean hiding Module

-- @@ L28-28 verbatim
open Meta Elab Qq Mathlib.Tactic List


-- @@ L30-33 verbatim
/-- Pair-or-single carrier used by the Lie-algebra atom store: each atom is either a single
expression or a pair of expressions tracked together. -/
@[expose, implicit_reducible]
def V (M : Type*) := Sum M (M × M)


-- @@ L35-35 verbatim
meta section


-- @@ L37-37 verbatim
namespace AtomD


-- @@ L39-42 verbatim
/-- State of the Lie-algebra atom monad: the running list of atoms collected so far. -/
structure State where
  /-- Distinct scalar atoms and bracket pairs, in their order of discovery. -/
  atoms : Array (V Expr) := #[]


-- @@ L44-44 verbatim
end AtomD


-- @@ L46-47 verbatim
/-- The Lie-algebra atom monad: `MetaM` with state tracking the atoms encountered. -/
abbrev AtomD := StateRefT AtomD.State MetaM


-- @@ L49-49 verbatim
namespace AtomD


-- @@ L51-54 verbatim
/-- Run an `AtomD` computation starting from the empty atom state. -/
def run {α : Type} (m : AtomD α) :
    MetaM α :=
  m.run' {}


-- @@ L56-67 verbatim
/-- Find an existing atom up to definitional equality, or append a new one. -/
def addAtomSimple (e : Expr) : AtomD (Nat × Bool × Expr) := do
  let c ← get
  match e with
  | e₁ =>
    for h : i in [:c.atoms.size] do
      match c.atoms[i] with
      | Sum.inl j =>
        if ← withTransparency .instances <| isDefEq e₁ j then
          return (i, true, j)
      | _ => continue
    modifyGet fun c ↦ ((c.atoms.size, true, e₁), { c with atoms := c.atoms.push (Sum.inl e₁) })

-- @@ L68-84 verbatim
/-- Intern a bracket pair, recording whether it matches the stored orientation. -/
def addAtomDouble (e₁ e₂ : Expr) : AtomD (Nat × Bool × (Expr × Expr)) := do
  let c ← get
  let e : Expr × Expr := ⟨ e₁, e₂ ⟩
  match e with
  | ⟨ e₁, e₂ ⟩ =>
    for h : i in [:c.atoms.size] do
      match c.atoms[i] with
      | Sum.inr ⟨j₁, j₂⟩ =>
        if ← withTransparency .instances (isDefEq e₁ j₁) then
          if ← withTransparency .instances (isDefEq e₂ j₂) then
            return (i, true, ⟨j₁, j₂⟩)
        if ← withTransparency .instances (isDefEq e₂ j₁) then
          if ← withTransparency .instances (isDefEq e₁ j₂) then
            return (i, false, ⟨j₁, j₂⟩)
      | _ => continue
    modifyGet fun c ↦ ((c.atoms.size, true, ⟨e₁,e₂⟩), { c with atoms := c.atoms.push (Sum.inr e) })


-- @@ L86-91 verbatim
open Qq in
/-- Intern a quoted atom and retain its definitional equality with the stored expression. -/
def addAtomQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    AtomD (Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (n, _, e') ← AtomD.addAtomSimple e
  return (n, ⟨e', ⟨⟩⟩)


-- @@ L93-102 verbatim
/-- Intern a quoted bracket pair, retaining the equalities for its chosen orientation. -/
def addAtomDoubleQ {u : Level} {α : Q(Type u)} (e₁ e₂ : Q($α)) :
    AtomD (Nat × Sum {e' : Q($α) × Q($α) // $e₁ =Q $(e'.2) ∧ $e₂ =Q $(e'.1)}
        {e' : Q($α) × Q($α) // $e₁ =Q $(e'.1) ∧ $e₂ =Q $(e'.2)}) := do
  let (n, b, e₁', e₂') ← AtomD.addAtomDouble e₁ e₂
  match b with
  | false =>
    return (n, Sum.inl ⟨⟨e₁',e₂'⟩, ⟨⟨⟩, ⟨⟩⟩⟩)
  | true =>
    return (n, Sum.inr ⟨⟨e₁',e₂'⟩, ⟨⟨⟩, ⟨⟩⟩⟩)

-- @@ L103-103 verbatim
end AtomD


-- @@ L105-105 verbatim
end


-- @@ L107-107 verbatim
namespace Mathlib.Tactic.LieSolver


-- @@ L109-112 verbatim
/-- Interpret an atom as an element or as the bracket of two elements. -/
@[expose]
def v {M : Type*} [LieRing M] (x : V M) :=
  Sum.elim (fun m ↦ m) (fun ⟨ m₁ , m₂ ⟩ ↦ ⁅ m₁ , m₂ ⁆) x


-- @@ L114-116 verbatim
/-- A Lie expression represented as a sum of scalar multiples of atoms. -/
@[expose, implicit_reducible]
def NF (R : Type*) (M : Type*) := List (R × V M)


-- @@ L118-118 verbatim
namespace NF

-- @@ L119-119 verbatim
variable {S : Type*} {R : Type*} {M : Type*}


-- @@ L121-123 verbatim
/-- Prepend a scalar multiple of an atom to a reflected Lie expression. -/
@[expose, match_pattern]
def cons (p : R × V M) (l : NF R M) : NF R M := p :: l


-- @@ L125-126 verbatim
/-- Constructor notation for reflected Lie expressions. -/
infixl:100 " ::ᵣ " => cons


-- @@ L128-131 verbatim
/-- Evaluate a reflected Lie expression by summing its scalar multiples of atoms. -/
@[expose]
def eval [SMul R M] [LieRing M] (l : NF R M) : M :=
  (l.map (fun (⟨r, x⟩ : R × V M) ↦ r • v x)).sum


-- @@ L133-136 expanded
@[simp]
theorem eval_cons [SMul R M] [LieRing M] (p : R × V M) (l : NF R M) :
    (cons p l).eval = p.1 • v p.2 + l.eval :=
  by
  unfold eval cons
  simp_all


-- @@ L138-139 verbatim
theorem atom_eq_eval [LieRing M] (x : M) : x = NF.eval [(1,
  Sum.inl x)] := by simp [eval, v]

-- @@ L140-144 expanded
theorem atom_eq_evalD [LieRing M] (x y : M) : ⁅x, y⁆ = NF.eval (cons (1, Sum.inr ⟨x, y⟩) []) :=
  by
  simp only [eval, v]
  dsimp!
  simp_all


-- @@ L145-149 expanded
theorem atom_eq_evalD_skew [LieRing M] (x y : M) :
    ⁅x, y⁆ = NF.eval (cons (-1, Sum.inr ⟨y, x⟩) []) :=
  by
  simp only [eval, v]
  dsimp!
  simp_all


-- @@ L151-152 verbatim
variable (M) in
theorem zero_eq_eval [LieRing M] : (0:M) = NF.eval (R := ℕ) (M := M) [] := rfl


-- @@ L154-157 expanded
theorem add_eq_eval₁ [SMul R M] [LieRing M] (a₁ : R × V M) {a₂ : R × V M} {l₁ l₂ l : NF R M}
    (h : l₁.eval + (cons a₂ l₂).eval = l.eval) :
    (cons a₁ l₁).eval + (cons a₂ l₂).eval = (cons a₁ l).eval := by
  simp only [eval_cons, ← h, add_assoc]


-- @@ L159-166 expanded
theorem add_eq_eval₂ [Semiring R] [LieRing M] [Module R M] (r₁ r₂ : R) (x : V M) {l₁ l₂ l : NF R M}
    (h : l₁.eval + l₂.eval = l.eval) :
    (cons (r₁, x) l₁).eval + (cons (r₂, x) l₂).eval = (cons (r₁ + r₂, x) l).eval :=
  by
  simp only [← h, eval_cons, add_smul, add_assoc]
  congr! 1
  simp only [← add_assoc]
  congr! 1
  rw [add_comm]


-- @@ L168-175 expanded
theorem add_eq_eval₃ [Semiring R] [LieRing M] [Module R M] {a₁ : R × V M} (a₂ : R × V M)
    {l₁ l₂ l : NF R M} (h : (cons a₁ l₁).eval + l₂.eval = l.eval) :
    (cons a₁ l₁).eval + (cons a₂ l₂).eval = (cons a₂ l).eval :=
  by
  simp only [eval_cons, ← h]
  nth_rw 4 [add_comm]
  simp only [add_assoc]
  congr! 2
  rw [add_comm]


-- @@ L177-183 verbatim
theorem add_eq_eval {R₁ R₂ : Type*} [LieRing M] [Semiring R] [Module R M]
    [Semiring R₁]
    [Module R₁ M] [Semiring R₂] [Module R₂ M] {l₁ l₂ l : NF R M} {l₁' : NF R₁ M} {l₂' : NF R₂ M}
    {x₁ x₂ : M} (hx₁ : x₁ = l₁'.eval) (hx₂ : x₂ = l₂'.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval + l₂.eval = l.eval) :
    x₁ + x₂ = l.eval := by
  rw [hx₁, hx₂, ← h₁, ← h₂, h]


-- @@ L185-188 expanded
theorem sub_eq_eval₁ [SMul R M] [LieRing M] (a₁ : R × V M) {a₂ : R × V M} {l₁ l₂ l : NF R M}
    (h : l₁.eval - (cons a₂ l₂).eval = l.eval) :
    (cons a₁ l₁).eval - (cons a₂ l₂).eval = (cons a₁ l).eval := by
  simp only [eval_cons, ← h, sub_eq_add_neg, add_assoc]


-- @@ L190-197 expanded
theorem sub_eq_eval₂ [Ring R] [LieRing M] [Module R M] (r₁ r₂ : R) (x : V M) {l₁ l₂ l : NF R M}
    (h : l₁.eval - l₂.eval = l.eval) :
    (cons (r₁, x) l₁).eval - (cons (r₂, x) l₂).eval = (cons (r₁ - r₂, x) l).eval :=
  by
  simp only [← h, eval_cons, sub_eq_add_neg, neg_add, add_smul, neg_smul, add_assoc]
  congr! 1
  simp only [← add_assoc]
  congr! 1
  rw [add_comm]


-- @@ L199-204 expanded
theorem sub_eq_eval₃ [Ring R] [LieRing M] [Module R M] {a₁ : R × V M} (a₂ : R × V M)
    {l₁ l₂ l : NF R M} (h : (cons a₁ l₁).eval - l₂.eval = l.eval) :
    (cons a₁ l₁).eval - (cons a₂ l₂).eval = (cons (-a₂.1, a₂.2) l).eval :=
  by
  simp only [eval_cons, neg_smul, neg_add, sub_eq_add_neg, ← h, ← add_assoc]
  congr! 1
  rw [add_comm, add_assoc]


-- @@ L206-213 verbatim
theorem sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} [LieRing M] [Ring R] [Module R M] [Semiring R₁]
    [Module R₁ M] [Semiring R₂] [Module R₂ M] [Semiring S₁] [Module S₁ M] [Semiring S₂]
    [Module S₂ M] {l₁ l₂ l : NF R M} {l₁' : NF R₁ M} {l₂' : NF R₂ M} {l₁'' : NF S₁ M}
    {l₂'' : NF S₂ M} {x₁ x₂ : M} (hx₁ : x₁ = l₁''.eval) (hx₂ : x₂ = l₂''.eval)
    (h₁' : l₁'.eval = l₁''.eval) (h₂' : l₂'.eval = l₂''.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval - l₂.eval = l.eval) :
    x₁ - x₂ = l.eval := by
  rw [hx₁, hx₂, ← h₁', ← h₂', ← h₁, ← h₂, h]


-- @@ L215-216 verbatim
instance [Neg R] : Neg (NF R M) where
  neg l := l.map fun (a, x) ↦ (-a, x)


-- @@ L218-222 verbatim
private lemma sum_map_neg_eq_neg_sum {M : Type*} [AddCommGroup M] (l : List M) :
    (l.map (fun x ↦ -x)).sum = -l.sum := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [ih, add_comm]


-- @@ L224-233 verbatim
theorem eval_neg [Ring R] [LieRing M] [Module R M] (l : NF R M) : (-l).eval = - l.eval := by
  change NF.eval (l.map (fun (a, x) ↦ (-a, x))) = -l.eval
  unfold NF.eval
  rw [List.map_map]
  have heq : (fun (x : R × V M) ↦ x.1 • v x.2) ∘ (fun x : R × V M ↦ (-x.1, x.2)) =
      fun x ↦ -(x.1 • v x.2) := by funext x; simp [neg_smul]
  rw [heq, show (fun x ↦ -((x : R × V M).1 • v x.2)) =
        (fun (z : M) ↦ -z) ∘ (fun (x : R × V M) ↦ x.1 • v x.2) from rfl,
      ← List.map_map]
  rw [sum_map_neg_eq_neg_sum]


-- @@ L235-237 verbatim
theorem zero_sub_eq_eval [Ring R] [LieRing M] [Module R M] (l : NF R M) :
    0 - l.eval = (-l).eval := by
  simp [eval_neg]


-- @@ L239-242 verbatim
theorem neg_eq_eval [LieRing M] [Semiring S] [Module S M] [Ring R] [Module R M] {l : NF R M}
    {l₀ : NF S M} (hl : l.eval = l₀.eval) {x : M} (h : x = l₀.eval) :
    - x = (-l).eval := by
  rw [h, ← hl, eval_neg]


-- @@ L244-245 verbatim
instance [Mul R] : SMul R (NF R M) where
  smul r l := l.map fun (a, x) ↦ (r * a, x)


-- @@ L247-248 verbatim
@[simp] theorem smul_apply [Mul R] (r : R) (l : NF R M) : r • l = l.map fun (a, x) ↦ (r * a, x) :=
  rfl


-- @@ L250-256 verbatim
theorem eval_smul [LieRing M] [Semiring R] [Module R M] {l : NF R M} {x : M} (h : x = l.eval)
    (r : R) : (r • l).eval = r • x := by
  unfold NF.eval at h ⊢
  simp only [h, smul_sum, map_map, NF.smul_apply]
  congr
  ext p
  simp [mul_smul]


-- @@ L258-263 verbatim
theorem smul_eq_eval {R₀ : Type*} [LieRing M] [Semiring R] [Module R M] [Semiring R₀]
    [Module R₀ M] [Semiring S] [Module S M] {l : NF R M} {l₀ : NF R₀ M} {s : S} {r : R}
    {x : M} (hx : x = l₀.eval) (hl : l.eval = l₀.eval) (hs : r • x = s • x) :
    s • x = (r • l).eval := by
  rw [← hs, hx, ← hl, eval_smul]
  rfl


-- @@ L265-268 expanded
theorem eq_cons_cons [LieRing M] [SMul R M] {r₁ r₂ : R} (m : V M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂)
    (h2 : l₁.eval = l₂.eval) : (cons (r₁, m) l₁).eval = (cons (r₂, m) l₂).eval := by simp_all


-- @@ L270-273 expanded
theorem eq_cons_const [LieRing M] [Semiring R] [Module R M] {r : R} (m : V M) {n : V M} {l : NF R M}
    (h1 : r = 0) (h2 : l.eval = v n) : (cons (r, m) l).eval = v n := by simp_all


-- @@ L275-279 expanded
theorem eq_const_cons [LieRing M] [Semiring R] [Module R M] {r : R} (m : V M) {n : V M} {l : NF R M}
    (h1 : 0 = r) (h2 : v n = l.eval) : v n = (cons (r, m) l).eval :=
  by
  simp only [NF.eval, NF.cons] at *
  simp [← h1, h2]


-- @@ L281-286 verbatim
theorem eq_of_eval_eq_eval {R₁ R₂ : Type*} [LieRing M] [Semiring R] [Module R M] [Semiring R₁]
    [Module R₁ M] [Semiring R₂] [Module R₂ M] {l₁ l₂ : NF R M} {l₁' : NF R₁ M} {l₂' : NF R₂ M}
    {x₁ x₂ : M} (hx₁ : x₁ = l₁'.eval) (hx₂ : x₂ = l₂'.eval) (h₁ : l₁.eval = l₁'.eval)
    (h₂ : l₂.eval = l₂'.eval) (h : l₁.eval = l₂.eval) :
    x₁ = x₂ := by
  rw [hx₁, hx₂, ← h₁, ← h₂, h]


-- @@ L288-288 verbatim
variable (R)


-- @@ L290-293 verbatim
/-- Extend the scalar ring of a reflected Lie expression through an algebra map. -/
@[expose]
def algebraMap [CommSemiring S] [Semiring R] [Algebra S R] (l : NF S M) : NF R M :=
  l.map (fun ⟨s, x⟩ ↦ (Algebra.algebraMap S R s, x))


-- @@ L295-302 verbatim
theorem eval_algebraMap [CommSemiring S] [Semiring R] [Algebra S R] [LieRing M]
    [SMul S M]
    [MulAction R M] [IsScalarTower S R M] (l : NF S M) :
    (l.algebraMap R).eval = l.eval := by
  simp only [NF.eval, algebraMap, map_map]
  congr
  ext
  simp [IsScalarTower.algebraMap_smul]


-- @@ L304-304 verbatim
end NF


-- @@ L306-306 verbatim
meta section


-- @@ L308-308 verbatim
variable {u v : Level}


-- @@ L310-311 verbatim
/-- Quoted scalar-atom pairs with identifiers used to order and combine equal atoms. -/
abbrev qNF (R : Q(Type u)) (M : Q(Type v)) := List ((Q($R) × Q(V $M)) × ℕ)


-- @@ L313-313 verbatim
namespace qNF


-- @@ L315-315 verbatim
variable {M : Q(Type v)} {R : Q(Type u)}


-- @@ L317-321 unexpanded
/-- Quote a normal form, discarding the atom identifiers used during normalization. -/
def toNF (l : qNF R M) : Q(NF $R $M) :=
  let l' : List Q($R × V $M) := (l.map Prod.fst).map (fun (a, x) ↦ q(($a, $x)))
  let qt : List Q($R × V $M) → Q(List ($R × V $M)) := List.rec q([]) (fun e _ l ↦ q($e ::ᵣ $l))
  qt l'


-- @@ L323-326 verbatim
/-- Apply a quoted function to every coefficient of a normal form. -/
def onScalar {u₁ u₂ : Level} {R₁ : Q(Type u₁)} {R₂ : Q(Type u₂)} (l : qNF R₁ M) (f : Q($R₁ → $R₂)) :
    qNF R₂ M :=
  l.map fun ((a, x), k) ↦ ((q($f $a), x), k)


-- @@ L328-338 verbatim
/-- Merge two normal forms ordered by atom identifier, adding matching coefficients. -/
def add (iR : Q(Semiring $R)) : qNF R M → qNF R M → qNF R M
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) :: add iR t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((q($a₁ + $a₂), x₁), k₁) :: add iR t₁ t₂
    else
      ((a₂, x₂), k₂) :: add iR (((a₁, x₁), k₁) :: t₁) t₂


-- @@ L340-356 verbatim
/-- Construct the proof that merging normal forms computes their sum. -/
def mkAddProof {iR : Q(Semiring $R)} {iMM : Q(LieRing $M)} (iRM : Q(Module $R $M))
    (l₁ l₂ : qNF R M) :
    Q(NF.eval $(l₁.toNF) + NF.eval $(l₂.toNF) = NF.eval $((qNF.add iR l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(zero_add (NF.eval $(l.toNF))):)
  | l, [] => (q(add_zero (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      let pf := mkAddProof iRM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.add_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkAddProof iRM t₁ t₂
      (q(NF.add_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkAddProof iRM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.add_eq_eval₃ ($a₂, $x₂) $pf):)


-- @@ L358-368 verbatim
/-- Merge two normal forms ordered by atom identifier, subtracting matching coefficients. -/
def sub (iR : Q(Ring $R)) : qNF R M → qNF R M → qNF R M
  | [], l => l.onScalar q(Neg.neg)
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      ((a₁, x₁), k₁) :: sub iR t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      ((q($a₁ - $a₂), x₁), k₁) :: sub iR t₁ t₂
    else
      ((q(-$a₂), x₂), k₂) :: sub iR (((a₁, x₁), k₁) :: t₁) t₂


-- @@ L370-386 verbatim
/-- Construct the proof that subtracting normal forms computes their difference. -/
def mkSubProof (iR : Q(Ring $R)) (iMM : Q(LieRing $M)) (iRM : Q(Module $R $M))
    (l₁ l₂ : qNF R M) :
    Q(NF.eval $(l₁.toNF) - NF.eval $(l₂.toNF) = NF.eval $((qNF.sub iR l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(NF.zero_sub_eq_eval $(l.toNF)):)
  | l, [] => (q(sub_zero (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ < k₂ then
      let pf := mkSubProof iR iMM iRM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.sub_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkSubProof iR iMM iRM t₁ t₂
      (q(NF.sub_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkSubProof iR iMM iRM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.sub_eq_eval₃ ($a₂, $x₂) $pf):)


-- @@ L388-390 verbatim
variable {iMM : Q(LieRing $M)}
  {u₁ : Level} {R₁ : Q(Type u₁)} {iR₁ : Q(Semiring $R₁)} (iRM₁ : Q(@Module $R₁ $M $iR₁ _))
  {u₂ : Level} {R₂ : Q(Type u₂)} (iR₂ : Q(Semiring $R₂)) (iRM₂ : Q(@Module $R₂ $M $iR₂ _))


-- @@ L392-420 verbatim
/-- Move two normal forms to a common scalar ring, retaining proofs of their values. -/
def matchRings (l₁ : qNF R₁ M) (l₂ : qNF R₂ M) (r : Q($R₂)) (x : Q($M)) :
    MetaM <| Σ u : Level, Σ R : Q(Type u), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR _),
      (Σ l₁' : qNF R M, Q(NF.eval $(l₁'.toNF) = NF.eval $(l₁.toNF)))
      × (Σ l₂' : qNF R M, Q(NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)))
      × (Σ r' : Q($R), Q($r' • $x = $r • $x)) := do
  if ← withReducible <| isDefEq R₁ R₂ then
    pure ⟨u₁, R₁, iR₁, iRM₁, ⟨l₁, q(rfl)⟩, ⟨l₂, (q(@rfl _ (NF.eval $(l₂.toNF))):)⟩,
      r, (q(@rfl _ ($r • $x)):)⟩
  else try
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
    assumeInstancesCommute
    let l₁' : qNF R₂ M := l₁.onScalar q(algebraMap $R₁ $R₂)
    pure ⟨u₂, R₂, iR₂, iRM₂, ⟨l₁', (q(NF.eval_algebraMap $R₂ $(l₁.toNF)):)⟩, ⟨l₂, q(rfl)⟩,
      r, q(rfl)⟩
  catch _ => try
    let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
    assumeInstancesCommute
    let l₂' : qNF R₁ M := l₂.onScalar q(algebraMap $R₂ $R₁)
    let r' : Q($R₁) := q(algebraMap $R₂ $R₁ $r)
    pure ⟨u₁, R₁, iR₁, iRM₁, ⟨l₁, q(rfl)⟩, ⟨l₂', (q(NF.eval_algebraMap $R₁ $(l₂.toNF)):)⟩,
      r', (q(IsScalarTower.algebraMap_smul $R₁ $r $x):)⟩
  catch _ =>
    throwError ("match_scalars_lie failed: {R₁} is not an {R₂}-algebra and {R₂} is not " ++
      "an {R₁}-algebra")


-- @@ L422-422 verbatim
end qNF


-- @@ L424-424 verbatim
variable {M : Q(Type v)}


-- @@ L426-427 verbatim
/-- Recursion budget for parsing expressions and comparing their coefficients. -/
def parseFuel : Nat := 4096


-- @@ L429-494 verbatim
/-- Normalize a quoted Lie expression with bounded recursion and prove its value. -/
def parseAux (fuel : Nat) (iMM : Q(LieRing $M)) (x : Q($M)) :
    AtomD (Σ u : Level, Σ R : Q(Type u), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR _),
      Σ l : qNF R M, Q($x = NF.eval $(l.toNF))) := do
  match fuel with
  | 0 => throwError "match_scalars_lie: ran out of fuel while parsing {x}"
  | fuel + 1 =>
    match x with
    | ~q($x₁ + $x₂) =>
      let ⟨_, _, _, iRM₁, l₁', pf₁'⟩ ← parseAux fuel iMM x₁
      let ⟨_, _, _, iRM₂, l₂', pf₂'⟩ ← parseAux fuel iMM x₂
      assumeInstancesCommute
      let ⟨u, R, iR, iRM, ⟨l₁, pf₁⟩, ⟨l₂, pf₂⟩, _⟩ ← qNF.matchRings iRM₁ _ iRM₂ l₁' l₂' q(0) q(0)
      let pf := qNF.mkAddProof iRM l₁ l₂
      pure ⟨u, R, iR, iRM, qNF.add iR l₁ l₂, (q(NF.add_eq_eval $pf₁' $pf₂' $pf₁ $pf₂ $pf):)⟩
    | ~q(@HSub.hSub _ _ _ (@instHSub _ $iM') $x₁ $x₂) =>
      let ⟨_, _, _, iRM₁, l₁'', pf₁''⟩ ← parseAux fuel iMM x₁
      let ⟨_, _, _, iRM₂, l₂'', pf₂''⟩ ← parseAux fuel iMM x₂
      let iZ := q(Int.instSemiring)
      let iMZ ← synthInstanceQ q(Module ℤ $M)
      let ⟨_, _, _, iRM₁', ⟨l₁', pf₁'⟩, _, _⟩ ← qNF.matchRings iRM₁ iZ iMZ l₁'' [] q(0) q(0)
      let ⟨_, _, _, iRM₂', ⟨l₂', pf₂'⟩, _, _⟩ ← qNF.matchRings iRM₂ iZ iMZ l₂'' [] q(0) q(0)
      let ⟨u, R, iR, iRM, ⟨l₁, pf₁⟩, ⟨l₂, pf₂⟩, _⟩ ← qNF.matchRings iRM₁' _ iRM₂' l₁' l₂' q(0) q(0)
      let iR' ← synthInstanceQ q(Ring $R)
      let iMM' ← synthInstanceQ q(LieRing $M)
      assumeInstancesCommute
      let pf := qNF.mkSubProof iR' iMM' iRM l₁ l₂
      pure ⟨u, R, iR, iRM, qNF.sub iR' l₁ l₂,
        q(NF.sub_eq_eval $pf₁'' $pf₂'' $pf₁' $pf₂' $pf₁ $pf₂ $pf)⟩
    | ~q(@Neg.neg _ $iM' $y) =>
      let ⟨u₀, _, _, iRM₀, l₀, pf₀⟩ ← parseAux fuel iMM y
      let _i ← synthInstanceQ q(AddCommGroup $M)
      let iZ := q(Int.instSemiring)
      let iMZ ← synthInstanceQ q(Module ℤ $M)
      let ⟨u, R, iR, iRM, ⟨l, pf⟩, _, _⟩ ← qNF.matchRings iRM₀ iZ iMZ l₀ [] q(0) q(0)
      let _i' ← synthInstanceQ q(Ring $R)
      assumeInstancesCommute
      pure ⟨u, R, iR, iRM, l.onScalar q(Neg.neg), (q(NF.neg_eq_eval $pf $pf₀):)⟩
    | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s₀ $y) =>
      let ⟨_, _, _, iRM₀, l₀, pf₀⟩ ← parseAux fuel iMM y
      let i₁ ← synthInstanceQ q(Semiring $S)
      let i₂ ← synthInstanceQ q(Module $S $M)
      assumeInstancesCommute
      let ⟨u, R, iR, iRM, ⟨l, pf_l⟩, _, ⟨s, pf_r⟩⟩ ← qNF.matchRings iRM₀ i₁ i₂ l₀ [] s₀ y
      pure ⟨u, R, iR, iRM, l.onScalar q(HMul.hMul $s), (q(NF.smul_eq_eval $pf₀ $pf_l $pf_r):)⟩
    | ~q(0) =>
      pure ⟨0, q(Nat), q(Nat.instSemiring), q(AddCommMonoid.toNatModule), [], q(NF.zero_eq_eval $M)⟩
    | ~q(@Bracket.bracket _ _ «$iMM».toBracket $x₁ $x₂) =>
      let (k, vmmm) ← AtomD.addAtomDoubleQ (q($x₁):Q($M)) (q($x₂):Q($M))
      match vmmm with
      | Sum.inl ⟨⟨x₁',x₂'⟩, ⟨_,_⟩⟩ =>
        let iMZ ← synthInstanceQ q(Module ℤ $M)
        assumeInstancesCommute
        pure ⟨0, q(Int), q(Int.instSemiring), q($iMZ), [((q(-1), q(Sum.inr ⟨$x₁', $x₂'⟩)), k)],
          q(NF.atom_eq_evalD_skew $x₁ $x₂)⟩
      | Sum.inr ⟨⟨x₁',x₂'⟩, ⟨_,_⟩⟩ =>
        assumeInstancesCommute
        pure ⟨0, q(Nat), q(Nat.instSemiring), q(AddCommMonoid.toNatModule), [((q(1),
          q(Sum.inr ⟨$x₁', $x₂'⟩)), k)],
          q(NF.atom_eq_evalD $x₁ $x₂)⟩
    | _ =>
      let (k, ⟨x', _⟩) ← AtomD.addAtomQ x
      assumeInstancesCommute
      pure ⟨0, q(Nat), q(Nat.instSemiring), q(AddCommMonoid.toNatModule), [((q(1), q(Sum.inl $x')),
        k)],
        q(NF.atom_eq_eval $x')⟩


-- @@ L496-500 verbatim
/-- Normalize a quoted Lie expression using the standard recursion budget. -/
def parse (iMM : Q(LieRing $M)) (x : Q($M)) :
    AtomD (Σ u : Level, Σ R : Q(Type u), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR _),
      Σ l : qNF R M, Q($x = NF.eval $(l.toNF))) :=
  parseAux parseFuel iMM x


-- @@ L502-503 verbatim
/-- Section boundary marker (keeps the proof-size linter happy). -/
private theorem _marker_after_parse : True := trivial


-- @@ L505-537 verbatim
/-- Reduce equality of normal forms to coefficient equalities with bounded recursion. -/
def reduceCoefficientwiseAux (fuel : Nat) {R : Q(Type u)} {_ : Q(LieRing $M)} {_ : Q(Semiring $R)}
    (iRM : Q(Module $R $M)) (l₁ l₂ : qNF R M) :
    MetaM (List MVarId × Q(v (Sum.inl (NF.eval $(l₁.toNF))) =
      v (Sum.inl (NF.eval $(l₂.toNF))))) := do
  match fuel with
  | 0 => throwError "match_scalars_lie: ran out of fuel in reduceCoefficientwise"
  | fuel + 1 =>
    match l₁, l₂ with
    | [], [] =>
      let pf : Q(NF.eval $(l₁.toNF) = NF.eval $(l₁.toNF)) := q(rfl)
      pure ([], pf)
    | [], ((a, x), _) :: L =>
      let mvar : Q((0:$R) = $a) ← mkFreshExprMVar q((0:$R) = $a)
      let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM [] L
      pure (mvar.mvarId! :: mvars, (q(NF.eq_const_cons $x $mvar $pf):))
    | ((a, x), _) :: L, [] =>
      let mvar : Q($a = (0:$R)) ← mkFreshExprMVar q($a = (0:$R))
      let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM L []
      pure (mvar.mvarId! :: mvars, (q(NF.eq_cons_const $x $mvar $pf):))
    | ((a₁, x₁), k₁) :: L₁, ((a₂, x₂), k₂) :: L₂ =>
      if k₁ < k₂ then
        let mvar : Q($a₁ = (0:$R)) ← mkFreshExprMVar q($a₁ = (0:$R))
        let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM L₁ (((a₂, x₂), k₂) :: L₂)
        pure (mvar.mvarId! :: mvars, (q(NF.eq_cons_const $x₁ $mvar $pf):))
      else if k₁ = k₂ then
        let mvar : Q($a₁ = $a₂) ← mkFreshExprMVar q($a₁ = $a₂)
        let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM L₁ L₂
        pure (mvar.mvarId! :: mvars, (q(NF.eq_cons_cons $x₁ $mvar $pf):))
      else
        let mvar : Q((0:$R) = $a₂) ← mkFreshExprMVar q((0:$R) = $a₂)
        let (mvars, pf) ← reduceCoefficientwiseAux fuel iRM (((a₁, x₁), k₁) :: L₁) L₂
        pure (mvar.mvarId! :: mvars, (q(NF.eq_const_cons $x₂ $mvar $pf):))


-- @@ L539-544 verbatim
/-- Produce coefficient goals and a proof that solving them equates the normal forms. -/
def reduceCoefficientwise {R : Q(Type u)} {_ : Q(LieRing $M)} {_ : Q(Semiring $R)}
    (iRM : Q(Module $R $M)) (l₁ l₂ : qNF R M) :
    MetaM (List MVarId × Q(v (Sum.inl (NF.eval $(l₁.toNF))) =
      v (Sum.inl (NF.eval $(l₂.toNF))))) :=
  reduceCoefficientwiseAux parseFuel iRM l₁ l₂


-- @@ L546-574 verbatim
/-- Normalize both sides of an equality and replace it with coefficient goals. -/
def matchScalarsAux (g : MVarId) : AtomD (List MVarId) := do
  let eqData ← do
    match (← g.getType').eq? with
    | some e => pure e
    | none => throwError "goal {← g.getType} is not an equality"
  let .sort v₀ ← whnf (← inferType eqData.1) | unreachable!
  let some v := v₀.dec | unreachable!
  let ((M : Q(Type v)), (lhs : Q($M)), (rhs :Q($M))) := eqData
  let iMM ← synthInstanceQ q(LieRing $M)
  let e₁ ← parse iMM lhs
  have u₁ : Level := e₁.fst
  have R₁ : Q(Type u₁) := e₁.snd.fst
  have _iR₁ : Q(Semiring.{u₁} $R₁) := e₁.snd.snd.fst
  let iRM₁ ← synthInstanceQ q(Module $R₁ $M)
  assumeInstancesCommute
  have l₁ : qNF R₁ M := e₁.snd.snd.snd.snd.fst
  let pf₁ : Q($lhs = NF.eval $(l₁.toNF)) := e₁.snd.snd.snd.snd.snd
  let e₂ ← parse iMM rhs
  have u₂ : Level := e₂.fst
  have R₂ : Q(Type u₂) := e₂.snd.fst
  have _iR₂ : Q(Semiring.{u₂} $R₂) := e₂.snd.snd.fst
  let iRM₂ ← synthInstanceQ q(Module $R₂ $M)
  have l₂ : qNF R₂ M := e₂.snd.snd.snd.snd.fst
  let pf₂ : Q($rhs = NF.eval $(l₂.toNF)) := e₂.snd.snd.snd.snd.snd
  let ⟨_, _, _, iRM, ⟨l₁', pf₁'⟩, ⟨l₂', pf₂'⟩, _⟩ ← qNF.matchRings iRM₁ _ iRM₂ l₁ l₂ q(0) q(0)
  let (mvars, pf) ← reduceCoefficientwise iRM l₁' l₂'
  g.assign q(NF.eq_of_eval_eq_eval $pf₁ $pf₂ $pf₁' $pf₂' $pf)
  return mvars


-- @@ L576-577 verbatim
/-- Algebra-map identities used to simplify natural, integer, and rational coefficients. -/
def algebraMapThms : Array Name := #[``eq_natCast, ``eq_intCast, ``eq_ratCast]


-- @@ L579-588 verbatim
/-- Simplify casts and algebra maps in a generated coefficient goal. -/
def postprocess (mvarId : MVarId) : MetaM MVarId := do
  let mut thms : SimpTheorems := ← NormCast.pushCastExt.getTheorems
  for thm in algebraMapThms do
    let ⟨levelParams, _, proof⟩ ← abstractMVars (mkConst thm)
    thms ← thms.add (.stx (← mkFreshId) Syntax.missing) levelParams proof
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (some r, _) ← simpTarget mvarId ctx (simprocs := #[]) |
    throwError "internal error in match_scalars_lie tactic: postprocessing should not close goals"
  return r


-- @@ L590-593 verbatim
/-- Reduce a Lie equality to coefficient goals and simplify their scalar expressions. -/
def matchScalars (g : MVarId) : MetaM (List MVarId) := do
  let mvars ← AtomD.run (matchScalarsAux g)
  mvars.mapM postprocess


-- @@ L595-597 verbatim
/-- `match_scalars_lie`: turn a Lie-algebra goal into a collection of scalar-coefficient goals
that can be discharged by `ring`-like tactics. -/
elab "match_scalars_lie" : tactic => Tactic.liftMetaTactic matchScalars


-- @@ L599-603 verbatim
/-- `module_lie`: finishing tactic that reduces a Lie-algebra equality to scalar equalities
and discharges each with `ring`. -/
elab "module_lie" : tactic => Tactic.liftMetaFinishingTactic fun g ↦ do
  let l ← matchScalars g
  discard <| l.mapM fun mvar ↦ AtomM.run .instances (Ring.proveEq mvar)


-- @@ L605-605 verbatim
end


-- @@ L607-607 verbatim
end Mathlib.Tactic.LieSolver


-- @@ L609-613 verbatim
/-- `simplify_lie`: unfold Lie-bracket bilinearity and reduce the goal to scalar equalities
using `match_scalars_lie`, then attempt to close each by `ring`. -/
macro (name := tacticSimplifyLie) "simplify_lie" : tactic => `(tactic| {
  try simp only [lie_add, add_lie, lie_smul, smul_lie, lie_neg, neg_lie, sub_lie, lie_sub]
  match_scalars_lie <;> try ring})


-- @@ L615-615 verbatim
variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]


-- @@ L617-620 expanded
theorem lie_solver3_example (v₁ v₂ v₃ : L) :
    4 • ⁅v₁, v₂⁆ + v₂ + ⁅v₁, v₃⁆ + ⁅v₂, v₁⁆ - ⁅-2 • v₁, v₂⁆ =
      ⁅v₁, (7 : K) • v₂⁆ + 2 • v₂ + ⁅v₂ + v₂, v₁⁆ - v₂ + ⁅(-1 : K) • v₃, v₁⁆ :=
  by
  { try simp only [lie_add, add_lie, lie_smul, smul_lie, lie_neg, neg_lie, sub_lie, lie_sub]
    match_scalars_lie <;> try ring
  }


-- @@ L622-625 expanded
theorem lie_solver3_example' (v₁ v₂ : L) : 4 • ⁅v₁, v₂⁆ + 4 • ⁅v₂, v₁⁆ = 0 := by
  { try simp only [lie_add, add_lie, lie_smul, smul_lie, lie_neg, neg_lie, sub_lie, lie_sub]
    match_scalars_lie <;> try ring
  }

