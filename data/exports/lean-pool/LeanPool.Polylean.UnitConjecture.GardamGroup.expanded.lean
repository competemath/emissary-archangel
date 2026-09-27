/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import LeanPool.Polylean.UnitConjecture.MetabelianGroup
public import LeanPool.Polylean.UnitConjecture.AddFreeGroup
import LeanPool.Polylean.UnitConjecture.Tactics.AesopRuleSets
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF


-- @@ L20-27 verbatim
/-!
## The construction of the group `P`

We construct the group `P` (the *Promislow* or *Hantzsche–Wendt* group) as a Metabelian group.

This is done via the cocycle construction, using the explicit action and cocycle described in
Section 3.1 of Giles Gardam's paper (https: //arxiv.org/abs/2102.11818).
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace LeanPool.Polylean



-- @@ L34-38 verbatim
/-!
### The components of the group `P`
The group `P` is constructed as a Metabelian group with kernel `K := ℤ³` and
quotient `Q := ℤ/2 × ℤ/2`.
-/


-- @@ L40-40 verbatim
/-! The *kernel* group -/


-- @@ L42-44 verbatim
/-- The *kernel* group - `ℤ³`, the free Abelian group on three generators. -/
@[aesop safe (rule_sets := [P])]
abbrev K := ℤ × ℤ × ℤ


-- @@ L46-46 verbatim
instance KGrp : AddCommGroup K := inferInstance


-- @@ L48-50 verbatim
/-- Equality of endomorphisms of `K` is decidable, as `K` is a free group with
basis `Unit ⊕ Unit ⊕ Unit`. -/
instance : DecidableEq (K →+ K) := decideHomsEqual (X := Unit ⊕ Unit ⊕ Unit)



-- @@ L53-53 verbatim
/-! The *quotient* group -/


-- @@ L55-56 verbatim
/-- The *quotient* group - `ℤ/2 × ℤ/2`, the Klein Four group. -/
abbrev Q := Fin 2 × Fin 2


-- @@ L58-58 verbatim
instance QGrp : AddCommGroup Q := inferInstance


-- @@ L60-62 verbatim
/-!
### The group elements
-/


-- @@ L64-64 verbatim
namespace K


-- @@ L66-66 verbatim
/-! The generators of the free Abelian group `K`. -/


-- @@ L68-70 verbatim
/-- The first generator of `K`. -/
@[aesop norm unfold (rule_sets := [P])]
abbrev x : K := (1, 0, 0)

-- @@ L71-73 verbatim
/-- The second generator of `K`. -/
@[aesop norm unfold (rule_sets := [P])]
abbrev y : K := (0, 1, 0)

-- @@ L74-76 verbatim
/-- The third generator of `K`. -/
@[aesop norm unfold (rule_sets := [P])]
abbrev z : K := (0, 0, 1)


-- @@ L78-78 verbatim
end K



-- @@ L81-81 verbatim
namespace Q


-- @@ L83-83 verbatim
/-! The elements of the Klein Four group `Q`. -/


-- @@ L85-87 verbatim
/-- The identity element of `Q`. -/
@[match_pattern]
def e : Q := (⟨0, by decide⟩, ⟨0, by decide⟩)

-- @@ L88-90 verbatim
/-- The first generator of `Q`. -/
@[match_pattern]
def a : Q := (⟨1, by decide⟩, ⟨0, by decide⟩)

-- @@ L91-93 verbatim
/-- The second generator of `Q`. -/
@[match_pattern]
def b : Q := (⟨0, by decide⟩, ⟨1, by decide⟩)

-- @@ L94-96 verbatim
/-- The product of the first two generators of `Q`. -/
@[match_pattern]
def c : Q := (⟨1, by decide⟩, ⟨1, by decide⟩)


-- @@ L98-98 verbatim
end Q



-- @@ L101-104 verbatim
/-!
### The action of `Q` on `K` by automorphisms
The action of the group `Q` on the kernel `K` by automorphisms required for constructing `P`.
-/


-- @@ L106-108 verbatim
/-- An abbreviation for the negation homomorphism on commutative groups. -/
@[aesop norm unfold (rule_sets := [P])]
abbrev neg (α : Type _) [SubtractionCommMonoid α] := negAddMonoidHom (α := α)


-- @@ L110-110 verbatim
attribute [aesop norm unfold (rule_sets := [P])] negAddMonoidHom


-- @@ L112-113 verbatim
/-- A temporary notation for easily describing products of additive monoid homomorphisms. -/
local infixr: 100 " × " => AddMonoidHom.prodMap


-- @@ L115-123 verbatim
/-- The action of `Q` on `K` by automorphisms.
The action can be given a component-wise description in terms of `id` and `neg`, the
identity and negation homomorphisms. -/
@[aesop norm unfold (rule_sets := [P]), reducible]
def action : Q → (K →+ K)
  | .e => .id ℤ × .id ℤ × .id ℤ
  | .a => .id ℤ × neg ℤ × neg ℤ
  | .b => neg ℤ × .id ℤ × neg ℤ
  | .c => neg ℤ × neg ℤ × .id ℤ


-- @@ L125-130 verbatim
/-- A verification that the above action is indeed an action by automorphisms.
  This is done automatically with the machinery of decidable equality of homomorphisms
  on free groups. -/
instance : AutAction action :=
  { id_action := rfl
    compatibility := by decide }


-- @@ L132-132 verbatim
/-! ### The cocycle -/


-- @@ L134-146 verbatim
open K Q in
/-- The cocycle in the construction of `P`. -/
@[aesop norm unfold (rule_sets := [P]), reducible]
def cocycle : Q → Q → K
  | a , a => x
  | a , c => x
  | b , b => y
  | c , b => -y
  | c , c => z
  | b , c => -x + -z
  | c , a => -y + z
  | b , a => -x + y + -z
  | _ , _ => 0


-- @@ L148-154 verbatim
/-- A verification that the `cocycle` function indeed satisfies the cocycle condition.
  This check is performed fully automatically using previously defined decision procedures. -/
instance PCocycle : Cocycle cocycle :=
  { α := action
    autAct := inferInstance
    cocycle_zero := rfl
    cocycle_condition := by decide }


-- @@ L156-159 verbatim
/-!
### The construction of `P`
The construction of the group `P` as a Metabelian group from the given action and cocycle.
-/


-- @@ L161-163 verbatim
/-- the group `P` constructed via the cocycle construction -/
@[aesop norm unfold (rule_sets := [P])]
def P := K × Q


-- @@ L165-165 verbatim
namespace P


-- @@ L167-167 verbatim
instance (priority := high) PGrp : Group P := MetabelianGroup.metabelianGroup cocycle


-- @@ L169-170 verbatim
/-- Multiplication for `P` coming from its metabelian group structure. -/
scoped instance (priority := high) : HMul (K × Q) (K × Q) (K × Q) := ⟨PGrp.mul⟩

-- @@ L171-172 verbatim
/-- Multiplication for `P` coming from its metabelian group structure. -/
scoped instance (priority := high) : Mul (K × Q) := ⟨PGrp.mul⟩

-- @@ L173-175 verbatim
@[reducible]
instance instPow : Pow (K × Q) ℕ :=
  ⟨fun p n => PGrp.toMonoid.npow n p⟩



-- @@ L178-178 verbatim
instance : DecidableEq P := inferInstanceAs <| DecidableEq (K × Q)


-- @@ L180-184 verbatim
/-- A confirmation that multiplication in `P` is as expected from the Metabelian
group structure. -/
@[aesop norm (rule_sets := [P]), simp]
theorem mul (k k' : K) (q q' : Q) :
    (k, q) * (k', q') = (k + action q k' + cocycle q q', q + q') := rfl


-- @@ L186-187 verbatim
@[aesop norm (rule_sets := [P])]
theorem one : (1 : P) = ((0, 0, 0), Q.e) := rfl


-- @@ L189-210 verbatim
/-- Powers of kernel elements remain in the kernel. -/
theorem kernel_pow (k : K) (n : ℕ) : ((k, Q.e) : P) ^ n = (n • k, Q.e) := by
  induction n with
  | zero =>
      unfold HPow.hPow instHPow Pow.pow instPow
      simp
      rfl
  | succ n ih =>
      unfold HPow.hPow instHPow Pow.pow instPow
      change PGrp.toMonoid.npow (n + 1) ((k, Q.e) : P) = ((n + 1) • k, Q.e)
      have step :
          PGrp.toMonoid.npow (n + 1) ((k, Q.e) : P) =
            PGrp.toMonoid.mul (PGrp.toMonoid.npow n ((k, Q.e) : P)) ((k, Q.e) : P) :=
        PGrp.toMonoid.npow_succ n ((k, Q.e) : P)
      apply step.trans
      change ((k, Q.e) : P) ^ n * (k, Q.e) = ((n + 1) • k, Q.e)
      rw [ih, P.mul]
      simp only [AddMonoidHom.coe_prodMap, AddMonoidHom.coe_id, Prod.map_id, id_eq,
        Prod.mk.injEq, add_eq_left]
      constructor
      · ext <;> simp [cocycle] <;> ring_nf
      · rfl


-- @@ L212-212 verbatim
end P


-- @@ L214-214 verbatim
end LeanPool.Polylean
