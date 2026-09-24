/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Lattice.Nat
public import Batteries.Data.Vector.Basic


-- @@ L16-25 verbatim
/-!
# Computable monomials

Monomials of the form `X₀ᵃ * X₁ᵇ * ... * Xₖᶻ`. These are represented as vectors of natural numbers,
where each element corresponds to the exponent of a variable.

## Main definitions

* `CPoly.CMvMonomial n`: The type of monomials in `n` variables, implemented as `Vector ℕ n`.
-/


-- @@ L27-27 verbatim
@[expose] public section

-- @@ L28-28 verbatim
namespace CPoly


-- @@ L30-34 verbatim
/--
  Monomial in `n` variables.
  - `#v[e₀, e₁, e₂]` denotes X₀^e₀ * X₁^e₁ * X₂^e₂
-/
@[grind =, implicit_reducible]

-- @@ L35-35 verbatim
def CMvMonomial (n : ℕ) : Type := Vector ℕ n


-- @@ L37-37 verbatim
syntax "#m[" withoutPosition(term,*,?) "]" : term


-- @@ L39-41 verbatim
open Lean in
macro_rules
  | `(#m[$elems,*]) => `(#v[$elems,*])


-- @@ L43-43 verbatim
variable {n : ℕ}


-- @@ L45-50 verbatim
instance : Repr (CMvMonomial n) where
  reprPrec m _ :=
    let indexed := (Array.range m.size).zip m.1
    let toFormat : Std.ToFormat (ℕ × ℕ) :=
      ⟨λ (i, p) ↦ "X" ++ repr i ++ "^" ++ repr p⟩
    @Std.Format.joinSep _ toFormat indexed.toList " * "


-- @@ L52-52 verbatim
section Instances


-- @@ L54-55 verbatim
instance : GetElem (CMvMonomial n) ℕ ℕ fun _ idx ↦ idx < n :=
  inferInstanceAs (GetElem (Vector ℕ n) ℕ ℕ _)


-- @@ L57-58 verbatim
instance : GetElem? (CMvMonomial n) ℕ ℕ fun _ idx ↦ idx < n :=
  inferInstanceAs (GetElem? (Vector ℕ n) ℕ ℕ _)


-- @@ L60-61 verbatim
instance : DecidableEq (CMvMonomial n) :=
  inferInstanceAs (DecidableEq (Vector ℕ n))


-- @@ L63-64 verbatim
instance : Ord (CMvMonomial n) :=
  inferInstanceAs (Ord (Vector ℕ n))


-- @@ L66-67 verbatim
instance : Std.TransCmp (Ord.compare (α := CMvMonomial n)) :=
  inferInstanceAs (Std.TransCmp (Ord.compare (α := Vector ℕ n)))


-- @@ L69-70 verbatim
instance : Std.LawfulEqCmp (Ord.compare (α := CMvMonomial n)) :=
  inferInstanceAs (Std.LawfulEqCmp (Ord.compare (α := Vector ℕ n)))


-- @@ L72-72 verbatim
end Instances


-- @@ L74-74 verbatim
namespace CMvMonomial


-- @@ L76-76 verbatim
variable {m m₁ m₂ : CMvMonomial n}


-- @@ L78-80 verbatim
@[ext, grind ext]
protected theorem ext (h : (i : Nat) → (_ : i < n) → m₁[i] = m₂[i]) : m₁ = m₂ :=
  Vector.ext h


-- @@ L82-90 verbatim
/-- Extend a monomial to a larger number of variables by padding with zeros. -/
def extend (n' : ℕ) (m : CMvMonomial n) : CMvMonomial (max n n') :=
  cast (have : n + (n' - n) = n ⊔ n' :=
          if h : n' ≤ n
          then by simp [h]
          else by have := le_of_lt (not_le.1 h)
                  rw [sup_of_le_right this, Nat.add_sub_cancel' this]
        this ▸ rfl)
       (m.append (Vector.replicate (n' - n) 0))


-- @@ L92-93 verbatim
/-- The total degree of a monomial (sum of all exponents). -/
def totalDegree (m : CMvMonomial n) : ℕ := m.sum


-- @@ L95-96 verbatim
/-- The degree of the $i$-th variable in the monomial. -/
def degreeOf (m : CMvMonomial n) (i : Fin n) : ℕ := m.get i


-- @@ L98-99 verbatim
/-- The zero monomial (all exponents are zero). -/
def zero : CMvMonomial n := Vector.replicate n 0


-- @@ L101-101 verbatim
instance : Zero (CMvMonomial n) := ⟨zero⟩


-- @@ L103-105 verbatim
/-- Monomial multiplication (adds exponents element-wise). -/
def add : CMvMonomial n → CMvMonomial n → CMvMonomial n :=
  Vector.zipWith .add


-- @@ L107-107 verbatim
instance : Add (CMvMonomial n) := ⟨add⟩


-- @@ L109-110 verbatim
@[simp]
lemma add_zero : m + 0 = m := by unfold_projs; dsimp [add, zero, CMvMonomial]; grind


-- @@ L112-114 verbatim
/-- Check if $m_1$ divides $m_2$ (true if all exponents of $m_1$ are $\le$ those of $m_2$). -/
def divides (m₁ m₂ : CMvMonomial n) : Bool :=
  Vector.all (Vector.zipWith (flip Nat.ble) m₁ m₂) (· == true)


-- @@ L116-116 verbatim
instance : Dvd (CMvMonomial n) := ⟨fun m₁ m₂ ↦ divides m₁ m₂⟩


-- @@ L118-118 verbatim
instance : Decidable (m₁ ∣ m₂) := by dsimp [(·∣·)]; infer_instance


-- @@ L120-126 verbatim
/--
  The monomial division $m_1 / m_2$ (subtracts exponents element-wise).

  The result makes sense assuming  `m₂ | m₁`.
-/
def div (m₁ m₂ : CMvMonomial n) : CMvMonomial n :=
  Vector.zipWith Nat.sub m₁ m₂


-- @@ L128-128 verbatim
instance : Div (CMvMonomial n) := ⟨div⟩


-- @@ L130-130 verbatim
instance : Decidable (m₁ ∣ m₂) := by dsimp [(·∣·)]; infer_instance


-- @@ L132-134 verbatim
/-- Convert a `CMvMonomial` to a `Finsupp`. -/
def toFinsupp (m : CMvMonomial n) : Fin n →₀ ℕ :=
  ⟨{i : Fin n | m[i] ≠ 0}, m.get, by aesop⟩


-- @@ L136-137 verbatim
/-- Convert a `Finsupp` to a `CMvMonomial`. -/
def ofFinsupp (m : Fin n →₀ ℕ) : CPoly.CMvMonomial n := Vector.ofFn m


-- @@ L139-139 verbatim
@[grind =, simp]

-- @@ L140-144 verbatim
theorem ofFinsupp_toFinsupp : ofFinsupp m.toFinsupp = m := by
  unfold toFinsupp ofFinsupp
  ext i hi
  erw [Vector.getElem_ofFn]
  rfl


-- @@ L146-146 verbatim
@[grind =, simp]

-- @@ L147-154 verbatim
theorem toFinsupp_ofFinsupp {m : Fin n →₀ ℕ} : (ofFinsupp m).toFinsupp = m := by
  ext i; aesop (add simp [CMvMonomial.toFinsupp, CMvMonomial.ofFinsupp, Vector.get])

lemma injective_ofFinsupp : Function.Injective (ofFinsupp (n := n)) :=
  Function.HasLeftInverse.injective ⟨toFinsupp, fun _ ↦ toFinsupp_ofFinsupp⟩

lemma injective_toFinsupp : Function.Injective (toFinsupp (n := n)) :=
  Function.HasLeftInverse.injective ⟨ofFinsupp, fun _ ↦ ofFinsupp_toFinsupp⟩


-- @@ L156-160 verbatim
def equivFinsupp : CMvMonomial n ≃ (Fin n →₀ ℕ) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv := fun _ ↦ ofFinsupp_toFinsupp
  right_inv := fun _ ↦ toFinsupp_ofFinsupp


-- @@ L162-169 verbatim
@[simp, grind =]
lemma map_mul {m₁ m₂ : Multiplicative (Fin n →₀ ℕ)} :
    ofFinsupp (m₁ * m₂) = (ofFinsupp m₁) + (ofFinsupp m₂) := by
  unfold_projs; ext
  erw [Vector.getElem_ofFn, Vector.getElem_zipWith]
  unfold ofFinsupp
  erw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  rfl


-- @@ L171-171 verbatim
end CMvMonomial


-- @@ L173-173 verbatim
abbrev MonoR (n : ℕ) (R : Type*) := CMvMonomial n × R


-- @@ L175-175 verbatim
namespace MonoR


-- @@ L177-177 verbatim
variable {n : ℕ} {R : Type*}


-- @@ L179-180 verbatim
instance [DecidableEq R] : DecidableEq (CMvMonomial n × R) :=
  instDecidableEqProd


-- @@ L182-182 verbatim
section


-- @@ L184-186 verbatim
instance [Repr R] : Repr (MonoR n R) where
  reprPrec
  | (m, c), _ => repr c ++ " * " ++ repr m


-- @@ L188-188 verbatim
@[simp, grind=]

-- @@ L189-189 verbatim
def C (c : R) : MonoR n R := (CMvMonomial.zero, c)


-- @@ L191-191 verbatim
variable [CommSemiring R] [HMod R R R] [BEq R]


-- @@ L193-194 verbatim
def divides (t₁ t₂ : MonoR n R) : Bool :=
  t₁.1 ∣ t₂.1 ∧ t₁.2 % t₂.2 == 0


-- @@ L196-196 verbatim
instance : Dvd (MonoR n R) := ⟨fun t₁ t₂ ↦ divides t₁ t₂⟩


-- @@ L198-200 verbatim
instance {t₁ t₂ : MonoR n R} : Decidable (t₁ ∣ t₂) := by
  dsimp [(·∣·)]
  infer_instance


-- @@ L202-202 verbatim
end


-- @@ L204-205 verbatim
def evalMonomial {R : Type*} {n : ℕ} [CommSemiring R] : (Fin n → R) → CMvMonomial n → R :=
  fun vals m => ∏ (i : Fin n), (vals i) ^ m.get i


-- @@ L207-207 verbatim
end MonoR


-- @@ L209-209 verbatim
end CPoly


-- @@ L211-212 verbatim
@[reducible]
alias Finsupp.ofCMvMonomial := CPoly.CMvMonomial.toFinsupp


-- @@ L214-215 verbatim
@[reducible]
alias Finsupp.toCMvMonomial := CPoly.CMvMonomial.ofFinsupp
