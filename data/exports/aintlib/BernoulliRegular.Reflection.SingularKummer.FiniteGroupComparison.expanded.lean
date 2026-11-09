/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic


-- @@ L11-34 verbatim
/-!
# Singular Kummer: finite group comparison

This file proves the elementary finite-group fact used at the start of the
singular-group construction.

For a finite abelian group `A`, the elementary quotient

```text
A / pA
```

is nontrivial if and only if the subgroup

```text
A[p] = {x : A | p • x = 0}
```

is nontrivial.  The proof is only the finite endomorphism fact that an
endomorphism of a finite type is injective if and only if it is surjective.

The component-refined statement will require the same comparison after passing
to character components; this file isolates the group-theoretic core.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
namespace BernoulliRegular

-- @@ L39-39 verbatim
namespace Reflection

-- @@ L40-40 verbatim
namespace SingularKummer


-- @@ L42-42 verbatim
variable {A : Type*} [AddCommGroup A]


-- @@ L44-46 verbatim
/-- The subgroup `nA` of `n`-multiples in an additive abelian group. -/
abbrev multiplesSubgroup (A : Type*) [AddCommGroup A] (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) n).range


-- @@ L48-50 verbatim
/-- The subgroup `A[n]` of elements killed by `n`. -/
abbrev torsionBySubgroup (A : Type*) [AddCommGroup A] (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) n).ker


-- @@ L52-54 verbatim
/-- The elementary quotient `A / nA`, written additively. -/
abbrev elementaryQuotient (A : Type*) [AddCommGroup A] (n : ℕ) : Type _ :=
  A ⧸ multiplesSubgroup A n


-- @@ L56-71 verbatim
/-- For an endomorphism of a finite additive abelian group, the quotient by its
range is nontrivial if and only if its kernel is nontrivial. -/
theorem quotient_range_nontrivial_iff_ker_nontrivial
    [Finite A] (f : A →+ A) :
    Nontrivial (A ⧸ f.range) ↔ Nontrivial f.ker := by
  rw [QuotientAddGroup.nontrivial_iff]
  rw [AddSubgroup.nontrivial_iff_ne_bot]
  constructor
  · intro h_range h_ker
    exact h_range ((AddMonoidHom.range_eq_top).2
      (Finite.injective_iff_surjective.1
        ((AddMonoidHom.ker_eq_bot_iff f).1 h_ker)))
  · intro h_ker h_range
    exact h_ker ((AddMonoidHom.ker_eq_bot_iff f).2
      (Finite.injective_iff_surjective.2
        ((AddMonoidHom.range_eq_top).1 h_range)))


-- @@ L73-78 verbatim
/-- The quotient `A / nA` is nontrivial if and only if `A[n]` is nontrivial. -/
theorem elementaryQuotient_nontrivial_iff_torsionBySubgroup_nontrivial
    [Finite A] (n : ℕ) :
    Nontrivial (elementaryQuotient A n) ↔ Nontrivial (torsionBySubgroup A n) :=
  quotient_range_nontrivial_iff_ker_nontrivial
    (A := A) (nsmulAddMonoidHom (α := A) n)


-- @@ L80-86 verbatim
/-- The direction used to pass from a nonzero elementary quotient to
`n`-torsion. -/
theorem torsionBySubgroup_nontrivial_of_elementaryQuotient_nontrivial
    [Finite A] {n : ℕ} :
    Nontrivial (elementaryQuotient A n) → Nontrivial (torsionBySubgroup A n) :=
  (elementaryQuotient_nontrivial_iff_torsionBySubgroup_nontrivial
    (A := A) n).1


-- @@ L88-94 verbatim
/-- The reverse direction, useful when switching back from `n`-torsion to the
elementary quotient. -/
theorem elementaryQuotient_nontrivial_of_torsionBySubgroup_nontrivial
    [Finite A] {n : ℕ} :
    Nontrivial (torsionBySubgroup A n) → Nontrivial (elementaryQuotient A n) :=
  (elementaryQuotient_nontrivial_iff_torsionBySubgroup_nontrivial
    (A := A) n).2


-- @@ L96-96 verbatim
end SingularKummer

-- @@ L97-97 verbatim
end Reflection

-- @@ L98-98 verbatim
end BernoulliRegular


-- @@ L100-100 verbatim
end
