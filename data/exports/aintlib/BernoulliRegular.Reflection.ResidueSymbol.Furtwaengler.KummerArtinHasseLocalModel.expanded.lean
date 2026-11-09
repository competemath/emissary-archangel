/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.Local.UnitQuotient


-- @@ L10-27 verbatim
/-!
# Kummer--Artin--Hasse local model at `lambda`

This file fixes the Lean objects used for the explicit `lambda`-local
correction in the Kummer reciprocity proof.  The mathematical model is

```text
F = Q_p(zeta_p),    O_F = its completed integer ring,
pi = zeta_p - 1,   U_n = 1 + pi^n O_F.
```

The current project already develops the completed local integer ring and
completed principal-unit filtration under
`BernoulliRegular.Reflection.Local`.  We expose those objects here under names
specific to the Kummer--Artin--Hasse formula.

This file only pins down the local model that the explicit formula must use.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
open scoped NumberField


-- @@ L35-35 verbatim
namespace BernoulliRegular

-- @@ L36-36 verbatim
namespace Furtwaengler

-- @@ L37-37 verbatim
namespace KummerArtinHasse


-- @@ L39-39 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L40-40 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L42-44 verbatim
/-- The completed local integer ring at `lambda = (zeta_p - 1)`. -/
abbrev LambdaLocalIntegerRing : Type _ :=
  Reflection.Local.completedLocalCyclotomicRing p K


-- @@ L46-50 verbatim
/-- The fraction-ring candidate for `Q_p(zeta_p)` attached to the completed
local integer ring.  Later formula files must either use this object or prove
an explicit equivalence from their local-field model to this one. -/
abbrev LambdaLocalField : Type _ :=
  FractionRing (LambdaLocalIntegerRing p K)


-- @@ L52-54 verbatim
/-- The completed maximal ideal in the completed local integer ring. -/
abbrev LambdaMaximalIdeal : Ideal (LambdaLocalIntegerRing p K) :=
  Reflection.Local.completedLocalCyclotomicMaximalIdeal p K


-- @@ L56-58 verbatim
/-- The completed local unit group. -/
abbrev LambdaUnitGroup : Type _ :=
  Reflection.Local.completedLocalCyclotomicUnitGroup p K


-- @@ L60-62 verbatim
/-- The completed principal-unit filtration `U_n = 1 + pi^n O_F`. -/
abbrev LambdaPrincipalUnitSubgroup (n : ℕ) : Subgroup (LambdaUnitGroup p K) :=
  Reflection.Local.completedPrincipalUnitSubgroup p K n


-- @@ L64-66 verbatim
/-- The completed local uniformizer `pi = zeta_p - 1`. -/
def lambdaPi : LambdaLocalIntegerRing p K :=
  Reflection.Local.completedLocalCyclotomicUniformizer p K


-- @@ L68-70 verbatim
/-- The completed distinguished `p`-th root of unity. -/
def lambdaZetaUnit : LambdaUnitGroup p K :=
  Reflection.Local.completedLocalCyclotomicZetaUnit p K


-- @@ L72-75 verbatim
@[simp]
theorem lambdaPi_ne_zero :
    lambdaPi p K ≠ 0 :=
  Reflection.Local.completedLocalCyclotomicUniformizer_ne_zero (p := p) (K := K)


-- @@ L77-81 verbatim
theorem lambdaMaximalIdeal_eq_span_pi :
    LambdaMaximalIdeal p K =
      Ideal.span ({lambdaPi p K} : Set (LambdaLocalIntegerRing p K)) :=
  Reflection.Local.completedLocalCyclotomicMaximalIdeal_eq_span_uniformizer
    (p := p) (K := K)


-- @@ L83-86 verbatim
theorem lambdaMaximalIdeal_isPrincipal :
    Submodule.IsPrincipal (LambdaMaximalIdeal p K) :=
  Reflection.Local.completedLocalCyclotomicMaximalIdeal_isPrincipal
    (p := p) (K := K)


-- @@ L88-90 verbatim
theorem lambdaZetaUnit_pow_eq_one :
    lambdaZetaUnit p K ^ p = 1 :=
  Reflection.Local.completedLocalCyclotomicZetaUnit_pow_eq_one p K


-- @@ L92-94 verbatim
theorem lambdaZetaUnit_mem_muP :
    lambdaZetaUnit p K ∈ Reflection.Local.completedLocalCyclotomicMuP p K :=
  Reflection.Local.completedLocalCyclotomicZetaUnit_mem_muP p K


-- @@ L96-99 verbatim
theorem lambdaZetaUnit_mem_principalUnits_one :
    lambdaZetaUnit p K ∈ LambdaPrincipalUnitSubgroup p K 1 :=
  Reflection.Local.completedLocalCyclotomicZetaUnit_mem_completedPrincipalUnitSubgroup_one
    (p := p) (K := K)


-- @@ L101-105 verbatim
theorem lambdaMuP_le_principalUnits_one :
    Reflection.Local.completedLocalCyclotomicMuP p K ≤
      LambdaPrincipalUnitSubgroup p K 1 :=
  Reflection.Local.completedLocalCyclotomicMuP_le_completedPrincipalUnitSubgroup_one
    (p := p) (K := K)


-- @@ L107-110 verbatim
theorem lambdaZetaUnit_not_mem_principalUnits_two :
    lambdaZetaUnit p K ∉ LambdaPrincipalUnitSubgroup p K 2 :=
  Reflection.Local.completedLocalCyclotomicZetaUnit_not_mem_completedPrincipalUnitSubgroup_two
    (p := p) (K := K)


-- @@ L112-112 verbatim
end KummerArtinHasse

-- @@ L113-113 verbatim
end Furtwaengler

-- @@ L114-114 verbatim
end BernoulliRegular
