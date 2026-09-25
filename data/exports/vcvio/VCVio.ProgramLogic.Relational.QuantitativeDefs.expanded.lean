/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.Basic


-- @@ L11-17 verbatim
/-!
# Core eRHL Definitions

This file contains the lightweight definitions for the quantitative relational logic layer.
It is intentionally separated from the heavier coupling-development file so downstream users
that only need the interfaces and notation do not import the full theorem stack.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open ENNReal OracleSpec OracleComp


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
namespace OracleComp.ProgramLogic.Relational


-- @@ L27-27 verbatim
variable {ι₁ : Type u} {ι₂ : Type u}

-- @@ L28-28 verbatim
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

-- @@ L29-29 verbatim
variable [IsUniformSpec spec₁] [IsUniformSpec spec₂]

-- @@ L30-30 verbatim
variable {α β : Type}


-- @@ L32-38 expanded
/-- eRHL-style quantitative relational WP for `OracleComp`.
`eRelWP oa ob g` is the supremum over all couplings `c` of the expected value of `g`
under `c`. -/
noncomputable def eRelWP (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (g : α → β → ℝ≥0∞) :
    ℝ≥0∞ :=
  ⨆ (c : SPMF.Coupling (evalSPMF oa) (evalSPMF ob)), ∑' z, probOutput c.1 z * g z.1 z.2


-- @@ L40-43 verbatim
/-- Indicator postcondition: lifts a `Prop`-valued relation to an `ℝ≥0∞`-valued one. -/
noncomputable def RelPost.indicator (R : RelPost α β) (a : α) (b : β) : ℝ≥0∞ :=
  letI := Classical.dec (R a b)
  if R a b then 1 else 0


-- @@ L45-49 verbatim
/-- pRHL-style exact relational triple, defined via quantitative relational WP with an
indicator postcondition. -/
def RelTriple' (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  1 ≤ eRelWP oa ob (RelPost.indicator R)


-- @@ L51-55 verbatim
/-- ε-approximate relational triple via quantitative relational WP:
`R` holds except with probability at most `ε`. -/
def ApproxRelTriple (ε : ℝ≥0∞) (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop :=
  1 - ε ≤ eRelWP oa ob (RelPost.indicator R)


-- @@ L57-61 verbatim
/-- Exact coupling is the zero-error special case of approximate coupling. -/
theorem relTriple'_eq_approxRelTriple_zero
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} :
    RelTriple' oa ob R ↔ ApproxRelTriple 0 oa ob R := by
  simp [RelTriple', ApproxRelTriple]


-- @@ L63-63 verbatim
end OracleComp.ProgramLogic.Relational
