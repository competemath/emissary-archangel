module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Patterns
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.Shell4
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Defs


-- @@ L6-19 verbatim
/-!
# Type I/II/III subsets of the shell

In the BS81 Lemma 21 counting argument, shell vectors are split into three families (`TypeI`,
`TypeII`, `TypeIII`) according to which integer coordinate pattern they realize.

This file isolates these definitions so later modules can depend on them without importing the
full counting development.

## Main definitions
* `CodeIsGolayCountFinal.TypeI`
* `CodeIsGolayCountFinal.TypeII`
* `CodeIsGolayCountFinal.TypeIII`
-/


-- @@ L21-21 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set


-- @@ L27-27 verbatim
open Uniqueness.BS81

-- @@ L28-28 verbatim
open Uniqueness.BS81.Thm15.Lemma21


-- @@ L30-30 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L32-32 verbatim
namespace CodeIsGolayCountFinal


-- @@ L34-34 verbatim
local notation "shell4" => Uniqueness.BS81.latticeShell4


-- @@ L36-38 verbatim
/-!
## Pattern subclasses of the shell
-/


-- @@ L40-44 verbatim
/-- Type I vectors: shell vectors whose integer coordinates satisfy `isPattern2`. -/
@[expose] public def TypeI (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) : Set ℝ²⁴ :=
  {u : ℝ²⁴ | u ∈ shell4 C ∧ ∃ z : Fin 24 → ℤ,
      (∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) ∧ isPattern2 z}


-- @@ L46-50 verbatim
/-- Type II vectors: shell vectors whose integer coordinates satisfy `isPattern1`. -/
@[expose] public def TypeII (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) : Set ℝ²⁴ :=
  {u : ℝ²⁴ | u ∈ shell4 C ∧ ∃ z : Fin 24 → ℤ,
      (∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) ∧ isPattern1 z}


-- @@ L52-56 verbatim
/-- Type III vectors: shell vectors whose integer coordinates satisfy `isPattern3`. -/
@[expose] public def TypeIII (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) : Set ℝ²⁴ :=
  {u : ℝ²⁴ | u ∈ shell4 C ∧ ∃ z : Fin 24 → ℤ,
      (∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) ∧ isPattern3 z}


-- @@ L58-58 verbatim
end CodeIsGolayCountFinal


-- @@ L60-60 verbatim
end


-- @@ L62-62 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
