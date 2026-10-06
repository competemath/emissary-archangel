/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Classes
import DescriptiveComplexity.Exponential.Reach
import DescriptiveComplexity.PSpaceCompl
import DescriptiveComplexity.PSpaceHierarchy
import DescriptiveComplexity.Problems.TwoSat


-- @@ L12-40 verbatim
/-!
# The exponential classes: complements and inclusions

Everything in this file is *inherited* rather than proved. The two facts it
rests on are polynomial-level and each cost a large development:

* `DescriptiveComplexity.piP_zero_eq` – polynomial time is closed under
  complement, Grädel's capture theorem at level 0, through FO(LFP);
* `DescriptiveComplexity.PSPACE_eq_coPSPACE` – polynomial space is closed under
  complement, Savitch, through the deterministic QSAT walk.

`DescriptiveComplexity.ComplexityClass.exp_compl` carries both one exponential
up, and `DescriptiveComplexity.ComplexityClass.exp_mono` carries every
polynomial-level inclusion. Nothing of the two developments above is spent
twice; that is the first payoff of making `exp` an operator on an abstract
class.

Read on the definitions, the complement equalities say that **SO(LFP) and
SO(PFP) are closed under complement**, which is the form a reader of the logic
will look for; they are stated that way too.

The one construction with content is
`DescriptiveComplexity.PSPACE_subset_PTIME_exp` – an SO(TC) walk is REACH on
the expansion whose points are its states – which lives in
`DescriptiveComplexity.Exponential.Reach` and starts the whole tower.

**No claim is made for NEXPTIME**, which is not expected to be closed under
complement.
-/


-- @@ L42-42 verbatim
namespace DescriptiveComplexity


-- @@ L44-44 verbatim
open FirstOrder


-- @@ L46-46 verbatim
open Language


-- @@ L48-48 verbatim
variable {L : Language.{0, 0}} [L.IsRelational]


-- @@ L50-50 verbatim
/-! ### The two polynomial-level complement facts, in the form used here -/


-- @@ L52-56 verbatim
/-- Polynomial time is closed under complement
(`DescriptiveComplexity.piP_zero_eq`, restated as an equality of classes).
Registered in the Lax archive as
[`Lax535992.PTIMEEqCoPTIME.PTIME_eq_coPTIME`](https://laxarchive.org/lax-535992/Lax535992.PTIMEEqCoPTIME.html#s-Lax535992.PTIMEEqCoPTIME.PTIME_eq_coPTIME). -/
theorem PTIME_compl_eq : PTIME.compl = PTIME := piP_zero_eq


-- @@ L58-60 verbatim
/-- Polynomial space is closed under complement
(`DescriptiveComplexity.PSPACE_eq_coPSPACE`, restated the same way). -/
theorem PSPACE_compl_eq : PSPACE.compl = PSPACE := PSPACE_eq_coPSPACE.symm


-- @@ L62-62 verbatim
/-! ### The complement equalities -/


-- @@ L64-68 verbatim
/-- **`EXPTIME = coEXPTIME`**: inherited from `PTIME.compl = PTIME` through
`DescriptiveComplexity.ComplexityClass.exp_compl`. -/
theorem EXPTIME_eq_coEXPTIME : EXPTIME = coEXPTIME := by
  rw [show coEXPTIME = EXPTIME.compl from rfl, EXPTIME_eq_PTIME_exp,
    ← ComplexityClass.exp_compl, PTIME_compl_eq]


-- @@ L70-74 verbatim
/-- **`EXPSPACE = coEXPSPACE`**: inherited from Savitch through the same
operator. -/
theorem EXPSPACE_eq_coEXPSPACE : EXPSPACE = coEXPSPACE := by
  rw [show coEXPSPACE = EXPSPACE.compl from rfl, EXPSPACE_eq_PSPACE_exp,
    ← ComplexityClass.exp_compl, PSPACE_compl_eq]


-- @@ L76-79 verbatim
/-- A problem is in EXPTIME exactly when its complement is. -/
theorem mem_EXPTIME_compl_iff (P : DecisionProblem L) : Pᶜ ∈ EXPTIME ↔ P ∈ EXPTIME := by
  conv_rhs => rw [EXPTIME_eq_coEXPTIME]
  exact Iff.rfl


-- @@ L81-84 verbatim
/-- A problem is in EXPSPACE exactly when its complement is. -/
theorem mem_EXPSPACE_compl_iff (P : DecisionProblem L) : Pᶜ ∈ EXPSPACE ↔ P ∈ EXPSPACE := by
  conv_rhs => rw [EXPSPACE_eq_coEXPSPACE]
  exact Iff.rfl


-- @@ L86-91 verbatim
/-- **SO(≤, LFP) is closed under complement** – the second-order shadow of
`DescriptiveComplexity.piP_zero_eq`, and the reading of
`DescriptiveComplexity.EXPTIME_eq_coEXPTIME` on the definition. -/
theorem SOLFPDefinable.compl {P : DecisionProblem L} (h : SOLFPDefinable P) :
    SOLFPDefinable Pᶜ :=
  (mem_EXPTIME_compl_iff P).mpr h


-- @@ L93-97 verbatim
/-- **SO(≤, PFP) is closed under complement** – the second-order shadow of
Savitch. -/
theorem SOPFPDefinable.compl {P : DecisionProblem L} (h : SOPFPDefinable P) :
    SOPFPDefinable Pᶜ :=
  (mem_EXPSPACE_compl_iff P).mpr h


-- @@ L99-103 verbatim
/-! ### The inclusions

Every line but the first is `DescriptiveComplexity.ComplexityClass.exp_mono` on
a polynomial-level inclusion, read through the bridge theorems of
`DescriptiveComplexity.Exponential.Classes`. -/


-- @@ L105-110 verbatim
/-- **`PSPACE ⊆ EXPTIME`**: an SO(TC) walk is a reachability question on the
expansion whose points are its states, and reachability is in polynomial time.
On the definitions this is **SO(TC) ⊆ SO(LFP)**. -/
theorem PSPACE_subset_EXPTIME : PSPACE ⊆ EXPTIME := by
  rw [EXPTIME_eq_PTIME_exp]
  exact PSPACE_subset_PTIME_exp


-- @@ L112-114 verbatim
/-- `PSPACE ⊆ coEXPTIME`, by the complement equality. -/
theorem PSPACE_subset_coEXPTIME : PSPACE ⊆ coEXPTIME :=
  EXPTIME_eq_coEXPTIME ▸ PSPACE_subset_EXPTIME


-- @@ L116-121 verbatim
/-- `PTIME ⊆ PSPACE`, routed through NP – the polynomial-level inclusion the
exponential ones are lifted from.
Registered in the Lax archive as
[`Lax134656.HierarchyInPSPACE.PTIME_subset_PSPACE`](https://laxarchive.org/lax-134656/Lax134656.HierarchyInPSPACE.html#s-Lax134656.HierarchyInPSPACE.PTIME_subset_PSPACE). -/
theorem PTIME_subset_PSPACE : PTIME ⊆ PSPACE :=
  fun _ _ _ h => NP_subset_PSPACE (PTIME_subset_NP h)


-- @@ L123-127 verbatim
/-- **`EXPTIME ⊆ EXPSPACE`**, i.e., **SO(LFP) ⊆ SO(PFP)** – the second-order
shadow of `PTIME ⊆ PSPACE`. -/
theorem EXPTIME_subset_EXPSPACE : EXPTIME ⊆ EXPSPACE := by
  rw [EXPTIME_eq_PTIME_exp, EXPSPACE_eq_PSPACE_exp]
  exact ComplexityClass.exp_mono PTIME_subset_PSPACE


-- @@ L129-131 verbatim
/-- `coEXPTIME ⊆ EXPSPACE`, by the complement equality. -/
theorem coEXPTIME_subset_EXPSPACE : coEXPTIME ⊆ EXPSPACE :=
  EXPTIME_eq_coEXPTIME ▸ EXPTIME_subset_EXPSPACE


-- @@ L133-136 verbatim
/-- **`EXPTIME ⊆ NEXPTIME`**, the second-order shadow of `PTIME ⊆ NP`. -/
theorem EXPTIME_subset_NEXPTIME : EXPTIME ⊆ NEXPTIME := by
  rw [EXPTIME_eq_PTIME_exp, NEXPTIME_eq_NP_exp]
  exact ComplexityClass.exp_mono PTIME_subset_NP


-- @@ L138-141 verbatim
/-- **`NEXPTIME ⊆ EXPSPACE`**, the second-order shadow of `NP ⊆ PSPACE`. -/
theorem NEXPTIME_subset_EXPSPACE : NEXPTIME ⊆ EXPSPACE := by
  rw [NEXPTIME_eq_NP_exp, EXPSPACE_eq_PSPACE_exp]
  exact ComplexityClass.exp_mono NP_subset_PSPACE


-- @@ L143-148 verbatim
/-- `NL.exp ⊆ EXPTIME`, the second-order shadow of `NL ⊆ PTIME`. Together with
`DescriptiveComplexity.PSPACE_subset_NL_exp` it sandwiches `NL.exp` between
PSPACE and EXPTIME. -/
theorem NL_exp_subset_EXPTIME : NL.exp ⊆ EXPTIME := by
  rw [EXPTIME_eq_PTIME_exp]
  exact ComplexityClass.exp_mono NL_subset_PTIME


-- @@ L150-153 verbatim
/-! ### The polynomial classes inside the exponential ones

All of these route through `PSPACE ⊆ EXPTIME`, which is the only inclusion of
this development with content. -/


-- @@ L155-156 verbatim
theorem PTIME_subset_EXPTIME : PTIME ⊆ EXPTIME :=
  fun _ _ _ h => PSPACE_subset_EXPTIME (PTIME_subset_PSPACE h)


-- @@ L158-159 verbatim
theorem NP_subset_NEXPTIME : NP ⊆ NEXPTIME :=
  fun _ _ _ h => EXPTIME_subset_NEXPTIME (PSPACE_subset_EXPTIME (NP_subset_PSPACE h))


-- @@ L161-162 verbatim
theorem PSPACE_subset_EXPSPACE : PSPACE ⊆ EXPSPACE :=
  fun _ _ _ h => EXPTIME_subset_EXPSPACE (PSPACE_subset_EXPTIME h)


-- @@ L164-167 verbatim
/-- The whole polynomial hierarchy sits inside EXPTIME, through
`DescriptiveComplexity.PH_subset_PSPACE`. -/
theorem PH_subset_EXPTIME : PH ⊆ EXPTIME :=
  fun _ _ _ h => PSPACE_subset_EXPTIME (PH_subset_PSPACE h)


-- @@ L169-169 verbatim
end DescriptiveComplexity
