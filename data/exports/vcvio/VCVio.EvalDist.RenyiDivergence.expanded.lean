/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence
public import ToMathlib.Probability.Divergence.RenyiDiscrete
public import VCVio.EvalDist.Monad.Map


-- @@ L12-35 verbatim
/-!
# Rényi Divergence for SPMFs and Monadic Computations

This file extends the Rényi divergence from `PMF` (defined in
`ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence`) to:

1. `SPMF.renyiDiv` — on sub-probability mass functions (via `toPMF`)
2. `renyiDiv` — on any monad with `MonadLiftT m SPMF` (via `evalSPMF`)

This mirrors the structure of `VCVio.EvalDist.TVDist`, which performs the same lift for
total variation distance.

## Application

The monadic `renyiDiv` is used to state sampler quality bounds:

```
renyiDiv a (concreteSamplerZ μ σ') (idealSamplerZ μ σ') ≤ 1 + ε
```

where `concreteSamplerZ` uses FPR arithmetic and `idealSamplerZ` samples from the exact
discrete Gaussian. The probability preservation theorem then translates this into a
security loss factor in the Falcon EUF-CMA proof.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
open ENNReal


-- @@ L43-43 verbatim
universe u v


-- @@ L45-45 verbatim
/-! ### SPMF.renyiDiv -/


-- @@ L47-47 verbatim
namespace SPMF


-- @@ L49-49 verbatim
variable {α : Type*}


-- @@ L51-53 verbatim
/-- Rényi MGF on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def renyiMGF (a : ℝ) (p q : SPMF α) : ℝ≥0∞ :=
  p.toPMF.renyiMGF a q.toPMF


-- @@ L55-57 verbatim
/-- Multiplicative Rényi divergence on SPMFs, defined via the underlying `PMF (Option α)`. -/
protected def renyiDiv (a : ℝ) (p q : SPMF α) : ℝ≥0∞ :=
  p.toPMF.renyiDiv a q.toPMF


-- @@ L59-60 verbatim
/-- Max-divergence on SPMFs. -/
protected def maxDiv (p q : SPMF α) : ℝ≥0∞ := p.toPMF.maxDiv q.toPMF


-- @@ L62-64 verbatim
@[simp]
theorem renyiDiv_self (a : ℝ) (p : SPMF α) : p.renyiDiv a p = 1 :=
  PMF.renyiDiv_self _ _


-- @@ L66-71 verbatim
universe w in
theorem renyiDiv_map_le (a : ℝ) (ha : 1 < a) {α' : Type w} {β : Type w}
    (f : α' → β) (p q : SPMF α') :
    SPMF.renyiDiv a (f <$> p) (f <$> q) ≤ SPMF.renyiDiv a p q := by
  simpa only [SPMF.renyiDiv, SPMF.toPMF_map] using
    PMF.renyiDiv_map_le a ha (Option.map f) p.toPMF q.toPMF


-- @@ L73-78 verbatim
universe w in
theorem renyiDiv_bind_right_le (a : ℝ) (ha : 1 < a) {α' : Type w} {β : Type w}
    (f : α' → SPMF β) (p q : SPMF α') :
    SPMF.renyiDiv a (p >>= f) (q >>= f) ≤ SPMF.renyiDiv a p q := by
  simpa only [SPMF.renyiDiv, SPMF.toPMF_bind, Option.elimM, PMF.monad_bind_eq_bind] using
    PMF.renyiDiv_bind_right_le a ha _ p.toPMF q.toPMF


-- @@ L80-80 verbatim
end SPMF


-- @@ L82-82 verbatim
/-! ### Monadic renyiDiv -/


-- @@ L84-84 verbatim
section monadic


-- @@ L86-86 verbatim
variable {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] {α : Type u}


-- @@ L88-91 expanded
/-- Rényi divergence between two monadic computations,
defined via their evaluation distributions. -/
noncomputable def renyiDiv (a : ℝ) (mx my : m α) : ℝ≥0∞ :=
  SPMF.renyiDiv a (evalSPMF mx) (evalSPMF my)


-- @@ L93-96 verbatim
omit [Monad m] [LawfulMonadLiftT m SPMF] in
@[simp]
theorem renyiDiv_self (a : ℝ) (mx : m α) : renyiDiv a mx mx = 1 :=
  SPMF.renyiDiv_self _ _


-- @@ L98-101 verbatim
theorem renyiDiv_map_le [LawfulMonad m] {β : Type u} (a : ℝ) (ha : 1 < a)
    (f : α → β) (mx my : m α) :
    renyiDiv a (f <$> mx) (f <$> my) ≤ renyiDiv a mx my := by
  simpa only [renyiDiv, _root_.evalSPMF_map] using SPMF.renyiDiv_map_le a ha f _ _


-- @@ L103-106 verbatim
theorem renyiDiv_bind_right_le [LawfulMonad m] {β : Type u} (a : ℝ) (ha : 1 < a)
    (f : α → m β) (mx my : m α) :
    renyiDiv a (mx >>= f) (my >>= f) ≤ renyiDiv a mx my := by
  simpa only [renyiDiv, _root_.evalSPMF_bind] using SPMF.renyiDiv_bind_right_le a ha _ _ _


-- @@ L108-108 verbatim
/-! ### Rényi to Probability Bounds -/


-- @@ L110-117 expanded
omit [Monad m] [LawfulMonadLiftT m SPMF] in
/-- If the Rényi divergence between two computations is at most `R`, then for any
output `x`, `Pr[= x | my] ≥ Pr[= x | mx]^{a/(a-1)} / R`. -/
theorem probOutput_le_of_renyiDiv (a : ℝ) (ha : 1 < a) (mx my : m α) (R : ℝ≥0∞)
    (hR : renyiDiv a mx my ≤ R) (x : α) :
    probOutput mx x ^ (a / (a - 1) : ℝ) / R ≤ probOutput my x :=
  by
  simp only [probOutput_def, renyiDiv, SPMF.renyiDiv] at *
  exact (ENNReal.div_le_div_left hR _).trans (PMF.renyiDiv_apply_bound a ha _ _ _)


-- @@ L119-119 verbatim
end monadic
