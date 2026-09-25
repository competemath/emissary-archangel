/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Flow.StoneAPI


-- @@ L10-32 verbatim
/-!
# The spectral-integral group's generator domain is invariant under its own group

The `V`-side counterpart of
`StoneExistence.GeneratorInvariance.stoneCandidateGenerator_translate`: for a domain-aware
spectral theorem `D : DomainAwareSelfAdjointSpectralTheorem T μS`, the operator `T` commutes with
the unitary group `D.expUnitaryGroup` it generates — `D.expUnitaryGroup s` preserves `T.domain`
and `T` commutes with it there. Combined with the `U`-side lemma, this is exactly the missing
ingredient an ODE-uniqueness argument identifying an abstract strongly continuous unitary group
with the spectral-integral group of its own generator would need on both sides (see
`Existence/STONE_GENERATOR_EXISTENCE_PLAN.md`, milestone M5).

The proof is the same "shift the known derivative-at-`s`" argument `expUnitaryGroup_hasDerivAt`
itself already uses internally, applied once more: differentiability of `t ↦ D.expUnitaryGroup t x`
at `t = s` is exactly differentiability of `t ↦ D.expUnitaryGroup t (D.expUnitaryGroup s x)` at
`t = 0`, via the group law `D.expUnitaryGroup t (D.expUnitaryGroup s x) = D.expUnitaryGroup (t + s)
x`.

## Main definitions

- `expUnitaryGroup_translate_mem` : `D.expUnitaryGroup s` preserves `T.domain`.
- `expUnitaryGroup_translate` : `T` commutes with `D.expUnitaryGroup s` on `T.domain`.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
open scoped Topology InnerProductSpace Function

-- @@ L39-39 verbatim
open QuantumMechanics.WOTSpectralMeasure


-- @@ L41-41 verbatim
namespace QuantumMechanics


-- @@ L43-43 verbatim
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- @@ L44-44 verbatim
variable {T : H →ₗ.[ℂ] H}

-- @@ L45-45 verbatim
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}


-- @@ L47-47 verbatim
namespace DomainAwareSelfAdjointSpectralTheorem


-- @@ L49-49 verbatim
variable (D : DomainAwareSelfAdjointSpectralTheorem T μS)


-- @@ L51-51 verbatim
include D


-- @@ L53-58 verbatim
/-- The group law: `D.expUnitaryGroup t (D.expUnitaryGroup s x) = D.expUnitaryGroup (t + s) x`,
via `expUnitaryGroup_add` and the (definitional) fact that `WOT`-multiplication is composition. -/
theorem expUnitaryGroup_translate_comm (x : H) (s t : ℝ) :
    D.expUnitaryGroup t (D.expUnitaryGroup s x) = D.expUnitaryGroup (t + s) x := by
  rw [D.expUnitaryGroup_add t s]
  rfl


-- @@ L60-81 verbatim
/-- `D.expUnitaryGroup s` preserves `T`'s domain: if `x ∈ T.domain`, so is `D.expUnitaryGroup s x`.

Proof: `x`'s orbit is differentiable at `t = s` (`expUnitaryGroup_hasDerivAt`); shifting by `s`
turns this into differentiability of `t ↦ D.expUnitaryGroup t (D.expUnitaryGroup s x)` at `t = 0`,
which is exactly membership of `D.expUnitaryGroup s x` in `T.domain`
(`mem_domain_iff_expUnitaryGroup_hasDerivAt_zero`). -/
theorem expUnitaryGroup_translate_mem (x : T.domain) (s : ℝ) :
    D.expUnitaryGroup s (x : H) ∈ T.domain := by
  have hf : HasDerivAt (fun r : ℝ => D.expUnitaryGroup r (x : H))
      (D.expUnitaryGroup s (Complex.I • T x)) s :=
    D.expUnitaryGroup_hasDerivAt x s
  have hadd : HasDerivAt (fun t : ℝ => t + s) 1 0 := by
    simpa using (hasDerivAt_id' (𝕜 := ℝ) 0).add_const s
  have hshift : HasDerivAt (fun t : ℝ => D.expUnitaryGroup (t + s) (x : H))
      (D.expUnitaryGroup s (Complex.I • T x)) 0 := by
    simpa [Function.comp_def] using hf.scomp_of_eq 0 hadd (by ring)
  have hfun_eq : (fun t : ℝ => D.expUnitaryGroup (t + s) (x : H)) =
      (fun t : ℝ => D.expUnitaryGroup t (D.expUnitaryGroup s (x : H))) := by
    funext t
    exact (D.expUnitaryGroup_translate_comm (x : H) s t).symm
  rw [hfun_eq] at hshift
  exact (D.mem_domain_iff_expUnitaryGroup_hasDerivAt_zero _).2 ⟨_, hshift⟩


-- @@ L83-112 verbatim
/-- `T` commutes with `D.expUnitaryGroup s` on `T.domain`: for `x ∈ T.domain`,
`D.expUnitaryGroup s x ∈ T.domain` and `T (D.expUnitaryGroup s x) = D.expUnitaryGroup s (T x)`. -/
theorem expUnitaryGroup_translate (x : T.domain) (s : ℝ) :
    T ⟨D.expUnitaryGroup s (x : H), D.expUnitaryGroup_translate_mem x s⟩ =
      D.expUnitaryGroup s (T x) := by
  set y : T.domain := ⟨D.expUnitaryGroup s (x : H), D.expUnitaryGroup_translate_mem x s⟩ with hy_def
  have hcanonical : HasDerivAt (fun t : ℝ => D.expUnitaryGroup t (y : H))
      (Complex.I • T y) 0 :=
    D.expUnitaryGroup_hasDerivAt_zero y
  have hf : HasDerivAt (fun r : ℝ => D.expUnitaryGroup r (x : H))
      (D.expUnitaryGroup s (Complex.I • T x)) s :=
    D.expUnitaryGroup_hasDerivAt x s
  have hadd : HasDerivAt (fun t : ℝ => t + s) 1 0 := by
    simpa using (hasDerivAt_id' (𝕜 := ℝ) 0).add_const s
  have hshift : HasDerivAt (fun t : ℝ => D.expUnitaryGroup (t + s) (x : H))
      (D.expUnitaryGroup s (Complex.I • T x)) 0 := by
    simpa [Function.comp_def] using hf.scomp_of_eq 0 hadd (by ring)
  have hfun_eq : (fun t : ℝ => D.expUnitaryGroup (t + s) (x : H)) =
      (fun t : ℝ => D.expUnitaryGroup t (y : H)) := by
    funext t
    rw [hy_def]
    exact (D.expUnitaryGroup_translate_comm (x : H) s t).symm
  rw [hfun_eq] at hshift
  have heq : Complex.I • T y = D.expUnitaryGroup s (Complex.I • T x) :=
    hcanonical.unique hshift
  have hscalar : D.expUnitaryGroup s (Complex.I • T x) = Complex.I • D.expUnitaryGroup s (T x) :=
    map_smul _ _ _
  rw [hscalar] at heq
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  exact smul_right_injective H hI heq


-- @@ L114-114 verbatim
end DomainAwareSelfAdjointSpectralTheorem


-- @@ L116-116 verbatim
end QuantumMechanics
