/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic


-- @@ L11-19 verbatim
/-!
# `RellichKondrachov.Analysis.Calculus.ContDiff.Support`

Small glue lemmas relating `ContDiffOn` to `ContDiff` using topological support.

The key pattern is: if `f` is `C^n` on an open set `s` and the topological support `tsupport f`
is contained in `s`, then `f` is globally `C^n` (it is `0` in a neighborhood of every point
outside `s`).
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace RellichKondrachov

-- @@ L24-24 verbatim
namespace Analysis

-- @@ L25-25 verbatim
namespace Calculus

-- @@ L26-26 verbatim
namespace ContDiff


-- @@ L28-28 verbatim
open Set Filter

-- @@ L29-29 verbatim
open scoped Topology


-- @@ L31-31 verbatim
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

-- @@ L32-32 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- @@ L33-33 verbatim
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]


-- @@ L35-48 verbatim
/-- If `f` is `C^n` on an open set `s` and `tsupport f ⊆ s`, then `f` is globally `C^n`. -/
lemma contDiff_of_contDiffOn_of_tsupport_subset {n : WithTop ℕ∞} {f : E → F} {s : Set E}
    (hs : IsOpen s) (hf : ContDiffOn 𝕜 n f s) (hSupp : tsupport f ⊆ s) :
    ContDiff 𝕜 n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact (hf.contDiffAt (hs.mem_nhds hx))
  · have hx' : x ∉ tsupport f := by
      exact fun hxSupp => hx (hSupp hxSupp)
    have hEq : f =ᶠ[𝓝 x] 0 :=
      (notMem_tsupport_iff_eventuallyEq (f := f) (x := x)).1 hx'
    -- On a neighborhood outside the support, `f` is identically `0`.
    exact (contDiffAt_const : ContDiffAt 𝕜 n (fun _ : E => (0 : F)) x).congr_of_eventuallyEq hEq


-- @@ L50-50 verbatim
end ContDiff

-- @@ L51-51 verbatim
end Calculus

-- @@ L52-52 verbatim
end Analysis

-- @@ L53-53 verbatim
end RellichKondrachov
