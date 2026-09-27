/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint


-- @@ L10-17 verbatim
/-!

# some obvious lemmas on self-adjoint operators

This file provides the polarization identity for self adjoint continuous linear maps
  over `is_R_or_C`.

-/


-- @@ L19-19 verbatim
@[expose] public section



-- @@ L22-22 verbatim
variable {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]


-- @@ L24-24 verbatim
local notation "⟪" x "," y "⟫" => @inner 𝕜 _ _ x y


-- @@ L26-26 verbatim
namespace ContinuousLinearMap

-- @@ L27-27 verbatim
namespace IsSelfAdjoint


-- @@ L29-36 expanded
/-- Given a self-adjoint continuous linear operator $T$ on $E$, we get
  $\langle T x, x \rangle = 0$ for any $x\in E$ if and only if $T=0$. -/
theorem inner_map_self_eq_zero [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    (∀ x, @inner 𝕜 _ _ (T x) x = 0) ↔ T = 0 :=
  by
  rw [isSelfAdjoint_iff_isSymmetric] at hT
  simp_rw [ContinuousLinearMap.ext_iff, ← ContinuousLinearMap.coe_coe, ← LinearMap.ext_iff,
    ContinuousLinearMap.toLinearMap_zero]
  exact hT.inner_map_self_eq_zero


-- @@ L38-38 verbatim
open RCLike


-- @@ L40-48 expanded
/-- The polarization identity for self-adjoint operators. -/
theorem inner_map_polarization [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (x y : E) :
    @inner 𝕜 _ _ (T x) y =
      (@inner 𝕜 _ _ (T (x + y)) (x + y) - @inner 𝕜 _ _ (T (x - y)) (x - y) -
            I * @inner 𝕜 _ _ (T (x + (I : 𝕜) • y)) (x + (I : 𝕜) • y) +
          I * @inner 𝕜 _ _ (T (x - (I : 𝕜) • y)) (x - (I : 𝕜) • y)) /
        4 :=
  by
  rw [← ContinuousLinearMap.coe_coe,
    LinearMap.IsSymmetric.inner_map_polarization (IsSelfAdjoint.isSymmetric hT)]


-- @@ L51-51 verbatim
end IsSelfAdjoint

-- @@ L52-52 verbatim
end ContinuousLinearMap
