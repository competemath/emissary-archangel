/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft


-- @@ L12-14 verbatim
/-! An actual continuous inverse has the inverse Jacobian as its derivative.
This is the easy half of the inverse function theorem; no differentiability
of the inverse is an independent assumption. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open scoped Topology


-- @@ L23-23 verbatim
namespace EulerContinuousInverseDerivative


-- @@ L25-27 verbatim
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L29-37 verbatim
theorem hasFDerivAt_inverse
    (X : F → E) (Y : E → F) (x : E)
    (J : F →L[ℝ] E) (I : E →L[ℝ] F)
    (hY : ContinuousAt Y x) (hX : HasFDerivAt X J (Y x))
    (hXY : ∀ᶠ y in 𝓝 x, X (Y y) = y)
    (hI : Function.LeftInverse I J) : HasFDerivAt Y I x := by
  have h := HasFDerivAt.of_comp_of_leftInverse (f'symm := I)
    hY hX (hasFDerivAt_id x) hXY hI
  simpa only [ContinuousLinearMap.comp_id] using h


-- @@ L39-39 verbatim
end EulerContinuousInverseDerivative
