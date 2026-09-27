/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset


-- @@ L12-14 verbatim
/-!
Kernel-checked shard 5 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace Connes

-- @@ L19-19 verbatim
namespace Sp4


-- @@ L21-25 verbatim
/-- The detector succeeds on 16-bit matrix block 16 (with indices 0 through 31). -/
theorem kernelDetectorBlock16 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 16 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel


-- @@ L27-31 verbatim
/-- The detector succeeds on 16-bit matrix block 17 (with indices 0 through 31). -/
theorem kernelDetectorBlock17 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 17 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel


-- @@ L33-37 verbatim
/-- The detector succeeds on 16-bit matrix block 18 (with indices 0 through 31). -/
theorem kernelDetectorBlock18 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 18 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel


-- @@ L39-43 verbatim
/-- The detector succeeds on 16-bit matrix block 19 (with indices 0 through 31). -/
theorem kernelDetectorBlock19 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 19 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel


-- @@ L45-45 verbatim
end Sp4

-- @@ L46-46 verbatim
end Connes
