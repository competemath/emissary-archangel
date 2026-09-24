/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs


-- @@ L8-13 verbatim
/-!
# Canonical normalization of an MPS tensor

Left-canonical normalization conditions for MPS tensors are used in the
canonical-form and periodic theories.
-/


-- @@ L15-15 verbatim
open scoped Matrix BigOperators


-- @@ L17-17 verbatim
namespace MPSTensor


-- @@ L19-19 verbatim
variable {d D : ℕ}


-- @@ L21-24 verbatim
/-- Left-canonical, equivalently trace-preserving, normalization of an MPS
tensor. -/
abbrev IsLeftCanonical (A : MPSTensor d D) : Prop :=
  Kraus.IsTP A


-- @@ L26-26 verbatim
end MPSTensor
