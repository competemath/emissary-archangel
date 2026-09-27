/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2


-- @@ L10-10 verbatim
/-! # Erdős 97 convex-octagon formalization: Basic -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace Erdos97Octagon


-- @@ L16-16 verbatim
open scoped InnerProductSpace

-- @@ L17-17 verbatim
open Module


-- @@ L19-20 verbatim
/-- The Euclidean plane, represented as `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)


-- @@ L22-22 verbatim
end Erdos97Octagon
