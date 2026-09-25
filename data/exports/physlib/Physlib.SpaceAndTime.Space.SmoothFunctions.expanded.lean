/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.SpaceAndTime.Space.Module
public import Mathlib.Geometry.Manifold.ContMDiffMap

-- @@ L10-19 verbatim
/-!

# Smooth real-valued functions on space

`Space.cmap` bundles a smooth real-valued function on `Space d`, given as a plain function
together with a `ContDiff` proof, into the space of bundled smooth maps
`C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯`. Such bundled maps are, for instance, the test
functions on which the mass distribution of a rigid body acts.

-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open Manifold


-- @@ L25-25 verbatim
namespace Space


-- @@ L27-31 verbatim
/-- Bundle a smooth real-valued function on `Space d` as an element of the space of bundled
smooth maps. Keeping this as a named constructor ensures the resulting type head stays
`ContMDiffMap`, so the module/ring operations and `comp` resolve correctly. -/
def cmap {d : ℕ} (f : Space d → ℝ) (hf : ContDiff ℝ ⊤ f) :
    C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨f, hf.contMDiff⟩


-- @@ L33-35 verbatim
@[simp]
lemma cmap_apply {d : ℕ} (f : Space d → ℝ) (hf : ContDiff ℝ ⊤ f) (y : Space d) :
    cmap f hf y = f y := rfl


-- @@ L37-37 verbatim
end Space
