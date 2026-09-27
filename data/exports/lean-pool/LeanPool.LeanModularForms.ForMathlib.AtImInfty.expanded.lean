/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/- Probably put this at Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean -/


-- @@ L12-12 verbatim
/-! # AtImInfty -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
open UpperHalfPlane


-- @@ L19-21 verbatim
lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (Set.ofPred p)


-- @@ L23-24 verbatim
lemma Filter.tendsto_im_atImInfty : Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop :=
  tendsto_iff_comap.mpr fun ⦃_⦄ a => a
