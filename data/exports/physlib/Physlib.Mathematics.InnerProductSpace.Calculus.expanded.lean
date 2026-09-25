/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
module

public import Physlib.Mathematics.InnerProductSpace.Basic

-- @@ L9-12 verbatim
/-!

# Generalization of calculus results to `InnerProductSpace'`
-/


-- @@ L14-14 verbatim
@[expose] public section

-- @@ L15-18 verbatim
variable {𝕜 : Type*} {E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [InnerProductSpace' ℝ F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [InnerProductSpace' 𝕜 G]


-- @@ L20-20 verbatim
local notation "⟪" x ", " y "⟫" => inner ℝ x y

-- @@ L21-21 verbatim
open InnerProductSpace'


-- @@ L23-25 verbatim
/-- Derivative of the inner product for the instance `InnerProductSpace'`. -/
noncomputable def fderivInnerCLM' [InnerProductSpace' ℝ E] (p : E × E) : E × E →L[ℝ] ℝ :=
  isBoundedBilinearMap_inner'.deriv p


-- @@ L27-33 expanded
lemma HasFDerivAt.inner' {f g : E → F} {f' g' : E →L[ℝ] F} (hf : HasFDerivAt f f' x)
    (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun t => inner ℝ (f t) (g t)) ((fderivInnerCLM' (f x, g x)).comp <| f'.prod g')
      x :=
  by
  exact
    isBoundedBilinearMap_inner' (E := F) |>.hasFDerivAt (f x, g x) |>.comp x
      (hf.prodMk hg)
        -- todo: move this


-- @@ L34-41 expanded
lemma fderiv_inner_apply' {f g : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (y : E) :
    fderiv ℝ (fun t => inner ℝ (f t) (g t)) x y =
      inner ℝ (f x) (fderiv ℝ g x y) + inner ℝ (fderiv ℝ f x y) (g x) :=
  by
  rw [(hf.hasFDerivAt.inner' hg.hasFDerivAt).fderiv]
  rfl
    -- todo: move this


-- @@ L42-48 expanded
lemma deriv_inner_apply' {f g : ℝ → F} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun t => inner ℝ (f t) (g t)) x =
      inner ℝ (f x) (deriv g x) + inner ℝ (deriv f x) (g x) :=
  fderiv_inner_apply' hf hg
    1
      -- todo: move this


-- @@ L49-54 expanded
@[fun_prop]
lemma DifferentiableAt.inner' {f g : E → F} {x} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : DifferentiableAt ℝ (fun x => inner ℝ (f x) (g x)) x :=
  by
  apply HasFDerivAt.differentiableAt
  exact hf.hasFDerivAt.inner' hg.hasFDerivAt

