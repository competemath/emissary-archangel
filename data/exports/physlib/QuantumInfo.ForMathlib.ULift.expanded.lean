/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib


-- @@ L10-17 verbatim
/-!
# Typeclass instances for `ULift`

This file equips `ULift` with algebraic and analytic typeclass instances lifted from the
underlying type, including `Star`, `StarMul`, `StarRing`, `NormedField`, `DenselyNormedField`
and `RCLike` structures, together with the corresponding `simp` lemmas relating operations on
`ULift.{v, u} α` to operations on the underlying `α`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open ComplexOrder


-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
instance AddZero.ulift {α : Type u} [AddZero α] : AddZero (ULift.{v, u} α) where


-- @@ L27-28 verbatim
instance ULift.instStar {𝕜 : Type u} [Star 𝕜] : Star (ULift.{v,u} 𝕜) where
  star x := .up (star x.down)


-- @@ L30-32 verbatim
@[simp]
theorem ULift.star_eq {𝕜 : Type u} [Star 𝕜] (x : ULift.{v,u} 𝕜) : star x = .up (star x.down) := by
  rfl


-- @@ L34-36 verbatim
instance ULift.instInvolutiveStar {𝕜 : Type u} [InvolutiveStar 𝕜] :
    InvolutiveStar (ULift.{v,u} 𝕜) where
  star_involutive x := by simp


-- @@ L38-39 verbatim
instance ULift.instStarMul {𝕜 : Type u} [Mul 𝕜] [StarMul 𝕜] : StarMul (ULift.{v,u} 𝕜) where
  star_mul x y := by simp; rfl


-- @@ L41-42 verbatim
instance {𝕜 : Type u} [NonUnitalNonAssocSemiring 𝕜] [StarRing 𝕜] : StarRing (ULift.{v,u} 𝕜) where
  star_add x y := by simp; rfl


-- @@ L44-47 verbatim
@[simp]
theorem ULift.starRingEnd_down {𝕜 : Type u} (x : ULift.{v,u} 𝕜) [CommSemiring 𝕜] [StarRing 𝕜] :
    ((starRingEnd (ULift.{v, u} 𝕜)) x).down = star x.down := by
  rfl


-- @@ L49-51 verbatim
instance {𝕜 : Type u} [NormedField 𝕜] : NormedField (ULift.{v,u} 𝕜) where
  dist_eq x y := NormedField.dist_eq x.down y.down
  norm_mul a b := NormedField.norm_mul a.down b.down


-- @@ L53-54 verbatim
instance {𝕜 : Type u} [DenselyNormedField 𝕜] : DenselyNormedField (ULift.{v,u} 𝕜) where
  lt_norm_lt x y := by simpa using DenselyNormedField.lt_norm_lt x y


-- @@ L56-59 verbatim
@[simp]
theorem AddEquiv.ulift_apply {α : Type u} [Add α] (x : ULift.{v, u} α) :
    AddEquiv.ulift.{u, v} x = x.down := by
  rfl


-- @@ L61-84 verbatim
noncomputable instance {𝕜 : Type u} [RCLike 𝕜] : RCLike (ULift.{v,u} 𝕜) where
  re := RCLike.re.comp AddEquiv.ulift.toAddMonoidHom (N := 𝕜)
  im := RCLike.im.comp AddEquiv.ulift.toAddMonoidHom (N := 𝕜)
  I := .up RCLike.I
  I_re_ax := by simp
  I_mul_I_ax := by
    rcases RCLike.I_mul_I_ax (K := 𝕜) with h |h
    · left
      ext1
      exact h
    · right
      ext1
      exact h
  re_add_im_ax z := by exact congrArg ULift.up (RCLike.re_add_im_ax z.down)
  ofReal_re_ax r := by simp
  ofReal_im_ax := by simp
  mul_re_ax z w := by simp
  mul_im_ax := by simp
  conj_re_ax x := by simp
  conj_im_ax := by simp
  conj_I_ax := by ext1; simp
  norm_sq_eq_def_ax x := by simpa using RCLike.norm_sq_eq_def_ax x.down
  mul_im_I_ax := by simp
  le_iff_re_im {z w} := by simpa using RCLike.le_iff_re_im (z := z.down) (w := w.down)
