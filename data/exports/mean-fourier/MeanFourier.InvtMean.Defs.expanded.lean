/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Analysis.Complex.Basic
public import MeanFourier.Mathlib.Analysis.Normed.Group.Pointwise
public import MeanFourier.Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import MeanFourier.Translate


-- @@ L14-16 verbatim
/-!
# Invariant means
-/


-- @@ L18-18 verbatim
public section


-- @@ L20-20 verbatim
open Bornology

-- @@ L21-21 verbatim
open scoped ComplexOrder Indicator


-- @@ L23-24 verbatim
variable {G 𝕜 E R : Type*} [Group G] [RCLike 𝕜] [NormedAddCommGroup E] [PartialOrder E]
  [NormedSpace 𝕜 E]


-- @@ L26-41 expanded
variable (G 𝕜 E) [NormedAddCommGroup E] [PartialOrder E] [NormedSpace 𝕜 E] in
structure InvtMean where
  IsMeasFun : (G → E) → Prop
  isMeasFun_const (z : E) : IsMeasFun fun _ ↦ z := by fun_prop
  isMeasFun_add (f : G → E) (hf : IsMeasFun f) (g : G → E) (hg : IsMeasFun g) :
    IsMeasFun (f + g) := by fun_prop
  isMeasFun_smul (c : 𝕜) (f : G → E) (hf : IsMeasFun f) : IsMeasFun (c • f) := by fun_prop
  isMeasFun_translate (x : G) (f : G → E) (hf : IsMeasFun f) : IsMeasFun ((translate x) f) := by
    fun_prop
  isBddFun_of_isMeasFun (f : G → E) (hf : IsMeasFun f) : IsBddFun f := by fun_prop
  toFun : (G → E) → E
  map_zero : toFun 0 = 0
  map_add (f : G → E) (hf : IsMeasFun f) (g : G → E) (hg : IsMeasFun g) :
    toFun (f + g) = toFun f + toFun g
  map_smul (f : G → E) (hf : IsMeasFun f) (c : 𝕜) : toFun (c • f) = c • toFun f
  map_nonneg (f : G → E) (hf₀ : 0 ≤ f) (hf : IsMeasFun f) : 0 ≤ toFun f
  map_translate (f : G → E) (hf : IsMeasFun f) (x : G) : toFun ((translate x) f) = toFun f


-- @@ L43-43 verbatim
namespace InvtMean

-- @@ L44-44 verbatim
section NormedAddCommGroup

-- @@ L45-45 verbatim
variable {m : InvtMean G 𝕜 E} {f g : G → E} {A : Set G} {x : G} {c : 𝕜} {z : E}


-- @@ L47-47 verbatim
instance : CoeFun (InvtMean G 𝕜 E) fun _ ↦ (G → E) → E where coe := toFun


-- @@ L49-49 verbatim
initialize_simps_projections InvtMean (toFun → apply, as_prefix IsMeasFun)


-- @@ L51-51 verbatim
attribute [fun_prop] IsMeasFun


-- @@ L53-54 verbatim
@[to_fun (attr := fun_prop, simp)]
lemma IsMeasFun.const : m.IsMeasFun (Function.const G z) := m.isMeasFun_const _


-- @@ L56-56 verbatim
@[fun_prop, simp] protected lemma IsMeasFun.zero : m.IsMeasFun 0 := .const


-- @@ L58-60 verbatim
@[to_fun (attr := fun_prop)]
protected lemma IsMeasFun.add (hf : m.IsMeasFun f) (hg : m.IsMeasFun g) : m.IsMeasFun (f + g) :=
  m.isMeasFun_add _ hf _ hg


-- @@ L62-63 verbatim
@[fun_prop]
protected lemma IsMeasFun.smul (hf : m.IsMeasFun f) : m.IsMeasFun (c • f) := m.isMeasFun_smul _ _ hf


-- @@ L65-66 expanded
protected lemma IsMeasFun.translate (hf : m.IsMeasFun f) : m.IsMeasFun ((translate x) f) :=
  m.isMeasFun_translate _ _ hf


-- @@ L68-70 verbatim
@[to_fun (attr := fun_prop)]
protected lemma IsMeasFun.neg (hf : m.IsMeasFun f) : m.IsMeasFun (-f) := by
  simpa using hf.smul (c := -1)


-- @@ L72-75 verbatim
@[to_fun (attr := simp)]
lemma isMeasFun_neg : m.IsMeasFun (-f) ↔ m.IsMeasFun f where
  mp hf := by simpa using hf.neg
  mpr := .neg


-- @@ L77-78 verbatim
@[fun_prop]
lemma IsMeasFun.isBddFun (hf : m.IsMeasFun f) : IsBddFun f := m.isBddFun_of_isMeasFun _ hf


-- @@ L80-80 verbatim
end NormedAddCommGroup


-- @@ L82-82 verbatim
section NormedRing

-- @@ L83-83 verbatim
variable [NormedRing R] [PartialOrder R] [NormedSpace 𝕜 R] {m : InvtMean G 𝕜 R}


-- @@ L85-85 verbatim
@[fun_prop, simp] lemma IsMeasFun.natCast {n : ℕ} : m.IsMeasFun n := .const

-- @@ L86-86 verbatim
@[fun_prop, simp] lemma IsMeasFun.intCast {n : ℤ} : m.IsMeasFun n := .const

-- @@ L87-87 verbatim
@[fun_prop, simp] protected lemma IsMeasFun.one : m.IsMeasFun 1 := .const


-- @@ L89-90 verbatim
@[fun_prop, simp]
protected lemma IsMeasFun.ofNat {n : ℕ} [n.AtLeastTwo] : m.IsMeasFun ofNat(n) := .const


-- @@ L92-94 verbatim
variable (m A) in
/-- A set `A` is `m`-measurable if `𝟭_[A]` is `m`-measurable. -/
@[expose] def IsMeasSet : Prop := m.IsMeasFun 𝟭_[A]


-- @@ L96-96 verbatim
end NormedRing


-- @@ L98-98 verbatim
section Complex

-- @@ L99-99 verbatim
variable {m : InvtMean G ℂ ℂ} {f g : G → ℂ}


-- @@ L101-103 verbatim
variable (m) in
@[expose]
def real (f : G → ℝ) : ℝ := (m fun g ↦ f g).re


-- @@ L105-109 verbatim
@[simp] lemma real_mk (IsMeasFun isMeasFun_const isMeasFun_add isMeasFun_smul isMeasFun_translate
    isBddFun_of_isMeasFun toFun map_zero map_add map_smul map_nonneg map_translate) (f : G → ℝ) :
    (mk IsMeasFun isMeasFun_const isMeasFun_add isMeasFun_smul isMeasFun_translate
      isBddFun_of_isMeasFun toFun map_zero map_add map_smul map_nonneg map_translate).real f
      = (toFun fun g ↦ f g).re := rfl


-- @@ L111-111 verbatim
instance : CoeFun (InvtMean G ℂ ℂ) fun _ ↦ (G → ℝ) → ℝ where coe := real


-- @@ L113-114 verbatim
variable (m) in
def l2 : Set (G → E) := {f | m.IsMeasFun fun g ↦ ‖f g‖ ^ 2}


-- @@ L116-116 verbatim
notation3 "L^2(" m ")" => l2 m


-- @@ L118-119 verbatim
variable (m f) in
noncomputable def l2Norm : ℝ := √(m fun g ↦ ‖f g‖ ^ 2)


-- @@ L121-123 verbatim
variable (m A) in
@[simp] lemma l2Norm_indicator_one : m.l2Norm 𝟭_[A] = √(m 𝟭_[A]) := by
  classical simp [l2Norm, Set.indicator_apply, apply_ite, norm_one, real]


-- @@ L125-125 verbatim
end Complex

-- @@ L126-126 verbatim
end InvtMean
