/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import AddCombi.Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Star

import AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
import AddCombi.Mathlib.Algebra.Star.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.Pointwise.Finset.Density
import Mathlib.Analysis.Complex.Basic


-- @@ L23-48 verbatim
/-!
# Convolution in the compact normalisation

This file defines several versions of the discrete convolution of functions with the compact
normalisation.

## Main declarations

* `conv`: Discrete convolution of two functions in the compact normalisation
* `dconv`: Discrete difference convolution of two functions in the compact normalisation
* `iterConv`: Iterated convolution of a function in the compact normalisation

## Notation

* `f ∗ g`: Convolution
* `f ○ g`: Difference convolution
* `f ∗^ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a division ring. Doesn't seem very useful given that
the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.
-/


-- @@ L50-50 verbatim
public section


-- @@ L52-52 verbatim
open Finset Fintype Function

-- @@ L53-54 verbatim
open scoped BigOperators ComplexConjugate NNReal Pointwise translate Indicator
  Combinatorics.Additive'


-- @@ L56-56 verbatim
local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a


-- @@ L58-58 verbatim
variable {G H K L : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]


-- @@ L60-60 verbatim
section Semifield

-- @@ L61-61 verbatim
variable [Semifield K] [CharZero K] {f g : G → K}


-- @@ L63-66 verbatim
/-- Compact convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b + c = a`. -/
@[expose] def conv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2


-- @@ L68-68 verbatim
@[inherit_doc] infixl:71 " ∗ " => conv


-- @@ L70-71 expanded
lemma conv_apply (f g : G → K) (a : G) :
    (conv f g) a = 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2 :=
  rfl


-- @@ L73-75 expanded
lemma conv_eq_smul_sum (f g : G → K) (a : G) :
    (conv f g) a = (Fintype.card G : ℚ≥0)⁻¹ • (∑ x : G × G with x.1 + x.2 = a, f x.1 * g x.2) := by
  simp [conv_apply, expect, ← univ_product_univ, card_add_eq]


-- @@ L77-77 expanded
@[simp]
lemma conv_zero (f : G → K) : conv f 0 = 0 := by ext; simp [conv_apply]


-- @@ L78-78 expanded
@[simp]
lemma zero_conv (f : G → K) : conv 0 f = 0 := by ext; simp [conv_apply]


-- @@ L80-81 expanded
lemma conv_add (f g h : G → K) : conv f (g + h) = conv f g + conv f h := by ext;
  simp [conv_apply, mul_add, expect_add_distrib]


-- @@ L83-84 expanded
lemma add_conv (f g h : G → K) : conv (f + g) h = conv f h + conv g h := by ext;
  simp [conv_apply, add_mul, expect_add_distrib]


-- @@ L86-90 expanded
lemma smul_conv [DistribSMul H K] [IsScalarTower H K K] [SMulCommClass H K K] (c : H)
    (f g : G → K) : conv (c • f) g = c • (conv f g) :=
  by
  have := SMulCommClass.symm H K K
  ext a
  simp only [Pi.smul_apply, smul_expect, conv_apply, smul_mul_assoc]


-- @@ L92-96 expanded
lemma conv_smul [DistribSMul H K] [SMulCommClass H K K] (c : H) (f g : G → K) :
    conv f (c • g) = c • (conv f g) :=
  by
  have := SMulCommClass.symm H K K
  ext a
  simp only [Pi.smul_apply, smul_expect, conv_apply, mul_smul_comm]


-- @@ L98-98 verbatim
alias smul_conv_assoc := smul_conv

-- @@ L99-99 verbatim
alias smul_conv_left_comm := conv_smul


-- @@ L101-103 expanded
@[simp]
lemma translate_conv (a : G) (f g : G → K) : conv (τ a f) g = τ a (conv f g) :=
  funext fun b ↦
    expect_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _) (by simp [sub_add_eq_add_sub])
      (by simp)


-- @@ L105-107 expanded
@[simp]
lemma conv_translate (a : G) (f g : G → K) : conv f (τ a g) = τ a (conv f g) :=
  funext fun b ↦
    expect_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a) (by simp [← add_sub_assoc])
      (by simp)


-- @@ L109-110 expanded
lemma conv_comm (f g : G → K) : conv f g = conv g f :=
  funext fun a ↦ Finset.expect_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp [mul_comm])


-- @@ L112-114 expanded
lemma mul_smul_conv_comm [Monoid H] [DistribMulAction H K] [IsScalarTower H K K]
    [SMulCommClass H K K] (c d : H) (f g : G → K) : (c * d) • (conv f g) = conv (c • f) (d • g) :=
  by rw [smul_conv, conv_smul, mul_smul]


-- @@ L116-122 expanded
lemma conv_assoc (f g h : G → K) : conv (conv f g) h = conv f (conv g h) :=
  by
  ext a
  simp only [conv_eq_smul_sum, mul_smul_comm, smul_mul_assoc, ← smul_sum, sum_mul, mul_sum,
    Finset.sum_sigma']
  congr! 2
  apply
      sum_nbij' (fun ⟨(_b, c), (d, e)⟩ ↦ ⟨(d, e + c), (e, c)⟩)
        (fun ⟨(b, _c), (d, e)⟩ ↦ ⟨(b + d, e), (b, d)⟩) <;>
    grind


-- @@ L124-125 expanded
lemma conv_right_comm (f g h : G → K) : conv (conv f g) h = conv (conv f h) g := by
  rw [conv_assoc, conv_assoc, conv_comm g]


-- @@ L127-128 expanded
lemma conv_left_comm (f g h : G → K) : conv f (conv g h) = conv g (conv f h) := by
  rw [← conv_assoc, ← conv_assoc, conv_comm g]


-- @@ L130-131 expanded
lemma conv_conv_conv_comm (f g h i : G → K) :
    conv (conv f g) (conv h i) = conv (conv f h) (conv g i) := by
  rw [conv_assoc, conv_assoc, conv_left_comm g]


-- @@ L133-135 expanded
lemma map_conv [Semifield L] [CharZero L] (m : K →+* L) (f g : G → K) (a : G) :
    m ((conv f g) a) = (conv (m ∘ f) (m ∘ g)) a := by
  simp_rw [conv_apply, map_expect, map_mul, Function.comp_apply]


-- @@ L137-138 expanded
lemma comp_conv [Semifield L] [CharZero L] (m : K →+* L) (f g : G → K) :
    m ∘ (conv f g) = conv (m ∘ f) (m ∘ g) :=
  funext <| map_conv _ _ _


-- @@ L140-145 expanded
lemma conv_eq_expect_sub (f g : G → K) (a : G) : (conv f g) a = 𝔼 t, f (a - t) * g t :=
  by
  rw [conv_apply]
  refine
    expect_nbij (fun x ↦ x.2) (fun x _ ↦ mem_univ _) ?_ ?_ fun b _ ↦
      ⟨(a - b, b), mem_filter.2 ⟨mem_univ _, sub_add_cancel _ _⟩, rfl⟩
  any_goals unfold Set.InjOn
  all_goals aesop


-- @@ L147-149 expanded
lemma conv_eq_expect_add (f g : G → K) (a : G) : (conv f g) a = 𝔼 t, f (a + t) * g (-t) :=
  (conv_eq_expect_sub _ _ _).trans <|
    Fintype.expect_equiv (Equiv.neg _) _ _ fun t ↦ by
      simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]


-- @@ L151-152 expanded
lemma conv_eq_expect_sub' (f g : G → K) (a : G) : (conv f g) a = 𝔼 t, f t * g (a - t) := by
  rw [conv_comm, conv_eq_expect_sub]; grind


-- @@ L154-155 expanded
lemma conv_eq_expect_add' (f g : G → K) (a : G) : (conv f g) a = 𝔼 t, f (-t) * g (a + t) := by
  rw [conv_comm, conv_eq_expect_add]; grind


-- @@ L157-159 expanded
lemma conv_apply_add (f g : G → K) (a b : G) : (conv f g) (a + b) = 𝔼 t, f (a + t) * g (b - t) :=
  (conv_eq_expect_sub _ _ _).trans <|
    Fintype.expect_equiv (Equiv.subLeft b) _ _ fun t ↦ by simp [add_sub_assoc]


-- @@ L161-165 expanded
lemma expect_conv_mul (f g h : G → K) : 𝔼 a, (conv f g) a * h a = 𝔼 a, 𝔼 b, f a * g b * h (a + b) :=
  by
  simp_rw [conv_eq_expect_sub', expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subRight x) _ _ fun y ↦ by simp


-- @@ L167-168 expanded
lemma expect_conv (f g : G → K) : 𝔼 a, (conv f g) a = (𝔼 a, f a) * 𝔼 a, g a := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_conv_mul f g 1


-- @@ L170-171 expanded
@[simp]
lemma conv_const (f : G → K) (b : K) : conv f (const _ b) = const _ ((𝔼 x, f x) * b) := by ext;
  simp [conv_eq_expect_sub', expect_mul]


-- @@ L173-174 expanded
@[simp]
lemma const_conv (b : K) (f : G → K) : conv (const _ b) f = const _ (b * 𝔼 x, f x) := by ext;
  simp [conv_eq_expect_sub, mul_expect]


-- @@ L176-179 expanded
lemma support_conv_subset (f g : G → K) : support (conv f g) ⊆ support f + support g :=
  by
  rintro a ha
  obtain ⟨x, hx, h⟩ := exists_ne_zero_of_expect_ne_zero ha
  exact ⟨_, left_ne_zero_of_mul h, _, right_ne_zero_of_mul h, (mem_filter.1 hx).2⟩


-- @@ L181-183 expanded
lemma indicator_one_conv (s : Finset G) (f : G → K) :
    conv (Set.indicator s fun _ ↦ (1 : _)) f = (Fintype.card G : ℚ≥0)⁻¹ • (∑ a ∈ s, τ a f) := by
  ext; simp [conv_eq_expect_sub', Set.indicator_apply, expect]


-- @@ L185-187 expanded
lemma conv_indicator_one (f : G → K) (s : Finset G) :
    conv f (Set.indicator s fun _ ↦ (1 : _)) = (Fintype.card G : ℚ≥0)⁻¹ • (∑ a ∈ s, τ a f) := by
  ext; simp [conv_eq_expect_sub, Set.indicator_apply, expect]


-- @@ L189-194 expanded
lemma indicator_one_conv_indicator_one_eq_dens (s t : Finset G) (a : G) :
    (conv (Set.indicator s fun _ ↦ (1 : K)) (Set.indicator t fun _ ↦ (1 : _))) a =
      (s ∩ (a +ᵥ -t)).dens :=
  by
  rw [← dens_vadd_finset (-a), ← dens_neg, inter_comm, neg_vadd_finset_distrib, neg_inter,
    vadd_finset_inter]
  simp [conv_indicator_one, Set.indicator_apply, NNRat.smul_def, dens, div_eq_inv_mul,
    ← filter_mem_eq_inter, ← neg_vadd_mem_iff, sub_eq_add_neg]


-- @@ L196-196 verbatim
variable [StarRing K]


-- @@ L198-202 verbatim
/-- Compact difference convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b - c = a`. -/
@[expose]
def dconv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2


-- @@ L204-204 verbatim
@[inherit_doc] infixl:71 " ○ " => dconv


-- @@ L206-207 expanded
lemma dconv_apply (f g : G → K) (a : G) :
    (dconv f g) a = 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2 :=
  rfl


-- @@ L209-211 expanded
lemma dconv_eq_smul_sum (f g : G → K) (a : G) :
    (dconv f g) a =
      (Fintype.card G : ℚ≥0)⁻¹ • (∑ x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2) :=
  by simp [dconv_apply, expect, ← univ_product_univ, card_sub_eq]


-- @@ L213-216 expanded
@[simp]
lemma conv_conjneg (f g : G → K) : conv f (conjneg g) = dconv f g :=
  funext fun a ↦
    expect_bij (fun x _ ↦ (x.1, -x.2)) (fun x hx ↦ by simpa using hx) (fun x _ ↦ rfl)
      (fun x y _ _ h ↦ by grind) fun x hx ↦ ⟨(x.1, -x.2), by grind, by simp⟩


-- @@ L218-219 expanded
@[simp]
lemma dconv_conjneg (f g : G → K) : dconv f (conjneg g) = conv f g := by
  rw [← conv_conjneg, conjneg_conjneg]


-- @@ L221-223 expanded
@[simp]
lemma translate_dconv (a : G) (f g : G → K) : dconv (τ a f) g = τ a (dconv f g) :=
  funext fun b ↦
    expect_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _) (by simp [sub_right_comm _ a])
      (by simp)


-- @@ L225-227 expanded
@[simp]
lemma dconv_translate (a : G) (f g : G → K) : dconv f (τ a g) = τ (-a) (dconv f g) :=
  funext fun b ↦
    expect_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
      (by simp [sub_sub_eq_add_sub, ← sub_add_eq_add_sub]) (by simp)


-- @@ L229-230 expanded
@[simp]
lemma conj_conv (f g : G → K) : conj (conv f g) = conv (conj f) (conj g) :=
  funext fun a ↦ by simp only [Pi.conj_apply, conv_apply, map_expect, map_mul]


-- @@ L232-233 expanded
@[simp]
lemma conj_dconv (f g : G → K) : conj (dconv f g) = dconv (conj f) (conj g) := by
  simp_rw [← conv_conjneg, conj_conv, conjneg_conj]


-- @@ L235-236 expanded
lemma IsSelfAdjoint.conv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (conv f g) :=
  (conj_conv _ _).trans <| congr_arg₂ _ hf hg


-- @@ L238-239 expanded
lemma IsSelfAdjoint.dconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) :
    IsSelfAdjoint (dconv f g) :=
  (conj_dconv _ _).trans <| congr_arg₂ _ hf hg


-- @@ L241-245 expanded
@[simp]
lemma conjneg_conv (f g : G → K) : conjneg (conv f g) = conv (conjneg f) (conjneg g) :=
  by
  funext a
  simp only [conv_apply, conjneg_apply, map_expect, map_mul]
  exact
    Finset.expect_equiv (Equiv.neg (G × G)) (by simp [eq_comm, ← neg_eq_iff_eq_neg, add_comm])
      (by simp)


-- @@ L247-248 expanded
@[simp]
lemma conjneg_dconv (f g : G → K) : conjneg (dconv f g) = dconv g f := by
  simp_rw [← conv_conjneg, conjneg_conv, conjneg_conjneg, conv_comm]


-- @@ L250-250 expanded
@[simp]
lemma dconv_zero (f : G → K) : dconv f 0 = 0 := by simp [← conv_conjneg]


-- @@ L251-251 expanded
@[simp]
lemma zero_dconv (f : G → K) : dconv 0 f = 0 := by rw [← conv_conjneg]; simp [-conv_conjneg]


-- @@ L253-254 expanded
lemma dconv_add (f g h : G → K) : dconv f (g + h) = dconv f g + dconv f h := by
  simp_rw [← conv_conjneg, conjneg_add, conv_add]


-- @@ L256-257 expanded
lemma add_dconv (f g h : G → K) : dconv (f + g) h = dconv f h + dconv g h := by
  simp_rw [← conv_conjneg, add_conv]


-- @@ L259-263 expanded
lemma smul_dconv [DistribSMul H K] [IsScalarTower H K K] [SMulCommClass H K K] (c : H)
    (f g : G → K) : dconv (c • f) g = c • (dconv f g) :=
  by
  have := SMulCommClass.symm H K K
  ext a
  simp only [Pi.smul_apply, smul_expect, dconv_apply, smul_mul_assoc]


-- @@ L265-269 expanded
lemma dconv_smul [Star H] [DistribSMul H K] [SMulCommClass H K K] [StarModule H K] (c : H)
    (f g : G → K) : dconv f (c • g) = star c • (dconv f g) :=
  by
  have := SMulCommClass.symm H K K
  ext a
  simp only [Pi.smul_apply, smul_expect, dconv_apply, mul_smul_comm, starRingEnd_apply, star_smul]


-- @@ L271-271 verbatim
alias smul_dconv_assoc := smul_dconv

-- @@ L272-272 verbatim
alias smul_dconv_left_comm := dconv_smul


-- @@ L274-275 expanded
lemma conv_dconv_conv_comm (f g h i : G → K) :
    dconv (conv f g) (conv h i) = conv (dconv f h) (dconv g i) := by
  simp_rw [← conv_conjneg, conjneg_conv, conv_conv_conv_comm]


-- @@ L277-278 expanded
lemma dconv_conv_dconv_comm (f g h i : G → K) :
    conv (dconv f g) (dconv h i) = dconv (conv f h) (conv g i) :=
  (conv_dconv_conv_comm f h g i).symm


-- @@ L280-286 expanded
lemma dconv_dconv_dconv_comm (f g h i : G → K) :
    dconv (dconv f g) (dconv h i) = dconv (dconv f h) (dconv g i) := by
  simp_rw [← conv_conjneg, conjneg_conv, conv_conv_conv_comm]
    --TODO: Can we generalise to star ring homs?
    -- lemma map_dconv (f g : G → ℝ≥0) (a : G) : (↑((f ○ g) a) : ℝ) = ((↑) ∘ f ○ (↑) ∘ g) a := by
    --   simp_rw [dconv_apply, NNReal.coe_expect, NNReal.coe_mul, starRingEnd_apply, star_trivial,
    --     Function.comp_apply]


-- @@ L288-289 expanded
lemma dconv_eq_expect_add (f g : G → K) (a : G) : (dconv f g) a = 𝔼 t, f (a + t) * conj (g t) := by
  simp [← conv_conjneg, conv_eq_expect_add]


-- @@ L291-292 expanded
lemma dconv_eq_expect_sub (f g : G → K) (a : G) : (dconv f g) a = 𝔼 t, f t * conj (g (t - a)) := by
  simp [← conv_conjneg, conv_eq_expect_sub']


-- @@ L294-295 expanded
lemma dconv_apply_neg (f g : G → K) (a : G) : (dconv f g) (-a) = conj ((dconv g f) a) := by
  rw [← conjneg_dconv f, conjneg_apply, Complex.conj_conj]


-- @@ L297-299 expanded
lemma dconv_apply_sub (f g : G → K) (a b : G) :
    (dconv f g) (a - b) = 𝔼 t, f (a + t) * conj (g (b + t)) := by
  simp [← conv_conjneg, sub_eq_add_neg, conv_apply_add, add_comm]


-- @@ L301-305 expanded
lemma expect_dconv_mul (f g h : G → K) :
    𝔼 a, (dconv f g) a * h a = 𝔼 a, 𝔼 b, f a * conj (g b) * h (a - b) :=
  by
  simp_rw [dconv_eq_expect_sub, expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp


-- @@ L307-308 expanded
lemma expect_dconv (f g : G → K) : 𝔼 a, (dconv f g) a = (𝔼 a, f a) * 𝔼 a, conj (g a) := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_dconv_mul f g 1


-- @@ L310-312 expanded
@[simp]
lemma dconv_const (f : G → K) (b : K) : dconv f (const _ b) = const _ ((𝔼 x, f x) * conj b) := by
  ext; simp [dconv_eq_expect_sub, expect_mul]


-- @@ L314-316 expanded
@[simp]
lemma const_dconv (b : K) (f : G → K) : dconv (const _ b) f = const _ (b * 𝔼 x, conj (f x)) := by
  ext; simp [dconv_eq_expect_add, mul_expect]


-- @@ L318-319 expanded
lemma support_dconv_subset (f g : G → K) : support (dconv f g) ⊆ support f - support g := by
  simpa [sub_eq_add_neg] using support_conv_subset f (conjneg g)


-- @@ L321-323 expanded
lemma indicator_one_dconv (s : Finset G) (f : G → K) :
    dconv (Set.indicator s fun _ ↦ (1 : _)) f =
      (Fintype.card G : ℚ≥0)⁻¹ • (∑ a ∈ s, τ a (conjneg f)) :=
  by ext; simp [dconv_eq_expect_sub, Set.indicator_apply, expect]


-- @@ L325-327 expanded
lemma dconv_indicator_one (f : G → K) (s : Finset G) :
    dconv f (Set.indicator s fun _ ↦ (1 : _)) = (Fintype.card G : ℚ≥0)⁻¹ • (∑ a ∈ s, τ (-a) f) := by
  ext; simp [dconv_eq_expect_add, Set.indicator_apply, expect]


-- @@ L329-333 expanded
lemma indicator_one_dconv_indicator_one_eq_dens (s t : Finset G) (a : G) :
    (dconv (Set.indicator s fun _ ↦ (1 : K)) (Set.indicator t fun _ ↦ (1 : _))) a =
      (s ∩ (a +ᵥ t)).dens :=
  by
  rw [← dens_vadd_finset (-a), inter_comm, vadd_finset_inter]
  simp [dconv_indicator_one, Set.indicator_apply, NNRat.smul_def, dens, div_eq_inv_mul,
    ← filter_mem_eq_inter, ← neg_vadd_mem_iff, sub_eq_add_neg]


-- @@ L335-338 expanded
lemma indicator_one_dconv_indicator_one_eq_addConvolution_div (s t : Finset G) (a : G) :
    (dconv (Set.indicator s fun _ ↦ (1 : K)) (Set.indicator t fun _ ↦ (1 : _))) a =
      s.addConvolution (-t) a / card G :=
  by
  rw [indicator_one_dconv_indicator_one_eq_dens, dens, card_inter_vadd]
  simp


-- @@ L340-342 expanded
lemma expect_indicator_one_dconv_indicator_one (s t : Finset G) :
    𝔼 a, (dconv (Set.indicator (s : Set G) fun _ ↦ (1 : K)) (Set.indicator t fun _ ↦ (1 : _))) a =
      s.dens * t.dens :=
  by simp [expect_dconv, Set.conj_indicator_one_apply]; simp [← Pi.one_def]


-- @@ L344-356 expanded
lemma expect_indicator_one_dconv_indicator_sq (s t : Finset G) :
    𝔼 x,
        (dconv (Set.indicator (s : Set G) fun _ ↦ (1 : K)) (Set.indicator t fun _ ↦ (1 : _))) x ^
          2 =
      Finset.addEnergy' s t :=
  by
  suffices
    ∑ x, #({yz ∈ s ×ˢ t | yz.1 - yz.2 = x}) ^ 2 =
      #({x ∈ (s ×ˢ s) ×ˢ t ×ˢ t | x.1.1 + x.2.1 = x.1.2 + x.2.2})
    by
    simp only [expect, card_univ, indicator_one_dconv_indicator_one_eq_dens, dens, NNRat.cast_div,
      NNRat.cast_natCast, sq, div_mul_div_comm, ← sum_div, NNRat.smul_def, NNRat.cast_inv,
      addEnergy', NNRat.cast_pow, card_inter_vadd, ← card_sub_eq]
    field_simp
    norm_cast
  simp only [card_eq_sum_ones, sq, Finset.sum_mul_sum, sum_filter, sum_product, boole_mul,
    univ.sum_comm, Finset.sum_ite_eq, mem_univ, ite_true, sub_eq_sub_iff_add_eq_add]
  exact sum_comm


-- @@ L358-358 verbatim
end Semifield


-- @@ L360-360 verbatim
section Field

-- @@ L361-361 verbatim
variable [Field K] [CharZero K]


-- @@ L363-363 expanded
@[simp]
lemma conv_neg (f g : G → K) : conv f (-g) = -(conv f g) := by ext; simp [conv_apply]


-- @@ L364-364 expanded
@[simp]
lemma neg_conv (f g : G → K) : conv (-f) g = -(conv f g) := by ext; simp [conv_apply]


-- @@ L366-367 expanded
lemma conv_sub (f g h : G → K) : conv f (g - h) = conv f g - conv f h := by
  simp only [sub_eq_add_neg, conv_add, conv_neg]


-- @@ L369-370 expanded
lemma sub_conv (f g h : G → K) : conv (f - g) h = conv f h - conv g h := by
  simp only [sub_eq_add_neg, add_conv, neg_conv]


-- @@ L372-373 expanded
@[simp]
lemma balance_conv (f g : G → K) : balance (conv f g) = conv (balance f) (balance g) := by
  simp [balance, conv_sub, sub_conv, expect_conv, expect_sub_distrib]


-- @@ L375-375 verbatim
variable [StarRing K]


-- @@ L377-377 expanded
@[simp]
lemma dconv_neg (f g : G → K) : dconv f (-g) = -(dconv f g) := by ext; simp [dconv_apply]


-- @@ L378-378 expanded
@[simp]
lemma neg_dconv (f g : G → K) : dconv (-f) g = -(dconv f g) := by ext; simp [dconv_apply]


-- @@ L380-381 expanded
lemma dconv_sub (f g h : G → K) : dconv f (g - h) = dconv f g - dconv f h := by
  simp only [sub_eq_add_neg, dconv_add, dconv_neg]


-- @@ L383-384 expanded
lemma sub_dconv (f g h : G → K) : dconv (f - g) h = dconv f h - dconv g h := by
  simp only [sub_eq_add_neg, add_dconv, neg_dconv]


-- @@ L386-387 expanded
@[simp]
lemma balance_dconv (f g : G → K) : balance (dconv f g) = dconv (balance f) (balance g) := by
  simp [balance, dconv_sub, sub_dconv, expect_dconv, map_expect, expect_sub_distrib]


-- @@ L389-389 verbatim
end Field


-- @@ L391-391 verbatim
namespace RCLike

-- @@ L392-392 verbatim
variable {𝕜 : Type} [RCLike 𝕜] (f g : G → ℝ) (a : G)


-- @@ L394-395 expanded
@[simp, norm_cast]
lemma coe_conv : (conv f g) a = (conv ((↑) ∘ f) ((↑) ∘ g) : G → 𝕜) a :=
  map_conv (algebraMap ℝ 𝕜) ..


-- @@ L397-398 expanded
@[simp, norm_cast]
lemma coe_dconv : (dconv f g) a = (dconv ((↑) ∘ f) ((↑) ∘ g) : G → 𝕜) a := by simp [dconv_apply]


-- @@ L400-401 expanded
@[simp]
lemma coe_comp_conv : ofReal ∘ (conv f g) = (conv ((↑) ∘ f) ((↑) ∘ g) : G → 𝕜) :=
  funext <| coe_conv _ _


-- @@ L403-404 expanded
@[simp]
lemma coe_comp_dconv : ofReal ∘ (dconv f g) = (dconv ((↑) ∘ f) ((↑) ∘ g) : G → 𝕜) :=
  funext <| coe_dconv _ _


-- @@ L406-406 verbatim
end RCLike


-- @@ L408-408 verbatim
namespace Complex

-- @@ L409-409 verbatim
variable (f g : G → ℝ) (a : G)


-- @@ L411-412 expanded
@[simp, norm_cast]
lemma coe_conv : (conv f g) a = (conv ((↑) ∘ f) ((↑) ∘ g) : G → ℂ) a :=
  RCLike.coe_conv _ _ _


-- @@ L414-415 expanded
@[simp, norm_cast]
lemma coe_dconv : (dconv f g) a = (dconv ((↑) ∘ f) ((↑) ∘ g) : G → ℂ) a :=
  RCLike.coe_dconv _ _ _


-- @@ L417-418 expanded
@[simp]
lemma ofReal_comp_conv : ofReal ∘ (conv f g) = (conv ((↑) ∘ f) ((↑) ∘ g) : G → ℂ) :=
  funext <| coe_conv _ _


-- @@ L420-421 expanded
@[simp]
lemma ofReal_comp_dconv : ofReal ∘ (dconv f g) = (dconv ((↑) ∘ f) ((↑) ∘ g) : G → ℂ) :=
  funext <| coe_dconv _ _


-- @@ L423-423 verbatim
end Complex


-- @@ L425-425 verbatim
namespace NNReal

-- @@ L426-426 verbatim
variable (f g : G → ℝ≥0) (a : G)


-- @@ L428-429 expanded
@[simp, norm_cast]
lemma coe_conv : (conv f g) a = (conv ((↑) ∘ f) ((↑) ∘ g) : G → ℝ) a :=
  map_conv NNReal.toRealHom _ _ _


-- @@ L431-432 expanded
@[simp, norm_cast]
lemma coe_dconv : (dconv f g) a = (dconv ((↑) ∘ f) ((↑) ∘ g) : G → ℝ) a := by
  simp [dconv_apply, coe_expect]


-- @@ L434-435 expanded
@[simp]
lemma coe_comp_conv : ((↑) : _ → ℝ) ∘ (conv f g) = conv ((↑) ∘ f) ((↑) ∘ g) :=
  funext <| coe_conv _ _


-- @@ L437-438 expanded
@[simp]
lemma coe_comp_dconv : ((↑) : _ → ℝ) ∘ (dconv f g) = dconv ((↑) ∘ f) ((↑) ∘ g) :=
  funext <| coe_dconv _ _


-- @@ L440-440 verbatim
end NNReal
