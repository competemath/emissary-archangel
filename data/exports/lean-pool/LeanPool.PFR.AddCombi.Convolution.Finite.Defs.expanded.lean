/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

module
public import LeanPool.PFR.AddCombi.Mathlib.Algebra.Notation.Indicator
public import LeanPool.PFR.AddCombi.Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Star.SelfAdjoint
import LeanPool.PFR.AddCombi.Mathlib.Algebra.Star.Pi
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Group.Pointwise.Finset.Density
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset


-- @@ L25-50 verbatim
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


-- @@ L63-68 verbatim
/-- Compact convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b + c = a`. -/
@[expose]
public
def conv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2


-- @@ L70-70 verbatim
@[inherit_doc] infixl:71 " ∗ " => conv


-- @@ L72-74 expanded
public lemma conv_apply (f g : G → K) (a : G) :
    (conv f g) a = 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2 :=
  rfl


-- @@ L76-78 expanded
public lemma conv_comm (f g : G → K) : conv f g = conv g f :=
  funext fun a ↦ Finset.expect_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp [mul_comm])


-- @@ L80-86 expanded
public lemma conv_eq_expect_sub (f g : G → K) (a : G) : (conv f g) a = 𝔼 t, f (a - t) * g t :=
  by
  rw [conv_apply]
  refine
    expect_nbij (fun x ↦ x.2) (fun x _ ↦ mem_univ _) ?_ ?_ fun b _ ↦
      ⟨(a - b, b), mem_filter.2 ⟨mem_univ _, sub_add_cancel _ _⟩, rfl⟩
  any_goals unfold Set.InjOn
  all_goals aesop


-- @@ L88-91 expanded
public lemma conv_eq_expect_add (f g : G → K) (a : G) : (conv f g) a = 𝔼 t, f (a + t) * g (-t) :=
  (conv_eq_expect_sub _ _ _).trans <|
    Fintype.expect_equiv (Equiv.neg _) _ _ fun t ↦ by
      simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]


-- @@ L93-95 expanded
public lemma conv_eq_expect_sub' (f g : G → K) (a : G) : (conv f g) a = 𝔼 t, f t * g (a - t) := by
  rw [conv_comm, conv_eq_expect_sub]; grind


-- @@ L97-100 expanded
public lemma conv_apply_add (f g : G → K) (a b : G) :
    (conv f g) (a + b) = 𝔼 t, f (a + t) * g (b - t) :=
  (conv_eq_expect_sub _ _ _).trans <|
    Fintype.expect_equiv (Equiv.subLeft b) _ _ fun t ↦ by simp [add_sub_assoc]


-- @@ L102-102 verbatim
variable [StarRing K]


-- @@ L104-109 verbatim
/-- Compact difference convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b - c = a`. -/
@[expose]
public
def dconv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2


-- @@ L111-111 verbatim
@[inherit_doc] infixl:71 " ○ " => dconv


-- @@ L113-118 expanded
@[simp]
public lemma conv_conjneg (f g : G → K) : conv f (conjneg g) = dconv f g :=
  funext fun a ↦
    expect_bij (fun x _ ↦ (x.1, -x.2)) (fun x hx ↦ by simpa using hx) (fun x _ ↦ rfl)
      (fun x y _ _ h ↦ by grind) fun x hx ↦ ⟨(x.1, -x.2), by grind, by simp⟩


-- @@ L120-123 expanded
@[simp]
public lemma conj_conv (f g : G → K) : conj (conv f g) = conv (conj f) (conj g) :=
  funext fun a ↦ by simp only [Pi.conj_apply, conv_apply, map_expect, map_mul]


-- @@ L125-128 expanded
@[simp]
public lemma conj_dconv (f g : G → K) : conj (dconv f g) = dconv (conj f) (conj g) := by
  simp_rw [← conv_conjneg, conj_conv, conjneg_conj]


-- @@ L130-132 expanded
public lemma IsSelfAdjoint.conv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) :
    IsSelfAdjoint (conv f g) :=
  (conj_conv _ _).trans <| congr_arg₂ _ hf hg


-- @@ L134-141 expanded
public lemma IsSelfAdjoint.dconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) :
    IsSelfAdjoint (dconv f g) :=
  (conj_dconv _ _).trans <| congr_arg₂ _ hf hg


-- @@ L143-145 expanded
public lemma dconv_eq_expect_add (f g : G → K) (a : G) :
    (dconv f g) a = 𝔼 t, f (a + t) * conj (g t) := by simp [← conv_conjneg, conv_eq_expect_add]


-- @@ L147-149 expanded
public lemma dconv_eq_expect_sub (f g : G → K) (a : G) :
    (dconv f g) a = 𝔼 t, f t * conj (g (t - a)) := by simp [← conv_conjneg, conv_eq_expect_sub']


-- @@ L151-156 expanded
public lemma expect_dconv_mul (f g h : G → K) :
    𝔼 a, (dconv f g) a * h a = 𝔼 a, 𝔼 b, f a * conj (g b) * h (a - b) :=
  by
  simp_rw [dconv_eq_expect_sub, expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp


-- @@ L158-160 expanded
public lemma expect_dconv (f g : G → K) : 𝔼 a, (dconv f g) a = (𝔼 a, f a) * 𝔼 a, conj (g a) := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_dconv_mul f g 1


-- @@ L162-165 expanded
public lemma dconv_indicator_one (f : G → K) (s : Finset G) :
    dconv f (Set.indicator s fun _ ↦ (1 : _)) = (Fintype.card G : ℚ≥0)⁻¹ • (∑ a ∈ s, τ (-a) f) := by
  ext; simp [dconv_eq_expect_add, Set.indicator_apply, expect]


-- @@ L167-172 expanded
public lemma indicator_one_dconv_indicator_one_eq_dens (s t : Finset G) (a : G) :
    (dconv (Set.indicator s fun _ ↦ (1 : K)) (Set.indicator t fun _ ↦ (1 : _))) a =
      (s ∩ (a +ᵥ t)).dens :=
  by
  rw [← dens_vadd_finset (-a), inter_comm, vadd_finset_inter]
  simp [dconv_indicator_one, Set.indicator_apply, NNRat.smul_def, dens, div_eq_inv_mul,
    ← filter_mem_eq_inter, ← neg_vadd_mem_iff, sub_eq_add_neg]


-- @@ L174-178 expanded
public lemma indicator_one_dconv_indicator_one_eq_addConvolution_div (s t : Finset G) (a : G) :
    (dconv (Set.indicator s fun _ ↦ (1 : K)) (Set.indicator t fun _ ↦ (1 : _))) a =
      s.addConvolution (-t) a / card G :=
  by
  rw [indicator_one_dconv_indicator_one_eq_dens, dens, card_inter_vadd]
  simp


-- @@ L180-183 expanded
public lemma expect_indicator_one_dconv_indicator_one (s t : Finset G) :
    𝔼 a, (dconv (Set.indicator (s : Set G) fun _ ↦ (1 : K)) (Set.indicator t fun _ ↦ (1 : _))) a =
      s.dens * t.dens :=
  by simp [expect_dconv, Set.conj_indicator_one_apply]; simp [← Pi.one_def]


-- @@ L185-198 expanded
public lemma expect_indicator_one_dconv_indicator_sq (s t : Finset G) :
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


-- @@ L200-200 verbatim
end Semifield
