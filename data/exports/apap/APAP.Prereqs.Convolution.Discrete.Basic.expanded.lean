module

public import APAP.Mathlib.Algebra.Star.Conjneg
public import APAP.Prereqs.Mu
public import APAP.Prereqs.Convolution.Discrete.Defs

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators
import Mathlib.Analysis.Complex.Order


-- @@ L11-39 verbatim
/-!
# Convolution

This file defines several versions of the discrete convolution of functions.

## Main declarations

* `ddconv`: Discrete convolution of two functions
* `dddconv`: Discrete difference convolution of two functions
* `iterConv`: Iterated convolution of a function

## Notation

* `f ∗ᵈ g`: Convolution
* `f ○ᵈ g`: Difference convolution
* `f ∗ᵈ^ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a non-commutative semiring domain. Doesn't seem very
useful given that the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.

## TODO

Multiplicativise? Probably ugly and not very useful.
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s


-- @@ L45-45 verbatim
open Finset Fintype Function

-- @@ L46-46 verbatim
open scoped BigOperators ComplexConjugate NNReal Pointwise translate Indicator mu


-- @@ L48-48 verbatim
variable {G R γ : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]


-- @@ L50-55 verbatim
/-!
### Convolution of functions

In this section, we define the convolution `f ∗ᵈ g` and difference convolution `f ○ᵈ g` of functions
`f g : G → R`, and show how they interact.
-/


-- @@ L57-57 verbatim
section CommSemiring

-- @@ L58-58 verbatim
variable [CommSemiring R] {f g : G → R}


-- @@ L60-63 expanded
lemma indicator_one_ddconv_indicator_one_eq_sum (s t : Finset G) (a : G) :
    (ddconv 𝟭_[s, R] 𝟭_[t]) a = #({x ∈ s ×ˢ t | x.1 + x.2 = a}) :=
  by
  simp only [ddconv_apply, Set.indicator_apply, ← ite_and, filter_comm, boole_mul, sum_boole]
  simp_rw [mem_coe, ← mem_product, filter_univ_mem]


-- @@ L65-66 expanded
lemma indicator_one_ddconv (s : Finset G) (f : G → R) : ddconv 𝟭_[s] f = ∑ a ∈ s, τ a f := by ext;
  simp [ddconv_eq_sum_sub', Set.indicator_apply]


-- @@ L68-69 expanded
lemma ddconv_indicator_one (f : G → R) (s : Finset G) : ddconv f 𝟭_[s] = ∑ a ∈ s, τ a f := by ext;
  simp [ddconv_eq_sum_sub, Set.indicator_apply]


-- @@ L71-75 expanded
lemma indicator_one_ddconv_indicator_one_eq_card_vadd_inter_neg (s t : Finset G) (a : G) :
    (ddconv 𝟭_[s, R] 𝟭_[t]) a = #((-a +ᵥ s) ∩ -t) :=
  by
  rw [← card_neg, neg_inter]
  simp [ddconv_indicator_one, Set.indicator_apply, inter_comm, ← filter_mem_eq_inter,
    ← neg_vadd_mem_iff, ← sub_eq_add_neg]


-- @@ L77-77 verbatim
variable [StarRing R]


-- @@ L79-83 expanded
lemma indicator_one_dddconv_Set.indicator_apply (s t : Finset G) (a : G) :
    (dddconv 𝟭_[s, R] 𝟭_[t]) a = #({x ∈ s ×ˢ t | x.1 - x.2 = a}) :=
  by
  simp only [dddconv_apply, Set.indicator_apply, ← ite_and, filter_comm, boole_mul, sum_boole,
    apply_ite conj, map_one, map_zero, Pi.conj_apply]
  simp_rw [mem_coe, ← mem_product, filter_univ_mem]


-- @@ L85-86 expanded
lemma indicator_one_dddconv (s : Finset G) (f : G → R) :
    dddconv 𝟭_[s] f = ∑ a ∈ s, τ a (conjneg f) := by ext;
  simp [dddconv_eq_sum_sub', Set.indicator_apply]


-- @@ L88-90 expanded
lemma dddconv_indicator_one_eq_sum (f : G → R) (s : Finset G) :
    dddconv f 𝟭_[s] = ∑ a ∈ s, τ (-a) f := by ext; simp [dddconv_eq_sum_add, Set.indicator_apply]


-- @@ L92-94 expanded
lemma dddconv_indicator_one (f : G → R) (s : Finset G) : dddconv f 𝟭_[s] = ddconv f 𝟭_[-s] :=
  by
  rw [← ddconv_conjneg]
  simp


-- @@ L96-96 verbatim
end CommSemiring


-- @@ L98-98 verbatim
section Semifield

-- @@ L99-99 verbatim
variable [Semifield R]


-- @@ L101-102 expanded
@[simp]
lemma mu_univ_ddconv_mu_univ : ddconv ((@mu R _ _) (univ : Finset G)) (mu univ) = mu univ := by ext;
  cases eq_or_ne (card G : R) 0 <;> simp [mu_apply, ddconv_eq_sum_add, card_univ, *]


-- @@ L104-105 expanded
lemma mu_ddconv (s : Finset G) (f : G → R) : ddconv (mu s) f = (#s : R)⁻¹ • ∑ a ∈ s, τ a f := by
  simp [mu, indicator_one_ddconv, smul_ddconv]


-- @@ L107-108 expanded
lemma ddconv_mu (f : G → R) (s : Finset G) : ddconv f (mu s) = (#s : R)⁻¹ • ∑ a ∈ s, τ a f := by
  simp [mu, ddconv_indicator_one, ddconv_smul]


-- @@ L110-110 verbatim
variable [StarRing R]


-- @@ L112-113 expanded
@[simp]
lemma mu_univ_dddconv_mu_univ : dddconv ((@mu R _ _) (univ : Finset G)) (mu univ) = mu univ := by
  ext; cases eq_or_ne (card G : R) 0 <;> simp [mu_apply, dddconv_eq_sum_add, card_univ, *]


-- @@ L115-117 expanded
lemma mu_dddconv (s : Finset G) (f : G → R) :
    dddconv (mu s) f = (#s : R)⁻¹ • ∑ a ∈ s, τ a (conjneg f) := by
  simp [mu, indicator_one_dddconv, smul_dddconv]


-- @@ L119-120 expanded
lemma dddconv_mu (f : G → R) (s : Finset G) : dddconv f (mu s) = (#s : R)⁻¹ • ∑ a ∈ s, τ (-a) f :=
  by simp [mu, dddconv_indicator_one_eq_sum, dddconv_smul]


-- @@ L122-122 verbatim
end Semifield


-- @@ L124-124 verbatim
section Semifield

-- @@ L125-125 verbatim
variable [Semifield R] [CharZero R]


-- @@ L127-128 expanded
lemma expect_ddconv (f g : G → R) : 𝔼 a, (ddconv f g) a = (∑ a, f a) * 𝔼 a, g a := by
  simp_rw [expect, sum_ddconv, mul_smul_comm]


-- @@ L130-131 expanded
lemma expect_ddconv' (f g : G → R) : 𝔼 a, (ddconv f g) a = (𝔼 a, f a) * ∑ a, g a := by
  simp_rw [expect, sum_ddconv, smul_mul_assoc]


-- @@ L133-133 verbatim
variable [StarRing R]


-- @@ L135-136 expanded
lemma expect_dddconv (f g : G → R) : 𝔼 a, (dddconv f g) a = (∑ a, f a) * 𝔼 a, conj (g a) := by
  simp_rw [expect, sum_dddconv, mul_smul_comm]


-- @@ L138-139 expanded
lemma expect_dddconv' (f g : G → R) : 𝔼 a, (dddconv f g) a = (𝔼 a, f a) * ∑ a, conj (g a) := by
  simp_rw [expect, sum_dddconv, smul_mul_assoc]


-- @@ L141-141 verbatim
end Semifield


-- @@ L143-143 verbatim
section Field

-- @@ L144-144 verbatim
variable [Field R] [CharZero R]


-- @@ L146-148 expanded
@[simp]
lemma balance_ddconv (f g : G → R) : balance (ddconv f g) = ddconv (balance f) (balance g) := by
  simpa [balance, ddconv_sub, sub_ddconv, expect_ddconv] using!
    (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm


-- @@ L150-150 verbatim
variable [StarRing R]


-- @@ L152-154 expanded
@[simp]
lemma balance_dddconv (f g : G → R) : balance (dddconv f g) = dddconv (balance f) (balance g) := by
  simpa [balance, dddconv_sub, sub_dddconv, expect_dddconv, map_expect] using!
    (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm


-- @@ L156-156 verbatim
end Field


-- @@ L158-158 verbatim
/-! ### Iterated convolution -/


-- @@ L160-160 verbatim
section CommSemiring

-- @@ L161-161 verbatim
variable [CommSemiring R] {f g : G → R} {n : ℕ}


-- @@ L163-172 expanded
lemma indicator_one_iterConv_apply (s : Finset G) :
    ∀ (n : ℕ) (a : G), (iterConv 𝟭_[s, R] n) a = #({x ∈ s ^^ n | ∑ i, x i = a})
  | 0, a => by simp [apply_ite card, eq_comm]
  | n + 1, a =>
    by
    simp_rw [iterConv_succ', ddconv_eq_sum_sub', indicator_one_iterConv_apply, Set.indicator_apply,
      boole_mul, sum_ite, mem_coe, filter_univ_mem, sum_const_zero, add_zero, ← Nat.cast_sum, ←
      Finset.card_sigma]
    congr 1
    refine card_equiv ((Equiv.sigmaEquivProd ..).trans <| Fin.consEquiv fun _ ↦ G) ?_
    aesop  (add simp [Fin.sum_cons, Fin.forall_fin_succ])


-- @@ L174-178 expanded
lemma indicator_one_iterConv_ddconv (s : Finset G) (n : ℕ) (f : G → R) :
    ddconv (iterConv 𝟭_[s] n) f = ∑ a ∈ s ^^ n, τ (∑ i, a i) f :=
  by
  ext b
  simp only [ddconv_eq_sum_sub', indicator_one_iterConv_apply, Finset.sum_apply, translate_apply,
    ← nsmul_eq_mul, ← sum_const, Finset.sum_fiberwise']


-- @@ L180-184 expanded
lemma ddconv_indicator_one_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    ddconv f (iterConv 𝟭_[s] n) = ∑ a ∈ s ^^ n, τ (∑ i, a i) f :=
  by
  ext b
  simp only [ddconv_eq_sum_sub, indicator_one_iterConv_apply, Finset.sum_apply, translate_apply,
    ← nsmul_eq_mul', ← sum_const, Finset.sum_fiberwise']


-- @@ L186-186 verbatim
variable [StarRing R]


-- @@ L188-190 expanded
lemma indicator_one_iterConv_dddconv (s : Finset G) (n : ℕ) (f : G → R) :
    dddconv (iterConv 𝟭_[s] n) f = ∑ a ∈ s ^^ n, τ (∑ i, a i) (conjneg f) := by
  rw [← ddconv_conjneg, indicator_one_iterConv_ddconv]


-- @@ L192-194 expanded
lemma dddconv_indicator_one_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    dddconv f (iterConv 𝟭_[s] n) = ∑ a ∈ s ^^ n, τ (-∑ i, a i) f := by
  simp [← ddconv_conjneg, conjneg_iterConv, ← coe_neg, ddconv_indicator_one_iterConv, piFinset_neg]


-- @@ L196-196 verbatim
end CommSemiring


-- @@ L198-198 verbatim
section Semifield

-- @@ L199-199 verbatim
variable [Semifield R] [CharZero R]


-- @@ L201-207 expanded
lemma mu_iterConv_ddconv (s : Finset G) (n : ℕ) (f : G → R) :
    ddconv (iterConv (mu s) n) f = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) f :=
  by
  simp only [mu, smul_iterConv, inv_pow, smul_ddconv, indicator_one_iterConv_ddconv, expect,
    card_piFinset_const, Nat.cast_pow]
  rw [← NNRat.cast_smul_eq_nnqsmul R]
  push_cast
  rfl


-- @@ L209-211 expanded
lemma ddconv_mu_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    ddconv f (iterConv (mu s) n) = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) f := by
  rw [ddconv_comm, mu_iterConv_ddconv]


-- @@ L213-222 expanded
lemma Finset.dens_addSubgroup_preimage_vadd_eq_indicator_one_ddconv_mu (a : G) (B : Finset G)
    {S : Type*} [SetLike S G] [AddSubgroupClass S G] (V : S) [Fintype V] :
    ((-a +ᵥ B).preimage (↑) Set.injOn_subtype_val : Finset V).dens =
      (ddconv 𝟭_[B, R] (mu (V : Set G).toFinset)) a :=
  by
  rw [mu, ddconv_smul, Pi.smul_apply, indicator_one_ddconv_indicator_one_eq_card_vadd_inter_neg,
    nnratCast_dens, card_preimage, smul_eq_mul, inv_mul_eq_div]
  congr
  · congr 1 with x
    simp
  · simp


-- @@ L224-224 verbatim
variable [StarRing R]


-- @@ L226-228 expanded
lemma mu_iterConv_dddconv (s : Finset G) (n : ℕ) (f : G → R) :
    dddconv (iterConv (mu s) n) f = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) (conjneg f) :=
  by rw [← ddconv_conjneg, mu_iterConv_ddconv]


-- @@ L230-233 expanded
lemma dddconv_mu_iterConv (f : G → R) (s : Finset G) (n : ℕ) :
    dddconv f (iterConv (mu s) n) = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (-∑ i, a i) f := by
  simp_rw [← ddconv_conjneg, conjneg_iterConv, conjneg_mu, ddconv_mu_iterConv, piFinset_neg,
    expect_neg_index, Pi.neg_apply, sum_neg_distrib]


-- @@ L235-235 verbatim
end Semifield


-- @@ L237-237 verbatim
section Field

-- @@ L238-238 verbatim
variable [Field R] [CharZero R]


-- @@ L240-243 expanded
@[simp]
lemma balance_iterConv (f : G → R) : ∀ {n}, n ≠ 0 → balance (iterConv f n) = iterConv (balance f) n
  | 0, h => by cases h rfl
  | 1, _ => by simp
  | n + 2, _ => by simp [iterConv_succ _ (n + 1), balance_iterConv _ n.succ_ne_zero]


-- @@ L245-245 verbatim
end Field
