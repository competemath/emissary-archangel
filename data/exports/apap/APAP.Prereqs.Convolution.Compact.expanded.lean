module

public import AddCombi.Convolution.Finite.Defs
public import APAP.Prereqs.Convolution.Discrete.Defs

import Mathlib.Analysis.Complex.Basic


-- @@ L8-33 verbatim
/-!
# Convolution in the compact normalisation

This file defines several versions of the discrete convolution of functions with the compact
normalisation.

## Main declarations

* `conv`: Discrete convolution of two functions in the compact normalisation
* `dconv`: Discrete difference convolution of two functions in the compact normalisation
* `iterCConv`: Iterated convolution of a function in the compact normalisation

## Notation

* `f ∗ g`: Convolution
* `f ○ g`: Difference convolution
* `f ∗^ₙ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a division ring. Doesn't seem very useful given that
the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
open Finset Fintype Function

-- @@ L38-38 verbatim
open scoped BigOperators ComplexConjugate NNReal Pointwise Indicator translate


-- @@ L40-40 verbatim
local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a


-- @@ L42-42 verbatim
variable {G H R S : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]


-- @@ L44-49 verbatim
/-!
### Convolution of functions

In this section, we define the convolution `f ∗ g` and difference convolution `f ○ g` of functions
`f g : G → R`, and show how they interact.
-/


-- @@ L51-51 verbatim
/-! ### Trivial character -/


-- @@ L53-53 verbatim
section Semifield

-- @@ L54-54 verbatim
variable [Semifield R]


-- @@ L56-57 verbatim
/-- The trivial character. -/
def trivNChar : G → R := fun a ↦ if a = 0 then card G else 0


-- @@ L59-59 verbatim
@[simp] lemma trivNChar_apply (a : G) : (trivNChar a : R) = if a = 0 then (card G : R) else 0 := rfl


-- @@ L61-61 verbatim
variable [StarRing R]


-- @@ L63-64 verbatim
@[simp] lemma conj_trivNChar : conj (trivNChar : G → R) = trivNChar := by
  ext; simp; split_ifs <;> simp


-- @@ L66-67 verbatim
@[simp] lemma conjneg_trivNChar : conjneg (trivNChar : G → R) = trivNChar := by
  ext; simp; split_ifs <;> simp


-- @@ L69-69 verbatim
@[simp] lemma isSelfAdjoint_trivNChar : IsSelfAdjoint (trivNChar : G → R) := conj_trivNChar


-- @@ L71-71 verbatim
end Semifield


-- @@ L73-73 verbatim
/-! ### Convolution -/


-- @@ L75-75 verbatim
section Semifield

-- @@ L76-76 verbatim
variable [Semifield R] [CharZero R] {f g : G → R}


-- @@ L78-83 expanded
lemma conv_apply_eq_smul_ddconv (f g : G → R) (a : G) :
    (f ∗ g) a = (Fintype.card G : ℚ≥0)⁻¹ • (ddconv f g) a :=
  by
  rw [conv_apply, expect, eq_comm]
  congr 3
  refine card_nbij' (fun b ↦ (b, a - b)) Prod.fst ?_ ?_ ?_ ?_ <;>
    simp [Set.LeftInvOn, Set.MapsTo, eq_sub_iff_add_eq', eq_comm]


-- @@ L85-86 expanded
lemma conv_eq_smul_ddconv (f g : G → R) : f ∗ g = (Fintype.card G : ℚ≥0)⁻¹ • (ddconv f g) :=
  funext <| conv_apply_eq_smul_ddconv _ _


-- @@ L88-89 verbatim
@[simp] lemma conv_trivNChar (f : G → R) : f ∗ trivNChar = f := by
  ext a; simp [conv_eq_expect_sub, card_univ, NNRat.smul_def, mul_comm]


-- @@ L91-92 verbatim
@[simp] lemma trivNChar_conv (f : G → R) : trivNChar ∗ f = f := by
  rw [conv_comm, conv_trivNChar]


-- @@ L94-94 verbatim
variable [StarRing R]


-- @@ L96-101 expanded
lemma dconv_apply_eq_smul_dddconv (f g : G → R) (a : G) :
    (f ○ g) a = (Fintype.card G : ℚ≥0)⁻¹ • (dddconv f g) a :=
  by
  rw [dconv_apply, expect, eq_comm]
  congr 3
  refine card_nbij' (fun b ↦ (a + b, b)) Prod.snd ?_ ?_ ?_ ?_ <;>
    simp [Set.MapsTo, Set.LeftInvOn, eq_sub_iff_add_eq, eq_comm]


-- @@ L103-104 expanded
lemma dconv_eq_smul_dddconv (f g : G → R) : (f ○ g) = (Fintype.card G : ℚ≥0)⁻¹ • (dddconv f g) :=
  funext <| dconv_apply_eq_smul_dddconv _ _


-- @@ L106-107 verbatim
@[simp] lemma dconv_trivNChar (f : G → R) : f ○ trivNChar = f := by
  rw [← conv_conjneg, conjneg_trivNChar, conv_trivNChar]


-- @@ L109-121 verbatim
@[simp] lemma trivNChar_dconv (f : G → R) : trivNChar ○ f = conjneg f := by
  rw [← conv_conjneg, trivNChar_conv]

-- lemma indicator_one_conv_Set.indicator_apply (s t : Finset G) (a : G) :
--     (𝟭_[s, R] ∗ 𝟭_[t]) a = ((s ×ˢ t).filter fun x : G × G ↦ x.1 + x.2 = a).card := by
--   simp only [conv_apply, Set.indicator_apply, ← ite_and, filter_comm, boole_mul, expect_boole]
--   simp_rw [← mem_product, filter_univ_mem]

-- lemma indicator_one_dconv_Set.indicator_apply (s t : Finset G) (a : G) :
--     (𝟭_[s, R] ○ 𝟭_[t]) a = ((s ×ˢ t).filter fun x : G × G ↦ x.1 - x.2 = a).card := by
--   simp only [dconv_apply, Set.indicator_apply, ← ite_and, filter_comm, boole_mul, expect_boole,
--     apply_ite conj, map_one, map_zero, Pi.conj_apply]
--   simp_rw [← mem_product, filter_univ_mem]


-- @@ L123-123 verbatim
end Semifield


-- @@ L125-125 verbatim
section Semifield

-- @@ L126-126 verbatim
variable [Semifield R] [CharZero R]


-- @@ L128-128 verbatim
@[simp] lemma one_conv_one : (1 : G → R) ∗ 1 = 1 := by ext; simp [conv_eq_expect_add, *]


-- @@ L130-130 verbatim
variable [StarRing R]


-- @@ L132-132 verbatim
@[simp] lemma one_dconv_one : (1 : G → R) ○ 1 = 1 := by ext; simp [dconv_eq_expect_add, *]


-- @@ L134-134 verbatim
end Semifield


-- @@ L136-136 verbatim
/-! ### Iterated convolution -/


-- @@ L138-138 verbatim
section Semifield

-- @@ L139-139 verbatim
variable [Semifield R] [CharZero R] {f g : G → R} {n : ℕ}


-- @@ L141-144 verbatim
/-- Iterated convolution. -/
def iterCConv (f : G → R) : ℕ → G → R
  | 0 => trivNChar
  | n + 1 => iterCConv f n ∗ f


-- @@ L146-146 verbatim
infixl:78 " ∗^ₙ " => iterCConv


-- @@ L148-148 expanded
@[simp]
lemma iterCConv_zero (f : G → R) : iterCConv f 0 = trivNChar :=
  rfl


-- @@ L149-149 expanded
@[simp]
lemma iterCConv_one (f : G → R) : iterCConv f 1 = f :=
  trivNChar_conv _


-- @@ L151-151 expanded
lemma iterCConv_succ (f : G → R) (n : ℕ) : iterCConv f (n + 1) = iterCConv f n ∗ f :=
  rfl


-- @@ L152-152 expanded
lemma iterCConv_succ' (f : G → R) (n : ℕ) : iterCConv f (n + 1) = f ∗ iterCConv f n :=
  conv_comm _ _


-- @@ L154-156 expanded
lemma iterCConv_add (f : G → R) (m : ℕ) : ∀ n, iterCConv f (m + n) = iterCConv f m ∗ iterCConv f n
  | 0 => by simp
  | n + 1 => by simp [← add_assoc, iterCConv_succ', iterCConv_add, conv_left_comm]


-- @@ L158-160 expanded
lemma iterCConv_mul (f : G → R) (m : ℕ) : ∀ n : ℕ, iterCConv f (m * n) = iterCConv (iterCConv f m) n
  | 0 => rfl
  | n + 1 => by simp [mul_add_one, iterCConv_succ, iterCConv_add, iterCConv_mul]


-- @@ L162-163 expanded
lemma iterCConv_mul' (f : G → R) (m n : ℕ) : iterCConv f (m * n) = iterCConv (iterCConv f n) m := by
  rw [mul_comm, iterCConv_mul]


-- @@ L165-167 expanded
lemma iterCConv_conv_distrib (f g : G → R) :
    ∀ n, iterCConv (f ∗ g) n = iterCConv f n ∗ iterCConv g n
  | 0 => (conv_trivNChar _).symm
  | n + 1 => by simp_rw [iterCConv_succ, iterCConv_conv_distrib, conv_conv_conv_comm]


-- @@ L169-171 expanded
@[simp]
lemma zero_iterCConv : ∀ {n}, n ≠ 0 → iterCConv (0 : G → R) n = 0
  | 0, hn => by cases hn rfl
  | n + 1, _ => conv_zero _


-- @@ L173-176 expanded
@[simp]
lemma smul_iterCConv [Monoid H] [DistribMulAction H R] [IsScalarTower H R R] [SMulCommClass H R R]
    (c : H) (f : G → R) : ∀ n, iterCConv (c • f) n = c ^ n • iterCConv f n
  | 0 => by simp
  | n + 1 => by simp_rw [iterCConv_succ, smul_iterCConv _ _ n, pow_succ, mul_smul_conv_comm]


-- @@ L178-181 expanded
lemma comp_iterCConv [Semifield S] [CharZero S] (m : R →+* S) (f : G → R) :
    ∀ n, m ∘ (iterCConv f n) = iterCConv (m ∘ f) n
  | 0 => by ext; simp; split_ifs <;> simp
  | n + 1 => by simp [iterCConv_succ, comp_conv, comp_iterCConv]


-- @@ L183-185 expanded
lemma expect_iterCConv (f : G → R) : ∀ n, 𝔼 a, (iterCConv f n) a = (𝔼 a, f a) ^ n
  | 0 => by simp [card_univ, NNRat.smul_def]
  | n + 1 => by simp only [iterCConv_succ, expect_conv, expect_iterCConv, pow_succ]


-- @@ L187-189 expanded
@[simp]
lemma iterCConv_trivNChar : ∀ n, iterCConv (trivNChar : G → R) n = trivNChar
  | 0 => rfl
  | _n + 1 => (conv_trivNChar _).trans <| iterCConv_trivNChar _


-- @@ L191-196 expanded
lemma support_iterCConv_subset (f : G → R) : ∀ n, support (iterCConv f n) ⊆ n • support f
  | 0 => by
    simp only [iterCConv_zero, zero_smul, support_subset_iff, Ne, ite_eq_right_iff, exists_prop,
      not_forall, Set.mem_zero, and_imp, forall_eq, imp_true_iff, trivNChar_apply]
  | n + 1 =>
    (support_conv_subset _ _).trans <| Set.add_subset_add_right <| support_iterCConv_subset _ _


-- @@ L198-199 expanded
lemma map_iterCConv [Semifield S] [CharZero S] (m : R →+* S) (f : G → R) (a : G) (n : ℕ) :
    m ((iterCConv f n) a) = (iterCConv (m ∘ f) n) a :=
  congr_fun (comp_iterCConv m _ _) _


-- @@ L201-201 verbatim
variable [StarRing R]


-- @@ L203-205 expanded
@[simp]
lemma conj_iterCConv (f : G → R) : ∀ n, conj (iterCConv f n) = iterCConv (conj f) n
  | 0 => by simp
  | n + 1 => by simp [iterCConv_succ, conj_iterCConv]


-- @@ L207-209 expanded
@[simp]
lemma conjneg_iterCConv (f : G → R) : ∀ n, conjneg (iterCConv f n) = iterCConv (conjneg f) n
  | 0 => by simp
  | n + 1 => by simp [iterCConv_succ, conjneg_iterCConv]


-- @@ L211-233 expanded
lemma iterCConv_dconv_distrib (f g : G → R) :
    ∀ n, iterCConv (f ○ g) n = iterCConv f n ○ iterCConv g n
  | 0 => (dconv_trivNChar _).symm
  | n + 1 => by
    simp_rw [iterCConv_succ, iterCConv_dconv_distrib, conv_dconv_conv_comm]
      -- lemma indicator_one_iterCConv_apply (s : Finset G) (n : ℕ) (a : G) :
      --     (𝟭_[ℝ] s ∗^ₙ n) a = #{x ∈ piFinset fun _i ↦ s | ∑ i, x i = a} := by
      --   induction' n with n ih generalizing a
      --   · simp [apply_ite card, eq_comm]
      --   simp_rw [iterCConv_succ, conv_eq_expect_sub', ih, Set.indicator_apply, boole_mul, expect_ite,
      --     filter_univ_mem, expect_const_zero, add_zero, ← Nat.cast_expect, ← Finset.card_sigma,
      --     Nat.cast_inj]
      --   refine Finset.card_bij (fun f _ ↦ Fin.cons f.1 f.2) _ _ _
      --   · simp only [Fin.expect_cons, eq_sub_iff_add_eq', mem_sigma, mem_filter, mem_piFinset, and_imp]
      --     refine fun bf hb hf ha ↦ ⟨Fin.cases _ _, ha⟩
      --     · exact hb
      --     · simpa only [Fin.cons_succ]
      --   · simp only [Sigma.ext_iff, Fin.cons_eq_cons, heq_iff_eq, imp_self, imp_true_iff, forall_const,
      --       Sigma.forall]
      --   · simp only [mem_filter, mem_piFinset, mem_sigma, exists_prop, Sigma.exists, and_imp,
      --       eq_sub_iff_add_eq', and_assoc]
      --     exact fun f hf ha ↦
      --       ⟨f 0, Fin.tail f, hf _, fun _ ↦ hf _, (Fin.expect_univ_succ _).symm.trans ha,
      --         Fin.cons_self_tail _⟩


-- @@ L235-235 verbatim
end Semifield


-- @@ L237-237 verbatim
section Field

-- @@ L238-238 verbatim
variable [Field R] [CharZero R]


-- @@ L240-243 expanded
@[simp]
lemma balance_iterCConv (f : G → R) :
    ∀ {n}, n ≠ 0 → balance (iterCConv f n) = iterCConv (balance f) n
  | 0, h => by cases h rfl
  | 1, _ => by simp
  | n + 2, _ => by simp [iterCConv_succ _ (n + 1), balance_iterCConv _ n.succ_ne_zero]


-- @@ L245-245 verbatim
end Field


-- @@ L247-247 verbatim
namespace NNReal

-- @@ L248-248 verbatim
variable {f : G → ℝ≥0}


-- @@ L250-252 expanded
@[simp, norm_cast]
lemma coe_iterCConv (f : G → ℝ≥0) (n : ℕ) (a : G) :
    (↑((iterCConv f n) a) : ℝ) = (iterCConv ((↑) ∘ f) n) a :=
  map_iterCConv NNReal.toRealHom _ _ _


-- @@ L254-254 verbatim
end NNReal
