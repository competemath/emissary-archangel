module

public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.NNReal.Star
public import Mathlib.Basic.Complex.Basic

import Mathlib.Analysis.Complex.Basic


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
open Finset Fintype Function

-- @@ L44-44 verbatim
open scoped ComplexConjugate NNReal Pointwise translate


-- @@ L46-46 verbatim
variable {G H R S : Type*} [DecidableEq G] [AddCommGroup G]


-- @@ L48-48 verbatim
/-! ### Trivial character -/


-- @@ L50-50 verbatim
section CommSemiring

-- @@ L51-51 verbatim
variable [CommSemiring R]


-- @@ L53-54 verbatim
/-- The trivial character. -/
def trivChar : G → R := fun a ↦ if a = 0 then 1 else 0


-- @@ L56-56 verbatim
@[simp] lemma trivChar_apply (a : G) : (trivChar a : R) = if a = 0 then 1 else 0 := rfl


-- @@ L58-58 verbatim
variable [StarRing R]


-- @@ L60-60 verbatim
@[simp] lemma conj_trivChar : conj (trivChar : G → R) = trivChar := by ext; simp

-- @@ L61-61 verbatim
@[simp] lemma conjneg_trivChar : conjneg (trivChar : G → R) = trivChar := by ext; simp


-- @@ L63-63 verbatim
@[simp] lemma isSelfAdjoint_trivChar : IsSelfAdjoint (trivChar : G → R) := conj_trivChar


-- @@ L65-65 verbatim
end CommSemiring


-- @@ L67-67 verbatim
variable [Fintype G]


-- @@ L69-69 verbatim
/-! ### Convolution -/


-- @@ L71-71 verbatim
section CommSemiring

-- @@ L72-72 verbatim
variable [CommSemiring R] {f g : G → R}


-- @@ L74-75 verbatim
/-- Convolution -/
def ddconv (f g : G → R) : G → R := fun a ↦ ∑ x : G × G with x.1 + x.2 = a , f x.1 * g x.2


-- @@ L77-77 verbatim
infixl:71 " ∗ᵈ " => ddconv


-- @@ L79-80 expanded
lemma ddconv_apply (f g : G → R) (a : G) :
    (ddconv f g) a = ∑ x : G × G with x.1 + x.2 = a, f x.1 * g x.2 :=
  rfl


-- @@ L82-82 expanded
@[simp]
lemma ddconv_zero (f : G → R) : ddconv f 0 = 0 := by ext; simp [ddconv_apply]


-- @@ L83-83 expanded
@[simp]
lemma zero_ddconv (f : G → R) : ddconv 0 f = 0 := by ext; simp [ddconv_apply]


-- @@ L85-86 expanded
lemma ddconv_add (f g h : G → R) : ddconv f (g + h) = ddconv f g + ddconv f h := by ext;
  simp [ddconv_apply, mul_add, sum_add_distrib]


-- @@ L88-89 expanded
lemma add_ddconv (f g h : G → R) : ddconv (f + g) h = ddconv f h + ddconv g h := by ext;
  simp [ddconv_apply, add_mul, sum_add_distrib]


-- @@ L91-92 expanded
lemma smul_ddconv [DistribSMul H R] [IsScalarTower H R R] (c : H) (f g : G → R) :
    ddconv (c • f) g = c • (ddconv f g) := by ext a; simp [ddconv_apply, smul_sum, smul_mul_assoc]


-- @@ L94-95 expanded
lemma ddconv_smul [DistribSMul H R] [SMulCommClass H R R] (c : H) (f g : G → R) :
    ddconv f (c • g) = c • (ddconv f g) := by ext a; simp [ddconv_apply, smul_sum, mul_smul_comm]


-- @@ L97-97 verbatim
alias smul_ddconv_assoc := smul_ddconv

-- @@ L98-98 verbatim
alias smul_ddconv_left_comm := ddconv_smul


-- @@ L100-102 expanded
@[simp]
lemma translate_ddconv (a : G) (f g : G → R) : ddconv (τ a f) g = τ a (ddconv f g) :=
  funext fun b ↦
    sum_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _) (by simp [sub_add_eq_add_sub])
      (by simp)


-- @@ L104-106 expanded
@[simp]
lemma ddconv_translate (a : G) (f g : G → R) : ddconv f (τ a g) = τ a (ddconv f g) :=
  funext fun b ↦
    sum_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a) (by simp [← add_sub_assoc]) (by simp)


-- @@ L108-109 expanded
lemma ddconv_comm (f g : G → R) : ddconv f g = ddconv g f :=
  funext fun a ↦ sum_equiv (Equiv.prodComm _ _) (by simp [add_comm]) <| by simp [mul_comm]


-- @@ L111-113 expanded
lemma mul_smul_ddconv_comm [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c d : H) (f g : G → R) :
    (c * d) • (ddconv f g) = ddconv (c • f) (d • g) := by rw [smul_ddconv, ddconv_smul, mul_smul]


-- @@ L115-119 expanded
lemma ddconv_assoc (f g h : G → R) : ddconv (ddconv f g) h = ddconv f (ddconv g h) :=
  by
  ext a
  simp only [sum_mul, mul_sum, ddconv_apply, Finset.sum_sigma']
  apply
      sum_nbij' (fun ⟨(_b, c), (d, e)⟩ ↦ ⟨(d, e + c), (e, c)⟩)
        (fun ⟨(b, _c), (d, e)⟩ ↦ ⟨(b + d, e), (b, d)⟩) <;>
    aesop  (add simp [add_assoc, mul_assoc])


-- @@ L121-122 expanded
lemma ddconv_right_comm (f g h : G → R) : ddconv (ddconv f g) h = ddconv (ddconv f h) g := by
  rw [ddconv_assoc, ddconv_assoc, ddconv_comm g]


-- @@ L124-125 expanded
lemma ddconv_left_comm (f g h : G → R) : ddconv f (ddconv g h) = ddconv g (ddconv f h) := by
  rw [← ddconv_assoc, ← ddconv_assoc, ddconv_comm g]


-- @@ L127-127 expanded
lemma ddconv_rotate (f g h : G → R) : ddconv (ddconv f g) h = ddconv (ddconv g h) f := by
  rw [ddconv_assoc, ddconv_comm]


-- @@ L128-129 expanded
lemma ddconv_rotate' (f g h : G → R) : ddconv f (ddconv g h) = ddconv g (ddconv h f) := by
  rw [ddconv_comm, ← ddconv_assoc]


-- @@ L131-132 expanded
lemma ddconv_ddconv_ddconv_comm (f g h i : G → R) :
    ddconv (ddconv f g) (ddconv h i) = ddconv (ddconv f h) (ddconv g i) := by
  rw [ddconv_assoc, ddconv_assoc, ddconv_left_comm g]


-- @@ L134-135 expanded
lemma map_ddconv [CommSemiring S] (m : R →+* S) (f g : G → R) (a : G) :
    m ((ddconv f g) a) = (ddconv (m ∘ f) (m ∘ g)) a := by simp [ddconv_apply, map_sum, map_mul]


-- @@ L137-138 expanded
lemma comp_ddconv [CommSemiring S] (m : R →+* S) (f g : G → R) :
    m ∘ (ddconv f g) = ddconv (m ∘ f) (m ∘ g) :=
  funext <| map_ddconv _ _ _


-- @@ L140-141 expanded
lemma ddconv_eq_sum_sub (f g : G → R) (a : G) : (ddconv f g) a = ∑ t, f (a - t) * g t := by
  rw [ddconv_apply]; apply sum_nbij' Prod.snd (fun b ↦ (a - b, b)) <;> aesop


-- @@ L143-145 expanded
lemma ddconv_eq_sum_add (f g : G → R) (a : G) : (ddconv f g) a = ∑ t, f (a + t) * g (-t) :=
  (ddconv_eq_sum_sub _ _ _).trans <|
    Fintype.sum_equiv (Equiv.neg _) _ _ fun t ↦ by
      simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]


-- @@ L147-148 expanded
lemma ddconv_eq_sum_sub' (f g : G → R) (a : G) : (ddconv f g) a = ∑ t, f t * g (a - t) := by
  rw [ddconv_comm, ddconv_eq_sum_sub]; simp_rw [mul_comm]


-- @@ L150-151 expanded
lemma ddconv_eq_sum_add' (f g : G → R) (a : G) : (ddconv f g) a = ∑ t, f (-t) * g (a + t) := by
  rw [ddconv_comm, ddconv_eq_sum_add]; simp_rw [mul_comm]


-- @@ L153-155 expanded
lemma ddconv_apply_add (f g : G → R) (a b : G) :
    (ddconv f g) (a + b) = ∑ t, f (a + t) * g (b - t) :=
  (ddconv_eq_sum_sub _ _ _).trans <|
    Fintype.sum_equiv (Equiv.subLeft b) _ _ fun t ↦ by simp [add_sub_assoc]


-- @@ L157-160 expanded
lemma sum_ddconv_mul (f g h : G → R) :
    ∑ a, (ddconv f g) a * h a = ∑ a, ∑ b, f a * g b * h (a + b) :=
  by
  simp_rw [ddconv_eq_sum_sub', sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun x _ ↦ Fintype.sum_equiv (Equiv.subRight x) _ _ fun y ↦ by simp


-- @@ L162-163 expanded
lemma sum_ddconv (f g : G → R) : ∑ a, (ddconv f g) a = (∑ a, f a) * ∑ a, g a := by
  simpa only [Fintype.sum_mul_sum, Pi.one_apply, mul_one] using sum_ddconv_mul f g 1


-- @@ L165-166 expanded
@[simp]
lemma ddconv_const (f : G → R) (b : R) : ddconv f (const _ b) = const _ ((∑ x, f x) * b) := by ext;
  simp [ddconv_eq_sum_sub', sum_mul]


-- @@ L168-169 expanded
@[simp]
lemma const_ddconv (b : R) (f : G → R) : ddconv (const _ b) f = const _ (b * ∑ x, f x) := by ext;
  simp [ddconv_eq_sum_sub, mul_sum]


-- @@ L171-171 expanded
@[simp]
lemma ddconv_trivChar (f : G → R) : ddconv f trivChar = f := by ext a; simp [ddconv_eq_sum_sub]


-- @@ L172-173 expanded
@[simp]
lemma trivChar_ddconv (f : G → R) : ddconv trivChar f = f := by rw [ddconv_comm, ddconv_trivChar]


-- @@ L175-178 expanded
lemma support_ddconv_subset (f g : G → R) : support (ddconv f g) ⊆ support f + support g :=
  by
  rintro a ha
  obtain ⟨x, hx, h⟩ := exists_ne_zero_of_sum_ne_zero ha
  exact ⟨_, left_ne_zero_of_mul h, _, right_ne_zero_of_mul h, (mem_filter.1 hx).2⟩


-- @@ L180-180 verbatim
/-! ### Difference convolution -/


-- @@ L182-182 verbatim
variable [StarRing R]


-- @@ L184-185 verbatim
/-- Difference convolution -/
def dddconv (f g : G → R) : G → R := fun a ↦ ∑ x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2


-- @@ L187-187 verbatim
infixl:71 " ○ᵈ " => dddconv


-- @@ L189-190 expanded
lemma dddconv_apply (f g : G → R) (a : G) :
    (dddconv f g) a = ∑ x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2 :=
  rfl


-- @@ L192-192 expanded
@[simp]
lemma dddconv_zero (f : G → R) : dddconv f 0 = 0 := by ext; simp [dddconv_apply]


-- @@ L193-193 expanded
@[simp]
lemma zero_dddconv (f : G → R) : dddconv 0 f = 0 := by ext; simp [dddconv_apply]


-- @@ L194-194 expanded
@[simp]
lemma dddconv_fun_zero (f : G → R) : dddconv f (fun _ ↦ 0) = 0 := by ext; simp [dddconv_apply]


-- @@ L195-195 expanded
@[simp]
lemma fun_zero_dddconv (f : G → R) : dddconv (fun _ ↦ 0) f = 0 := by ext; simp [dddconv_apply]


-- @@ L197-198 expanded
lemma dddconv_add (f g h : G → R) : dddconv f (g + h) = dddconv f g + dddconv f h := by ext;
  simp [dddconv_apply, mul_add, sum_add_distrib]


-- @@ L200-201 expanded
lemma add_dddconv (f g h : G → R) : dddconv (f + g) h = dddconv f h + dddconv g h := by ext;
  simp [dddconv_apply, add_mul, sum_add_distrib]


-- @@ L203-204 expanded
lemma smul_dddconv [DistribSMul H R] [IsScalarTower H R R] (c : H) (f g : G → R) :
    dddconv (c • f) g = c • (dddconv f g) := by ext; simp [dddconv_apply, smul_sum, smul_mul_assoc]


-- @@ L206-208 expanded
lemma dddconv_smul [Star H] [DistribSMul H R] [SMulCommClass H R R] [StarModule H R] (c : H)
    (f g : G → R) : dddconv f (c • g) = star c • (dddconv f g) := by ext;
  simp [dddconv_apply, smul_sum, mul_smul_comm, starRingEnd_apply, star_smul]


-- @@ L210-212 expanded
@[simp]
lemma translate_dddconv (a : G) (f g : G → R) : dddconv (τ a f) g = τ a (dddconv f g) :=
  funext fun b ↦
    sum_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _) (by simp [sub_right_comm _ a])
      (by simp)


-- @@ L214-216 expanded
@[simp]
lemma dddconv_translate (a : G) (f g : G → R) : dddconv f (τ a g) = τ (-a) (dddconv f g) :=
  funext fun b ↦
    sum_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
      (by simp [sub_sub_eq_add_sub, ← sub_add_eq_add_sub]) (by simp)


-- @@ L218-219 expanded
@[simp]
lemma ddconv_conjneg (f g : G → R) : ddconv f (conjneg g) = dddconv f g :=
  funext fun a ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.neg _) (by simp) (by simp)


-- @@ L221-222 expanded
@[simp]
lemma dddconv_conjneg (f g : G → R) : dddconv f (conjneg g) = ddconv f g := by
  rw [← ddconv_conjneg, conjneg_conjneg]


-- @@ L224-226 expanded
@[simp]
lemma conj_ddconv_apply (f g : G → R) (a : G) :
    conj ((ddconv f g) a) = (ddconv (conj f) (conj g)) a := by
  simp only [Pi.conj_apply, ddconv_apply, map_sum, map_mul]


-- @@ L228-230 expanded
@[simp]
lemma conj_dddconv_apply (f g : G → R) (a : G) :
    conj ((dddconv f g) a) = (dddconv (conj f) (conj g)) a := by
  simp_rw [← ddconv_conjneg, conj_ddconv_apply, conjneg_conj]


-- @@ L232-233 expanded
@[simp]
lemma conj_ddconv (f g : G → R) : conj (ddconv f g) = ddconv (conj f) (conj g) :=
  funext <| conj_ddconv_apply _ _


-- @@ L235-236 expanded
@[simp]
lemma conj_dddconv (f g : G → R) : conj (dddconv f g) = dddconv (conj f) (conj g) :=
  funext <| conj_dddconv_apply _ _


-- @@ L238-239 expanded
lemma IsSelfAdjoint.ddconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) :
    IsSelfAdjoint (ddconv f g) :=
  (conj_ddconv _ _).trans <| congr_arg₂ _ hf hg


-- @@ L241-242 expanded
lemma IsSelfAdjoint.dddconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) :
    IsSelfAdjoint (dddconv f g) :=
  (conj_dddconv _ _).trans <| congr_arg₂ _ hf hg


-- @@ L244-247 expanded
@[simp]
lemma conjneg_ddconv (f g : G → R) : conjneg (ddconv f g) = ddconv (conjneg f) (conjneg g) :=
  by
  funext a
  simp only [ddconv_apply, conjneg_apply, map_sum, map_mul]
  exact sum_equiv (Equiv.neg _) (by simp [← neg_eq_iff_eq_neg, add_comm]) (by simp)


-- @@ L249-250 expanded
@[simp]
lemma conjneg_dddconv (f g : G → R) : conjneg (dddconv f g) = dddconv g f := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, conjneg_conjneg, ddconv_comm]


-- @@ L251-251 verbatim
alias smul_dddconv_assoc := smul_dddconv

-- @@ L252-252 verbatim
alias smul_dddconv_left_comm := dddconv_smul


-- @@ L254-255 expanded
lemma dddconv_right_comm (f g h : G → R) : dddconv (dddconv f g) h = dddconv (dddconv f h) g := by
  simp_rw [← ddconv_conjneg, ddconv_right_comm]


-- @@ L257-258 expanded
lemma ddconv_dddconv_assoc (f g h : G → R) : dddconv (ddconv f g) h = ddconv f (dddconv g h) := by
  simp_rw [← ddconv_conjneg, ddconv_assoc]


-- @@ L260-261 expanded
lemma ddconv_dddconv_left_comm (f g h : G → R) : ddconv f (dddconv g h) = ddconv g (dddconv f h) :=
  by simp_rw [← ddconv_conjneg, ddconv_left_comm]


-- @@ L263-264 expanded
lemma ddconv_dddconv_right_comm (f g h : G → R) : dddconv (ddconv f g) h = ddconv (dddconv f h) g :=
  by simp_rw [← ddconv_conjneg, ddconv_right_comm]


-- @@ L266-267 expanded
lemma ddconv_dddconv_ddconv_comm (f g h i : G → R) :
    dddconv (ddconv f g) (ddconv h i) = ddconv (dddconv f h) (dddconv g i) := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, ddconv_ddconv_ddconv_comm]


-- @@ L269-270 expanded
lemma dddconv_ddconv_dddconv_comm (f g h i : G → R) :
    ddconv (dddconv f g) (dddconv h i) = dddconv (ddconv f h) (ddconv g i) := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, ddconv_ddconv_ddconv_comm]


-- @@ L272-275 expanded
lemma dddconv_dddconv_dddconv_comm (f g h i : G → R) :
    dddconv (dddconv f g) (dddconv h i) = dddconv (dddconv f h) (dddconv g i) := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, ddconv_ddconv_ddconv_comm]
    --TODO: Can we generalise to star ring homs?


-- @@ L276-278 expanded
lemma map_dddconv (f g : G → ℝ≥0) (a : G) :
    (↑((dddconv f g) a) : ℝ) = (dddconv ((↑) ∘ f) ((↑) ∘ g)) a := by
  simp_rw [dddconv_apply, NNReal.coe_sum, NNReal.coe_mul, starRingEnd_apply, star_trivial,
    Function.comp_apply]


-- @@ L280-281 expanded
lemma comp_dddconv (f g : G → ℝ≥0) : ((↑) ∘ (dddconv f g) : G → ℝ) = dddconv ((↑) ∘ f) ((↑) ∘ g) :=
  funext <| map_dddconv _ _


-- @@ L283-284 expanded
lemma dddconv_eq_sum_sub (f g : G → R) (a : G) : (dddconv f g) a = ∑ t, f (a - t) * conj (g (-t)) :=
  by simp [← ddconv_conjneg, ddconv_eq_sum_sub]


-- @@ L286-287 expanded
lemma dddconv_eq_sum_add (f g : G → R) (a : G) : (dddconv f g) a = ∑ t, f (a + t) * conj (g t) := by
  simp [← ddconv_conjneg, ddconv_eq_sum_add]


-- @@ L289-290 expanded
lemma dddconv_eq_sum_sub' (f g : G → R) (a : G) : (dddconv f g) a = ∑ t, f t * conj (g (t - a)) :=
  by simp [← ddconv_conjneg, ddconv_eq_sum_sub']


-- @@ L292-293 expanded
lemma dddconv_eq_sum_add' (f g : G → R) (a : G) :
    (dddconv f g) a = ∑ t, f (-t) * conj g (-(a + t)) := by
  simp [← ddconv_conjneg, ddconv_eq_sum_add']


-- @@ L295-296 expanded
lemma dddconv_apply_neg (f g : G → R) (a : G) : (dddconv f g) (-a) = conj ((dddconv g f) a) := by
  rw [← conjneg_dddconv f, conjneg_apply, Complex.conj_conj]


-- @@ L298-300 expanded
lemma dddconv_apply_sub (f g : G → R) (a b : G) :
    (dddconv f g) (a - b) = ∑ t, f (a + t) * conj (g (b + t)) := by
  simp [← ddconv_conjneg, sub_eq_add_neg, ddconv_apply_add, add_comm]


-- @@ L302-306 expanded
lemma sum_dddconv_mul (f g h : G → R) :
    ∑ a, (dddconv f g) a * h a = ∑ a, ∑ b, f a * conj (g b) * h (a - b) :=
  by
  simp_rw [dddconv_eq_sum_sub', sum_mul]
  rw [sum_comm]
  exact Fintype.sum_congr _ _ fun x ↦ Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp


-- @@ L308-309 expanded
lemma sum_dddconv (f g : G → R) : ∑ a, (dddconv f g) a = (∑ a, f a) * ∑ a, conj (g a) := by
  simpa only [Fintype.sum_mul_sum, Pi.one_apply, mul_one] using sum_dddconv_mul f g 1


-- @@ L311-313 expanded
@[simp]
lemma dddconv_const (f : G → R) (b : R) : dddconv f (const _ b) = const _ ((∑ x, f x) * conj b) :=
  by ext; simp [dddconv_eq_sum_sub', sum_mul]


-- @@ L315-317 expanded
@[simp]
lemma const_dddconv (b : R) (f : G → R) : dddconv (const _ b) f = const _ (b * ∑ x, conj (f x)) :=
  by ext; simp [dddconv_eq_sum_add, mul_sum]


-- @@ L319-320 expanded
@[simp]
lemma dddconv_trivChar (f : G → R) : dddconv f trivChar = f := by ext a; simp [dddconv_eq_sum_add]


-- @@ L322-323 expanded
@[simp]
lemma trivChar_dddconv (f : G → R) : dddconv trivChar f = conjneg f := by
  rw [← ddconv_conjneg, trivChar_ddconv]


-- @@ L325-326 expanded
lemma support_dddconv_subset (f g : G → R) : support (dddconv f g) ⊆ support f - support g := by
  simpa [sub_eq_add_neg] using support_ddconv_subset f (conjneg g)


-- @@ L328-328 verbatim
end CommSemiring


-- @@ L330-330 verbatim
section CommRing

-- @@ L331-331 verbatim
variable [CommRing R]


-- @@ L333-333 expanded
@[simp]
lemma ddconv_neg (f g : G → R) : ddconv f (-g) = -(ddconv f g) := by ext; simp [ddconv_apply]


-- @@ L334-334 expanded
@[simp]
lemma neg_ddconv (f g : G → R) : ddconv (-f) g = -(ddconv f g) := by ext; simp [ddconv_apply]


-- @@ L336-337 expanded
lemma ddconv_sub (f g h : G → R) : ddconv f (g - h) = ddconv f g - ddconv f h := by
  simp only [sub_eq_add_neg, ddconv_add, ddconv_neg]


-- @@ L339-340 expanded
lemma sub_ddconv (f g h : G → R) : ddconv (f - g) h = ddconv f h - ddconv g h := by
  simp only [sub_eq_add_neg, add_ddconv, neg_ddconv]


-- @@ L342-342 verbatim
variable [StarRing R]


-- @@ L344-344 expanded
@[simp]
lemma dddconv_neg (f g : G → R) : dddconv f (-g) = -(dddconv f g) := by ext; simp [dddconv_apply]


-- @@ L345-345 expanded
@[simp]
lemma neg_dddconv (f g : G → R) : dddconv (-f) g = -(dddconv f g) := by ext; simp [dddconv_apply]


-- @@ L347-348 expanded
lemma dddconv_sub (f g h : G → R) : dddconv f (g - h) = dddconv f g - dddconv f h := by
  simp only [sub_eq_add_neg, dddconv_add, dddconv_neg]


-- @@ L350-351 expanded
lemma sub_dddconv (f g h : G → R) : dddconv (f - g) h = dddconv f h - dddconv g h := by
  simp only [sub_eq_add_neg, add_dddconv, neg_dddconv]


-- @@ L353-353 verbatim
end CommRing


-- @@ L355-355 verbatim
namespace RCLike

-- @@ L356-356 verbatim
variable {𝕜 : Type} [RCLike 𝕜] (f g : G → ℝ) (a : G)


-- @@ L358-360 expanded
@[simp, norm_cast]
lemma coe_ddconv : (↑((ddconv f g) a) : 𝕜) = (ddconv ((↑) ∘ f) ((↑) ∘ g)) a :=
  map_ddconv (algebraMap ℝ 𝕜) _ _ _


-- @@ L362-363 expanded
@[simp, norm_cast]
lemma coe_dddconv : (↑((dddconv f g) a) : 𝕜) = (dddconv ((↑) ∘ f) ((↑) ∘ g)) a := by
  simp [dddconv_apply]


-- @@ L365-366 expanded
@[simp]
lemma coe_comp_ddconv : ((↑) : ℝ → 𝕜) ∘ (ddconv f g) = ddconv ((↑) ∘ f) ((↑) ∘ g) :=
  funext <| coe_ddconv _ _


-- @@ L368-369 expanded
@[simp]
lemma coe_comp_dddconv : ((↑) : ℝ → 𝕜) ∘ (dddconv f g) = dddconv ((↑) ∘ f) ((↑) ∘ g) :=
  funext <| coe_dddconv _ _


-- @@ L371-371 verbatim
end RCLike


-- @@ L373-373 verbatim
namespace Complex

-- @@ L374-374 verbatim
variable (f g : G → ℝ) (n : ℕ) (a : G)


-- @@ L376-377 expanded
@[simp, norm_cast]
lemma ofReal_ddconv : (↑((ddconv f g) a) : ℂ) = (ddconv ((↑) ∘ f) ((↑) ∘ g)) a :=
  RCLike.coe_ddconv _ _ _


-- @@ L379-380 expanded
@[simp, norm_cast]
lemma ofReal_dddconv : (↑((dddconv f g) a) : ℂ) = (dddconv ((↑) ∘ f) ((↑) ∘ g)) a :=
  RCLike.coe_dddconv _ _ _


-- @@ L382-383 expanded
@[simp]
lemma ofReal_comp_ddconv : ((↑) : ℝ → ℂ) ∘ (ddconv f g) = ddconv ((↑) ∘ f) ((↑) ∘ g) :=
  funext <| ofReal_ddconv _ _


-- @@ L385-386 expanded
@[simp]
lemma ofReal_comp_dddconv : ((↑) : ℝ → ℂ) ∘ (dddconv f g) = dddconv ((↑) ∘ f) ((↑) ∘ g) :=
  funext <| ofReal_dddconv _ _


-- @@ L388-388 verbatim
end Complex


-- @@ L390-390 verbatim
namespace NNReal

-- @@ L391-391 verbatim
variable (f g : G → ℝ≥0) (a : G)


-- @@ L393-394 expanded
@[simp, norm_cast]
lemma coe_ddconv : (↑((ddconv f g) a) : ℝ) = (ddconv ((↑) ∘ f) ((↑) ∘ g)) a :=
  map_ddconv NNReal.toRealHom _ _ _


-- @@ L396-397 expanded
@[simp, norm_cast]
lemma coe_dddconv : (↑((dddconv f g) a) : ℝ) = (dddconv ((↑) ∘ f) ((↑) ∘ g)) a := by
  simp [dddconv_apply, coe_sum]


-- @@ L399-400 expanded
@[simp]
lemma coe_comp_ddconv : ((↑) : _ → ℝ) ∘ (ddconv f g) = ddconv ((↑) ∘ f) ((↑) ∘ g) :=
  funext <| coe_ddconv _ _


-- @@ L402-403 expanded
@[simp]
lemma coe_comp_dddconv : ((↑) : _ → ℝ) ∘ (dddconv f g) = dddconv ((↑) ∘ f) ((↑) ∘ g) :=
  funext <| coe_dddconv _ _


-- @@ L405-405 verbatim
end NNReal


-- @@ L407-407 verbatim
/-! ### Iterated convolution -/


-- @@ L409-409 verbatim
section CommSemiring

-- @@ L410-410 verbatim
variable [CommSemiring R] {f g : G → R} {n : ℕ}


-- @@ L412-415 expanded
/-- Iterated convolution. -/
def iterConv (f : G → R) : ℕ → G → R
  | 0 => trivChar
  | n + 1 => ddconv (iterConv f n) f


-- @@ L417-417 verbatim
infixl:78 " ∗ᵈ^ " => iterConv


-- @@ L419-419 expanded
@[simp]
lemma iterConv_zero (f : G → R) : iterConv f 0 = trivChar :=
  rfl


-- @@ L420-420 expanded
@[simp]
lemma iterConv_one (f : G → R) : iterConv f 1 = f :=
  trivChar_ddconv _


-- @@ L422-422 expanded
lemma iterConv_succ (f : G → R) (n : ℕ) : iterConv f (n + 1) = ddconv (iterConv f n) f :=
  rfl


-- @@ L423-423 expanded
lemma iterConv_succ' (f : G → R) (n : ℕ) : iterConv f (n + 1) = ddconv f (iterConv f n) :=
  ddconv_comm _ _


-- @@ L425-427 expanded
lemma iterConv_add (f : G → R) (m : ℕ) :
    ∀ n, iterConv f (m + n) = ddconv (iterConv f m) (iterConv f n)
  | 0 => by simp
  | n + 1 => by simp [← add_assoc, iterConv_succ', iterConv_add, ddconv_left_comm]


-- @@ L429-431 expanded
lemma iterConv_mul (f : G → R) (m : ℕ) : ∀ n : ℕ, iterConv f (m * n) = iterConv (iterConv f m) n
  | 0 => rfl
  | n + 1 => by simp [mul_add_one, iterConv_succ, iterConv_add, iterConv_mul]


-- @@ L433-434 expanded
lemma iterConv_mul' (f : G → R) (m n : ℕ) : iterConv f (m * n) = iterConv (iterConv f n) m := by
  rw [mul_comm, iterConv_mul]


-- @@ L436-438 expanded
lemma iterConv_ddconv_distrib (f g : G → R) :
    ∀ n, iterConv (ddconv f g) n = ddconv (iterConv f n) (iterConv g n)
  | 0 => (ddconv_trivChar _).symm
  | n + 1 => by simp_rw [iterConv_succ, iterConv_ddconv_distrib, ddconv_ddconv_ddconv_comm]


-- @@ L440-442 expanded
@[simp]
lemma zero_iterConv : ∀ {n}, n ≠ 0 → iterConv (0 : G → R) n = 0
  | 0, hn => by cases hn rfl
  | n + 1, _ => ddconv_zero _


-- @@ L444-447 expanded
@[simp]
lemma smul_iterConv [Monoid H] [DistribMulAction H R] [IsScalarTower H R R] [SMulCommClass H R R]
    (c : H) (f : G → R) : ∀ n, iterConv (c • f) n = c ^ n • iterConv f n
  | 0 => by simp
  | n + 1 => by simp_rw [iterConv_succ, smul_iterConv _ _ n, pow_succ, mul_smul_ddconv_comm]


-- @@ L449-452 expanded
lemma comp_iterConv [CommSemiring S] (m : R →+* S) (f : G → R) :
    ∀ n, m ∘ (iterConv f n) = iterConv (m ∘ f) n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, comp_ddconv, comp_iterConv]


-- @@ L454-455 expanded
lemma map_iterConv [CommSemiring S] (m : R →+* S) (f : G → R) (a : G) (n : ℕ) :
    m ((iterConv f n) a) = (iterConv (m ∘ f) n) a :=
  congr_fun (comp_iterConv m _ _) _


-- @@ L457-459 expanded
lemma sum_iterConv (f : G → R) : ∀ n, ∑ a, (iterConv f n) a = (∑ a, f a) ^ n
  | 0 => by simp
  | n + 1 => by simp [iterConv_succ, sum_ddconv, sum_iterConv, pow_succ]


-- @@ L461-463 expanded
@[simp]
lemma iterConv_trivChar : ∀ n, iterConv (trivChar : G → R) n = trivChar
  | 0 => rfl
  | _n + 1 => (ddconv_trivChar _).trans <| iterConv_trivChar _


-- @@ L465-468 expanded
lemma support_iterConv_subset (f : G → R) : ∀ n, support (iterConv f n) ⊆ n • support f
  | 0 => by simp
  | n + 1 =>
    (support_ddconv_subset _ _).trans <| Set.add_subset_add_right <| support_iterConv_subset _ _


-- @@ L470-470 verbatim
variable [StarRing R]


-- @@ L472-474 expanded
lemma iterConv_dddconv_distrib (f g : G → R) :
    ∀ n, iterConv (dddconv f g) n = dddconv (iterConv f n) (iterConv g n)
  | 0 => (dddconv_trivChar _).symm
  | n + 1 => by simp_rw [iterConv_succ, iterConv_dddconv_distrib, ddconv_dddconv_ddconv_comm]


-- @@ L476-478 expanded
@[simp]
lemma conj_iterConv (f : G → R) : ∀ n, conj (iterConv f n) = iterConv (conj f) n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, conj_iterConv]


-- @@ L480-481 expanded
@[simp]
lemma conj_iterConv_apply (f : G → R) (n : ℕ) (a : G) :
    conj ((iterConv f n) a) = (iterConv (conj f) n) a :=
  congr_fun (conj_iterConv _ _) _


-- @@ L483-484 expanded
lemma IsSelfAdjoint.iterConv (hf : IsSelfAdjoint f) (n : ℕ) : IsSelfAdjoint (iterConv f n) :=
  (conj_iterConv _ _).trans <| congr_arg (iterConv · n) hf


-- @@ L486-489 expanded
@[simp]
lemma conjneg_iterConv (f : G → R) : ∀ n, conjneg (iterConv f n) = iterConv (conjneg f) n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, conjneg_iterConv]


-- @@ L491-491 verbatim
end CommSemiring


-- @@ L493-493 verbatim
namespace NNReal


-- @@ L495-497 expanded
@[simp, norm_cast]
lemma ofReal_iterConv (f : G → ℝ≥0) (n : ℕ) (a : G) :
    (↑((iterConv f n) a) : ℝ) = (iterConv ((↑) ∘ f) n) a :=
  map_iterConv NNReal.toRealHom _ _ _


-- @@ L499-499 verbatim
end NNReal


-- @@ L501-501 verbatim
namespace Complex


-- @@ L503-505 expanded
@[simp, norm_cast]
lemma ofReal_iterConv (f : G → ℝ) (n : ℕ) (a : G) :
    (↑((iterConv f n) a) : ℂ) = (iterConv ((↑) ∘ f) n) a :=
  map_iterConv ofRealHom _ _ _


-- @@ L507-507 verbatim
end Complex
