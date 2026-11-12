/-
# The convolution algebra is pre-Lie

`Operad.Convolution` built `Conv R C P`, the degreewise linear maps from a cooperad to an operad,
with the product that decomposes in `C`, applies the two maps and recomposes in `P`. This file
proves that the product is right pre-Lie,

  `(f ⋆c g) ⋆c h - f ⋆c (g ⋆c h) = (f ⋆c h) ⋆c g - f ⋆c (h ⋆c g)`,

and packages `Conv` as a right pre-Lie algebra, a Lie ring and a Lie algebra over `R`.

## The route

It is the one `Operad.PreLie` walks for the total space, transposed to linear maps. Expanding
`(f ⋆c g) ⋆c h` at arity `m` gives a double sum over an outer decomposition `x = (a, n, b)` of
`m`, where `h` is inserted, and an inner decomposition `y = (a', n', b')` of `a + 1 + b`, where `g`
is. Where `h`'s slot `a` sits relative to `g`'s block `[a', a' + n')` sorts the terms:

* **nested**, `a' ≤ a < a' + n'`: `h` goes into `g`. These terms are exactly those of
  `f ⋆c (g ⋆c h)`, by `decomp_assoc_seq` against `comp_assoc_seq` (`nested_term`);
* **before** and **after**: `h` goes into a slot of `f` disjoint from `g`'s. A term with `h` after
  `g` is a term of `(f ⋆c h) ⋆c g` with `g` before `h`, by `decomp_assoc_par` against
  `comp_assoc_par` (`parallel_term`), and the same bijection with `g` and `h` exchanged matches
  the rest.

So the associator is the sum of the two disjoint parts, and exchanging `g` and `h` exchanges them.

Two things differ from the total-space proof. The cooperad axioms are equalities of linear maps
into tensor products, so each term identity is proved by factoring both sides through the same
decomposition map and comparing the two remaining maps on pure tensors. And arity `0` is allowed
throughout: an operation with no inputs can be inserted, which is why the nested condition is a
strict interval rather than a block of fixed length.

## Index bookkeeping

`decomps m` is the finset of triples `(a, n, b)` with `a + n + b = m`. The term identities are
stated first for clean parameters (`nested_term`, `parallel_term`) and then for index variables
tied to the parameters by equations (`nested_term'`, `parallel_term'`); the second form is what the
bijections of sums consume, and `subst_vars` turns it into the first. So subtraction appears in
the bijections and never in a type.
-/
import Operad.Convolution
import Operad.PreLieLie
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma


-- @@ L46-46 verbatim
universe u v w


-- @@ L48-48 verbatim
namespace Operad


-- @@ L50-50 verbatim
open scoped TensorProduct

-- @@ L51-51 verbatim
open Finset


-- @@ L53-53 verbatim
namespace Conv


-- @@ L55-55 verbatim
variable {R : Type u} [CommRing R]

-- @@ L56-56 verbatim
variable {C : ℕ → Type v} [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [NSCooperad R C]

-- @@ L57-57 verbatim
variable {P : ℕ → Type w} [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]


-- @@ L59-59 verbatim
/-! ## Reindexing -/


-- @@ L61-65 verbatim
/-- Reindexing along a reflexive equality is the identity map. -/
@[simp] lemma reindex_toLinearMap_self {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)]
    [∀ n, Module R (Q n)] {n : ℕ} (h : n = n) :
    (reindex R Q h).toLinearMap = LinearMap.id := by
  ext x; exact reindex_self h x


-- @@ L67-71 verbatim
omit [NSCooperad R C] [NSOperad R P] in
/-- A degreewise family of maps commutes with reindexing. -/
lemma apply_reindex (f : Conv R C P) {k k' : ℕ} (e : k = k') (x : C k) :
    f k' (reindex R C e x) = reindex R P e (f k x) := by
  subst e; rfl


-- @@ L73-73 verbatim
/-! ## One term, with its two maps separated -/


-- @@ L75-83 verbatim
/-- The contribution of the decomposition `m = a + n + b` to a convolution product, for an
arbitrary map `φ` in the outer arity and `ψ` in the inner one: decompose, apply, recompose.
`convTerm f g m a n b` is `cterm m a b n (f _) (g n)`. -/
noncomputable def cterm (m a b n : ℕ) (φ : C (a + 1 + b) →ₗ[R] P (a + 1 + b))
    (ψ : C n →ₗ[R] P n) : C m →ₗ[R] P m :=
  if h : a + n + b = m then
    (reindex R P h).toLinearMap ∘ₗ compT a b ∘ₗ TensorProduct.map φ ψ ∘ₗ
      NSCooperad.decomp a b n ∘ₗ (reindex R C h.symm).toLinearMap
  else 0


-- @@ L85-90 verbatim
lemma cterm_of_eq {m a b n : ℕ} (h : a + n + b = m) (φ : C (a + 1 + b) →ₗ[R] P (a + 1 + b))
    (ψ : C n →ₗ[R] P n) :
    cterm m a b n φ ψ
      = (reindex R P h).toLinearMap ∘ₗ compT a b ∘ₗ TensorProduct.map φ ψ ∘ₗ
          NSCooperad.decomp a b n ∘ₗ (reindex R C h.symm).toLinearMap :=
  dif_pos h


-- @@ L92-94 verbatim
lemma cterm_of_ne {m a b n : ℕ} (h : a + n + b ≠ m) (φ : C (a + 1 + b) →ₗ[R] P (a + 1 + b))
    (ψ : C n →ₗ[R] P n) : cterm m a b n φ ψ = 0 :=
  dif_neg h


-- @@ L96-97 verbatim
lemma convTerm_eq_cterm (f g : Conv R C P) (m a n b : ℕ) :
    convTerm f g m a n b = cterm m a b n (f (a + 1 + b)) (g n) := rfl


-- @@ L99-99 verbatim
/-! ### Bilinearity of a term -/


-- @@ L101-107 verbatim
lemma cterm_add_left (m a b n : ℕ) (φ₁ φ₂ : C (a + 1 + b) →ₗ[R] P (a + 1 + b))
    (ψ : C n →ₗ[R] P n) :
    cterm m a b n (φ₁ + φ₂) ψ = cterm m a b n φ₁ ψ + cterm m a b n φ₂ ψ := by
  by_cases h : a + n + b = m
  · simp only [cterm_of_eq h, TensorProduct.map_add_left, LinearMap.add_comp,
      LinearMap.comp_add]
  · simp only [cterm_of_ne h, add_zero]


-- @@ L109-115 verbatim
lemma cterm_add_right (m a b n : ℕ) (φ : C (a + 1 + b) →ₗ[R] P (a + 1 + b))
    (ψ₁ ψ₂ : C n →ₗ[R] P n) :
    cterm m a b n φ (ψ₁ + ψ₂) = cterm m a b n φ ψ₁ + cterm m a b n φ ψ₂ := by
  by_cases h : a + n + b = m
  · simp only [cterm_of_eq h, TensorProduct.map_add_right, LinearMap.add_comp,
      LinearMap.comp_add]
  · simp only [cterm_of_ne h, add_zero]


-- @@ L117-122 verbatim
lemma cterm_zero_left (m a b n : ℕ) (ψ : C n →ₗ[R] P n) :
    cterm m a b n (0 : C (a + 1 + b) →ₗ[R] P (a + 1 + b)) ψ = 0 := by
  by_cases h : a + n + b = m
  · simp only [cterm_of_eq h, TensorProduct.map_zero_left, LinearMap.zero_comp,
      LinearMap.comp_zero]
  · exact cterm_of_ne h _ _


-- @@ L124-129 verbatim
lemma cterm_zero_right (m a b n : ℕ) (φ : C (a + 1 + b) →ₗ[R] P (a + 1 + b)) :
    cterm m a b n φ (0 : C n →ₗ[R] P n) = 0 := by
  by_cases h : a + n + b = m
  · simp only [cterm_of_eq h, TensorProduct.map_zero_right, LinearMap.zero_comp,
      LinearMap.comp_zero]
  · exact cterm_of_ne h _ _


-- @@ L131-136 verbatim
/-- A term, as an additive map in its outer map. -/
noncomputable def ctermLeft (m a b n : ℕ) (ψ : C n →ₗ[R] P n) :
    (C (a + 1 + b) →ₗ[R] P (a + 1 + b)) →+ (C m →ₗ[R] P m) where
  toFun φ := cterm m a b n φ ψ
  map_zero' := cterm_zero_left m a b n ψ
  map_add' φ₁ φ₂ := cterm_add_left m a b n φ₁ φ₂ ψ


-- @@ L138-143 verbatim
/-- A term, as an additive map in its inner map. -/
noncomputable def ctermRight (m a b n : ℕ) (φ : C (a + 1 + b) →ₗ[R] P (a + 1 + b)) :
    (C n →ₗ[R] P n) →+ (C m →ₗ[R] P m) where
  toFun ψ := cterm m a b n φ ψ
  map_zero' := cterm_zero_right m a b n φ
  map_add' ψ₁ ψ₂ := cterm_add_right m a b n φ ψ₁ ψ₂


-- @@ L145-148 verbatim
lemma cterm_sum_left {ι : Type*} (s : Finset ι) (m a b n : ℕ)
    (φ : ι → (C (a + 1 + b) →ₗ[R] P (a + 1 + b))) (ψ : C n →ₗ[R] P n) :
    cterm m a b n (∑ i ∈ s, φ i) ψ = ∑ i ∈ s, cterm m a b n (φ i) ψ :=
  map_sum (ctermLeft m a b n ψ) φ s


-- @@ L150-153 verbatim
lemma cterm_sum_right {ι : Type*} (s : Finset ι) (m a b n : ℕ)
    (φ : C (a + 1 + b) →ₗ[R] P (a + 1 + b)) (ψ : ι → (C n →ₗ[R] P n)) :
    cterm m a b n φ (∑ i ∈ s, ψ i) = ∑ i ∈ s, cterm m a b n φ (ψ i) :=
  map_sum (ctermRight m a b n φ) ψ s


-- @@ L155-155 verbatim
/-! ## Decompositions of an arity -/


-- @@ L157-159 verbatim
/-- The decompositions `a + n + b = m` of an arity, as triples `(a, n, b)`. -/
def decomps (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (m + 1) ×ˢ range (m + 1) ×ˢ range (m + 1)).filter fun x => x.1 + x.2.1 + x.2.2 = m


-- @@ L161-164 verbatim
@[simp] lemma mem_decomps {m : ℕ} {x : ℕ × ℕ × ℕ} :
    x ∈ decomps m ↔ x.1 + x.2.1 + x.2.2 = m := by
  simp only [decomps, mem_filter, mem_product, mem_range]
  omega


-- @@ L166-176 verbatim
/-- **The convolution product as a sum over the decompositions of the arity.** -/
lemma star_eq_sum (f g : Conv R C P) (m : ℕ) :
    (f ⋆c g) m = ∑ x ∈ decomps m, cterm m x.1 x.2.2 x.2.1 (f (x.1 + 1 + x.2.2)) (g x.2.1) := by
  rw [star_apply, decomps, sum_filter, sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_product]
  refine sum_congr rfl fun n _ => sum_congr rfl fun b _ => ?_
  dsimp only
  split_ifs with h
  · rfl
  · exact cterm_of_ne h _ _


-- @@ L178-182 verbatim
/-- The summand of `(f ⋆c g) ⋆c h` at arity `m`: `h` inserted at the outer decomposition `x`, and
`g` at the inner decomposition `y` of `x.1 + 1 + x.2.2`. -/
noncomputable def lterm (f g h : Conv R C P) (m : ℕ) (x y : ℕ × ℕ × ℕ) : C m →ₗ[R] P m :=
  cterm m x.1 x.2.2 x.2.1
    (cterm (x.1 + 1 + x.2.2) y.1 y.2.2 y.2.1 (f (y.1 + 1 + y.2.2)) (g y.2.1)) (h x.2.1)


-- @@ L184-188 verbatim
/-- The summand of `f ⋆c (g ⋆c h)` at arity `m`: `g ⋆c h` inserted at the outer decomposition `x`,
and `h` at the decomposition `y` of `x.2.1`. -/
noncomputable def rterm (f g h : Conv R C P) (m : ℕ) (x y : ℕ × ℕ × ℕ) : C m →ₗ[R] P m :=
  cterm m x.1 x.2.2 x.2.1 (f (x.1 + 1 + x.2.2))
    (cterm x.2.1 y.1 y.2.2 y.2.1 (g (y.1 + 1 + y.2.2)) (h y.2.1))


-- @@ L190-196 verbatim
lemma star_star_left_eq (f g h : Conv R C P) (m : ℕ) :
    ((f ⋆c g) ⋆c h) m
      = ∑ x ∈ decomps m, ∑ y ∈ decomps (x.1 + 1 + x.2.2), lterm f g h m x y := by
  rw [star_eq_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [star_eq_sum, cterm_sum_left]
  rfl


-- @@ L198-203 verbatim
lemma star_star_right_eq (f g h : Conv R C P) (m : ℕ) :
    (f ⋆c (g ⋆c h)) m = ∑ x ∈ decomps m, ∑ y ∈ decomps x.2.1, rterm f g h m x y := by
  rw [star_eq_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [star_eq_sum, cterm_sum_right]
  rfl


-- @@ L205-205 verbatim
/-! ## Sorting the inner decompositions -/


-- @@ L207-221 verbatim
/-- The inner decompositions fall in three classes, by where the outer slot `x.1` sits relative to
the inner block `[y.1, y.1 + y.2.1)`: inside it, before it, or after it. -/
lemma sum_split3 {M : Type*} [AddCommMonoid M] (x : ℕ × ℕ × ℕ) (s : Finset (ℕ × ℕ × ℕ))
    (F : ℕ × ℕ × ℕ → M) :
    ∑ y ∈ s, F y
      = ∑ y ∈ s.filter (fun y => y.1 ≤ x.1 ∧ x.1 < y.1 + y.2.1), F y
        + ∑ y ∈ s.filter (fun y => x.1 < y.1), F y
        + ∑ y ∈ s.filter (fun y => y.1 + y.2.1 ≤ x.1), F y := by
  simp only [sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  by_cases h1 : y.1 ≤ x.1 ∧ x.1 < y.1 + y.2.1
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega), add_zero, add_zero]
  · by_cases h2 : x.1 < y.1
    · rw [if_neg h1, if_pos h2, if_neg (by omega), zero_add, add_zero]
    · rw [if_neg h1, if_neg h2, if_pos (by omega), zero_add, zero_add]


-- @@ L223-229 verbatim
/-! ## The nested terms: `h` inserted into `g`

With `g` of arity `c + 1 + d` sitting after `a` inputs of `f`, and `h` of arity `p` inserted after
`c` inputs of `g`, the term of `(f ⋆c g) ⋆c h` has `h` after `a + c` inputs of `f ⋆c g`, and the
term of `f ⋆c (g ⋆c h)` has `g ⋆c h` after `a` inputs of `f`. Both factor through the same
two-step decomposition of `C m`, by `decomp_assoc_seq`, and the two remaining maps agree on pure
tensors by `comp_assoc_seq`. -/


-- @@ L231-269 verbatim
/-- **Sequential associativity, termwise.** -/
theorem nested_term {a b c d p : ℕ} (m : ℕ) (hm : a + (c + p + d) + b = m)
    (φ : C (a + 1 + b) →ₗ[R] P (a + 1 + b)) (χ : C (c + 1 + d) →ₗ[R] P (c + 1 + d))
    (ψ : C p →ₗ[R] P p) :
    cterm m (a + c) (d + b) p (cterm (a + c + 1 + (d + b)) a b (c + 1 + d) φ χ) ψ
      = cterm m a b (c + p + d) φ (cterm (c + p + d) c d p χ ψ) := by
  subst hm
  have e1 : a + c + 1 + (d + b) = a + (c + 1 + d) + b := by omega
  have e2 : a + (c + p + d) + b = a + c + p + (d + b) := by omega
  rw [cterm_of_eq e2.symm, cterm_of_eq e1.symm, cterm_of_eq rfl, cterm_of_eq rfl]
  simp only [reindex_toLinearMap_self, LinearMap.id_comp, LinearMap.comp_id]
  -- The common two-step decomposition, and the two maps out of it.
  let D : C (a + (c + p + d) + b) →ₗ[R] (C (a + 1 + b) ⊗[R] C (c + 1 + d)) ⊗[R] C p :=
    LinearMap.rTensor (C p)
        (NSCooperad.decomp a b (c + 1 + d) ∘ₗ (reindex R C e1).toLinearMap) ∘ₗ
      NSCooperad.decomp (a + c) (d + b) p ∘ₗ (reindex R C e2).toLinearMap
  let Φ₁ : (C (a + 1 + b) ⊗[R] C (c + 1 + d)) ⊗[R] C p →ₗ[R] P (a + (c + p + d) + b) :=
    (reindex R P e2.symm).toLinearMap ∘ₗ compT (a + c) (d + b) ∘ₗ
      TensorProduct.map ((reindex R P e1.symm).toLinearMap ∘ₗ compT a b ∘ₗ
        TensorProduct.map φ χ) ψ
  let Φ₂ : (C (a + 1 + b) ⊗[R] C (c + 1 + d)) ⊗[R] C p →ₗ[R] P (a + (c + p + d) + b) :=
    compT a b ∘ₗ TensorProduct.map φ (compT c d ∘ₗ TensorProduct.map χ ψ) ∘ₗ
      (TensorProduct.assoc R (C (a + 1 + b)) (C (c + 1 + d)) (C p)).toLinearMap
  have hΦ : Φ₁ = Φ₂ := by
    refine TensorProduct.ext_threefold fun x y z => ?_
    simp only [Φ₁, Φ₂, LinearMap.comp_apply, TensorProduct.map_tmul, compT_tmul,
      LinearEquiv.coe_coe, TensorProduct.assoc_tmul]
    exact NSOperad.comp_assoc_seq a b c d (φ x) (χ y) (ψ z)
  calc _ = Φ₁ ∘ₗ D := by
        ext x
        simp only [Φ₁, D, LinearMap.comp_apply, LinearMap.map_rTensor, LinearMap.comp_assoc]
    _ = Φ₂ ∘ₗ D := by rw [hΦ]
    _ = _ := by
        ext x
        have hco := LinearMap.congr_fun
          (NSCooperad.decomp_assoc_seq (R := R) (C := C) a b c d p) x
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hco
        simp only [Φ₂, D, LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [← hco, LinearMap.map_lTensor, LinearMap.comp_assoc]


-- @@ L271-278 verbatim
/-- `nested_term` for index variables tied to its parameters by equations. -/
theorem nested_term' (f g h : Conv R C P) (m a b c d p A N B A' N' B' A₂ N₂ B₂ C₂ P₂ D₂ : ℕ)
    (hA : A = a + c) (hN : N = p) (hB : B = d + b) (hA' : A' = a) (hN' : N' = c + 1 + d)
    (hB' : B' = b) (hA₂ : A₂ = a) (hN₂ : N₂ = c + p + d) (hB₂ : B₂ = b) (hC₂ : C₂ = c)
    (hP₂ : P₂ = p) (hD₂ : D₂ = d) (hm : a + (c + p + d) + b = m) :
    lterm f g h m (A, N, B) (A', N', B') = rterm f g h m (A₂, N₂, B₂) (C₂, P₂, D₂) := by
  subst_vars
  exact nested_term _ rfl _ _ _


-- @@ L280-309 verbatim
/-- **The nested part of `(f ⋆c g) ⋆c h` is `f ⋆c (g ⋆c h)`.** -/
lemma sum_nested (f g h : Conv R C P) (m : ℕ) :
    ∑ x ∈ decomps m, ∑ y ∈ (decomps (x.1 + 1 + x.2.2)).filter
        (fun y => y.1 ≤ x.1 ∧ x.1 < y.1 + y.2.1), lterm f g h m x y
      = ∑ x ∈ decomps m, ∑ y ∈ decomps x.2.1, rterm f g h m x y := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij'
    (fun q => ⟨(q.2.1, q.1.1 - q.2.1 + q.1.2.1 + (q.2.1 + q.2.2.1 - 1 - q.1.1), q.2.2.2),
      (q.1.1 - q.2.1, q.1.2.1, q.2.1 + q.2.2.1 - 1 - q.1.1)⟩)
    (fun q => ⟨(q.1.1 + q.2.1, q.2.2.1, q.2.2.2 + q.1.2.2),
      (q.1.1, q.2.1 + 1 + q.2.2.2, q.1.2.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨A, N, B⟩, ⟨A', N', B'⟩⟩ hq
    simp only [mem_sigma, mem_decomps, mem_filter, and_true] at hq ⊢
    omega
  · rintro ⟨⟨A, N, B⟩, ⟨C₂, P₂, D₂⟩⟩ hq
    simp only [mem_sigma, mem_decomps, mem_filter] at hq ⊢
    omega
  · rintro ⟨⟨A, N, B⟩, ⟨A', N', B'⟩⟩ hq
    simp only [mem_sigma, mem_decomps, mem_filter] at hq
    simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, and_true, true_and]
    omega
  · rintro ⟨⟨A, N, B⟩, ⟨C₂, P₂, D₂⟩⟩ hq
    simp only [mem_sigma, mem_decomps] at hq
    simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, and_true, true_and]
    omega
  · rintro ⟨⟨A, N, B⟩, ⟨A', N', B'⟩⟩ hq
    simp only [mem_sigma, mem_decomps, mem_filter] at hq
    dsimp only
    exact nested_term' f g h m A' B' (A - A') (A' + N' - 1 - A) N A N B A' N' B' _ _ _ _ _ _
      (by omega) rfl (by omega) rfl (by omega) rfl rfl (by omega) rfl rfl rfl rfl (by omega)


-- @@ L311-317 verbatim
/-! ## The disjoint terms

`f` of arity `a + 1 + b + 1 + c` has two slots, after `a` inputs and after `a + 1 + b`. Inserting
`X` of arity `n` in the first and `Y` of arity `p` in the second can be done in either order, and
`decomp_assoc_par` against `comp_assoc_par` says the two orders agree term by term. In
`(f ⋆c g) ⋆c h` the first order is a term with `h` after `g`; in `(f ⋆c h) ⋆c g` the second order
is a term with `g` before `h`. -/


-- @@ L319-368 verbatim
/-- **Parallel associativity, termwise.** -/
theorem parallel_term (f : Conv R C P) {a b c n p : ℕ} (m : ℕ) (hm : a + n + b + p + c = m)
    (X : C n →ₗ[R] P n) (Y : C p →ₗ[R] P p) :
    cterm m (a + n + b) c p
        (cterm (a + n + b + 1 + c) a (b + 1 + c) n (f (a + 1 + (b + 1 + c))) X) Y
      = cterm m a (b + p + c) n
          (cterm (a + 1 + (b + p + c)) (a + 1 + b) c p (f (a + 1 + b + 1 + c)) Y) X := by
  subst hm
  have k1 : a + n + (b + 1 + c) = a + n + b + 1 + c := by omega
  have l1 : a + 1 + b + p + c = a + 1 + (b + p + c) := by omega
  have l2 : a + n + (b + p + c) = a + n + b + p + c := by omega
  have q2 : a + 1 + b + 1 + c = a + 1 + (b + 1 + c) := by omega
  rw [cterm_of_eq rfl, cterm_of_eq k1, cterm_of_eq l2, cterm_of_eq l1]
  simp only [reindex_toLinearMap_self, LinearMap.id_comp, LinearMap.comp_id]
  -- The common two-step decomposition, and the two maps out of it.
  let E : C (a + n + b + p + c) →ₗ[R] (C (a + 1 + b + 1 + c) ⊗[R] C p) ⊗[R] C n :=
    LinearMap.rTensor (C n)
        (NSCooperad.decomp (a + 1 + b) c p ∘ₗ (reindex R C l1.symm).toLinearMap) ∘ₗ
      NSCooperad.decomp a (b + p + c) n ∘ₗ (reindex R C l2.symm).toLinearMap
  let Ψ₁ : (C (a + 1 + b + 1 + c) ⊗[R] C p) ⊗[R] C n →ₗ[R] P (a + n + b + p + c) :=
    compT (a + n + b) c ∘ₗ
      TensorProduct.map ((reindex R P k1).toLinearMap ∘ₗ compT a (b + 1 + c) ∘ₗ
        TensorProduct.map (f (a + 1 + (b + 1 + c))) X) Y ∘ₗ
      (swapLast R (C (a + 1 + (b + 1 + c))) (C p) (C n)).toLinearMap ∘ₗ
      LinearMap.rTensor (C n)
        (TensorProduct.congr (reindex R C q2) (LinearEquiv.refl R (C p))).toLinearMap
  let Ψ₂ : (C (a + 1 + b + 1 + c) ⊗[R] C p) ⊗[R] C n →ₗ[R] P (a + n + b + p + c) :=
    (reindex R P l2).toLinearMap ∘ₗ compT a (b + p + c) ∘ₗ
      TensorProduct.map ((reindex R P l1).toLinearMap ∘ₗ compT (a + 1 + b) c ∘ₗ
        TensorProduct.map (f (a + 1 + b + 1 + c)) Y) X
  have hΨ : Ψ₁ = Ψ₂ := by
    refine TensorProduct.ext_threefold fun x y z => ?_
    simp only [Ψ₁, Ψ₂, swapLast, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      TensorProduct.map_tmul, compT_tmul, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.assoc_tmul,
      TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul, apply_reindex]
    rw [← NSOperad.comp_assoc_par a b c (f (a + 1 + b + 1 + c) x) (X z) (Y y), reindex_reindex,
      reindex_self]
  calc _ = Ψ₁ ∘ₗ E := by
        ext x
        have hco := LinearMap.congr_fun
          (NSCooperad.decomp_assoc_par (R := R) (C := C) a b c n p) x
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hco
        simp only [Ψ₁, E, LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [← LinearMap.rTensor_comp_apply, ← hco, LinearMap.map_rTensor]
        simp only [LinearMap.comp_assoc]
    _ = Ψ₂ ∘ₗ E := by rw [hΨ]
    _ = _ := by
        ext x
        simp only [Ψ₂, E, LinearMap.comp_apply, LinearMap.map_rTensor, LinearMap.comp_assoc]


-- @@ L370-379 verbatim
/-- `parallel_term` for index variables tied to its parameters by equations: a term of
`(f ⋆c g) ⋆c h` with `h` after `g` is a term of `(f ⋆c h) ⋆c g` with `g` before `h`. -/
theorem parallel_term' (f g h : Conv R C P)
    (m a b c n p A N B A' N' B' A₂ N₂ B₂ A₂' N₂' B₂' : ℕ)
    (hA : A = a + n + b) (hN : N = p) (hB : B = c) (hA' : A' = a) (hN' : N' = n)
    (hB' : B' = b + 1 + c) (hA₂ : A₂ = a) (hN₂ : N₂ = n) (hB₂ : B₂ = b + p + c)
    (hA₂' : A₂' = a + 1 + b) (hN₂' : N₂' = p) (hB₂' : B₂' = c) (hm : a + n + b + p + c = m) :
    lterm f g h m (A, N, B) (A', N', B') = lterm f h g m (A₂, N₂, B₂) (A₂', N₂', B₂') := by
  subst_vars
  exact parallel_term f _ rfl _ _


-- @@ L381-412 verbatim
/-- **The terms of `(f ⋆c g) ⋆c h` with `h` after `g` are the terms of `(f ⋆c h) ⋆c g` with `g`
before `h`.** -/
lemma sum_after_eq_sum_before (f g h : Conv R C P) (m : ℕ) :
    ∑ x ∈ decomps m, ∑ y ∈ (decomps (x.1 + 1 + x.2.2)).filter (fun y => y.1 + y.2.1 ≤ x.1),
        lterm f g h m x y
      = ∑ x ∈ decomps m, ∑ y ∈ (decomps (x.1 + 1 + x.2.2)).filter (fun y => x.1 < y.1),
          lterm f h g m x y := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij'
    (fun q => ⟨(q.2.1, q.2.2.1, q.1.1 - q.2.1 - q.2.2.1 + q.1.2.1 + q.1.2.2),
      (q.1.1 + 1 - q.2.2.1, q.1.2.1, q.1.2.2)⟩)
    (fun q => ⟨(q.2.1 - 1 + q.1.2.1, q.2.2.1, q.2.2.2),
      (q.1.1, q.1.2.1, q.2.1 - q.1.1 + q.2.2.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨A, N, B⟩, ⟨A', N', B'⟩⟩ hq
    simp only [mem_sigma, mem_decomps, mem_filter] at hq ⊢
    omega
  · rintro ⟨⟨A, N, B⟩, ⟨A', N', B'⟩⟩ hq
    simp only [mem_sigma, mem_decomps, mem_filter] at hq ⊢
    omega
  · rintro ⟨⟨A, N, B⟩, ⟨A', N', B'⟩⟩ hq
    simp only [mem_sigma, mem_decomps, mem_filter] at hq
    simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, and_true, true_and]
    omega
  · rintro ⟨⟨A, N, B⟩, ⟨A', N', B'⟩⟩ hq
    simp only [mem_sigma, mem_decomps, mem_filter] at hq
    simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, and_true, true_and]
    omega
  · rintro ⟨⟨A, N, B⟩, ⟨A', N', B'⟩⟩ hq
    simp only [mem_sigma, mem_decomps, mem_filter] at hq
    dsimp only
    exact parallel_term' f g h m A' (A - A' - N') B N' N A N B A' N' B' _ _ _ _ _ _
      (by omega) rfl rfl rfl rfl (by omega) rfl rfl (by omega) (by omega) rfl rfl (by omega)


-- @@ L414-414 verbatim
/-! ## The pre-Lie identity -/


-- @@ L416-419 verbatim
/-- The part of `(f ⋆c g) ⋆c h` in which `h` is inserted before `g`. -/
noncomputable def beforePart (f g h : Conv R C P) (m : ℕ) : C m →ₗ[R] P m :=
  ∑ x ∈ decomps m, ∑ y ∈ (decomps (x.1 + 1 + x.2.2)).filter (fun y => x.1 < y.1),
    lterm f g h m x y


-- @@ L421-424 verbatim
/-- The part of `(f ⋆c g) ⋆c h` in which `h` is inserted after `g`. -/
noncomputable def afterPart (f g h : Conv R C P) (m : ℕ) : C m →ₗ[R] P m :=
  ∑ x ∈ decomps m, ∑ y ∈ (decomps (x.1 + 1 + x.2.2)).filter (fun y => y.1 + y.2.1 ≤ x.1),
    lterm f g h m x y


-- @@ L426-432 verbatim
/-- **The associator is the disjoint part.** -/
lemma associator_eq (f g h : Conv R C P) (m : ℕ) :
    ((f ⋆c g) ⋆c h) m - (f ⋆c (g ⋆c h)) m = beforePart f g h m + afterPart f g h m := by
  rw [star_star_left_eq, star_star_right_eq, ← sum_nested]
  simp only [fun x => sum_split3 x (decomps (x.1 + 1 + x.2.2)) (lterm f g h m x),
    sum_add_distrib, beforePart, afterPart]
  abel


-- @@ L434-442 verbatim
/-- **The pre-Lie identity.** The associator of the convolution product is symmetric in its last
two arguments. -/
theorem star_assoc_symm (f g h : Conv R C P) :
    (f ⋆c g) ⋆c h - f ⋆c (g ⋆c h) = (f ⋆c h) ⋆c g - f ⋆c (h ⋆c g) := by
  funext m
  show ((f ⋆c g) ⋆c h) m - (f ⋆c (g ⋆c h)) m = ((f ⋆c h) ⋆c g) m - (f ⋆c (h ⋆c g)) m
  rw [associator_eq, associator_eq, afterPart, afterPart, sum_after_eq_sum_before,
    sum_after_eq_sum_before]
  exact add_comm _ _


-- @@ L444-444 verbatim
end Conv


-- @@ L446-449 verbatim
/-! ## The convolution algebra as a pre-Lie, Lie ring and Lie algebra

`Conv R C P` is a `Pi` type, so its ring structure is put on a type synonym, `ConvAlg`, rather
than as instances on all families of linear maps. -/


-- @@ L451-455 verbatim
/-- **The convolution algebra**, as a type carrying its product. -/
def ConvAlg (R : Type u) [CommRing R] (C : ℕ → Type v) (P : ℕ → Type w)
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] : Type (max v w) :=
  Conv R C P


-- @@ L457-457 verbatim
namespace ConvAlg


-- @@ L459-459 verbatim
noncomputable section


-- @@ L461-461 verbatim
variable {R : Type u} [CommRing R]

-- @@ L462-462 verbatim
variable {C : ℕ → Type v} [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [NSCooperad R C]

-- @@ L463-463 verbatim
variable {P : ℕ → Type w} [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]


-- @@ L465-465 verbatim
instance : AddCommGroup (ConvAlg R C P) := inferInstanceAs (AddCommGroup (Conv R C P))


-- @@ L467-467 verbatim
instance : Module R (ConvAlg R C P) := inferInstanceAs (Module R (Conv R C P))


-- @@ L469-470 verbatim
/-- Into the algebra. -/
def of : Conv R C P ≃ₗ[R] ConvAlg R C P := LinearEquiv.refl R (Conv R C P)


-- @@ L472-472 verbatim
instance : Mul (ConvAlg R C P) := ⟨fun f g => of (Conv.star (of.symm f) (of.symm g))⟩


-- @@ L474-474 verbatim
lemma mul_def (f g : ConvAlg R C P) : f * g = of (Conv.star (of.symm f) (of.symm g)) := rfl


-- @@ L476-482 verbatim
instance : NonUnitalNonAssocRing (ConvAlg R C P) where
  __ := (inferInstance : AddCommGroup (ConvAlg R C P))
  mul := (· * ·)
  left_distrib f g h := Conv.star_add_right (R := R) (C := C) (P := P) f g h
  right_distrib f g h := Conv.star_add_left (R := R) (C := C) (P := P) f g h
  zero_mul f := Conv.star_zero_left (R := R) (C := C) (P := P) f
  mul_zero f := Conv.star_zero_right (R := R) (C := C) (P := P) f


-- @@ L484-489 verbatim
/-- **The convolution algebra is a right pre-Lie ring.** -/
instance : RightPreLieRing (ConvAlg R C P) where
  __ := (inferInstance : NonUnitalNonAssocRing (ConvAlg R C P))
  assoc_symm' f g h := by
    simp only [associator_apply]
    exact Conv.star_assoc_symm (R := R) (C := C) (P := P) f g h


-- @@ L491-492 verbatim
instance : IsScalarTower R (ConvAlg R C P) (ConvAlg R C P) where
  smul_assoc t f g := Conv.star_smul_left (R := R) (C := C) (P := P) t f g


-- @@ L494-495 verbatim
instance : SMulCommClass R (ConvAlg R C P) (ConvAlg R C P) where
  smul_comm t f g := (Conv.star_smul_right (R := R) (C := C) (P := P) t f g).symm


-- @@ L497-501 verbatim
/-- **The convolution algebra is a right pre-Lie algebra over `R`.** -/
instance : RightPreLieAlgebra R (ConvAlg R C P) where
  __ := (inferInstance : Module R (ConvAlg R C P))
  __ := (inferInstance : IsScalarTower R (ConvAlg R C P) (ConvAlg R C P))
  __ := (inferInstance : SMulCommClass R (ConvAlg R C P) (ConvAlg R C P))


-- @@ L503-504 verbatim
/-- **The convolution algebra is a Lie ring** under the commutator of `⋆c`. -/
instance : LieRing (ConvAlg R C P) := RightPreLieRing.toLieRing


-- @@ L506-507 verbatim
/-- **The convolution algebra is a Lie algebra over `R`.** -/
instance : LieAlgebra R (ConvAlg R C P) := RightPreLieRing.toLieAlgebra R


-- @@ L509-509 verbatim
lemma lie_def (f g : ConvAlg R C P) : ⁅f, g⁆ = f * g - g * f := rfl


-- @@ L511-513 verbatim
/-- The Lie bracket is the bracket `Conv.bracket` of `Operad.Convolution`. -/
lemma lie_eq_bracket (f g : Conv R C P) :
    ⁅of f, of g⁆ = of (Conv.bracket f g) := rfl


-- @@ L515-515 verbatim
end


-- @@ L517-517 verbatim
end ConvAlg


-- @@ L519-519 verbatim
end Operad
