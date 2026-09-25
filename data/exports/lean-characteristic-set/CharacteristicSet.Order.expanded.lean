import CharacteristicSet.MainDegree
import CharacteristicSet.TriangularSet


-- @@ L4-29 verbatim
/-!
# Orderings on polynomials and triangular sets

This file defines order structures on multivariate polynomials and triangular sets,
which are essential for the Characteristic Set Method (Wu's Method).

## Main definitions

* `MvPolynomial.order`: The order of a polynomial `p` is the pair `(max_vars p, mainDegree p)`,
  ordered lexicographically. This defines a well-ordering on polynomials when the variable type
  is well-founded.

* `TriangularSet.order`: The order of a triangular set is a lexicographic sequence
  of orders of its polynomials. For two triangular sets `S` and `T`, `S < T` if either:
  1. There exists `k < S.length` such that `S₀ ≈ T₀`, `S₁ ≈ T₁`, ..., `Sₖ₋₁ ≈ Tₖ₋₁` and `Sₖ < Tₖ`;
  2. `S.length > T.length` and `∀ i < T.length, Sᵢ ≈ Tᵢ`.

## Main results

* `MvPolynomial.instWellFoundedLT`: When `σ` is well-founded, polynomials are well-founded
  under the order ordering.

* `TriangularSet.instWellFoundedLT`: When `σ` is finite, triangular sets are well-founded
  under the order ordering. This guarantees termination of characteristic set algorithms.

-/


-- @@ L31-31 verbatim
variable {R σ : Type*} [CommSemiring R] [LinearOrder σ] {p q : MvPolynomial σ R}


-- @@ L33-33 verbatim
namespace MvPolynomial


-- @@ L35-35 verbatim
section Order


-- @@ L37-39 verbatim
/-- The order of a polynomial `p` is the pair `(max_vars p, degree p)`,
which is ordered lexicographically. -/
noncomputable def order (p : MvPolynomial σ R) : WithBot σ ×ₗ ℕ := (p.vars.max, p.mainDegree)


-- @@ L41-42 verbatim
theorem order_eq_iff : p.order = q.order ↔
    p.vars.max = q.vars.max ∧ p.mainDegree = q.mainDegree := Prod.mk_inj


-- @@ L44-47 verbatim
instance instPreorder : Preorder (MvPolynomial σ R) where
  le := InvImage (· ≤ ·) order
  le_refl := fun _ ↦ by rw [InvImage]
  le_trans := fun _ _ _ ↦ le_trans


-- @@ L49-49 verbatim
theorem le_def' : p ≤ q ↔ p.order ≤ q.order := Iff.rfl


-- @@ L51-52 verbatim
noncomputable instance instDecidableLE : DecidableLE (MvPolynomial σ R) := fun _ _ ↦
  decidable_of_iff _ le_def'.symm


-- @@ L54-54 verbatim
noncomputable instance instDecidableLT : DecidableLT (MvPolynomial σ R) := decidableLTOfDecidableLE


-- @@ L56-57 verbatim
instance instIsTotalLe : Std.Total (@LE.le (MvPolynomial σ R) _) where
  total p q := le_total p.order q.order


-- @@ L59-60 verbatim
theorem le_def : p ≤ q ↔ p.vars.max < q.vars.max ∨
    p.vars.max = q.vars.max ∧ p.mainDegree ≤ q.mainDegree := Prod.lex_def


-- @@ L62-64 verbatim
theorem le_iff_not_imp : p ≤ q ↔ ¬p.vars.max < q.vars.max →
    p.vars.max = q.vars.max ∧ p.mainDegree ≤ q.mainDegree :=
  Iff.trans le_def <| Decidable.or_iff_not_imp_left


-- @@ L66-67 verbatim
theorem max_vars_le_of_le : p ≤ q → p.vars.max ≤ q.vars.max :=
  fun h ↦ Or.elim (le_def.mp h) le_of_lt (fun h ↦ le_of_eq h.1)


-- @@ L69-71 verbatim
theorem lt_def' : p < q ↔ p.order < q.order := Iff.trans lt_iff_le_not_ge (by
  rw [le_def', le_def', not_le, and_iff_right_iff_imp]
  exact le_of_lt)


-- @@ L73-75 verbatim
theorem lt_def : p < q ↔ p.vars.max < q.vars.max ∨
    p.vars.max = q.vars.max ∧ p.mainDegree < q.mainDegree :=
  Iff.trans lt_def' Prod.lex_def


-- @@ L77-79 verbatim
theorem lt_iff_not_imp : p < q ↔ ¬p.vars.max < q.vars.max
    → p.vars.max = q.vars.max ∧ p.mainDegree < q.mainDegree :=
  Iff.trans lt_def <| Decidable.or_iff_not_imp_left


-- @@ L81-82 verbatim
theorem lt_of_max_vars_lt : p.vars.max < q.vars.max → p < q :=
  fun h ↦ lt_def.mpr <| Or.inl h


-- @@ L84-84 verbatim
@[simp] theorem not_lt_iff_ge : ¬(p < q) ↔ q ≤ p := by rw [le_def', lt_def', not_lt]


-- @@ L86-86 verbatim
@[simp] theorem not_le_iff_gt : ¬(p ≤ q) ↔ q < p := by rw [le_def', lt_def', not_le]


-- @@ L88-89 verbatim
theorem X_lt_of_lt [Nontrivial R] {i j : σ} : i < j → (X i : MvPolynomial σ R) < X j := fun h ↦ by
  apply lt_of_max_vars_lt; simpa only [vars_X, Finset.max_singleton, WithBot.coe_lt_coe] using h


-- @@ L91-91 verbatim
instance instSetoid : Setoid (MvPolynomial σ R) := AntisymmRel.setoid (MvPolynomial σ R) (· ≤ ·)


-- @@ L93-94 verbatim
noncomputable instance instDecidableRelEquiv : @DecidableRel (MvPolynomial σ R) _ (· ≈ ·) :=
  fun _ _ ↦ instDecidableAnd


-- @@ L96-96 verbatim
theorem equiv_def'' : p ≈ q ↔ p ≤ q ∧ q ≤ p := Iff.rfl


-- @@ L98-99 verbatim
theorem equiv_def' : p ≈ q ↔ p.order = q.order := Iff.trans equiv_def''
  (by rw [le_def', le_def']; exact Std.le_antisymm_iff)


-- @@ L101-102 verbatim
theorem equiv_def : p ≈ q ↔ ¬p < q ∧ ¬q < p := Iff.trans equiv_def''
  (by rw [not_lt_iff_ge, not_lt_iff_ge, and_comm])


-- @@ L104-105 verbatim
theorem equiv_iff : p ≈ q ↔ p.vars.max = q.vars.max ∧ p.mainDegree = q.mainDegree :=
  Iff.trans equiv_def' order_eq_iff


-- @@ L107-107 verbatim
theorem le_iff_lt_or_equiv : p ≤ q ↔ p < q ∨ p ≈ q := le_iff_lt_or_antisymmRel


-- @@ L109-109 verbatim
theorem lt_of_equiv_of_lt {r : MvPolynomial σ R} : p ≈ q → q < r → p < r := lt_of_antisymmRel_of_lt


-- @@ L111-111 verbatim
theorem lt_of_lt_of_equiv {r : MvPolynomial σ R} : p < q → q ≈ r → p < r := lt_of_lt_of_antisymmRel


-- @@ L113-113 verbatim
theorem equiv_of_le_of_ge : p ≤ q → q ≤ p → p ≈ q := And.intro


-- @@ L115-116 verbatim
protected theorem zero_le : 0 ≤ p :=
  le_def'.mpr <| StrictMono.minimal_preimage_bot (fun ⦃_ _⦄ a ↦ a) rfl p.order


-- @@ L118-118 verbatim
end Order


-- @@ L120-120 verbatim
section WellFounded


-- @@ L122-127 verbatim
theorem wellFoundedLT_variables_of_wellFoundedLT [Nontrivial R] :
    WellFoundedLT (MvPolynomial σ R) → WellFoundedLT σ := fun h ↦ by
  rw [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain] at h ⊢
  contrapose! h
  rcases nonempty_subtype.mp h with ⟨f, hf⟩
  exact ⟨X ∘ f, fun n ↦ X_lt_of_lt <| hf n⟩


-- @@ L129-130 verbatim
instance instWellFoundedLT [WellFoundedLT σ] : WellFoundedLT (MvPolynomial σ R) :=
  Subrelation.isWellFounded (InvImage _ _) lt_def'.mp


-- @@ L132-133 verbatim
theorem wellFoundedLT_iff [Nontrivial R] : WellFoundedLT (MvPolynomial σ R) ↔ WellFoundedLT σ :=
  ⟨wellFoundedLT_variables_of_wellFoundedLT, @instWellFoundedLT _ _ _ _⟩


-- @@ L135-135 verbatim
variable [WellFoundedLT (MvPolynomial σ R)] (PS : Set (MvPolynomial σ R))


-- @@ L137-139 verbatim
theorem Set.has_min (h : PS.Nonempty) : ∃ p ∈ PS, ∀ q ∈ PS, ¬q < p :=
  haveI : WellFounded (· < ·) := @wellFounded_lt (MvPolynomial σ R) _ _
  WellFounded.has_min this PS h


-- @@ L141-142 verbatim
/-- The minimal element of a nonempty set of multivariate polynomials. -/
noncomputable def Set.min (h : PS.Nonempty) : MvPolynomial σ R := Exists.choose (has_min PS h)


-- @@ L144-144 verbatim
theorem Set.min_mem (h : PS.Nonempty) : (min PS h) ∈ PS := (Exists.choose_spec (has_min PS h)).1


-- @@ L146-146 verbatim
end WellFounded

-- @@ L147-147 verbatim
end MvPolynomial



-- @@ L150-150 verbatim
open MvPolynomial


-- @@ L152-152 verbatim
namespace TriangularSet


-- @@ L154-154 verbatim
variable {S T : TriangularSet σ R} {m n : ℕ}


-- @@ L156-157 verbatim
theorem apply_lt_of_index_lt (h : n < S.length) : m < n → S m < S n :=
  fun hmn ↦ MvPolynomial.lt_of_max_vars_lt <| max_vars_lt_of_index_lt h hmn


-- @@ L159-162 verbatim
theorem index_lt_of_apply_lt (h : m < S.length) : S m < S n → m < n := fun hs ↦
  Decidable.byContradiction fun hmn ↦ False.elim <| match Nat.eq_or_lt_of_not_lt hmn with
    | Or.inl hmn => Eq.not_lt (congrArg S hmn) hs
    | Or.inr hmn => (MvPolynomial.not_lt_iff_ge.mpr <| le_of_lt hs) (apply_lt_of_index_lt h hmn)


-- @@ L164-167 verbatim
theorem le_of_index_le : m ≤ n → n < S.length → S m ≤ S n := fun hmn h ↦
  Or.elim (lt_or_eq_of_le hmn)
    (fun hmn ↦ le_of_lt <| MvPolynomial.lt_of_max_vars_lt <| max_vars_lt_of_index_lt h hmn)
    (fun hmn ↦ by simp only [hmn, le_refl])


-- @@ L169-169 verbatim
/-! ### Order and Ordering -/


-- @@ L171-171 verbatim
section Order


-- @@ L173-179 verbatim
/-- The order of a Triangular Set is a lexicographic sequence of orders of its polynomials.
A more intuitive definition is `order_lt_iff`, `S < T` if one of the following two occurs:
1. There exists some `k < S.length` such that
   `S₀ ≈ T₀`, `S₁ ≈ T₁`, ..., `Sₖ₋₁ ≈ Tₖ₋₁` and `Sₖ < Tₖ`.
2. `S.length > T.length` and `∀ i < T.length, Sᵢ ≈ Tᵢ` -/
noncomputable def order (S : TriangularSet σ R) : Lex (ℕ → WithTop (WithBot σ ×ₗ ℕ)) :=
  fun i ↦ if i < S.length then WithTop.some (S i).order else ⊤


-- @@ L181-181 verbatim
theorem order_def : S.order = fun i ↦ if i < S.length then WithTop.some (S i).order else ⊤ := rfl


-- @@ L183-183 verbatim
theorem order_apply {i : ℕ} (h : i < S.length) : S.order i = (S i).order := if_pos h


-- @@ L185-185 verbatim
theorem order_apply' {i : ℕ} (h : S.length ≤ i) : S.order i = ⊤ := if_neg <| not_lt_of_ge h


-- @@ L187-224 verbatim
theorem order_lt_iff : S.order < T.order ↔ (∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i) ∨
    (T.length < S.length ∧ ∀ i < T.length, S i ≈ T i) where
  mp h := by
    rw [order_def, order_def, Pi.instLTLexForall] at h
    simp only [Pi.Lex] at h
    rcases h with ⟨k, hk1, hk2⟩
    have klts : k < S.length := Decidable.byContradiction fun h ↦ not_top_lt <| if_neg h ▸ hk2
    rw [if_pos klts] at hk2
    by_cases kltt : k < T.length
    · rw [if_pos kltt, WithTop.coe_lt_coe, ← MvPolynomial.lt_def'] at hk2
      refine Or.inl ⟨k, klts, hk2, fun i hi ↦ ?_⟩
      have := hk1 i hi
      rw [if_pos <| lt_trans hi klts, if_pos <| lt_trans hi kltt, WithTop.coe_eq_coe] at this
      exact MvPolynomial.equiv_def'.mpr this
    have tlek : T.length ≤ k := Nat.le_of_not_lt kltt
    have tlts : T.length < S.length := lt_of_le_of_lt tlek klts
    refine Or.inr ⟨tlts, fun i hi ↦ ?_⟩
    have := hk1 i <| lt_of_lt_of_le hi tlek
    rw [if_pos (lt_trans hi tlts), if_pos hi, WithTop.coe_eq_coe] at this
    exact MvPolynomial.equiv_def'.mpr this
  mpr h := by
    rw [order_def, order_def, Pi.instLTLexForall]
    simp only [Pi.Lex]
    rcases h with (⟨k, hk, hk1, hk2⟩ | ⟨hlen, heq⟩)
    · use k ⊓ T.length
      constructor
      · intro i hi
        have hi := lt_min_iff.mp hi
        simp only [if_pos <| lt_trans hi.1 hk]
        rw [if_pos hi.2, WithTop.coe_eq_coe, ← MvPolynomial.equiv_def']
        exact hk2 i hi.1
      by_cases klt' : k < T.length
      · simpa [min_eq_left_of_lt klt', hk, klt'] using MvPolynomial.lt_def'.mp hk1
      have : T.length ≤ k := Nat.le_of_not_lt klt'
      simp [min_eq_right_iff.mpr this, lt_of_le_of_lt this hk]
    refine ⟨T.length, fun i hi ↦ ?_, ?_⟩
    · simpa [lt_trans hi hlen, hi] using MvPolynomial.equiv_def'.mp (heq i hi)
    simp only [hlen, reduceIte, lt_self_iff_false, WithTop.coe_lt_top]


-- @@ L226-249 verbatim
theorem order_eq_iff : S.order = T.order ↔ S.length = T.length ∧ ∀ k, S k ≈ T k where
  mp h := by
    rw [order_def, order_def] at h
    have h := funext_iff.mp h
    have tles := h S.length
    have slet := h T.length
    simp only [lt_self_iff_false, reduceIte, right_eq_ite_iff, WithTop.top_ne_coe, imp_false,
      not_lt, ite_eq_right_iff, WithTop.coe_ne_top] at tles slet
    have ltheq := eq_of_le_of_ge slet tles
    refine ⟨ltheq, fun i ↦ ?_⟩
    by_cases ilt : i < T.length
    · have := h i
      simp only [ltheq, ilt, reduceIte, WithTop.coe_eq_coe] at this
      exact MvPolynomial.equiv_def'.mpr this
    have t0 : T i = 0 := eq_zero_iff_length_le.mp <| Nat.le_of_not_lt ilt
    have s0 : S i = 0 := eq_zero_iff_length_le.mp <| Nat.le_of_not_lt <| ltheq ▸ ilt
    rw [t0, s0]
  mpr h := by
    rw [order_def, order_def, h.1]
    funext i
    split_ifs with ilt
    · rw [WithTop.coe_eq_coe]
      exact MvPolynomial.equiv_def'.mp <| h.2 i
    rfl


-- @@ L251-271 verbatim
open scoped Classical in
theorem order_le_iff : S.order ≤ T.order ↔ (∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i) ∨
    (T.length ≤ S.length ∧ ∀ k < T.length, S k ≤ T k) := by
  rw [Iff.trans le_iff_lt_or_eq (or_congr order_lt_iff order_eq_iff), or_assoc]
  refine ⟨fun h ↦ Or.elim h Or.inl (fun h ↦ Or.inr <| Or.elim h
      (fun h ↦ ⟨le_of_lt h.1, fun k hk ↦ (MvPolynomial.equiv_def''.mp <| h.2 k hk).1⟩)
      (fun h ↦ ⟨ge_of_eq h.1, fun k hk ↦ (MvPolynomial.equiv_def''.mp <| h.2 k).1⟩)),
    fun h ↦ Or.elim h Or.inl (fun ⟨h1, h2⟩ ↦ ?_)⟩
  by_cases h : ∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i
  · exact Or.inl h
  have h2 : ∀ k < T.length, S k ≈ T k := by
    contrapose! h
    let ⟨k, ⟨hk1, hk2⟩, hk3⟩ := Nat.findX h
    rw [MvPolynomial.equiv_def, not_and', MvPolynomial.not_lt_iff_ge, not_not] at hk2
    exact ⟨k, lt_of_lt_of_le hk1 h1, hk2 <| h2 k hk1,
      fun i hi ↦ not_not.mp <| not_and.mp (hk3 _ hi) <| lt_trans hi hk1⟩
  refine Or.inr <| Or.elim (lt_or_eq_of_le h1)
    (fun h ↦ Or.inl ⟨h, h2⟩)
    (fun h ↦ Or.inr ⟨h.symm, fun k ↦ if hk : k < T.length then (h2 k hk) else by
      rw [eq_zero_iff_length_le.mp <| le_of_not_gt hk,
        eq_zero_iff_length_le.mp <| le_of_not_gt <| h ▸ hk]⟩)


-- @@ L273-278 verbatim
instance instPreorder : Preorder (TriangularSet σ R) where
  le := InvImage (· ≤ ·) order
  le_refl := fun _ ↦ by rw [InvImage]
  le_trans := fun _ _ _ hpq hqr ↦ le_trans hpq hqr
  lt S T := S.order ≤ T.order ∧ ¬T.order ≤ S.order
  lt_iff_le_not_ge := by intros; rw [InvImage, InvImage]


-- @@ L280-280 verbatim
theorem le_def' : S ≤ T ↔ S.order ≤ T.order := Iff.rfl


-- @@ L282-283 verbatim
noncomputable instance : DecidableLE (TriangularSet σ R) :=
  fun _ _ ↦ decidable_of_iff _ le_def'.symm


-- @@ L285-285 verbatim
noncomputable instance : DecidableLT (TriangularSet σ R) := decidableLTOfDecidableLE


-- @@ L287-288 verbatim
instance : Std.Total (@LE.le (TriangularSet σ R) _) where
  total S T := le_total S.order T.order


-- @@ L290-291 verbatim
theorem le_def : S ≤ T ↔ (∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i) ∨
    (T.length ≤ S.length ∧ ∀ k < T.length, S k ≤ T k) := order_le_iff


-- @@ L293-295 verbatim
theorem lt_def' : S < T ↔ S.order < T.order := Iff.trans lt_iff_le_not_ge (by
  rw [le_def', le_def', not_le]
  exact and_iff_right_iff_imp.mpr le_of_lt)


-- @@ L297-298 verbatim
theorem lt_def : S < T ↔ (∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i) ∨
    (T.length < S.length ∧ ∀ i < T.length, S i ≈ T i) := Iff.trans lt_def' order_lt_iff


-- @@ L300-302 verbatim
theorem lt_empty : S ≠ ∅ → S < ∅ := fun h ↦ lt_def.mpr <| Or.inr
  ⟨by rw [length_empty]; exact length_ge_one_iff.mpr h,
  fun i hi ↦ by rw [length_empty] at hi; exact absurd hi <| Nat.not_lt_zero i⟩


-- @@ L304-305 verbatim
theorem le_empty (S : TriangularSet σ R) : S ≤ ∅ :=
  Or.elim (eq_or_ne S ∅) le_of_eq <| le_of_lt ∘ lt_empty


-- @@ L307-307 verbatim
@[simp] theorem not_lt_iff_ge : ¬(S < T) ↔ T ≤ S := by rw [le_def', lt_def']; exact not_lt


-- @@ L309-309 verbatim
@[simp] theorem not_le_iff_gt : ¬(S ≤ T) ↔ T < S := by rw [le_def', lt_def']; exact not_le


-- @@ L311-328 verbatim
theorem ge_of_forall_equiv : (∀ n < S.length, ∃ i < T.length, T i ≈ S n) → T ≤ S := fun h ↦ by
  contrapose! h
  match lt_def.mp <| not_le_iff_gt.mp h with
  | .inl ⟨k, hk1, hk2, hk3⟩ =>
    refine ⟨k, hk1, fun i hi1 ↦ ?_⟩
    match Nat.lt_trichotomy i k with
    | .inl hi2 =>
      apply not_antisymmRel_of_lt
      rw [AntisymmRel.lt_congr_left <| Setoid.symm <| hk3 i hi2]
      exact apply_lt_of_index_lt hk1 hi2
    | .inr hi2 => match hi2 with
    | .inl hi2 => exact not_antisymmRel_of_gt (hi2 ▸ hk2)
    | .inr hi2 => exact not_antisymmRel_of_gt <| lt_trans hk2 <| apply_lt_of_index_lt hi1 hi2
  | .inr ⟨h1, h2⟩ =>
    refine ⟨T.length, h1, fun i hi1 ↦ ?_⟩
    apply not_antisymmRel_of_lt
    rw [AntisymmRel.lt_congr_left <| Setoid.symm <| h2 i hi1]
    exact apply_lt_of_index_lt h1 hi1


-- @@ L330-333 verbatim
theorem ge_of_subset : S ⊆ T → T ≤ S := fun h ↦
  ge_of_forall_equiv fun n hn ↦
    have ⟨i, hi1, hi2⟩ : S n ∈ T := h <| apply_mem hn
    ⟨i, hi1, by rw [hi2]⟩


-- @@ L335-335 verbatim
instance instSetoid : Setoid (TriangularSet σ R) := AntisymmRel.setoid _ (· ≤ ·)


-- @@ L337-338 verbatim
noncomputable instance instDecidableRelEquiv : @DecidableRel (TriangularSet σ R) _ (· ≈ ·) :=
  fun _ _ ↦ instDecidableAnd


-- @@ L340-340 verbatim
theorem equiv_def'' : S ≈ T ↔ S ≤ T ∧ T ≤ S := Iff.rfl


-- @@ L342-343 verbatim
theorem equiv_def' : S ≈ T ↔ S.order = T.order := Iff.trans equiv_def''
  (by rw [le_def', le_def']; exact Std.le_antisymm_iff)


-- @@ L345-346 verbatim
theorem equiv_def : S ≈ T ↔ ¬S < T ∧ ¬T < S := Iff.trans equiv_def''
  (by rw [not_lt_iff_ge, not_lt_iff_ge, and_comm])


-- @@ L348-349 verbatim
theorem equiv_iff : S ≈ T ↔ S.length = T.length ∧ (∀ k, S k ≈ T k) :=
  Iff.trans equiv_def' order_eq_iff


-- @@ L351-357 verbatim
theorem equiv_iff' : S ≈ T ↔ S.length = T.length ∧ (∀ k < S.length, S k ≈ T k) := by
  simp only [equiv_iff, and_congr_right_iff]
  refine fun h1 ↦ ⟨fun h2 k _ ↦ h2 k, fun h2 k ↦ ?_⟩
  if hk : k < S.length then exact h2 k hk
  else
    have : S.length ≤ k := Nat.le_of_not_lt hk
    rw [eq_zero_iff_length_le.mp this, eq_zero_iff_length_le.mp (h1 ▸ this)]


-- @@ L359-359 verbatim
theorem le_iff_lt_or_equiv : S ≤ T ↔ S < T ∨ S ≈ T := le_iff_lt_or_antisymmRel


-- @@ L361-362 verbatim
theorem lt_of_equiv_of_lt {U : TriangularSet σ R} : S ≈ T → T < U → S < U :=
  lt_of_antisymmRel_of_lt


-- @@ L364-365 verbatim
theorem lt_of_lt_of_equiv {U : TriangularSet σ R} : S < T → T ≈ U → S < U :=
  lt_of_lt_of_antisymmRel


-- @@ L367-367 verbatim
theorem equiv_of_le_of_ge : S ≤ T → T ≤ S → S ≈ T := And.intro


-- @@ L369-373 verbatim
theorem gt_of_ssubset : S ⊂ T → T < S := fun h ↦ by
  have := Set.ssubset_iff_subset_ne.mp h
  apply or_iff_not_imp_right.mp <|  le_iff_lt_or_equiv.mp <| ge_of_subset this.1
  refine Not.intro fun con ↦ absurd (length_lt_of_ssubset h) ?_
  exact not_lt_of_ge <| le_of_eq (equiv_iff.mp con).1




-- @@ L377-379 verbatim
theorem lt_take : n < S.length → S < S.take n := fun h ↦
  lt_def.mpr <| Or.inr ⟨S.length_take n ▸ inf_lt_of_left_lt h,
  fun i hi ↦ by rw [take_apply, if_pos (min_eq_left_of_lt h ▸ length_take S n ▸ hi)]⟩


-- @@ L381-387 verbatim
theorem lt_drop : S ≠ ∅ → 0 < n → S < S.drop n := fun h1 h2 ↦
  if gel : S.length ≤ n then drop_eq_empty_of_ge_length gel ▸ lt_empty h1
  else lt_def.mpr <| Or.inl ⟨0, length_gt_zero_iff.mpr h1, by
      rw [drop_apply, add_zero]
      apply MvPolynomial.lt_of_max_vars_lt
      exact max_vars_lt_of_index_lt (Nat.lt_of_not_le gel) h2,
    fun i hi ↦ absurd hi <| Nat.not_lt_zero i⟩


-- @@ L389-390 verbatim
theorem concat_lt {p : MvPolynomial σ R} (h : S.CanConcat p) : S.concat p h < S := lt_def.mpr <|
  Or.inr ⟨length_concat h ▸ lt_add_one S.length, fun i hi ↦ by rw [concat_apply h, if_pos hi]⟩


-- @@ L392-393 verbatim
theorem single_lt_empty [DecidableEq R] : p ≠ 0 → (single p) < ∅ :=
  fun h ↦ lt_empty <| (not_iff_not.mpr single_eq_zero_iff).mp h


-- @@ L395-399 verbatim
theorem gt_single_of_first_gt [DecidableEq R] : p ≠ 0 → p < S 0 → single p < S := fun hp hs ↦
  lt_def.mpr <| Or.inl ⟨0,
    Nat.lt_of_sub_eq_succ <| length_single hp,
    (single_apply_zero p).symm ▸ hs,
    fun i hi ↦ absurd hi <| Nat.not_lt_zero i⟩


-- @@ L401-401 verbatim
end Order



-- @@ L404-404 verbatim
/-! ### Well-Foundedness -/


-- @@ L406-406 verbatim
section WellFounded


-- @@ L408-420 verbatim
theorem wellFoundedLT_mvPolynomial_of_wellFoundedLT :
    WellFoundedLT (TriangularSet σ R) → WellFoundedLT (MvPolynomial σ R) := fun h ↦ by
  rw [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain] at h ⊢
  contrapose! h
  rcases nonempty_subtype.mp h with ⟨f, hf1⟩
  have hf2 (n : ℕ) : f n ≠ 0 := by
    by_contra con
    absurd con ▸ (hf1 n)
    exact MvPolynomial.not_lt_iff_ge.mpr MvPolynomial.zero_le
  use fun n ↦ single' (hf2 n)
  intro n
  refine lt_def.mpr <| Or.inl ⟨0, ?_⟩
  simpa [length_single'] using hf1 n


-- @@ L422-425 verbatim
theorem wellFoundedLT_variables_of_wellFoundedLT [Nontrivial R] :
    WellFoundedLT (TriangularSet σ R) → WellFoundedLT σ :=
  MvPolynomial.wellFoundedLT_variables_of_wellFoundedLT ∘
    wellFoundedLT_mvPolynomial_of_wellFoundedLT


-- @@ L427-447 verbatim
theorem wellFoundedGT_variables_of_wellFoundedLT [Nontrivial R] :
    WellFoundedLT (TriangularSet σ R) → WellFoundedGT σ := fun h ↦ by
  rw [WellFoundedGT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain]
  rw [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain] at h
  contrapose! h
  rcases nonempty_subtype.mp h with ⟨f, hf1⟩
  have hf2 (n : ℕ) : (MvPolynomial.X (f n) : MvPolynomial σ R) < MvPolynomial.X (f (n + 1)) :=
    MvPolynomial.X_lt_of_lt <| hf1 n
  let S (n : ℕ) : TriangularSet σ R := {
    toList := List.ofFn (fun i : Fin n ↦ MvPolynomial.X (f i.1))
    zero_notMem' := by simp only [List.mem_ofFn, X_ne_zero, exists_false, not_false_eq_true]
    isChain_max_vars' := List.isChain_iff_getElem.mpr fun i hi ↦ by
      simpa only [List.getElem_ofFn, vars_X, Finset.max_singleton, WithBot.coe_lt_coe] using hf1 i}
  have length_S (n : ℕ) : (S n).length = n := List.length_ofFn
  have S_apply (n i : ℕ) : S n i = if i < n then MvPolynomial.X (f i) else 0 := by
    rw [← (S n).toList_getElem?_getD]
    aesop
  refine ⟨S, fun n ↦ lt_def.mpr <| Or.inr ?_⟩
  simp only [length_S, lt_add_iff_pos_right, zero_lt_one, S_apply, true_and]
  intro i hi
  simp only [Nat.lt_add_right 1 hi, ↓reduceIte, hi, Setoid.refl]


-- @@ L449-456 verbatim
theorem length_le [Fintype σ] : S.length ≤ Fintype.card σ + 1 := by
  let f : Fin S.length → WithBot σ := fun i ↦ (S i).vars.max
  have : f.Injective :=
    fun ⟨_, hi⟩ ⟨_, hj⟩ h ↦ Fin.mk.injEq _ hi _ hj ▸ index_eq_of_max_vars_eq hi hj h
  have card_le := Fintype.card_le_of_injective f this
  have : Fintype.card (WithBot σ) = Fintype.card (Option σ) := rfl
  rw [Fintype.card_fin, this, Fintype.card_option] at card_le
  exact card_le


-- @@ L458-460 verbatim
/-- An auxiliary order mapping into a finite domain to prove well-foundedness. -/
private noncomputable def _order [Fintype σ] (S : TriangularSet σ R) :
  Lex (Fin (Fintype.card σ + 1) → WithTop (WithBot σ ×ₗ ℕ)) := fun i ↦ S.order i.1


-- @@ L462-462 verbatim
private theorem _order_def [Fintype σ] : S._order = fun i ↦ S.order i.1 := rfl


-- @@ L464-482 verbatim
private theorem _order_lt_iff [Fintype σ] : S._order < T._order ↔ S.order < T.order where
  mp h := by
    rw [Pi.instLTLexForall] at h ⊢
    rw [_order_def, _order_def] at h
    simp only [Pi.Lex] at h
    rcases h with ⟨k, hk1, hk2⟩
    have kn : k < Fintype.card σ + 1 := Decidable.byContradiction fun con ↦ by
      simp only [order_apply' <| le_trans length_le <| Nat.le_of_not_lt con] at hk2
      exact (lt_self_iff_false ⊤).mp hk2
    exact Exists.intro k.1 ⟨fun i hi ↦ hk1 ⟨i, lt_trans hi kn⟩ hi, hk2⟩
  mpr h := by
    rw [Pi.instLTLexForall] at h ⊢
    rw [_order_def, _order_def] at ⊢
    simp only [Pi.Lex] at h
    rcases h with ⟨k, hk1, hk2⟩
    have kn : k < Fintype.card σ + 1 := Decidable.byContradiction fun con ↦ by
      simp only [order_apply' <| le_trans length_le <| Nat.le_of_not_lt con] at hk2
      exact (lt_self_iff_false ⊤).mp hk2
    exact Exists.intro ⟨k, kn⟩ ⟨fun _ hi ↦ hk1 _ hi, hk2⟩


-- @@ L484-484 verbatim
variable [Finite σ] (S' : Set (TriangularSet σ R))


-- @@ L486-490 verbatim
/-- The set of Triangular Sets is well-founded under the lexicographic order ordering.
This is a crucial result that guarantees the termination of the Characteristic Set Algorithm. -/
instance instIsWellFoundedOrderLT : IsWellFounded (TriangularSet σ R) (InvImage (· < ·) order) :=
  haveI : Fintype σ := Fintype.ofFinite σ
  Subrelation.isWellFounded (InvImage (· < ·) _order) _order_lt_iff.mpr


-- @@ L492-493 verbatim
instance : WellFoundedLT (TriangularSet σ R) :=
  Subrelation.isWellFounded (InvImage (· < ·) order) lt_def'.mp


-- @@ L495-495 verbatim
instance : WellFoundedRelation (TriangularSet σ R) := ⟨(· < ·), instWellFoundedLT.wf⟩


-- @@ L497-500 verbatim
theorem Set.has_min (h : S'.Nonempty) : ∃ S ∈ S', ∀ T ∈ S', S ≤ T :=
  haveI : WellFounded (· < ·) := @wellFounded_lt (TriangularSet σ R) _ _
  have ⟨S, hS1, hS2⟩ := WellFounded.has_min this S' h
  ⟨S, hS1, fun T hT ↦ not_lt_iff_ge.mp (hS2 T hT)⟩


-- @@ L502-503 verbatim
/-- The minimal element of a nonempty set of triangular sets. -/
noncomputable def Set.min (h : S'.Nonempty) : TriangularSet σ R := Exists.choose (has_min S' h)


-- @@ L505-506 verbatim
theorem Set.min_mem (h : S'.Nonempty) : min S' h ∈ S' :=
  (Exists.choose_spec (has_min S' h)).1


-- @@ L508-509 verbatim
theorem Set.min_le (h : S'.Nonempty) : ∀ T ∈ S', min S' h ≤ T :=
  (Exists.choose_spec (has_min S' h)).2


-- @@ L511-511 verbatim
end WellFounded

-- @@ L512-512 verbatim
end TriangularSet
