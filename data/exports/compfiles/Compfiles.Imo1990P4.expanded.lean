/-
Copyright (c) 2026 Constantin Seebach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Algebra.Algebra.Hom.Rat

public import ProblemExtraction


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-21 verbatim
problem_file {
  tags := [.NumberTheory, .Algebra]
}


-- @@ L23-28 verbatim
/-!
# International Mathematical Olympiad 1990, Problem 4

Let $\mathbb{Q^+}$ be the set of positive rational numbers.
Construct a function $f :\mathbb{Q^+}\rightarrow\mathbb{Q^+}$ such that $f(xf(y)) = \frac{f(x)}{y}$ for all $x, y\in\mathbb{Q^+}$.
-/


-- @@ L30-30 verbatim
namespace Imo1990P4


-- @@ L32-32 verbatim
abbrev PRat := { q : ℚ // 0 < q }


-- @@ L34-34 verbatim
notation "ℚ+" => PRat



-- @@ L37-39 verbatim
snip begin

-- We follow the proof from https://prase.cz/kalva/imo/isoln/isoln904.html .


-- @@ L41-43 verbatim
@[simp]
theorem Nat.Primes.toPnat_val (p : Nat.Primes) : p.toPNat.val = p.val := by
  rfl


-- @@ L45-47 verbatim
@[simp]
theorem Nat.Primes.PNat_mk_val (p : Nat.Primes) (h : _) : (⟨p.val, h⟩ : ℕ+) = (p : ℕ+) := by
  rfl


-- @@ L49-53 expanded
@[simp]
theorem PRat.num_toNat (q : PRat) : q.val.num.toNat = q.val.num :=
  by
  simp only [Int.ofNat_toNat, sup_eq_left, Rat.num_nonneg]
  apply le_of_lt
  apply Subtype.prop


-- @@ L55-61 expanded
@[simp]
theorem PRat.cast_num_toNat (q : PRat) : (q.val.num.toNat : ℚ) = q.val.num :=
  by
  nth_rw 2 [← (@Int.natCast_toNat_eq_self (q.val.num)).mpr]
  · rfl
  · simp only [Rat.num_nonneg]
    apply le_of_lt
    exact (Subtype.prop _)


-- @@ L63-66 expanded
@[simp↓]
theorem PRat.num_toNat_div_den (q : PRat) : q.val.num.toNat / q.val.den = q.val :=
  by
  simp only [cast_num_toNat]
  rw [Rat.num_div_den]


-- @@ L69-71 expanded
instance coePRatNNRat : Coe PRat ℚ≥0 :=
  { coe := fun ⟨q, p⟩ ↦ ⟨q, Rat.le_of_lt p⟩ }


-- @@ L73-75 expanded
instance coePrimesPRat : Coe Nat.Primes PRat :=
  { coe p := ⟨p.val, by simpa using Nat.Prime.pos p.prop⟩ }


-- @@ L78-157 expanded
theorem PRat.prime_induction (P : PRat → Prop) (base : P 1)
    (ind_mul : ∀ x, ∀ p : Nat.Primes, P x → P (x * p))
    (ind_div : ∀ x, ∀ p : Nat.Primes, P x → P (x / p)) : ∀ x, P x :=
  by
  have : ∀ nd : ℕ × ℕ, ∀ h, P ⟨nd.1 / nd.2, h⟩ :=
    by
    simp only [Prod.forall]
    intro a
    apply induction_on_primes (motive := fun n => ∀ (b : ℕ) (h), P ⟨n / b, h⟩)
    · simp
    · simp only [Nat.cast_one]
      intro b bpos
      simp only [one_div, inv_pos, Nat.cast_pos] at bpos
      apply induction_on_primes (motive := fun n => ∀ (h), P ⟨1 / n, h⟩)
      · simp
      · simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, zero_lt_one,
          forall_true_left]
        apply base
      · intro p b p_prime ih1 h1
        let p' : Nat.Primes := ⟨p, p_prime⟩
        let x : PRat :=
          ⟨1 / b, by {
            simp at ⊢ h1
            contrapose! h1
            simp at h1
            subst b
            simp
          }⟩
        simp_rw [show (1 / (p * b).cast : ℚ) = x / p' by unfold x p';
            simpa using Eq.symm (Rat.div_def _ _)]
        apply ind_div
        apply ih1
    · intro p a p_prime ih1 b h1
      apply induction_on_primes (motive := fun n => ∀ (h), P ⟨↑(p * a) / n, h⟩)
      · simp
      · intro h2
        simp only [Nat.cast_mul, Nat.cast_one, div_one]
        let p' : Nat.Primes := ⟨p, p_prime⟩
        let x : PRat :=
          ⟨a, by {
            simp at ⊢ h2
            rw [← Nat.cast_mul, ← Rat.natCast_ofNat, Nat.cast_lt] at h2
            exact Nat.pos_of_mul_pos_left h2
          }⟩
        simp_rw [show ((p.cast * a.cast) : ℚ) = x * p' by unfold x p'; ring]
        apply ind_mul
        rw [show x = x / 1 by simp]
        apply ih1
      · intro q b q_prime ih2 h2
        let q' : Nat.Primes := ⟨q, q_prime⟩
        let x : PRat :=
          ⟨p * a / b, by {
            simp at ⊢ h2
            refine (Rat.lt_div_iff ?_).mpr ?_
            · simp only [Nat.cast_pos]
              contrapose! h2
              simp only [nonpos_iff_eq_zero] at h2
              subst b
              simp
            · simp only [zero_mul]
              rw [← Nat.cast_mul, ← Nat.cast_mul, ← Rat.natCast_ofNat] at h2
              refine (Rat.mul_pos_iff_of_pos_left ?_).mpr ?_
              · simp
                exact Nat.Prime.pos p_prime
              · simp only [Nat.cast_pos]
                contrapose! h2
                simp only [nonpos_iff_eq_zero] at h2
                subst a
                simp
          }⟩
        simp_rw [show ((p * a).cast / (q * b).cast : ℚ) = x / q' by unfold x q';
            simp only [Nat.cast_mul]; field]
        apply ind_div
        unfold x
        simp_rw [← Nat.cast_mul]
        apply ih2
  intro x
  have :=
    this ⟨x.val.num.toNat, x.val.den⟩
      (by {
        simp only [cast_num_toNat]
        refine (Rat.lt_div_iff ?_).mpr ?_
        · simpa using Rat.den_pos _
        · simpa using Subtype.prop _
      })
  have h (t) : ⟨x.val.num.toNat / x.val.den, t⟩ = x := by simp
  rw [h] at this
  exact this


-- @@ L159-160 expanded
theorem PRat.mk_mul_mk (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    (⟨a, ha⟩ : PRat) * ⟨b, hb⟩ = ⟨a * b, Rat.mul_pos ha hb⟩ :=
  Subtype.coe_eq_of_eq_mk rfl


-- @@ L162-164 verbatim
/-! The theorems in the following section are part of the original proof and
  illustrate the thought process behind solving the problem, but we do not need them - they are here just_for_fun.
-/

-- @@ L165-165 verbatim
namespace just_for_fun


-- @@ L167-174 expanded
theorem f_one_eq_one (f : PRat → PRat) (h : ∀ x y : PRat, f (x * f y) = f x / y) : f 1 = 1 :=
  by
  let h1 := h 1 1
  simp only [one_mul, div_one] at h1
  let h2 := h 1 (f 1)
  simp only [one_mul, div_self'] at h2
  rw [h1] at h2
  rw [h2] at h1
  exact Eq.symm h1


-- @@ L176-187 expanded
theorem f_mul_hom (f : PRat → PRat) (h : ∀ x y : PRat, f (x * f y) = f x / y) (x y : PRat) :
    f (x * y) = f x * f y := by
  let h1 := h (1 / f y) y
  simp only [one_div, inv_mul_cancel] at h1
  let z := 1 / f y
  have : f z = y := by
    unfold z
    rw [one_div, ← div_eq_one, ← h1]
    exact f_one_eq_one f h
  nth_rw 1 [← this]
  rw [h]
  unfold z
  simp


-- @@ L189-190 expanded
theorem f_chain (f : PRat → PRat) (h : ∀ x y : PRat, f (x * f y) = f x / y) (x : PRat) :
    f (f x) = 1 / x := by rw [show f x = 1 * f x by simp, h, f_one_eq_one f h]


-- @@ L192-192 verbatim
end just_for_fun



-- @@ L195-197 verbatim
instance PRat.coePNat : Coe PNat PRat := {
  coe n := ⟨n, Rat.natCast_pos.mpr (Nat.pos_of_neZero n)⟩
}


-- @@ L199-209 verbatim
theorem Set.Infinite.exists_union_disjoint_infinite_of_infinite {α : Type} {s : Set α} (h : s.Infinite) :
    ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ t.Infinite ∧ u.Infinite := by
  let ⟨t,u, ⟨h1,h2,h3⟩⟩ := Set.Infinite.exists_union_disjoint_cardinal_eq_of_infinite h
  use t, u
  simp only [h1, h2, true_and]
  repeat rw [← Set.infinite_coe_iff, Cardinal.infinite_iff]
  rw [h3, and_self]
  rw [← Set.infinite_coe_iff, Cardinal.infinite_iff, ← h1, Cardinal.mk_union_of_disjoint h2] at h
  contrapose! h
  rw [h3]
  exact Cardinal.add_lt_aleph0 h h



-- @@ L212-219 verbatim
def PNat.mk_mul_hom_fun {R : Type} [CommMonoid R] (g : ℕ → R) : ℕ+ →ₙ* R := {
  toFun n := (n.val.primeFactorsList.map g).prod
  map_mul' a b := by
    have := Nat.perm_primeFactorsList_mul (PNat.ne_zero a) (PNat.ne_zero b)
    have := this.map g
    rw [PNat.mul_coe, this.prod_eq]
    simp
}


-- @@ L221-228 verbatim
theorem PNat.mk_mul_hom_fun.nonZero {R : Type} [CommMonoidWithZero R] [NoZeroDivisors R] [Nontrivial R] (g : ℕ → R) (gnz : ∀ n, Nat.Prime n → ¬ g n = 0)
: ∀ n, PNat.mk_mul_hom_fun g n ≠ 0 := by
  unfold mk_mul_hom_fun
  intro n
  simp only [MulHom.coe_mk, ne_eq, List.prod_eq_zero_iff, List.mem_map, Nat.mem_primeFactorsList',
    PNat.ne_zero, not_false_eq_true, and_true, not_exists, not_and, and_imp]
  intro p pprime _
  apply gnz _ pprime


-- @@ L230-238 verbatim
@[simp]
theorem PNat.mk_mul_hom_fun.prime {R : Type} [CommMonoid R] (g : ℕ → R)
: ∀ p : Nat.Primes, PNat.mk_mul_hom_fun g p = g p := by
  unfold mk_mul_hom_fun
  intro p
  simp only [MulHom.coe_mk, Nat.Primes.toPnat_val]
  rw [Nat.primeFactorsList_prime]
  · simp
  · exact Subtype.prop _


-- @@ L240-244 verbatim
@[simp]
theorem PNat.mk_mul_hom_fun.one {R : Type} [CommMonoid R] (g : ℕ → R)
: PNat.mk_mul_hom_fun g 1 = 1 := by
  unfold mk_mul_hom_fun
  simp


-- @@ L246-259 verbatim
theorem PNat.mk_mul_hom_fun.cancel {R : Type} [CommMonoid R]
    (g : ℕ → R) (g' : ℕ → R) (w : ∀ n, Nat.Prime n → g n * g' n = 1) (a b c : ℕ+)
    : (PNat.mk_mul_hom_fun g) (a*c) * (PNat.mk_mul_hom_fun g') (b*c) = (PNat.mk_mul_hom_fun g) a * (PNat.mk_mul_hom_fun g') b := by
  simp only [map_mul]
  calc
    _ = (PNat.mk_mul_hom_fun g) a * (PNat.mk_mul_hom_fun g') b * ((PNat.mk_mul_hom_fun g) c * (PNat.mk_mul_hom_fun g') c) := by
      exact mul_mul_mul_comm _ _ _ _
    _ = _ := by
      unfold mk_mul_hom_fun
      simp only [MulHom.coe_mk]
      suffices ((List.map g c.val.primeFactorsList).prod * (List.map g' c.val.primeFactorsList).prod) = 1 by simp [this]
      rw [← List.prod_map_mul]
      apply List.prod_eq_one
      aesop


-- @@ L261-264 expanded
theorem PNat.mk_mul_hom_fun.inv (g : ℕ → PRat) (a : ℕ+) :
    mk_mul_hom_fun g⁻¹ a = (mk_mul_hom_fun g a)⁻¹ :=
  by
  simp [mk_mul_hom_fun, List.prod_inv, List.map_map]
  rfl


-- @@ L266-267 verbatim
theorem PNat.mk_mul_mk (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : (⟨a, ha⟩ : ℕ+) * ⟨b, hb⟩ = ⟨a * b, Nat.mul_pos ha hb⟩ :=
  Subtype.coe_eq_of_eq_mk rfl


-- @@ L269-270 verbatim
theorem Nat.toPNat_mul_toPNat (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a.toPNat ha * b.toPNat hb = (a * b).toPNat (Nat.mul_pos ha hb) := rfl


-- @@ L272-273 verbatim
@[simp]
theorem Nat.toPNat_coe (a : ℕ) (ha : 0 < a) : (a.toPNat ha : ℕ) = a := rfl


-- @@ L275-276 verbatim
@[simp]
theorem Nat.toPNat_one (h : 0 < 1) : Nat.toPNat 1 h = 1 := rfl


-- @@ L278-279 verbatim
@[simp]
theorem Nat.Primes.val_toPNat (p : Nat.Primes) (h : _) : p.val.toPNat h = (p : ℕ+) := rfl


-- @@ L281-304 expanded
def PRat.mk_mul_hom_fun (g : ℕ → PRat) : PRat →* PRat :=
  { toFun
      q :=
      ⟨(PNat.mk_mul_hom_fun g (q.val.num.toNat.toPNat (by simpa using q.prop))) *
          (PNat.mk_mul_hom_fun g⁻¹ (q.val.den.toPNat (Rat.den_pos ↑q))),
        by refine (Rat.mul_pos_iff_of_pos_left ?_).mpr ?_ <;> exact Subtype.prop _⟩
    map_mul' a
      b :=
      by
      simp_rw [PNat.mk_mul_hom_fun.inv, Positive.coe_inv, ← Rat.div_def, PRat.mk_mul_mk, ←
        Subtype.coe_inj]
      field_simp
      rw [div_eq_div_iff (by simp [@Subtype.coe_eq_iff]) (by simp [@Subtype.coe_eq_iff])]
      simp_rw [← Positive.val_mul, ← map_mul]
      congr 2
      simp only [Positive.val_mul]
      repeat rw [Nat.toPNat_mul_toPNat]
      rw [← PNat.coe_inj]
      simp_rw [Nat.toPNat_coe]
      zify [Int.toNat_of_nonneg <| Rat.num_nonneg.mpr a.2.le,
        Int.toNat_of_nonneg <| Rat.num_nonneg.mpr b.2.le,
        Int.toNat_of_nonneg <| Rat.num_nonneg.mpr <| Rat.mul_nonneg a.2.le b.2.le]
      rw [← Rat.mul_num_den', mul_assoc]
    map_one' := by
      unfold PNat.mk_mul_hom_fun
      simp only [MulHom.coe_mk, Nat.toPNat_coe, Positive.val_one, Rat.num_ofNat, Int.toNat_one,
        Nat.primeFactorsList_one, List.map_nil, List.prod_nil, Rat.den_ofNat, mul_one]
      rfl }


-- @@ L306-309 expanded
@[simp]
theorem PRat.mk_mul_hom_fun.prime (g : ℕ → PRat) :
    ∀ p : Nat.Primes, PRat.mk_mul_hom_fun g p = g p :=
  by
  unfold mk_mul_hom_fun
  simp


-- @@ L311-327 expanded
@[simp]
theorem PRat.mk_mul_hom_fun.inv_prime (g : ℕ → PRat) :
    ∀ p : Nat.Primes, PRat.mk_mul_hom_fun g p⁻¹ = (g p)⁻¹ :=
  by
  unfold mk_mul_hom_fun
  intro p
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, Positive.coe_inv, Rat.num_inv, Rat.num_natCast,
    Rat.den_natCast, Nat.cast_one, mul_one, Rat.den_inv, Int.natCast_eq_zero, Int.natAbs_natCast]
  split_ifs with h
  · grind only
  · simp
    ext
    simp only [Positive.coe_inv]
    suffices (@Nat.cast Int _ p.val).sign.toNat = 1
      by
      simp_rw [this]
      simp
    rw [Int.sign_eq_one_iff_pos.mpr]
    · simp
    · simpa using Nat.zero_lt_of_ne_zero h


-- @@ L330-423 expanded
theorem exists_f : ∃ f : PRat → PRat, ∀ x y : PRat, f (x * f y) = f x / y :=
  by
  let ⟨S, T, hU, hdU, Sinf, Tinf⟩ :=
    Set.Infinite.exists_union_disjoint_infinite_of_infinite Nat.infinite_setOfPred_prime
  have S_equiv_T : S ≃ T :=
    (@nonempty_equiv_of_countable S T _ Sinf.to_subtype _ Tinf.to_subtype).some
  have := Classical.dec
  let g (p : ℕ) : PRat :=
    if hS : p ∈ S then
      ⟨S_equiv_T ⟨p, hS⟩, by
        {
        suffices ∀ t ∈ T, t ≠ 0 by simp only [Nat.cast_pos]; grind only
        intro t h
        have : t ∈ S ∪ T := Set.mem_union_right S h
        rw [hU] at this
        exact Nat.Prime.ne_zero this
      }⟩
    else
      if hT : p ∈ T then
        ⟨1 / S_equiv_T.symm ⟨p, hT⟩, by
          {
          suffices ∀ s ∈ S, s ≠ 0 by simp only [one_div, inv_pos, Nat.cast_pos]; grind only
          intro s h
          have : s ∈ S ∪ T := Set.mem_union_left T h
          rw [hU] at this
          exact Nat.Prime.ne_zero this
        }⟩
      else 1
  let f := PRat.mk_mul_hom_fun g
  have : ∀ p : Nat.Primes, f (f p) = 1 / p := by
    intro p
    unfold f
    simp
    unfold g
    split_ifs with hS hT
    · let q : Nat.Primes :=
        ⟨S_equiv_T ⟨p, hS⟩, by
          {
          have : (S_equiv_T ⟨p, hS⟩).val ∈ S ∪ T := by simp
          rw [hU] at this
          simp only [Set.mem_ofPred_eq] at this
          exact this
        }⟩
      have : ∀ h, (⟨S_equiv_T ⟨p, hS⟩, h⟩ : PRat) = (q : PRat) :=
        by
        unfold q
        simp
      rw [this]
      simp only [PRat.mk_mul_hom_fun.prime]
      unfold q
      simp only [Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply, one_div]
      have : ¬↑(S_equiv_T ⟨↑p, hS⟩) ∈ S := by grind
      simp only [this, ↓reduceDIte]
      rfl
    · simp only [one_div]
      let q : Nat.Primes :=
        ⟨S_equiv_T.symm ⟨p, hT⟩, by
          {
          have : (S_equiv_T.symm ⟨p, hT⟩).val ∈ S ∪ T := by simp
          rw [hU] at this
          simp only [Set.mem_ofPred_eq] at this
          exact this
        }⟩
      have : ∀ h, (⟨(S_equiv_T.symm ⟨p, hT⟩)⁻¹, h⟩ : PRat) = (q⁻¹ : PRat) :=
        by
        unfold q
        intro _
        ext
        simp
      rw [this]
      simp only [PRat.mk_mul_hom_fun.inv_prime]
      unfold q
      simp
    · have : ¬p.val ∈ {p | Nat.Prime p} := by
        rw [← hU]
        grind only [= Set.mem_union]
      simp at this
      exact absurd p.prop this
  have f_chain (x : PRat) : f (f x) = 1 / x :=
    by
    apply PRat.prime_induction (fun x => f (f x) = 1 / x)
    · unfold f
      simp
    · intro x p ih
      simp only [map_mul]
      rw [ih]
      simp only [one_div, mul_inv_rev]
      rw [mul_comm, mul_left_inj, ← one_div]
      apply this
    · intro x p ih
      simp only [map_div]
      rw [ih]
      simp only [one_div, inv_div]
      rw [div_eq_inv_mul, div_eq_inv_mul, mul_comm, mul_right_inj]
      rw [inv_eq_iff_eq_inv, ← one_div]
      apply this
  use f
  intro x y
  rw [map_mul, f_chain]
  exact Eq.symm (div_eq_mul_one_div _ _)


-- @@ L426-426 verbatim
snip end


-- @@ L428-428 expanded
noncomputable determine f : PRat → PRat :=
  exists_f.choose


-- @@ L430-431 expanded
problem imo1990_p4 (x y : PRat) : f (x * f y) = f x / y := by apply exists_f.choose_spec


-- @@ L434-434 verbatim
end Imo1990P4
