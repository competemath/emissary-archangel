/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
module

import all CompPoly.Univariate.Basic
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import CompPoly.Data.Array.Lemmas
public import CompPoly.Univariate.Basic
public import CompPoly.Univariate.Linear


-- @@ L17-21 verbatim
/-!
# Computable Univariate To `Polynomial`

Conversions between computable univariate polynomials and mathlib `Polynomial`.
-/


-- @@ L23-23 verbatim
public section


-- @@ L25-25 verbatim
open Polynomial


-- @@ L27-32 verbatim
/-- Convert a mathlib `Polynomial` to a `CPolynomial.Raw` by extracting coefficients
up to the degree. -/
def Polynomial.toImpl {R : Type*} [Semiring R] (p : R[X]) : CompPoly.CPolynomial.Raw R :=
  match p.degree with
  | ⊥ => #[]
  | some d  => .ofFn (fun i : Fin (d + 1) => p.coeff i)


-- @@ L34-34 verbatim
namespace CompPoly


-- @@ L36-36 verbatim
namespace CPolynomial


-- @@ L38-38 verbatim
open Raw


-- @@ L40-40 verbatim
variable {R : Type*}

-- @@ L41-41 verbatim
variable {Q : Type*}


-- @@ L43-43 verbatim
section ToPolyDefs


-- @@ L45-47 verbatim
/-- Convert a `CPolynomial.Raw` to a (mathlib) `Polynomial`. -/
noncomputable def Raw.toPoly [Semiring R] (p : CPolynomial.Raw R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X


-- @@ L49-57 verbatim
/-- Alternative definition of `toPoly` using `Finsupp`; currently unused. -/
noncomputable def Raw.toPoly' [Semiring R] (p : CPolynomial.Raw R) : Polynomial R :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (Finset.range p.size) p.coeff (by
    intro n hn
    rw [Finset.mem_range]
    by_contra! h
    have h' : p.coeff n = 0 := by simp [h]
    contradiction
  )))


-- @@ L59-60 verbatim
/-- Convert a canonical polynomial to a (mathlib) `Polynomial`. -/
noncomputable def toPoly [Semiring R] (p : CPolynomial R) : Polynomial R := p.val.toPoly


-- @@ L62-62 verbatim
end ToPolyDefs


-- @@ L64-64 verbatim
section ToPoly


-- @@ L66-66 verbatim
variable [Semiring R] [BEq R]

-- @@ L67-67 verbatim
variable [Semiring Q]


-- @@ L69-71 verbatim
namespace Raw

alias ofPoly := Polynomial.toImpl


-- @@ L73-80 verbatim
/-- Evaluation is preserved by `toPoly`. -/
theorem eval_toPoly_eq_eval (x : Q) (p : CPolynomial.Raw Q) : p.toPoly.eval x = p.eval x := by
  unfold Raw.toPoly Raw.eval eval₂
  rw [← Array.foldl_hom (Polynomial.eval x)
    (g₁ := fun acc (t : Q × ℕ) ↦ acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) ↦ acc + a * x ^ i) ]
  · congr; exact Polynomial.eval_zero
  simp


-- @@ L82-116 verbatim
/-- The coefficients of `p.toPoly` match those of `p`. -/
lemma coeff_toPoly {p : CPolynomial.Raw Q} {n : ℕ} : p.toPoly.coeff n = p.coeff n := by
  unfold Raw.toPoly Raw.eval₂

  let f := fun (acc: Q[X]) ((a,i): Q × ℕ) ↦ acc + Polynomial.C a * Polynomial.X ^ i
  change (Array.foldl f 0 p.zipIdx).coeff n = p.coeff n

  let motive (size: ℕ) (acc: Q[X]) := acc.coeff n = if (n < size) then p.coeff n else 0

  have zipIdx_size : p.zipIdx.size = p.size := by simp [Array.zipIdx]

  suffices h : motive p.zipIdx.size (Array.foldl f 0 p.zipIdx) by
    rw [h, ite_eq_left_iff, zipIdx_size]
    intro hn
    replace hn : n ≥ p.size := by linarith
    rw [Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hn, Option.getD_none]

  apply Array.foldl_induction motive
  · simp [motive]

  change ∀ (i : Fin p.zipIdx.size) acc, motive i acc → motive (i + 1) (f acc p.zipIdx[i])
  unfold motive f
  intros i acc h
  have i_lt_p : i < p.size := by linarith [i.is_lt]
  have : p.zipIdx[i] = (p[i], ↑i) := by simp [Array.getElem_zipIdx]
  rw [this, Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_X_pow, mul_ite, h]
  rcases (Nat.lt_trichotomy i n) with hlt | rfl | hgt
  · have h1 : ¬ (n < i) := by linarith
    have h2 : ¬ (n = i) := by linarith
    have h3 : ¬ (n < i + 1) := by linarith
    simp [h1, h2, h3]
  · simp [i_lt_p]
  · have h1 : ¬ (n = i) := by linarith
    have h2 : n < i + 1 := by linarith
    simp [hgt, h1, h2]


-- @@ L118-130 verbatim
/-- Case analysis for `toImpl`: either the polynomial is zero or has a specific form. -/
lemma toImpl_elim (p : Q[X]) :
    (p = 0 ∧ p.toImpl = #[])
  ∨ (p ≠ 0 ∧ p.toImpl = .ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i)) := by
  unfold toImpl
  by_cases hbot : p.degree = ⊥
  · left
    use degree_eq_bot.mp hbot
    rw [hbot]
  right
  use degree_ne_bot.mp hbot
  have hnat : p.degree = p.natDegree := Polynomial.degree_eq_natDegree (degree_ne_bot.mp hbot)
  simp [hnat]


-- @@ L132-147 verbatim
/-- `toImpl` is a right-inverse of `toPoly`: the round-trip from `Polynomial` is the identity.

  This shows `toPoly` is surjective and `toImpl` is injective. -/
theorem toPoly_toImpl {p : Q[X]} : p.toImpl.toPoly = p := by
  ext n
  rw [coeff_toPoly]
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨_, h⟩
  · simp [h]
  rw [h]
  by_cases h : n < p.natDegree + 1
  · simp [h]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [h, reduceDIte, Option.getD_none]
  replace h := Nat.lt_of_succ_le (not_lt.mp h)
  symm
  exact coeff_eq_zero_of_natDegree_lt h


-- @@ L149-153 verbatim
/-- Trimming doesn't change the `toPoly` image. -/
@[grind =]
lemma toPoly_trim [LawfulBEq R] {p : CPolynomial.Raw R} : p.trim.toPoly = p.toPoly := by
  ext n
  rw [coeff_toPoly, coeff_toPoly, Trim.coeff_eq_coeff]


-- @@ L155-156 verbatim
/-- `toPoly` preserves addition. -/
@[grind =]

-- @@ L157-159 verbatim
theorem toPoly_addRaw {p q : CPolynomial.Raw Q} : (addRaw p q).toPoly = p.toPoly + q.toPoly := by
  ext n
  rw [Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, add_coeff?]


-- @@ L161-163 verbatim
/-- `toPoly` of a right-scalar multiplication is multiplication by `Polynomial.C r`
on the right. -/
@[grind =]

-- @@ L164-172 verbatim
theorem toPoly_smulRight {p : CPolynomial.Raw Q} {r : Q} :
    (smulRight r p).toPoly = p.toPoly * Polynomial.C r := by
  ext n
  rw [Polynomial.coeff_mul_C, coeff_toPoly, coeff_toPoly]
  show (Array.map (fun a => a * r) p).getD n 0 = p.getD n 0 * r
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : p[n]? with
  | none => simp
  | some a => simp


-- @@ L174-178 verbatim
@[grind =]
lemma toPoly_add [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by
  change (p.add q).toPoly = p.toPoly + q.toPoly; unfold add
  rw [toPoly_trim, toPoly_addRaw]


-- @@ L180-185 verbatim
/-- Non-zero polynomials map to non-empty arrays. -/
lemma toImpl_nonzero {p : Q[X]} (hp : p ≠ 0) : p.toImpl.size > 0 := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  suffices h : p.toImpl ≠ #[] from Array.size_pos_iff.mpr h
  simp [h]


-- @@ L187-192 verbatim
/-- The last coefficient of `toImpl p` is the leading coefficient of `p`. -/
lemma getLast_toImpl {p : Q[X]} (hp : p ≠ 0) : let h : p.toImpl.size > 0 := toImpl_nonzero hp;
    p.toImpl[p.toImpl.size - 1] = p.leadingCoeff := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  simp [h]


-- @@ L194-204 verbatim
omit [BEq R] in
/-- `toImpl` lands in the semantic canonical carrier used by `CPolynomial`. -/
@[simp]
theorem isCanonical_toImpl (p : R[X]) : IsCanonical p.toImpl := by
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨h_nz, _⟩
  · simpa [h] using (Trim.isCanonical_empty (R := R))
  · intro hp
    have hlast : p.toImpl.getLast hp = p.leadingCoeff := by
      simpa [Array.getLast] using (getLast_toImpl (Q := R) (p := p) h_nz)
    rw [hlast]
    exact Polynomial.leadingCoeff_ne_zero.mpr h_nz


-- @@ L206-207 verbatim
/-- `toImpl` produces canonical polynomials (no trailing zeros). -/
@[simp, grind =]

-- @@ L208-209 verbatim
theorem trim_toImpl [LawfulBEq R] (p : R[X]) : p.toImpl.trim = p.toImpl := by
  exact Trim.trim_eq_of_isCanonical (isCanonical_toImpl p)


-- @@ L211-211 verbatim
end Raw


-- @@ L213-218 verbatim
omit [BEq R] in
/-- Building a canonical polynomial from `toImpl` and converting it back yields the
original mathlib polynomial. -/
theorem toPoly_mk_toImpl (p : R[X]) :
    CPolynomial.toPoly ⟨p.toImpl, Raw.isCanonical_toImpl p⟩ = p := by
  exact Raw.toPoly_toImpl


-- @@ L220-224 verbatim
/-- `ofArray` preserves the raw polynomial's `toPoly` image. -/
theorem ofArray_toPoly [LawfulBEq R] (p : CPolynomial.Raw R) :
    (CPolynomial.ofArray p).toPoly = p.toPoly := by
  unfold CPolynomial.ofArray
  exact Raw.toPoly_trim


-- @@ L226-242 verbatim
/-- On canonical polynomials, `toImpl` is a left-inverse of `toPoly`.

  This shows `toPoly` is a bijection from `CPolynomial R` to `Polynomial R`. -/
@[grind =]
lemma toImpl_toPoly_of_canonical [LawfulBEq R] (p : CPolynomial R) : p.toPoly.toImpl = p := by
  suffices h_inj : ∀ q : CPolynomial R, p.toPoly = q.toPoly → p = q by
    have : p.toPoly = p.toPoly.toImpl.toPoly := by rw [toPoly_toImpl]
    exact
      h_inj ⟨p.toPoly.toImpl, isCanonical_toImpl p.toPoly⟩ this
        |> congrArg Subtype.val
        |>.symm
  intro q hpq
  apply CPolynomial.ext
  apply Trim.isCanonical_ext p.property q.property
  intro i
  rw [← coeff_toPoly, ← coeff_toPoly]
  exact hpq |> congrArg (fun p => p.coeff i)


-- @@ L244-245 verbatim
/-- The round-trip from `CPolynomial.Raw` to `Polynomial` and back yields the canonical form. -/
@[simp, grind =]

-- @@ L246-248 verbatim
theorem Raw.toImpl_toPoly [LawfulBEq R] (p : CPolynomial.Raw R) : p.toPoly.toImpl = p.trim := by
  rw [← toPoly_trim]
  exact toImpl_toPoly_of_canonical ⟨ p.trim, Trim.isCanonical_trim p⟩


-- @@ L250-263 verbatim
/-- A nonempty trimmed raw polynomial bounds the degree of its `toPoly` image. -/
theorem Raw.toPoly_natDegree_lt_trim_size_of_pos [LawfulBEq R]
    (p : CPolynomial.Raw R) (hp : 0 < p.trim.size) :
    p.toPoly.natDegree < p.trim.size := by
  have hround := Raw.toImpl_toPoly (R := R) p
  have hsize : p.toPoly.toImpl.size = p.trim.size := congrArg Array.size hround
  rcases Raw.toImpl_elim p.toPoly with ⟨_hzero, himpl⟩ | ⟨_hnz, himpl⟩
  · have : p.trim.size = 0 := by
      rw [← hsize, himpl]
      simp
    omega
  · have himpl_size : p.toPoly.toImpl.size = p.toPoly.natDegree + 1 := by
      simp [himpl]
    omega


-- @@ L265-278 verbatim
/-- `toPoly` maps a canonical polynomial to `0` iff the polynomial is `0`. -/
theorem toPoly_eq_zero_iff [LawfulBEq R] (p : CPolynomial R) :
    p.toPoly = 0 ↔ p = 0 := by
  constructor
  · intro hp
    apply CPolynomial.ext
    calc
      (p : CPolynomial.Raw R) = p.toPoly.toImpl := (toImpl_toPoly_of_canonical p).symm
      _ = (0 : CPolynomial.Raw R) := by
        simp [hp, Polynomial.toImpl]
  · rintro rfl
    ext n
    rw [CPolynomial.toPoly, Raw.coeff_toPoly, Polynomial.coeff_zero]
    simpa [CPolynomial.coeff] using (CPolynomial.coeff_zero (R := R) n)


-- @@ L280-281 verbatim
/-- Evaluation is preserved by `toImpl`. -/
@[simp, grind =]

-- @@ L282-283 verbatim
theorem eval_toImpl_eq_eval [LawfulBEq R] (x : R) (p : R[X]) : p.toImpl.eval x = p.eval x := by
  rw [← toPoly_toImpl (p := p), toImpl_toPoly, ← toPoly_trim, eval_toPoly_eq_eval]


-- @@ L285-289 verbatim
/-- Evaluation is unchanged by trimming. -/
@[simp, grind =]
lemma Raw.eval_trim_eq_eval [LawfulBEq R] (x : R) (p : CPolynomial.Raw R) :
    p.trim.eval x = p.eval x := by
  rw [← toImpl_toPoly, eval_toImpl_eq_eval, eval_toPoly_eq_eval]


-- @@ L291-291 verbatim
end ToPoly


-- @@ L293-293 verbatim
end CPolynomial


-- @@ L295-295 verbatim
end CompPoly
