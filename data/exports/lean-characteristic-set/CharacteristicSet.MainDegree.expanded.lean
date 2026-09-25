import CharacteristicSet.Lemmas


-- @@ L3-21 verbatim
/-!
# Main degree of a polynomial

This file defines the *main degree* of a multivariate polynomial,
which is the degree with respect to its main variable.

## Main definitions

* `MvPolynomial.mainDegree p`:
  The degree of `p` with respect to its main variable.
  If `max_vars p = ⊥` (i.e., `p` is a constant or zero), the degree is `0`.

## Main theorems

* `mainDegree_eq_zero_iff`: `p.mainDegree = 0` iff `p.max_vars = ⊥`
* `mainDegree_of_max_vars_isSome`: When `p.max_vars = c ≠ ⊥`,
  `p.mainDegree = p.degreeOf c`

-/


-- @@ L23-23 verbatim
namespace MvPolynomial


-- @@ L25-25 verbatim
variable {R σ : Type*} [CommSemiring R] {p q : MvPolynomial σ R}


-- @@ L27-27 verbatim
section MainDegree


-- @@ L29-29 verbatim
variable [LinearOrder σ] {i j c : σ}


-- @@ L31-36 verbatim
/-- The "main degree" of `p`: the degree of `p` with respect to its main variable.
If `max_vars p = ⊥` (i.e., `p` is a constant or zero), the degree is 0. -/
noncomputable def mainDegree (p : MvPolynomial σ R) : ℕ :=
  match p.vars.max with
  | ⊥ => 0
  | some c => p.degreeOf c


-- @@ L38-39 verbatim
theorem mainDegree_of_max_vars_isSome : p.vars.max = c → p.mainDegree = p.degreeOf c :=
  fun h ↦ by rw [mainDegree, h]


-- @@ L41-43 verbatim
theorem mainDegree_of_max_vars_isSome' :
    p.vars.max = c → p.mainDegree = p.support.sup (fun s ↦ s c) :=
  fun h ↦ by rw [mainDegree_of_max_vars_isSome h, degreeOf_eq_sup]


-- @@ L45-55 verbatim
theorem mainDegree_eq_zero_iff : p.mainDegree = 0 ↔ p.vars.max = ⊥ where
  mp h :=
    match hc : p.vars.max with
    | ⊥ => rfl
    | some c => by
      rw [mainDegree_of_max_vars_isSome hc, degreeOf] at h
      have : c ∉ p.degrees := by simpa only [Multiset.count_eq_zero] using h
      have hc := Finset.mem_of_max hc
      simp only [vars_def, Multiset.mem_toFinset] at hc
      exact absurd hc this
  mpr h := by rw [mainDegree, h]


-- @@ L57-58 verbatim
theorem mainDegree_eq_zero_iff_eq_C : p.mainDegree = 0 ↔ p = C (p.coeff 0) :=
  mainDegree_eq_zero_iff.trans <| Finset.max_eq_bot.trans vars_eq_empty_iff_eq_C


-- @@ L60-62 verbatim
theorem degreeOf_max_vars_ne_zero : p.vars.max = c → p.degreeOf c ≠ 0 := fun h ↦
  have := (not_iff_not.mpr mainDegree_eq_zero_iff).mpr (h ▸ WithBot.coe_ne_bot)
  mainDegree_of_max_vars_isSome h ▸ this


-- @@ L64-65 verbatim
theorem max_vars_mem_degrees : p.vars.max = c → c ∈ p.degrees := fun h ↦
  have := degreeOf_max_vars_ne_zero h; Multiset.count_ne_zero.mp (degreeOf_def c p ▸ this)


-- @@ L67-67 verbatim
@[simp] theorem mainDegree_zero : (0 : MvPolynomial σ R).mainDegree = 0 := rfl


-- @@ L69-72 verbatim
@[simp] theorem mainDegree_monomial {s : σ →₀ ℕ} {r : R} (hr : r ≠ 0)
    (hs : s.support.max = c) : (monomial s r).mainDegree = s c := by
  rw [mainDegree_of_max_vars_isSome <| (congrArg _ (vars_monomial hr)).trans hs]
  exact degreeOf_monomial_eq s c hr


-- @@ L74-75 verbatim
@[simp] theorem mainDegree_C (r : R) : (C r : MvPolynomial σ R).mainDegree = 0 :=
  mainDegree_eq_zero_iff.mpr <| congrArg _ (vars_C)


-- @@ L77-82 verbatim
@[simp] theorem mainDegree_X_pow [Nontrivial R] (i : σ) (k : ℕ) :
    ((X i : MvPolynomial σ R) ^ k).mainDegree = k := by
  by_cases hk : k = 0
  · exact hk ▸ pow_zero (X i : MvPolynomial σ R) ▸ mainDegree_C 1
  have : (Finsupp.single i k).support.max = i := by rw [Finsupp.support_single_ne_zero i hk]; rfl
  rw [X_pow_eq_monomial, mainDegree_monomial one_ne_zero this, Finsupp.single_eq_same]


-- @@ L84-85 verbatim
@[simp] theorem mainDegree_X [Nontrivial R] (i : σ) : (X i : MvPolynomial σ R).mainDegree = 1 :=
  pow_one (X i : MvPolynomial σ R) ▸ mainDegree_X_pow i 1


-- @@ L87-87 verbatim
end MainDegree

-- @@ L88-88 verbatim
end MvPolynomial
