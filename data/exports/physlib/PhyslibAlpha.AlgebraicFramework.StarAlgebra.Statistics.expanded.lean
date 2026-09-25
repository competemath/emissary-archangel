/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Observable


-- @@ L10-36 verbatim
/-!

# State statistics

A state assigns real expectation values to observables (`UnitalPositiveLinearMap.expectation`,
notation `ω⟨a⟩`, built directly from `UnitalPositiveLinearMap.onObservables`). Centering an
observable around its mean produces `covariance` and `variance`, the quantities the uncertainty
relations in `CStarAlgebra.Uncertainty` are stated in terms of.

None of this needs a C⋆-norm or completeness: a state `ω : 𝓢[A]` already restricts to a real
state on `Observable A`, and positivity of `variance` is already positivity of a state applied to
`star x * x` for `x` self-adjoint. Consequently almost everything here is stated for a bare star
ring with a compatible order (`Ring`, `StarRing`, `PartialOrder`, plus `SelfAdjointDecompose`,
`Module ℂ`, `StarModule ℂ` for `𝓢[A]`/`onObservables` themselves to make sense) — exactly the
level `UnitalPositiveLinearMap.onObservables` needs. `StarOrderedRing` is added locally, only on
`variance_nonneg`, for the one positivity fact (`star_mul_self_nonneg`) that actually needs it;
symmetry of `covariance` needs no order at all, just `apply_mul_comm_eq_star`.

## Main definitions

- `UnitalPositiveLinearMap.expectation`, notation `ω⟨a⟩` : the real expectation value of an
  observable `a` in state `ω`.
- `UnitalPositiveLinearMap.centered` : an observable with its mean subtracted off.
- `UnitalPositiveLinearMap.covariance`, `UnitalPositiveLinearMap.variance` : the correlation
  between two observables' fluctuations, and the spread of one observable's own fluctuations.

-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
open scoped ComplexOrder


-- @@ L42-43 verbatim
variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
    [SelfAdjointDecompose A] [Module ℂ A] [StarModule ℂ A]


-- @@ L45-45 verbatim
namespace UnitalPositiveLinearMap


-- @@ L47-47 verbatim
/-! ## Expectation -/


-- @@ L49-54 expanded
/-- The real state on observables induced by `ω`. Its value at `a` is the mean value a physicist
would call `⟨a⟩`, obtained by averaging repeated measurements of `a` on systems prepared in
state `ω`. This is exactly `onObservables`, under a name and notation that reads as expectation
rather than restriction. -/
noncomputable def expectation (ω : UnitalPositiveLinearMap ℂ A ℂ) :
    UnitalPositiveLinearMap ℝ (Observable A) ℝ :=
  ω.onObservables


-- @@ L56-57 verbatim
@[inherit_doc expectation]
scoped notation:max ω "⟨" a "⟩" => UnitalPositiveLinearMap.expectation ω a


-- @@ L59-59 verbatim
attribute [nolint docBlame] UnitalPositiveLinearMap.«term_⟨_⟩»


-- @@ L61-65 expanded
/-- The complex-valued state functional agrees with the real expectation notation `ω⟨a⟩` on
observables: no information is lost, since self-adjoint elements have vanishing imaginary part. -/
lemma apply_observable_eq_expectation (ω : UnitalPositiveLinearMap ℂ A ℂ) (a : Observable A) :
    ω (a : A) = (ω⟨a⟩ : ℂ) :=
  (coe_onObservables_apply ω a).symm


-- @@ L67-71 expanded
/-- The trivial "do-nothing" observable `1` is measured with certainty: probabilities sum to one. -/
@[simp]
lemma expectation_one (ω : UnitalPositiveLinearMap ℂ A ℂ) : ω⟨(1 : Observable A)⟩ = 1 := by
  simp [expectation]


-- @@ L73-76 expanded
/-- Positive observables have nonnegative expectation. -/
lemma expectation_nonneg (ω : UnitalPositiveLinearMap ℂ A ℂ) {a : Observable A} (ha : 0 ≤ (a : A)) :
    0 ≤ ω⟨a⟩ :=
  (expectation ω).map_nonneg ha


-- @@ L78-78 verbatim
/-! ## Centering -/


-- @@ L80-83 expanded
/-- The fluctuation of an observable around its mean: `a` with `ω⟨a⟩` subtracted off. Its
statistics (`covariance`, `variance`) describe the spread of `a`'s outcomes. -/
noncomputable def centered (ω : UnitalPositiveLinearMap ℂ A ℂ) (a : Observable A) : Observable A :=
  a - ω⟨a⟩ • 1


-- @@ L85-89 expanded
/-- A fluctuation has zero mean by construction: the average deviation from the average is zero. -/
@[simp]
lemma expectation_centered (ω : UnitalPositiveLinearMap ℂ A ℂ) (a : Observable A) :
    ω⟨centered ω a⟩ = 0 := by simp [centered]


-- @@ L91-97 expanded
/-- Shifting an observable by a deterministic constant `c` shifts its mean by `c` too, so the
fluctuation around the new mean is unchanged. -/
@[simp]
lemma centered_add_smul_one (ω : UnitalPositiveLinearMap ℂ A ℂ) (a : Observable A) (c : ℝ) :
    centered ω (a + c • 1) = centered ω a :=
  by
  simp only [centered, map_add, map_smul, expectation_one]
  module


-- @@ L99-99 verbatim
/-! ## Reversing a product -/


-- @@ L101-106 expanded
/-- Reversing the order of two self-adjoint elements in a product conjugates the state's value on
it. Purely algebraic — needs only `map_star` and self-adjointness, no positivity or completeness —
so it is what makes `covariance` symmetric below without any detour through a Jordan product. -/
lemma apply_mul_comm_eq_star (ω : UnitalPositiveLinearMap ℂ A ℂ) (a b : Observable A) :
    ω ((b : A) * a) = star (ω ((a : A) * b)) := by
  rw [← map_star, star_mul, a.property.star_eq, b.property.star_eq]


-- @@ L108-108 verbatim
/-! ## Covariance and variance -/


-- @@ L110-115 expanded
/-- The correlation between two observables' fluctuations in state `ω`: the real part of the
expectation of the (uncentered) product of their fluctuations. `apply_mul_comm_eq_star` makes this
symmetric in `a`, `b` (`covariance_comm`) without needing a symmetrized product to define it.
Nonzero covariance means a measurement of `a` carries statistical information about `b`. -/
noncomputable def covariance (ω : UnitalPositiveLinearMap ℂ A ℂ) (a b : Observable A) : ℝ :=
  (ω ((centered ω a : A) * centered ω b)).re


-- @@ L117-120 expanded
/-- The spread of `a`'s measurement outcomes about its mean — the quantum analogue of a random
variable's variance, whose square root is the uncertainty `Δa` in `CStarAlgebra.Uncertainty`. -/
noncomputable def variance (ω : UnitalPositiveLinearMap ℂ A ℂ) (a : Observable A) : ℝ :=
  covariance ω a a


-- @@ L122-126 expanded
/-- Unfolds `variance` as covariance of an observable with itself. -/
@[simp]
lemma covariance_self (ω : UnitalPositiveLinearMap ℂ A ℂ) (a : Observable A) :
    covariance ω a a = variance ω a :=
  rfl


-- @@ L128-133 expanded
/-- Variance is the expectation of the squared fluctuation about the mean: unfolds `variance` and
`covariance` together. Stated as its own lemma (even though now definitionally `rfl`) since
`CStarAlgebra.Uncertainty` uses it under this name. -/
lemma variance_eq_re_apply_centered_mul_self (ω : UnitalPositiveLinearMap ℂ A ℂ)
    (a : Observable A) : variance ω a = (ω ((centered ω a : A) * centered ω a)).re :=
  rfl


-- @@ L135-140 expanded
/-- Covariance is symmetric: reversing a product of self-adjoint fluctuations conjugates the
state's value on it, and conjugation does not change the real part. -/
lemma covariance_comm (ω : UnitalPositiveLinearMap ℂ A ℂ) (a b : Observable A) :
    covariance ω a b = covariance ω b a :=
  by
  show (ω ((centered ω a : A) * centered ω b)).re = (ω ((centered ω b : A) * centered ω a)).re
  rw [apply_mul_comm_eq_star ω (centered ω a) (centered ω b), Complex.star_def, Complex.conj_re]


-- @@ L142-146 expanded
/-- Covariance depends only on fluctuations: shifting the left observable by a constant `c`
leaves it unchanged. -/
lemma covariance_add_smul_one_left (ω : UnitalPositiveLinearMap ℂ A ℂ) (a b : Observable A)
    (c : ℝ) : covariance ω (a + c • 1) b = covariance ω a b := by
  simp only [covariance, centered_add_smul_one]


-- @@ L148-152 expanded
/-- Covariance depends only on fluctuations: shifting the right observable by a constant `c`
leaves it unchanged. -/
lemma covariance_add_smul_one_right (ω : UnitalPositiveLinearMap ℂ A ℂ) (a b : Observable A)
    (c : ℝ) : covariance ω a (b + c • 1) = covariance ω a b := by
  simp only [covariance, centered_add_smul_one]


-- @@ L154-165 expanded
variable [StarOrderedRing A] in
/-- Repeated measurements of an observable can never have negative spread about their mean: the
physical content of variance being an honest measure of statistical uncertainty. Algebraically,
this is positivity of the state applied to `(centered a)† (centered a) = (centered a)^2`, which
already lands in the positive cone via `star_mul_self_nonneg` — no Jordan product needed. -/
lemma variance_nonneg (ω : UnitalPositiveLinearMap ℂ A ℂ) (a : Observable A) : 0 ≤ variance ω a :=
  by
  rw [variance_eq_re_apply_centered_mul_self]
  have h : (0 : A) ≤ (centered ω a : A) * centered ω a :=
    by
    have hpos := star_mul_self_nonneg (centered ω a : A)
    rwa [(centered ω a).property.star_eq] at hpos
  exact (RCLike.nonneg_iff.mp (ω.map_nonneg h)).1


-- @@ L167-167 verbatim
end UnitalPositiveLinearMap
