module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteLogLocalized


-- @@ L5-12 verbatim
/-!
# Homogeneous product-coordinate expansions

This file records the homogeneous polynomial for the product coordinate
`(1 + x) * (1 + y) - 1 = x + y + x*y`.  The coefficient-order lemma below is
the expansion input needed to transfer the formal two-variable logarithm
identity to the localized finite-log quotient sums.
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open scoped NumberField


-- @@ L20-20 verbatim
namespace BernoulliRegular


-- @@ L22-22 verbatim
namespace Furtwaengler


-- @@ L24-24 verbatim
universe u v w


-- @@ L26-26 verbatim
namespace ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L28-28 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L29-29 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L30-30 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L31-31 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']


-- @@ L33-33 verbatim
variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')


-- @@ L35-38 verbatim
/-- The additive coordinate of the product of the principal units `1 + x` and
`1 + y`. -/
def finiteLogProductCoord (x y : 𝓞 R') : 𝓞 R' :=
  x + y + x * y


-- @@ L40-43 verbatim
theorem finiteLogProductCoord_mem_Q {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q) :
    finiteLogProductCoord x y ∈ F.Q := by
  have hxy : x * y ∈ F.Q := Ideal.mul_mem_right y F.Q hx
  exact F.Q.add_mem (F.Q.add_mem hx hy) hxy


-- @@ L45-48 verbatim
/-- Homogeneous bookkeeping polynomial for `x + y + x*y`, where `x` and `y`
have degree `1` and `x*y` has degree `2`. -/
def finiteLogProductArgPoly (x y : 𝓞 R') : Polynomial (𝓞 R') :=
  Polynomial.monomial 1 (x + y) + Polynomial.monomial 2 (x * y)


-- @@ L50-53 verbatim
omit [NumberField R'] in
theorem finiteLogProductArgPoly_eval_one (x y : 𝓞 R') :
    (finiteLogProductArgPoly x y).eval 1 = finiteLogProductCoord x y := by
  simp [finiteLogProductArgPoly, finiteLogProductCoord, Polynomial.eval_monomial]


-- @@ L55-58 verbatim
omit [NumberField R'] in
theorem finiteLogProductArgPoly_pow_eval_one (n : ℕ) (x y : 𝓞 R') :
    ((finiteLogProductArgPoly x y) ^ n).eval 1 = (finiteLogProductCoord x y) ^ n := by
  simp [finiteLogProductArgPoly_eval_one, Polynomial.eval_pow]


-- @@ L60-76 verbatim
theorem finiteLogProductArgPoly_coeff_mem_Q_pow {x y : 𝓞 R'}
    (hx : x ∈ F.Q) (hy : y ∈ F.Q) (d : ℕ) :
    (finiteLogProductArgPoly x y).coeff d ∈ F.Q ^ d := by
  by_cases h1 : d = 1
  · subst d
    simpa [finiteLogProductArgPoly, Polynomial.coeff_monomial] using F.Q.add_mem hx hy
  by_cases h2 : d = 2
  · subst d
    have hxy : x * y ∈ F.Q ^ 2 := by
      have hmul : x * y ∈ F.Q * F.Q := Ideal.mul_mem_mul hx hy
      simpa [pow_two] using hmul
    simpa [finiteLogProductArgPoly, Polynomial.coeff_monomial] using hxy
  have hne1 : 1 ≠ d := fun h =>
    h1 h.symm
  have hne2 : 2 ≠ d := fun h =>
    h2 h.symm
  simp [finiteLogProductArgPoly, Polynomial.coeff_monomial, hne1, hne2]


-- @@ L78-103 verbatim
/-- Every homogeneous coefficient of
`(T*x + T*y + T^2*(x*y))^n` has at least its formal total degree as `Q`-adic
order. -/
theorem finiteLogProductArgPoly_pow_coeff_mem_Q_pow {x y : 𝓞 R'}
    (hx : x ∈ F.Q) (hy : y ∈ F.Q) (n d : ℕ) :
    ((finiteLogProductArgPoly x y) ^ n).coeff d ∈ F.Q ^ d := by
  induction n generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst d
        simp
      · simp [Polynomial.coeff_one, hd]
  | succ n ih =>
      rw [pow_succ, Polynomial.coeff_mul]
      refine Ideal.sum_mem _ ?_
      intro a ha
      have hsum : a.1 + a.2 = d := by
        simpa using (Finset.mem_antidiagonal.mp ha)
      have hleft : ((finiteLogProductArgPoly x y) ^ n).coeff a.1 ∈ F.Q ^ a.1 :=
        ih a.1
      have hright : (finiteLogProductArgPoly x y).coeff a.2 ∈ F.Q ^ a.2 :=
        finiteLogProductArgPoly_coeff_mem_Q_pow (F := F) hx hy a.2
      have hmul : ((finiteLogProductArgPoly x y) ^ n).coeff a.1 *
          (finiteLogProductArgPoly x y).coeff a.2 ∈ F.Q ^ (a.1 + a.2) := by
        simpa [pow_add] using Ideal.mul_mem_mul hleft hright
      simpa [hsum] using hmul


-- @@ L105-105 verbatim
end ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L107-107 verbatim
end Furtwaengler


-- @@ L109-109 verbatim
end BernoulliRegular
