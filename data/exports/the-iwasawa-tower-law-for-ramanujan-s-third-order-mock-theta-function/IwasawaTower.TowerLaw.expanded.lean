import IwasawaTower.FiniteCongruence
import IwasawaTower.DenominatorReversal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation


-- @@ L8-12 verbatim
/-!
# The Iwasawa tower valuation law

Author: Joesph D. Burke III.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open scoped BigOperators


-- @@ L18-18 verbatim
namespace IwasawaTower


-- @@ L20-20 verbatim
open Polynomial Ideal NumberField RingOfIntegers


-- @@ L22-27 verbatim
private theorem eval₂_mem_ideal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : S) (P : R[X]) (I : Ideal S)
    (hterm : ∀ i : ℕ, f (P.coeff i) * x ^ i ∈ I) :
    Polynomial.eval₂ f x P ∈ I := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact I.sum_mem fun i hi ↦ hterm i


-- @@ L29-29 verbatim
section PrimePower


-- @@ L31-33 verbatim
variable {K : Type*} [Field K] [NumberField K]
  (a : ℕ) [hK : IsCyclotomicExtension {3 ^ (a + 1)} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ (a + 1)))


-- @@ L35-35 verbatim
local notation "𝓞" => 𝓞 K


-- @@ L37-38 verbatim
/-- The unique prime over three, written using the generator `ζ-1`. -/
def cyclotomicPrime : Ideal 𝓞 := Ideal.span {hζ.toInteger - 1}


-- @@ L40-43 verbatim
/-- The integral value of the denominator-reversed sum. -/
def integralTowerElement : 𝓞 :=
  Polynomial.eval₂ (algebraMap ℤ 𝓞) (1 - hζ.toInteger)
    (integerReversedPolynomial (3 ^ (a + 1)))


-- @@ L45-46 verbatim
/-- The integer whose image in `ℚ` is the field norm of the tower sum. -/
def towerNormInteger : ℤ := Algebra.norm ℤ (integralTowerElement a hζ)


-- @@ L48-67 verbatim
/-- Substituting `Y = 1 - ζ` in the reversed integer polynomial recovers
the denominator-reversed finite sum. -/
theorem integralTowerElement_eq_F :
    integralTowerElement a hζ = F (3 ^ (a + 1)) hζ.toInteger := by
  rw [integralTowerElement, integerReversedPolynomial, Polynomial.eval₂_comp]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_X]
  have hy : (1 : 𝓞) - (1 - hζ.toInteger) = hζ.toInteger := by ring
  rw [hy]
  have hA (r : ℕ) : Polynomial.eval₂ (Int.castRingHom 𝓞) hζ.toInteger
      (APoly r : ℤ[X]) = pochhammer hζ.toInteger r := by
    change (Polynomial.eval₂RingHom (Int.castRingHom 𝓞) hζ.toInteger)
      (∏ j ∈ Finset.range r, (1 + X ^ (j + 1))) = _
    rw [map_prod]
    simp [pochhammer]
  have hA2 (r : ℕ) : Polynomial.eval₂ (Int.castRingHom 𝓞) hζ.toInteger
      ((APoly r : ℤ[X]) ^ 2) = pochhammer hζ.toInteger r ^ 2 := by
    rw [Polynomial.eval₂_pow, hA]
  change (Polynomial.eval₂RingHom (Int.castRingHom 𝓞) hζ.toInteger)
    (FPoly (3 ^ (a + 1)) : ℤ[X]) = _
  simp [FPoly, F, hA2]


-- @@ L69-80 verbatim
/-- The integral representative maps to the original finite mock-theta sum.
This is where denominator reversal enters the number-field theorem. -/
theorem algebraMap_integralTowerElement_eq_T :
    algebraMap 𝓞 K (integralTowerElement a hζ) = T (3 ^ (a + 1)) ζ := by
  rw [integralTowerElement_eq_F]
  have hmap : algebraMap 𝓞 K (F (3 ^ (a + 1)) hζ.toInteger) =
      F (3 ^ (a + 1)) ζ := by
    simp [F, pochhammer, hζ.coe_toInteger]
  rw [hmap, ← T_eq_F]
  · exact Odd.pow (by decide : Odd (3 : ℕ))
  · positivity
  · exact hζ


-- @@ L82-85 verbatim
/-- The additive prime-ideal order, implemented as Dedekind-domain
multiplicity of the prime in the principal ideal. -/
def primeIdealOrder (x : 𝓞) : ℕ :=
  multiplicity (cyclotomicPrime a hζ) (Ideal.span {x})


-- @@ L87-91 verbatim
private theorem cyclotomicPrime_eq_span_one_sub :
    cyclotomicPrime a hζ = Ideal.span {1 - hζ.toInteger} := by
  apply Ideal.span_singleton_eq_span_singleton.mpr
  simpa [sub_eq_add_neg, add_comm] using
    Associated.neg_right (Associated.refl (hζ.toInteger - 1))


-- @@ L93-95 verbatim
private theorem cyclotomicPrime_isPrime : (cyclotomicPrime a hζ).IsPrime := by
  dsimp [cyclotomicPrime]
  exact IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one 3 a hζ


-- @@ L97-99 verbatim
private theorem cyclotomicPrime_ne_bot : cyclotomicPrime a hζ ≠ ⊥ := by
  rw [cyclotomicPrime, ne_eq, Ideal.span_singleton_eq_bot]
  exact (hζ.zeta_sub_one_prime.ne_zero)


-- @@ L101-104 verbatim
/-- The height-one point associated with `(1-ζ)`. -/
def cyclotomicPlace : IsDedekindDomain.HeightOneSpectrum 𝓞 :=
  ⟨cyclotomicPrime a hζ, cyclotomicPrime_isPrime a hζ,
    cyclotomicPrime_ne_bot a hζ⟩


-- @@ L106-113 verbatim
private theorem ramification_ideal_identity :
    Ideal.map (algebraMap ℤ 𝓞) (Ideal.span {(3 : ℤ)}) =
      cyclotomicPrime a hζ ^ (2 * 3 ^ a) := by
  have h := IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow 3 a hζ
  have hfin : Module.finrank ℚ K = (3 ^ (a + 1)).totient :=
    IsCyclotomicExtension.Rat.finrank (3 ^ (a + 1)) K
  rw [hfin, Nat.totient_prime_pow_succ (by decide)] at h
  simpa [cyclotomicPrime, mul_comm] using h


-- @@ L115-118 verbatim
private theorem cyclotomicPrime_liesOver :
    (cyclotomicPrime a hζ).LiesOver (Ideal.span {(3 : ℤ)}) := by
  dsimp [cyclotomicPrime]
  exact IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one 3 a hζ


-- @@ L120-223 verbatim
private theorem integralTowerElement_exact_membership :
    let d := 2 * 3 ^ a - 1
    integralTowerElement a hζ ∈ cyclotomicPrime a hζ ^ d ∧
      integralTowerElement a hζ ∉ cyclotomicPrime a hζ ^ (d + 1) := by
  let d := 2 * 3 ^ a - 1
  let e := 2 * 3 ^ a
  let Pz := integerReversedPolynomial (3 ^ (a + 1))
  let y : 𝓞 := 1 - hζ.toInteger
  let P := cyclotomicPrime a hζ
  let c : ℤ := Pz.coeff d
  let R : ℤ[X] := Pz - C c * X ^ d
  have heq : e = d + 1 := by
    have hp : 0 < 3 ^ a := pow_pos (by omega) _
    dsimp [d, e]
    omega
  have hPy : P = Ideal.span {y} := by
    simpa [P, y] using cyclotomicPrime_eq_span_one_sub a hζ
  have hyP : y ∈ P := by rw [hPy]; exact Ideal.mem_span_singleton_self y
  have hram : Ideal.map (algebraMap ℤ 𝓞) (Ideal.span {(3 : ℤ)}) = P ^ e := by
    simpa [P, e] using ramification_ideal_identity a hζ
  have lowCoeffMem {i m : ℕ} (hi : i < d) (hm : m ≤ e) :
      algebraMap ℤ 𝓞 (Pz.coeff i) * y ^ i ∈ P ^ m := by
    obtain ⟨z, hz⟩ := three_dvd_integerReversedPolynomial_coeff_lt a i (by
      simpa [d, Pz] using hi)
    have hthree : algebraMap ℤ 𝓞 (3 : ℤ) ∈ P ^ e := by
      rw [← hram]
      exact Ideal.mem_map_of_mem (algebraMap ℤ 𝓞) (Ideal.mem_span_singleton_self (3 : ℤ))
    have hcoeff : algebraMap ℤ 𝓞 (Pz.coeff i) ∈ P ^ e := by
      rw [hz, map_mul]
      exact (P ^ e).mul_mem_right (algebraMap ℤ 𝓞 z) hthree
    exact (P ^ m).mul_mem_right (y ^ i)
      ((Ideal.pow_le_pow_right hm) hcoeff)
  have highCoeffMem {i m : ℕ} (hi : m ≤ i) :
      algebraMap ℤ 𝓞 (Pz.coeff i) * y ^ i ∈ P ^ m := by
    exact (P ^ m).mul_mem_left (algebraMap ℤ 𝓞 (Pz.coeff i))
      ((Ideal.pow_le_pow_right hi) (Ideal.pow_mem_pow hyP i))
  have htotal : Polynomial.eval₂ (algebraMap ℤ 𝓞) y Pz ∈ P ^ d := by
    apply eval₂_mem_ideal
    intro i
    by_cases hi : i < d
    · exact lowCoeffMem hi (by rw [heq]; omega)
    · exact highCoeffMem (Nat.le_of_not_gt hi)
  have hrem : Polynomial.eval₂ (algebraMap ℤ 𝓞) y R ∈ P ^ e := by
    apply eval₂_mem_ideal
    intro i
    by_cases hi : i < d
    · have hid : i ≠ d := by omega
      simpa [R, coeff_sub, coeff_C_mul, coeff_X_pow, if_neg hid] using
        (lowCoeffMem hi le_rfl)
    · by_cases hid : i = d
      · subst i
        simp [R, c]
      · have hie : e ≤ i := by rw [heq]; omega
        have hhigh := highCoeffMem (m := e) hie
        simpa [R, coeff_sub, coeff_C_mul, coeff_X_pow, if_neg hid] using hhigh
  have hcoeffMod : (c : ZMod 3) = -1 := by
    simpa [c, d, Pz] using integerReversedPolynomial_coeff_lead_mod_three a
  have hcoeffNotMem : algebraMap ℤ 𝓞 c ∉ P := by
    intro hc
    haveI : P.LiesOver (Ideal.span {(3 : ℤ)}) := by
      simpa [P] using cyclotomicPrime_liesOver a hζ
    have hcUnder : c ∈ Ideal.under ℤ P := by
      rw [Ideal.under_def, Ideal.mem_comap]
      exact hc
    have hcThree : c ∈ Ideal.span {(3 : ℤ)} := by
      have hover : Ideal.span {(3 : ℤ)} = Ideal.under ℤ P :=
        (Ideal.liesOver_iff P (Ideal.span {(3 : ℤ)})).mp
          (show P.LiesOver (Ideal.span {(3 : ℤ)}) from inferInstance)
      rw [hover]
      exact hcUnder
    have hdiv : (3 : ℤ) ∣ c := Ideal.mem_span_singleton.mp hcThree
    have hzero : (c : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd c 3).2 hdiv
    rw [hzero] at hcoeffMod
    norm_num at hcoeffMod
  have hyPrime : Prime y := by
    have hz : Prime (hζ.toInteger - 1) := hζ.zeta_sub_one_prime
    have hy : y = -(hζ.toInteger - 1) := by simp [y]
    rw [hy]
    exact hz.neg
  have hleadNot : algebraMap ℤ 𝓞 c * y ^ d ∉ P ^ e := by
    intro hmem
    have hdiv : y ^ (d + 1) ∣ y ^ d * algebraMap ℤ 𝓞 c := by
      rw [heq] at hmem
      rw [hPy, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
      simpa [mul_comm] using hmem
    rcases prime_pow_succ_dvd_mul hyPrime hdiv with hpow | hc
    · have := (pow_dvd_pow_iff hyPrime.ne_zero hyPrime.not_unit).mp hpow
      omega
    · exact hcoeffNotMem (by rw [hPy, Ideal.mem_span_singleton]; exact hc)
  have hnot : Polynomial.eval₂ (algebraMap ℤ 𝓞) y Pz ∉ P ^ e := by
    intro hmem
    have hleadMem : algebraMap ℤ 𝓞 c * y ^ d ∈ P ^ e := by
      have hsub := (P ^ e).sub_mem hmem hrem
      have heval : Polynomial.eval₂ (algebraMap ℤ 𝓞) y Pz -
          Polynomial.eval₂ (algebraMap ℤ 𝓞) y R =
          algebraMap ℤ 𝓞 c * y ^ d := by
        dsimp only [R]
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul,
          Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
        ring
      rwa [heval] at hsub
    exact hleadNot hleadMem
  simpa [integralTowerElement, Pz, y, P, d, heq] using And.intro htotal hnot


-- @@ L225-236 verbatim
/-- Exact additive `(1-ζ)`-adic order of the integral tower element. -/
theorem primeIdealOrder_integralTowerElement :
    primeIdealOrder a hζ (integralTowerElement a hζ) = 2 * 3 ^ a - 1 := by
  let d := 2 * 3 ^ a - 1
  have hm := integralTowerElement_exact_membership a hζ
  have hdvd : cyclotomicPrime a hζ ^ d ∣
      Ideal.span {integralTowerElement a hζ} :=
    Ideal.dvd_span_singleton.mpr hm.1
  have hnotdvd : ¬cyclotomicPrime a hζ ^ (d + 1) ∣
      Ideal.span {integralTowerElement a hζ} := by
    simpa [Ideal.dvd_span_singleton] using hm.2
  simpa [primeIdealOrder, d] using multiplicity_eq_of_dvd_of_not_dvd hdvd hnotdvd


-- @@ L238-250 verbatim
/-- Multiplicative valuation form of the tower law. -/
theorem intValuation_integralTowerElement :
    (cyclotomicPlace a hζ).intValuation (integralTowerElement a hζ) =
      WithZero.exp (-(2 * 3 ^ a - 1 : ℕ) : ℤ) := by
  have hx : integralTowerElement a hζ ≠ 0 := by
    intro hx
    have hm := (integralTowerElement_exact_membership a hζ).2
    exact hm (by simp [hx])
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hx]
  rw [show multiplicity (cyclotomicPlace a hζ).asIdeal
      (Ideal.span {integralTowerElement a hζ}) = 2 * 3 ^ a - 1 by
    simpa [cyclotomicPlace, primeIdealOrder] using
      primeIdealOrder_integralTowerElement a hζ]


-- @@ L252-259 verbatim
/-- Multiplicative valuation of the original finite sum in the fraction field.
Equivalently, its additive `(1-ζ)`-adic order is `2 * 3^a - 1`. -/
theorem valuation_T :
    (cyclotomicPlace a hζ).valuation K (T (3 ^ (a + 1)) ζ) =
      WithZero.exp (-(2 * 3 ^ a - 1 : ℕ) : ℤ) := by
  rw [← algebraMap_integralTowerElement_eq_T a hζ,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_integralTowerElement]


-- @@ L261-322 verbatim
/-- The ordinary three-adic order of the integer norm of the integral tower
element.  The proof uses total ramification and exact prime-ideal membership. -/
theorem padicValInt_norm_integralTowerElement :
    padicValInt 3 (Algebra.norm ℤ (integralTowerElement a hζ)) =
      2 * 3 ^ a - 1 := by
  let d := 2 * 3 ^ a - 1
  let e := 2 * 3 ^ a
  let x := integralTowerElement a hζ
  let P := cyclotomicPrime a hζ
  let I := Ideal.span {x}
  have heq : e = d + 1 := by
    have hp : 0 < 3 ^ a := pow_pos (by omega) _
    dsimp [d, e]
    omega
  have hm := integralTowerElement_exact_membership a hζ
  have hdvd : P ^ d ∣ I := by
    simpa [P, I, x, Ideal.dvd_span_singleton] using hm.1
  have hnotdvd : ¬P ^ (d + 1) ∣ I := by
    simpa [P, I, x, Ideal.dvd_span_singleton] using hm.2
  obtain ⟨J, hJ⟩ := hdvd
  have hx : x ≠ 0 := by
    intro hx
    exact hm.2 (by simp [x, hx])
  have hIbot : I ≠ ⊥ := by
    simpa [I, Ideal.span_singleton_eq_bot] using hx
  have hPnotJ : ¬P ∣ J := by
    intro hPJ
    apply hnotdvd
    rw [hJ, pow_succ]
    exact mul_dvd_mul_left (P ^ d) hPJ
  have hJbot : J ≠ ⊥ := by
    intro hbot
    apply hIbot
    rw [hJ, hbot, mul_bot]
  have hPmax : P.IsMaximal :=
    (cyclotomicPrime_isPrime a hζ).isMaximal (cyclotomicPrime_ne_bot a hζ)
  have hthreeNot : ¬3 ∣ Ideal.absNorm J := by
    intro hthree
    obtain ⟨Q, hQmax, hQunder, hQJ⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' (by decide : Nat.Prime 3) J hthree
    have hmaple : Ideal.map (algebraMap ℤ 𝓞) (Ideal.span {(3 : ℤ)}) ≤ Q := by
      rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, hQunder]
      norm_num
    have hQeq : Q = P := by
      have hpowle : P ^ e ≤ Q := by
        rw [← ramification_ideal_identity a hζ]
        exact hmaple
      haveI : Q.IsPrime := hQmax.isPrime
      have hPle : P ≤ Q := Ideal.IsPrime.le_of_pow_le hpowle
      exact (hPmax.eq_of_le hQmax.ne_top hPle).symm
    exact hPnotJ (hQeq ▸ hQJ)
  have hnormJ : Ideal.absNorm J ≠ 0 := by
    rwa [ne_eq, Ideal.absNorm_eq_zero_iff]
  have hnormP : Ideal.absNorm P = 3 := by
    dsimp [P, cyclotomicPrime]
    exact IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one 3 a hζ
  have hnorm : (Algebra.norm ℤ x).natAbs = 3 ^ d * Ideal.absNorm J := by
    rw [← Ideal.absNorm_span_singleton, show Ideal.span {x} = I by rfl,
      hJ, map_mul, map_pow, hnormP]
  rw [padicValInt, hnorm,
    padicValNat.mul (pow_ne_zero d (by decide)) hnormJ,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hthreeNot, add_zero]


-- @@ L324-328 verbatim
/-- Norm form of the Iwasawa tower law. -/
theorem norm_T_padic_order :
    padicValInt 3 (Algebra.norm ℤ (integralTowerElement a hζ)) =
      2 * 3 ^ a - 1 :=
  padicValInt_norm_integralTowerElement a hζ


-- @@ L330-336 verbatim
/-- Compatibility between the integral norm and the field norm of the
original sum. -/
theorem algebraNorm_T_eq_towerNormInteger :
    Algebra.norm ℚ (T (3 ^ (a + 1)) ζ) =
      algebraMap ℤ ℚ (towerNormInteger a hζ) := by
  rw [← algebraMap_integralTowerElement_eq_T a hζ]
  exact (Algebra.coe_norm_int (x := integralTowerElement a hζ)).symm


-- @@ L338-342 verbatim
/-- Ordinary three-adic order of the norm
`N_{ℚ(ζ)/ℚ}(T_{3^(a+1)})`. -/
theorem v3_towerNormInteger :
    padicValInt 3 (towerNormInteger a hζ) = 2 * 3 ^ a - 1 := by
  exact padicValInt_norm_integralTowerElement a hζ


-- @@ L344-348 verbatim
/-- The exponent is also `φ(3^(a+1)) - 1`. -/
theorem towerExponent_eq_totient_sub_one :
    2 * 3 ^ a - 1 = (3 ^ (a + 1)).totient - 1 := by
  rw [Nat.totient_prime_pow_succ (by decide : Nat.Prime 3)]
  omega


-- @@ L350-356 verbatim
/-- Recurrence corollary for the exact tower orders.  It is a consequence of
the independently proved closed formula, not an input to its proof. -/
theorem towerExponent_recurrence :
    2 * 3 ^ (a + 1) - 1 = 3 * (2 * 3 ^ a - 1) + 2 := by
  have hp : 0 < 3 ^ a := pow_pos (by omega) _
  rw [pow_succ]
  omega


-- @@ L358-358 verbatim
end PrimePower


-- @@ L360-360 verbatim
section PositiveLevel


-- @@ L362-362 verbatim
variable {K : Type*} [Field K] [NumberField K]


-- @@ L364-367 verbatim
/-- The integral representative at a level indexed directly by `n ≥ 1`. -/
def positiveLevelIntegral (n : ℕ) {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ n)) : 𝓞 K :=
  Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) (1 - hζ.toInteger)
    (integerReversedPolynomial (3 ^ n))


-- @@ L369-371 verbatim
/-- The integer norm at a level indexed directly by `n ≥ 1`. -/
def positiveLevelNormInteger (n : ℕ) {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ n)) : ℤ :=
  Algebra.norm ℤ (positiveLevelIntegral n hζ)


-- @@ L373-384 verbatim
/-- The `(1-ζ)` height-one place at a level indexed directly by `n ≥ 1`. -/
def positiveLevelPlace (n : ℕ) (hn : 1 ≤ n)
    [hK : IsCyclotomicExtension {3 ^ n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ n)) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) := by
  let a := n - 1
  have han : a + 1 = n := by dsimp [a]; omega
  letI hKa : IsCyclotomicExtension {3 ^ (a + 1)} ℚ K := by
    rw [han]
    infer_instance
  have hζa : IsPrimitiveRoot ζ (3 ^ (a + 1)) := by simpa [han] using hζ
  exact cyclotomicPlace a hζa


-- @@ L386-400 verbatim
/-- Additive prime-ideal form of the Iwasawa tower law, stated for every
`n ≥ 1`. -/
theorem iwasawa_tower_law {n : ℕ} (hn : 1 ≤ n)
    [hK : IsCyclotomicExtension {3 ^ n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ n)) :
    multiplicity (Ideal.span {hζ.toInteger - 1})
      (Ideal.span {positiveLevelIntegral n hζ}) = 2 * 3 ^ (n - 1) - 1 := by
  let a := n - 1
  have han : a + 1 = n := by dsimp [a]; omega
  letI hKa : IsCyclotomicExtension {3 ^ (a + 1)} ℚ K := by
    rw [han]
    infer_instance
  have hζa : IsPrimitiveRoot ζ (3 ^ (a + 1)) := by simpa [han] using hζ
  simpa [primeIdealOrder, cyclotomicPrime, integralTowerElement,
    positiveLevelIntegral, a, han] using primeIdealOrder_integralTowerElement a hζa


-- @@ L402-411 verbatim
/-- Euler-totient form of the additive tower law. -/
theorem iwasawa_tower_law_totient {n : ℕ} (hn : 1 ≤ n)
    [hK : IsCyclotomicExtension {3 ^ n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ n)) :
    multiplicity (Ideal.span {hζ.toInteger - 1})
      (Ideal.span {positiveLevelIntegral n hζ}) = (3 ^ n).totient - 1 := by
  rw [iwasawa_tower_law hn hζ]
  let a := n - 1
  have han : a + 1 = n := by dsimp [a]; omega
  simpa [han, a] using towerExponent_eq_totient_sub_one a


-- @@ L413-426 verbatim
/-- Valuation form of the Iwasawa tower law, stated directly for every
`n ≥ 1`. -/
theorem iwasawa_tower_valuation {n : ℕ} (hn : 1 ≤ n)
    [hK : IsCyclotomicExtension {3 ^ n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ n)) :
    (positiveLevelPlace n hn hζ).valuation K (T (3 ^ n) ζ) =
      WithZero.exp (-(2 * 3 ^ (n - 1) - 1 : ℕ) : ℤ) := by
  let a := n - 1
  have han : a + 1 = n := by dsimp [a]; omega
  letI hKa : IsCyclotomicExtension {3 ^ (a + 1)} ℚ K := by
    rw [han]
    infer_instance
  have hζa : IsPrimitiveRoot ζ (3 ^ (a + 1)) := by simpa [han] using hζ
  simpa [positiveLevelPlace, a, han] using valuation_T a hζa


-- @@ L428-442 verbatim
/-- The field norm of `T_(3^n)` is the rational image of the explicitly
defined integer norm. -/
theorem algebraNorm_T_eq_positiveLevelNormInteger {n : ℕ} (hn : 1 ≤ n)
    [hK : IsCyclotomicExtension {3 ^ n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ n)) :
    Algebra.norm ℚ (T (3 ^ n) ζ) =
      algebraMap ℤ ℚ (positiveLevelNormInteger n hζ) := by
  let a := n - 1
  have han : a + 1 = n := by dsimp [a]; omega
  letI hKa : IsCyclotomicExtension {3 ^ (a + 1)} ℚ K := by
    rw [han]
    infer_instance
  have hζa : IsPrimitiveRoot ζ (3 ^ (a + 1)) := by simpa [han] using hζ
  simpa [positiveLevelNormInteger, positiveLevelIntegral, towerNormInteger,
    integralTowerElement, a, han] using algebraNorm_T_eq_towerNormInteger a hζa


-- @@ L444-456 verbatim
/-- Norm form of the Iwasawa tower law, stated for every `n ≥ 1`. -/
theorem iwasawa_norm_tower_law {n : ℕ} (hn : 1 ≤ n)
    [hK : IsCyclotomicExtension {3 ^ n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ n)) :
    padicValInt 3 (positiveLevelNormInteger n hζ) = 2 * 3 ^ (n - 1) - 1 := by
  let a := n - 1
  have han : a + 1 = n := by dsimp [a]; omega
  letI hKa : IsCyclotomicExtension {3 ^ (a + 1)} ℚ K := by
    rw [han]
    infer_instance
  have hζa : IsPrimitiveRoot ζ (3 ^ (a + 1)) := by simpa [han] using hζ
  simpa [positiveLevelNormInteger, positiveLevelIntegral, towerNormInteger,
    integralTowerElement, a, han] using v3_towerNormInteger a hζa


-- @@ L458-466 verbatim
/-- Euler-totient form of the norm theorem. -/
theorem iwasawa_norm_tower_law_totient {n : ℕ} (hn : 1 ≤ n)
    [hK : IsCyclotomicExtension {3 ^ n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (3 ^ n)) :
    padicValInt 3 (positiveLevelNormInteger n hζ) = (3 ^ n).totient - 1 := by
  rw [iwasawa_norm_tower_law hn hζ]
  let a := n - 1
  have han : a + 1 = n := by dsimp [a]; omega
  simpa [han, a] using towerExponent_eq_totient_sub_one a


-- @@ L468-468 verbatim
end PositiveLevel


-- @@ L470-470 verbatim
end IwasawaTower
