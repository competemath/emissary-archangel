module

public import BernoulliRegular.Reflection.ResidueSymbol.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm


-- @@ L7-13 verbatim
/-!
# Non-canonical p-th power residue symbols

This file contains the older choice-dependent residue-symbol API used by some
algebraic Stickelberger support lemmas.  It is only the finite-field
definition and its elementary multiplicativity/vanishing facts.
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open scoped NumberField


-- @@ L21-21 verbatim
namespace BernoulliRegular


-- @@ L23-23 verbatim
namespace Furtwaengler


-- @@ L25-25 verbatim
variable {p : ℕ} [Fact p.Prime]


-- @@ L27-35 verbatim
/-- Global noncomputable Fintype instance for `𝓞 K ⧸ q` when `q ≠ ⊥`. -/
noncomputable instance instFintype_OK_quotient {K : Type*}
    [Field K] [NumberField K] (q : Ideal (𝓞 K)) [NeZero q] :
    Fintype (𝓞 K ⧸ q) :=
  have : Finite (𝓞 K ⧸ q) := by
    rw [← Ideal.absNorm_ne_zero_iff]
    exact Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne q)⟩
  Fintype.ofFinite _


-- @@ L37-55 verbatim
/-- The choice-dependent prime-level `p`-th power residue symbol. -/
noncomputable def pthSymbolAtPrime {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) (q : Ideal (𝓞 K)) : ZMod p := by
  classical
  by_cases hbot : q = ⊥
  · exact 0
  haveI : NeZero q := ⟨hbot⟩
  by_cases hmax : q.IsMaximal
  · by_cases hα : α ∈ q
    · exact 0
    by_cases hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1
    · by_cases hroot : ∃ ζ : (𝓞 K ⧸ q)ˣ, IsPrimitiveRoot ζ p
      · haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        haveI : q.IsMaximal := hmax
        exact Reflection.ResidueSymbol.PowerResidue.primeExponent q
          hroot.choose hroot.choose_spec hdiv α hα
      · exact 0
    · exact 0
  · exact 0


-- @@ L57-62 verbatim
/-- Symbol vanishes at the bottom ideal. -/
theorem pthSymbolAtPrime_eq_zero_of_eq_bot {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) :
    pthSymbolAtPrime (p := p) α (⊥ : Ideal (𝓞 K)) = 0 := by
  unfold pthSymbolAtPrime
  rw [dif_pos rfl]


-- @@ L64-70 verbatim
/-- Symbol vanishes for non-maximal `q ≠ ⊥`. -/
theorem pthSymbolAtPrime_eq_zero_of_not_isMaximal {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : ¬ q.IsMaximal) :
    pthSymbolAtPrime (p := p) α q = 0 := by
  unfold pthSymbolAtPrime
  rw [dif_neg hbot, dif_neg hmax]


-- @@ L72-78 verbatim
/-- Symbol vanishes when `α ∈ q`. -/
theorem pthSymbolAtPrime_eq_zero_of_mem {K : Type*}
    [Field K] [NumberField K] {α : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal) (hα : α ∈ q) :
    pthSymbolAtPrime (p := p) α q = 0 := by
  unfold pthSymbolAtPrime
  rw [dif_neg hbot, dif_pos hmax, dif_pos hα]


-- @@ L80-98 verbatim
/-- Multiplicativity of the residue symbol in the numerator. -/
theorem pthSymbolAtPrime_mul {K : Type*}
    [Field K] [NumberField K] {α β : 𝓞 K} {q : Ideal (𝓞 K)}
    (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hα : α ∉ q) (hβ : β ∉ q) :
    pthSymbolAtPrime (p := p) (α * β) q =
      pthSymbolAtPrime (p := p) α q + pthSymbolAtPrime (p := p) β q := by
  have : NeZero q := ⟨hbot⟩
  have hqK_prime : q.IsPrime := hmax.isPrime
  have hαβ : α * β ∉ q := fun h ↦ (hqK_prime.mem_or_mem h).elim hα hβ
  simp only [pthSymbolAtPrime, dif_neg hbot, dif_pos hmax, dif_neg hαβ,
    dif_neg hα, dif_neg hβ]
  split_ifs with hdiv hroot
  · have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    have : q.IsMaximal := hmax
    exact Reflection.ResidueSymbol.PowerResidue.primeExponent_mul q
      hroot.choose hroot.choose_spec hdiv hα hβ hαβ
  · simp
  · simp


-- @@ L100-104 verbatim
/-- The `p`-th power residue symbol `(α/I)_p` extended to integral ideals. -/
noncomputable def pthSymbolAtIdeal {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) (I : Ideal (𝓞 K)) : ZMod p :=
  ((UniqueFactorizationMonoid.normalizedFactors I).map
    (fun P ↦ pthSymbolAtPrime (p := p) α P)).sum


-- @@ L106-112 verbatim
/-- The symbol vanishes at the unit ideal. -/
@[simp] theorem pthSymbolAtIdeal_one {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) :
    pthSymbolAtIdeal (p := p) α (1 : Ideal (𝓞 K)) = 0 := by
  simp only [pthSymbolAtIdeal]
  rw [UniqueFactorizationMonoid.normalizedFactors_one]
  simp


-- @@ L114-119 verbatim
/-- The symbol vanishes at `⊤`. -/
@[simp] theorem pthSymbolAtIdeal_top {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) :
    pthSymbolAtIdeal (p := p) α (⊤ : Ideal (𝓞 K)) = 0 := by
  rw [← Ideal.one_eq_top]
  exact pthSymbolAtIdeal_one (p := p) α


-- @@ L121-127 verbatim
/-- The symbol vanishes at `⊥`. -/
@[simp] theorem pthSymbolAtIdeal_bot {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) :
    pthSymbolAtIdeal (p := p) α (⊥ : Ideal (𝓞 K)) = 0 := by
  simp only [pthSymbolAtIdeal]
  rw [← Ideal.zero_eq_bot, UniqueFactorizationMonoid.normalizedFactors_zero]
  simp


-- @@ L129-138 verbatim
/-- Multiplicativity in the ideal slot for non-zero ideals. -/
theorem pthSymbolAtIdeal_mul_ideal {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    pthSymbolAtIdeal (p := p) α (I * J) =
      pthSymbolAtIdeal (p := p) α I + pthSymbolAtIdeal (p := p) α J := by
  simp only [pthSymbolAtIdeal]
  have hI' : (I : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  have hJ' : (J : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hI' hJ',
      Multiset.map_add, Multiset.sum_add]


-- @@ L140-147 verbatim
/-- Power form in the ideal slot. -/
theorem pthSymbolAtIdeal_pow_ideal {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) (I : Ideal (𝓞 K)) (n : ℕ) :
    pthSymbolAtIdeal (p := p) α (I ^ n) =
      n * pthSymbolAtIdeal (p := p) α I := by
  simp only [pthSymbolAtIdeal]
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.map_nsmul, Multiset.sum_nsmul, nsmul_eq_mul]


-- @@ L149-153 verbatim
/-- Vanishing engine in the ideal-denominator slot. -/
@[simp] theorem pthSymbolAtIdeal_pow_p_ideal_eq_zero {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal (p := p) α (I ^ p) = 0 := by
  rw [pthSymbolAtIdeal_pow_ideal α I p, ZMod.natCast_self, zero_mul]


-- @@ L155-166 verbatim
/-- Each element of `normalizedFactors I` is a prime, nonzero, maximal ideal. -/
theorem isPrime_of_mem_normalizedFactors {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} {P : Ideal (𝓞 K)}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ ∧ P.IsMaximal := by
  have hPrime : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hP_ne : P ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot]
    exact hPrime.ne_zero
  have hP_isPrime : P.IsPrime := Ideal.isPrime_of_prime hPrime
  refine ⟨hP_isPrime, hP_ne, ?_⟩
  exact Ideal.IsPrime.isMaximal hP_isPrime hP_ne


-- @@ L168-179 verbatim
/-- Multiplicativity in the numerator. -/
theorem pthSymbolAtIdeal_mul {K : Type*} [Field K] [NumberField K]
    {α β : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∉ P)
    (hβ : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, β ∉ P) :
    pthSymbolAtIdeal (p := p) (α * β) I =
      pthSymbolAtIdeal (p := p) α I + pthSymbolAtIdeal (p := p) β I := by
  simp only [pthSymbolAtIdeal]
  rw [← Multiset.sum_map_add]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun P hP ↦ ?_)
  obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
  exact pthSymbolAtPrime_mul hP_ne_bot hP_max (hα P hP) (hβ P hP)


-- @@ L181-196 verbatim
/-- If `α` lies in every prime factor of `I`, then `(α/I)_p` is zero. -/
theorem pthSymbolAtIdeal_eq_zero_of_mem_all_factors {K : Type*} [Field K] [NumberField K]
    {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∈ P) :
    pthSymbolAtIdeal (p := p) α I = 0 := by
  simp only [pthSymbolAtIdeal]
  have hmap :
      (UniqueFactorizationMonoid.normalizedFactors I).map
          (fun P ↦ pthSymbolAtPrime (p := p) α P) =
        (UniqueFactorizationMonoid.normalizedFactors I).map
          (fun _P ↦ (0 : ZMod p)) := by
    refine Multiset.map_congr rfl fun P hP ↦ ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_eq_zero_of_mem hP_ne_bot hP_max (hα P hP)
  rw [hmap]
  simp


-- @@ L198-209 verbatim
/-- The self-symbol `(α/(α))_p` is zero in this totalized encoding. -/
theorem pthSymbolAtIdeal_self_span_eq_zero {K : Type*} [Field K] [NumberField K]
    (α : 𝓞 K) :
    pthSymbolAtIdeal (p := p) α (Ideal.span ({α} : Set (𝓞 K))) = 0 := by
  by_cases hα0 : α = 0
  · rw [hα0]
    simp
  · apply pthSymbolAtIdeal_eq_zero_of_mem_all_factors
    intro P hP
    have hP_dvd : P ∣ Ideal.span ({α} : Set (𝓞 K)) :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    exact (Ideal.dvd_span_singleton (I := P) (x := α)).mp hP_dvd


-- @@ L211-214 verbatim
/-- `(α/β)_p` for principal denominator `β`. -/
noncomputable def pthSymbolAtPrincipal {K : Type*} [Field K] [NumberField K]
    (α β : 𝓞 K) : ZMod p :=
  pthSymbolAtIdeal (p := p) α (Ideal.span ({β} : Set (𝓞 K)))


-- @@ L216-220 verbatim
/-- `pthSymbolAtPrincipal α β = pthSymbolAtIdeal α (Ideal.span {β})`. -/
@[simp] theorem pthSymbolAtPrincipal_eq_atIdeal_span {K : Type*}
    [Field K] [NumberField K] (α β : 𝓞 K) :
    pthSymbolAtPrincipal (p := p) α β =
      pthSymbolAtIdeal (p := p) α (Ideal.span ({β} : Set (𝓞 K))) := rfl


-- @@ L222-228 verbatim
/-- The symbol vanishes when the denominator is one. -/
@[simp] theorem pthSymbolAtPrincipal_one_right {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) :
    pthSymbolAtPrincipal (p := p) α 1 = 0 := by
  simp only [pthSymbolAtPrincipal]
  rw [Ideal.span_singleton_one]
  exact pthSymbolAtIdeal_top _


-- @@ L230-235 verbatim
/-- The symbol vanishes when the denominator is zero. -/
@[simp] theorem pthSymbolAtPrincipal_zero_right {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) :
    pthSymbolAtPrincipal (p := p) α 0 = 0 := by
  simp only [pthSymbolAtPrincipal]
  simp


-- @@ L237-241 verbatim
/-- The self-symbol `(α/α)_p` is zero in this totalized encoding. -/
@[simp] theorem pthSymbolAtPrincipal_self_eq_zero {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) :
    pthSymbolAtPrincipal (p := p) α α = 0 :=
  pthSymbolAtIdeal_self_span_eq_zero α


-- @@ L243-249 verbatim
/-- If `α` lies in every prime factor of `(β)`, then `(α/β)_p = 0`. -/
theorem pthSymbolAtPrincipal_eq_zero_of_mem_all_factors {K : Type*}
    [Field K] [NumberField K] {α β : 𝓞 K}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({β} : Set (𝓞 K))), α ∈ P) :
    pthSymbolAtPrincipal (p := p) α β = 0 :=
  pthSymbolAtIdeal_eq_zero_of_mem_all_factors hα


-- @@ L251-261 verbatim
/-- Multiplicativity in the numerator. -/
theorem pthSymbolAtPrincipal_mul_left {K : Type*}
    [Field K] [NumberField K] {α₁ α₂ β : 𝓞 K}
    (hα₁ : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({β} : Set (𝓞 K))), α₁ ∉ P)
    (hα₂ : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({β} : Set (𝓞 K))), α₂ ∉ P) :
    pthSymbolAtPrincipal (p := p) (α₁ * α₂) β =
      pthSymbolAtPrincipal (p := p) α₁ β +
        pthSymbolAtPrincipal (p := p) α₂ β :=
  pthSymbolAtIdeal_mul hα₁ hα₂


-- @@ L263-274 verbatim
/-- Multiplicativity in the denominator. -/
theorem pthSymbolAtPrincipal_mul_right {K : Type*}
    [Field K] [NumberField K] (α : 𝓞 K) {β γ : 𝓞 K}
    (hβ : β ≠ 0) (hγ : γ ≠ 0) :
    pthSymbolAtPrincipal (p := p) α (β * γ) =
      pthSymbolAtPrincipal (p := p) α β +
        pthSymbolAtPrincipal (p := p) α γ := by
  simp only [pthSymbolAtPrincipal]
  rw [← Ideal.span_singleton_mul_span_singleton]
  refine pthSymbolAtIdeal_mul_ideal _ ?_ ?_
  · exact (Ideal.span_singleton_eq_bot.not).mpr hβ
  · exact (Ideal.span_singleton_eq_bot.not).mpr hγ


-- @@ L276-276 verbatim
end Furtwaengler


-- @@ L278-278 verbatim
end BernoulliRegular


-- @@ L280-280 verbatim
end
