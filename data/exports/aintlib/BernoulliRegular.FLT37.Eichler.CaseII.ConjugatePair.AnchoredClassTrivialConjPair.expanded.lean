import BernoulliRegular.FLT37.Eichler.CaseII.ConjugatePair.ConjPairDatum


-- @@ L3-34 verbatim
/-!
# [FLT37-CASEII-R2] II1 (`c = 1`) over σ-conjugate-pair data — the *clean* collapse

Over a σ-conjugate-pair Case-II datum `D : ConjPairCaseIIData37 K m` (`σx = y`, `σy = x`), the
anchored class

  `c = [𝔞(η)] · [𝔞(η₀)]⁻¹`

is **trivial**, `[𝔞(η)] = [𝔞(η₀)]`, by an argument that is *strictly cleaner* than the
individually-real one (`CaseIIRealAnchoredClass.lean`):

* the conjugate-self-fixedness `σ𝔞(η) = 𝔞(η)` (`ConjPairCaseIIData37.map_rootIdeal`) gives
  `σ[𝔞(η)] = [𝔞(η)]` and `σ[𝔞(η₀)] = [𝔞(η₀)]` **directly**, hence `σc = c` — with **no Lemma 9.2
  input** and **no** `η₀⁻¹ = η₀` lemma;
* the **reality-free** `c · σc = 1` (`caseII_anchored_classGroup_mul_conj_eq_one`, Vandiver
  `37 ∤ h⁺`) then gives `c² = 1`;
* the **reality-free** `c³⁷ = 1` (`caseII_anchored_class_pow_eq_one`) gives, with `gcd(2,37)=1`,
  `c = 1`.

So II1 transfers to the σ-conjugate-pair structure *more cleanly* than to the individually-real
one: the swap `σ𝔞(η) = 𝔞(η⁻¹)` is replaced by the fixedness `σ𝔞(η) = 𝔞(η)`, which makes `σc = c`
*automatic* (the individually-real route needed the genuine Lemma-9.2 `[𝔞(η)]=[𝔞(η⁻¹)]` plus
`η₀⁻¹=η₀` to reach `σc=c`).

This file proves `c = 1` and the resulting `η₀`-principalization
(`CaseIIPrincipalizationAgainstEtaZero`) over `ConjPairCaseIIData37`.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1, Lemma 9.2), Thm 9.4.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
open NumberField Polynomial NumberField.IsCMField


-- @@ L42-42 verbatim
namespace BernoulliRegular.FLT37.Eichler


-- @@ L44-44 verbatim
open FLT37.LehmerVandiver.CaseII


-- @@ L46-47 verbatim
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]


-- @@ L49-49 verbatim
namespace ConjPairCaseIIData37


-- @@ L51-51 verbatim
variable {m : ℕ} (D : ConjPairCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)


-- @@ L53-70 verbatim
/-- **`σ[𝔞(η)] = [𝔞(η)]` (the root class is σ-fixed) over a σ-conjugate pair.**

Cleaner than the individually-real Lemma-9.2 input.  The naturality `ClassGroup.mulEquiv σ [𝔞] =
[σ𝔞]` (`caseII_classGroup_conj_mk0`) plus the *self*-fixedness `σ𝔞(η) = 𝔞(η)`
(`ConjPairCaseIIData37.map_rootIdeal`) give `σ[𝔞(η)] = [σ𝔞(η)] = [𝔞(η)]` immediately. -/
theorem classGroup_conj_rootIdeal_eq (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    ClassGroup.mulEquiv (ringOfIntegersComplexConj K).toRingEquiv
        (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩) =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hne : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η ≠ ⊥ :=
    caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η
  rw [caseII_classGroup_conj_mk0 hne]
  exact congrArg ClassGroup.mk0 (Subtype.ext (D.map_rootIdeal hp η))


-- @@ L72-95 verbatim
set_option maxRecDepth 4000 in
/-- **`c² = 1` over a σ-conjugate pair**, from `σc = c` (free, `classGroup_conj_rootIdeal_eq`) and
the reality-free `c·σc = 1` (`caseII_anchored_classGroup_mul_conj_eq_one`, Vandiver).  The anchored
class `c = [𝔞(η)]·[𝔞(η₀)]⁻¹` satisfies `σc = [σ𝔞(η)]·[σ𝔞(η₀)]⁻¹ = [𝔞(η)]·[𝔞(η₀)]⁻¹ = c`
(both root classes σ-fixed), so `1 = c·σc = c²`. -/
theorem anchored_class_sq_eq_one
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ *
      (ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero)⟩)⁻¹) ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `c · σc = 1` (reality-free Vandiver form).
  have hcc := caseII_anchored_classGroup_mul_conj_eq_one D.toCaseIIData37 hp h_VC η
  -- `σc = c`: `σ` is a group hom, so `σc = σ[𝔞(η)] · (σ[𝔞(η₀)])⁻¹ = [𝔞(η)]·[𝔞(η₀)]⁻¹ = c`.
  rw [map_mul, map_inv, D.classGroup_conj_rootIdeal_eq hp η,
    D.classGroup_conj_rootIdeal_eq hp D.etaZero] at hcc
  -- `hcc : c · c = 1`, i.e. `c² = 1`.
  rw [sq]; exact hcc


-- @@ L97-119 verbatim
set_option maxRecDepth 4000 in
/-- **`c = 1` over a σ-conjugate pair**: the anchored class is trivial, `[𝔞(η)] = [𝔞(η₀)]`.

From `c² = 1` (`anchored_class_sq_eq_one`) and `c³⁷ = 1` (`caseII_anchored_class_pow_eq_one`,
reality-free), the order of `c` divides `gcd(2, 37) = 1`, so `c = 1`. -/
theorem anchored_class_eq_one
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]; exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp η)⟩ =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (by rw [Ideal.zero_eq_bot]
              exact caseII_rootIdeal_ne_bot D.toCaseIIData37 hp D.etaZero)⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hpow37 := caseII_anchored_class_pow_eq_one D.toCaseIIData37 hp η
  have hpow2 := D.anchored_class_sq_eq_one hp h_VC η
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow2)
    (orderOf_dvd_of_pow_eq_one hpow37)
  rw [show Nat.gcd 2 37 = 1 by decide] at hdvd
  exact mul_inv_eq_one.mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))


-- @@ L121-143 verbatim
/-- **The `η₀`-principalization holds over a σ-conjugate pair** (II1 over `ConjPairCaseIIData37`).

For `K = CyclotomicField 37 ℚ`, the proven `¬ 37 ∣ h⁺` (`Sinnott.flt37_not_dvd_hPlus`) supplies the
Vandiver coprimality, so `c = 1` (`anchored_class_eq_one`) at every adjacent root, and the anchored
quotient `𝔞(η)/𝔞₀` is principal — exactly `CaseIIPrincipalizationAgainstEtaZero`.  This is the
genuine, non-vacuous II1 over the σ-conjugate-pair structure. -/
theorem etaZeroPrincipalization
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m) :
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))))) :=
    (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)).mpr Sinnott.flt37_not_dvd_hPlus
  intro η hη
  have h_classEq := D.anchored_class_eq_one (by decide : (37 : ℕ) ≠ 2) h_VC η
  -- `[𝔞(η)] = [𝔞(η₀)] ⟹ 𝔞(η)/𝔞(η₀) principal ⟹ 𝔞(η)/𝔞₀ principal`.
  have h_root := caseII_rootQuotientPrincipal_of_classEq D.toCaseIIData37
    (by decide : (37 : ℕ) ≠ 2) η h_classEq
  exact caseII_isPrincipal_aDivAEtaZero_of_rootQuotientPrincipal
    (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy η h_root


-- @@ L145-145 verbatim
end ConjPairCaseIIData37


-- @@ L147-147 verbatim
end BernoulliRegular.FLT37.Eichler


-- @@ L149-149 verbatim
end


-- @@ L151-151 verbatim
end
