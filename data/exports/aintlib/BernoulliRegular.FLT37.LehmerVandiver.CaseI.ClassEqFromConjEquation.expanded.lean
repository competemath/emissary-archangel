import BernoulliRegular.FLT37.LehmerVandiver.CaseI.ClassEqFromKummerRatioInt


-- @@ L3-21 verbatim
/-!
# LV010-class-eq-1d: Class equality from σ-conjugate Kummer equation

Convenience wrapper: given `α · δ^p = σ(α) · γ^p` in `𝓞 K` (the integral
form of `α / σα = (γ/δ)^p`), and `(α) = 𝔞^p`, derive `[σ𝔞] = [𝔞]` in
`Cl(𝓞 K)`.

This combines `caseI_class_eq_of_ideal_pow_factored` (LV010-class-eq-1c)
with the standard ideal-arithmetic conversion from element identity to
ideal identity.

Used downstream in LV010-D (`CaseIBridge` term construction): once
Stage 2's Kummer's lemma is shipped, it provides this hypothesis form.

## References

* `caseI_class_eq_of_ideal_pow_factored` (LV010-class-eq-1c).
* `Ideal.span_singleton_mul_span_singleton`, `Ideal.span_singleton_pow`.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open NumberField NumberField.IsCMField


-- @@ L29-29 verbatim
namespace BernoulliRegular


-- @@ L31-31 verbatim
namespace FLT37


-- @@ L33-33 verbatim
namespace LehmerVandiver


-- @@ L35-35 verbatim
namespace CaseI


-- @@ L37-75 verbatim
/-- **Class equality from σ-conjugate Kummer equation in 𝓞 K.** Given:
- `(α) = 𝔞^p` and `(σα) = (σ𝔞)^p` (case-I factor identities)
- `α · δ^p = σ(α) · γ^p` for nonzero γ, δ ∈ 𝓞 K

derive `[σ𝔞] = [𝔞]` in `Cl(𝓞 K)`.

The full input chain: `α/σα = β^p` in `K^×` (Stage 2 Kummer's lemma)
→ write `β = γ/δ` (γ, δ ∈ 𝓞 K, δ ≠ 0; clearing denominators)
→ `α · δ^p = σα · γ^p` (this hypothesis form). -/
theorem caseI_class_eq_complexConj_of_conj_kummer_eq
    {p : ℕ} [Fact p.Prime] (hp_pos : 0 < p) {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (_hα : α ≠ 0)
    {𝔞 : Ideal (𝓞 K)} (h𝔞_nz : 𝔞 ≠ ⊥)
    (h_ideal : Ideal.span ({α} : Set (𝓞 K)) = 𝔞 ^ p)
    (h_conj_ideal :
      Ideal.span ({ringOfIntegersComplexConj K α} : Set (𝓞 K)) =
        (𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ^ p)
    {γ δ : 𝓞 K} (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (h_kummer_eq : α * δ ^ p = ringOfIntegersComplexConj K α * γ ^ p) :
    ClassGroup.mk0
        (⟨𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            intro h
            exact h𝔞_nz <| (Ideal.map_eq_bot_iff_of_injective
              (ringOfIntegersComplexConj K).injective).mp h)⟩
          : nonZeroDivisors (Ideal (𝓞 K))) =
      ClassGroup.mk0
        (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) := by
  have h_ideal_eq : Ideal.span ({α * δ ^ p} : Set (𝓞 K)) =
      Ideal.span ({ringOfIntegersComplexConj K α * γ ^ p} : Set (𝓞 K)) := by
    rw [h_kummer_eq]
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
    ← Ideal.span_singleton_mul_span_singleton (ringOfIntegersComplexConj K α) (γ ^ p),
    ← Ideal.span_singleton_pow, h_ideal, h_conj_ideal, ← mul_pow, ← mul_pow] at h_ideal_eq
  exact caseI_class_eq_of_ideal_pow_factored hp_pos h𝔞_nz
    (mt (Ideal.map_eq_bot_iff_of_injective
      (ringOfIntegersComplexConj K).injective).mp h𝔞_nz) hδ hγ h_ideal_eq


-- @@ L77-77 verbatim
end CaseI


-- @@ L79-79 verbatim
end LehmerVandiver


-- @@ L81-81 verbatim
end FLT37


-- @@ L83-83 verbatim
end BernoulliRegular


-- @@ L85-85 verbatim
end
