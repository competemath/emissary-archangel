module

public import BernoulliRegular.TotallyRealSubfield.Conjugation


-- @@ L5-7 verbatim
/-!
# K-level σ(ζ^m) = ζ^{-m}
-/


-- @@ L9-9 verbatim
@[expose] public section


-- @@ L11-11 verbatim
noncomputable section


-- @@ L13-13 verbatim
open BernoulliRegular NumberField NumberField.IsCMField


-- @@ L15-15 verbatim
namespace BernoulliRegular


-- @@ L17-17 verbatim
variable {p : ℕ} [hp : Fact p.Prime]

-- @@ L18-19 verbatim
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]


-- @@ L21-40 verbatim
/-- **`complexConj K (ζ^m) = (ζ^m)⁻¹`** at K-level. -/
theorem complexConj_zeta_pow_eq_inv (m : ℕ) :
    complexConj K (IsCyclotomicExtension.zeta p ℚ K ^ m) =
      (IsCyclotomicExtension.zeta p ℚ K ^ m)⁻¹ := by
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  have h_unit := conj_zeta_pow (p := p) (K := K) (hζ := hζ) (m := m)
  set η : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit with hη_def
  have h_pow_eq : (((η ^ m : (𝓞 K)ˣ) : 𝓞 K) : K) =
      IsCyclotomicExtension.zeta p ℚ K ^ m := by
    rw [hη_def, Units.val_pow_eq_pow_val]
    push_cast
    rfl
  have h_inv_eq : ((((η ^ m)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) =
      (IsCyclotomicExtension.zeta p ℚ K ^ m)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← h_pow_eq, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  rw [show IsCyclotomicExtension.zeta p ℚ K ^ m =
    (((η ^ m : (𝓞 K)ˣ) : 𝓞 K) : K) from h_pow_eq.symm, h_unit]
  exact h_inv_eq


-- @@ L42-42 verbatim
end BernoulliRegular


-- @@ L44-44 verbatim
end
