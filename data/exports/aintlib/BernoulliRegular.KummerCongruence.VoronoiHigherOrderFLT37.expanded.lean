import BernoulliRegular.KummerCongruence.VoronoiHigherOrder
import BernoulliRegular.BernoulliFast.Tactic



-- @@ L5-17 verbatim
/-!
# FLT37 instances of the order-2 Voronoi congruence at k = 68

This file ships the `(p, k) = (37, 68)` specialisation of
`voronoi_congruence_mod_p_sq_extended` from the `module`-mode
`VoronoiHigherOrder.lean`, plus the cached Bernoulli-denominator
coprimality lemmas (which require `bernoulli_decide` from the
non-`module` `BernoulliFast.Tactic`).

Together with `voronoi_congruence_mod_37_sq_thirtytwo`, this
provides the two mod-37² constraints on `B_32` and `B_68` needed for
Kellner's Prop 2.7 α₀, α₁ chain at the FLT37 irregular pair.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace BernoulliRegular


-- @@ L25-25 verbatim
/-! ## Cached Bernoulli denominator coprimality for FLT37 k=68 ih_B -/


-- @@ L27-28 verbatim
private theorem bernoulli_den_38_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 38).den := by bernoulli_decide


-- @@ L30-31 verbatim
private theorem bernoulli_den_40_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 40).den := by bernoulli_decide


-- @@ L33-34 verbatim
private theorem bernoulli_den_42_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 42).den := by bernoulli_decide


-- @@ L36-37 verbatim
private theorem bernoulli_den_44_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 44).den := by bernoulli_decide


-- @@ L39-40 verbatim
private theorem bernoulli_den_46_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 46).den := by bernoulli_decide


-- @@ L42-43 verbatim
private theorem bernoulli_den_48_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 48).den := by bernoulli_decide


-- @@ L45-46 verbatim
private theorem bernoulli_den_50_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 50).den := by bernoulli_decide


-- @@ L48-49 verbatim
private theorem bernoulli_den_52_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 52).den := by bernoulli_decide


-- @@ L51-52 verbatim
private theorem bernoulli_den_54_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 54).den := by bernoulli_decide


-- @@ L54-55 verbatim
private theorem bernoulli_den_56_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 56).den := by bernoulli_decide


-- @@ L57-58 verbatim
private theorem bernoulli_den_58_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 58).den := by bernoulli_decide


-- @@ L60-61 verbatim
private theorem bernoulli_den_60_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 60).den := by bernoulli_decide


-- @@ L63-64 verbatim
private theorem bernoulli_den_62_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 62).den := by bernoulli_decide


-- @@ L66-67 verbatim
private theorem bernoulli_den_64_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 64).den := by bernoulli_decide


-- @@ L69-70 verbatim
private theorem bernoulli_den_66_coprime_37 :
    ¬ (37 : ℕ) ∣ (bernoulli 66).den := by bernoulli_decide


-- @@ L72-117 verbatim
/-- **FLT37 specialisation** of the order-2 Voronoi congruence at
`(p, k) = (37, 68)`: the substantive mod-`37²` constraint on `B_{68}`
that feeds into Kellner's Prop 2.7 chain for the α₁ invariant of the
FLT37 irregular pair (37, 32).

Discharge of the parametric `ih_B` is via numerical denominator checks
for j ∈ {38, 40, …, 66} (even, ≠ 36). -/
theorem voronoi_congruence_mod_37_sq_sixtyeight
    {a : ℕ} (ha_coprime : ¬ (37 : ℕ) ∣ a) :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    ∃ z : ℤ_[37],
      ((a : ℚ_[37]) ^ 68 - 1) * ((bernoulli 68 : ℚ) : ℚ_[37]) -
          (68 : ℚ_[37]) * ((a : ℚ_[37]) ^ 67) *
            ((∑ j ∈ Finset.range 37, j ^ 67 * (j * a / 37) : ℕ) : ℚ_[37]) +
          ((Nat.choose 68 2 : ℕ) : ℚ_[37]) * ((a : ℚ_[37]) ^ 66) *
            (37 : ℚ_[37]) *
              ((∑ j ∈ Finset.range 37, j ^ 66 * (j * a / 37) ^ 2 : ℕ) :
                ℚ_[37]) =
        (37 : ℚ_[37]) ^ 2 * ((z : ℤ_[37]) : ℚ_[37]) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply voronoi_congruence_mod_p_sq_extended (p := 37) (k := 68) (a := a)
    (by decide : (37 : ℕ) ≠ 2) ha_coprime
    (by decide : 37 + 2 ≤ 68)
    (by decide : Even 68)
    (by decide : (68 : ℕ) ≤ 2 * 37 - 3)
    (by decide : ¬ (37 : ℕ) ∣ (68 + 1))
  intro j hj1 hj2 hj_even hj_not_dvd
  apply bernoulli_mem_padicInt_of_p_not_dvd_den
  interval_cases j <;>
    first
    | (exfalso; revert hj_even; decide)
    | exact bernoulli_den_38_coprime_37
    | exact bernoulli_den_40_coprime_37
    | exact bernoulli_den_42_coprime_37
    | exact bernoulli_den_44_coprime_37
    | exact bernoulli_den_46_coprime_37
    | exact bernoulli_den_48_coprime_37
    | exact bernoulli_den_50_coprime_37
    | exact bernoulli_den_52_coprime_37
    | exact bernoulli_den_54_coprime_37
    | exact bernoulli_den_56_coprime_37
    | exact bernoulli_den_58_coprime_37
    | exact bernoulli_den_60_coprime_37
    | exact bernoulli_den_62_coprime_37
    | exact bernoulli_den_64_coprime_37
    | exact bernoulli_den_66_coprime_37


-- @@ L119-119 verbatim
end BernoulliRegular


-- @@ L121-121 verbatim
end
