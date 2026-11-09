/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Flexible
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteLog


-- @@ L11-18 verbatim
/-!
# Finite Artin-Hasse exponential coordinates

This file defines the principal-unit coordinate `E_N(x) - 1` of the truncated
Artin-Hasse exponential in `𝓞 R' / Q^(N+1)`.  The coefficient representatives
are the existing precision-indexed Artin-Hasse coefficients
`dworkCoeffArtinHasseAtTo`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open scoped NumberField


-- @@ L26-26 verbatim
namespace BernoulliRegular


-- @@ L28-28 verbatim
namespace Furtwaengler


-- @@ L30-30 verbatim
universe u v w


-- @@ L32-32 verbatim
namespace ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L34-34 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L35-35 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L36-36 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L37-37 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']


-- @@ L39-39 verbatim
variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')


-- @@ L41-44 verbatim
/-- The finite Artin-Hasse exponential evaluation `E_N(x)` lifted to
`𝓞 R'`, using the precision-indexed Artin-Hasse coefficient representatives. -/
noncomputable def finiteArtinHasseExp (N : ℕ) (x : 𝓞 R') : 𝓞 R' :=
  dworkThetaTrunc (F.concrete.dworkCoeffArtinHasseAtTo x N) N 1


-- @@ L46-48 verbatim
/-- The principal-unit coordinate `E_N(x) - 1` lifted to `𝓞 R'`. -/
noncomputable def finiteArtinHasseExpCoord (N : ℕ) (x : 𝓞 R') : 𝓞 R' :=
  F.finiteArtinHasseExp N x - 1


-- @@ L50-52 verbatim
@[simp] theorem finiteArtinHasseExpCoord_add_one (N : ℕ) (x : 𝓞 R') :
    F.finiteArtinHasseExpCoord N x + 1 = F.finiteArtinHasseExp N x := by
  simp [finiteArtinHasseExpCoord]


-- @@ L54-59 verbatim
theorem finiteArtinHasseExpCoord_eq_positive_sum (N : ℕ) (x : 𝓞 R') :
    F.finiteArtinHasseExpCoord N x =
      ∑ n ∈ Finset.range N,
        F.concrete.dworkCoeffArtinHasseAtTo x N (n + 1) := by
  simp [finiteArtinHasseExpCoord, finiteArtinHasseExp, dworkThetaTrunc,
    Finset.sum_range_succ']


-- @@ L61-75 verbatim
/-- If `x ∈ Q`, then the Artin-Hasse exponential coordinate lies in `Q`. -/
theorem finiteArtinHasseExpCoord_mem_Q (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseExpCoord N x ∈ F.Q := by
  classical
  rw [F.finiteArtinHasseExpCoord_eq_positive_sum]
  refine Ideal.sum_mem _ ?_
  intro n _hn
  have hcoeff :
      F.concrete.dworkCoeffArtinHasseAtTo x N (n + 1) ∈
        F.Q ^ (n + 1) :=
    F.concrete.dworkCoeffArtinHasseAtTo_mem_Q_pow hx N (n + 1)
  have hle : F.Q ^ (n + 1) ≤ F.Q := by
    simpa using
      (Ideal.pow_le_pow_right (Nat.succ_pos n) : F.Q ^ (n + 1) ≤ F.Q ^ 1)
  exact hle hcoeff


-- @@ L77-93 verbatim
/-- Quotient form of the finite Artin-Hasse exponential evaluation. -/
theorem quotient_mk_finiteArtinHasseExp_eq_trunc_eval (N : ℕ) (x : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.concrete.rIntegralRatToQuotient N)
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExp N x) =
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id (𝓞 R' ⧸ F.Q ^ (N + 1)))
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) x) := by
  dsimp only
  rw [finiteArtinHasseExp]
  have hterm := F.concrete.quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval
    x 1 N
  rw [mul_one] at hterm
  exact hterm


-- @@ L95-110 verbatim
/-- Quotient form of the Artin-Hasse principal-unit coordinate `E_N(x) - 1`. -/
theorem quotient_mk_finiteArtinHasseExpCoord_eq_trunc_eval_sub_one
    (N : ℕ) (x : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.concrete.rIntegralRatToQuotient N)
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExpCoord N x) =
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id (𝓞 R' ⧸ F.Q ^ (N + 1)))
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) x) - 1 := by
  dsimp only
  rw [finiteArtinHasseExpCoord, map_sub,
    F.quotient_mk_finiteArtinHasseExp_eq_trunc_eval]
  simp


-- @@ L112-127 verbatim
/-- Adding back the removed constant term recovers the truncated
Artin-Hasse evaluation in the quotient. -/
theorem one_add_quotient_mk_finiteArtinHasseExpCoord_eq_trunc_eval
    (N : ℕ) (x : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.concrete.rIntegralRatToQuotient N)
    1 + Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExpCoord N x) =
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id (𝓞 R' ⧸ F.Q ^ (N + 1)))
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) x) := by
  dsimp only
  rw [F.quotient_mk_finiteArtinHasseExpCoord_eq_trunc_eval_sub_one]
  ring


-- @@ L129-133 verbatim
theorem quotient_mk_finiteArtinHasseExpCoord_mem_map_Q
    (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExpCoord N x) ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) F.Q :=
  Ideal.mem_map_of_mem _ (F.finiteArtinHasseExpCoord_mem_Q N hx)


-- @@ L135-135 verbatim
end ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L137-137 verbatim
end Furtwaengler


-- @@ L139-139 verbatim
end BernoulliRegular


-- @@ L141-141 verbatim
end
