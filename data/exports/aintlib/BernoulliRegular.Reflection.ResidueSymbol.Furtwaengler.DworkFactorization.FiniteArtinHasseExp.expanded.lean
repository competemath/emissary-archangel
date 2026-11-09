/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Concrete
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLog


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
namespace FullTeichStickelbergerSetup


-- @@ L34-34 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L35-35 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L36-36 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L37-38 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']


-- @@ L40-40 verbatim
variable (F : FullTeichStickelbergerSetup ℓ p k K R')


-- @@ L42-45 verbatim
/-- The finite Artin-Hasse exponential evaluation `E_N(x)` lifted to
`𝓞 R'`, using the precision-indexed Artin-Hasse coefficient representatives. -/
noncomputable def finiteArtinHasseExp (N : ℕ) (x : 𝓞 R') : 𝓞 R' :=
  dworkThetaTrunc (dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N) N 1


-- @@ L47-49 verbatim
/-- The principal-unit coordinate `E_N(x) - 1` lifted to `𝓞 R'`. -/
noncomputable def finiteArtinHasseExpCoord (N : ℕ) (x : 𝓞 R') : 𝓞 R' :=
  F.finiteArtinHasseExp N x - 1


-- @@ L51-53 verbatim
@[simp] theorem finiteArtinHasseExpCoord_add_one (N : ℕ) (x : 𝓞 R') :
    F.finiteArtinHasseExpCoord N x + 1 = F.finiteArtinHasseExp N x := by
  simp [finiteArtinHasseExpCoord]


-- @@ L55-60 verbatim
theorem finiteArtinHasseExpCoord_eq_positive_sum (N : ℕ) (x : 𝓞 R') :
    F.finiteArtinHasseExpCoord N x =
      ∑ n ∈ Finset.range N,
        dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N (n + 1) := by
  simp [finiteArtinHasseExpCoord, finiteArtinHasseExp, dworkThetaTrunc,
    Finset.sum_range_succ']


-- @@ L62-76 verbatim
/-- If `x ∈ Q`, then the Artin-Hasse exponential coordinate lies in `Q`. -/
theorem finiteArtinHasseExpCoord_mem_Q (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseExpCoord N x ∈ F.Q := by
  classical
  rw [F.finiteArtinHasseExpCoord_eq_positive_sum]
  refine Ideal.sum_mem _ ?_
  intro n _hn
  have hcoeff :
      dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup x N (n + 1) ∈
        F.Q ^ (n + 1) :=
    dworkCoeffArtinHasseAtTo_mem_Q_pow F.toConcreteStickelbergerSetup hx N (n + 1)
  have hle : F.Q ^ (n + 1) ≤ F.Q := by
    simpa using
      (Ideal.pow_le_pow_right (Nat.succ_pos n) : F.Q ^ (n + 1) ≤ F.Q ^ 1)
  exact hle hcoeff


-- @@ L78-92 verbatim
/-- Quotient form of the finite Artin-Hasse exponential evaluation. -/
theorem quotient_mk_finiteArtinHasseExp_eq_trunc_eval (N : ℕ) (x : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExp N x) =
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id (𝓞 R' ⧸ F.Q ^ (N + 1)))
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) x) := by
  dsimp only
  simpa [finiteArtinHasseExp] using
    F.toConcreteStickelbergerSetup.quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval
      x 1 N


-- @@ L94-109 verbatim
/-- Quotient form of the Artin-Hasse principal-unit coordinate `E_N(x) - 1`. -/
theorem quotient_mk_finiteArtinHasseExpCoord_eq_trunc_eval_sub_one
    (N : ℕ) (x : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExpCoord N x) =
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id (𝓞 R' ⧸ F.Q ^ (N + 1)))
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) x) - 1 := by
  dsimp only
  rw [finiteArtinHasseExpCoord, map_sub,
    F.quotient_mk_finiteArtinHasseExp_eq_trunc_eval]
  simp


-- @@ L111-126 verbatim
/-- Adding back the removed constant term recovers the truncated
Artin-Hasse evaluation in the quotient. -/
theorem one_add_quotient_mk_finiteArtinHasseExpCoord_eq_trunc_eval
    (N : ℕ) (x : 𝓞 R') :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    1 + Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExpCoord N x) =
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id (𝓞 R' ⧸ F.Q ^ (N + 1)))
        (Ideal.Quotient.mk (F.Q ^ (N + 1)) x) := by
  dsimp only
  rw [F.quotient_mk_finiteArtinHasseExpCoord_eq_trunc_eval_sub_one]
  ring


-- @@ L128-132 verbatim
theorem quotient_mk_finiteArtinHasseExpCoord_mem_map_Q
    (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.finiteArtinHasseExpCoord N x) ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) F.Q :=
  Ideal.mem_map_of_mem _ (F.finiteArtinHasseExpCoord_mem_Q N hx)


-- @@ L134-134 verbatim
end FullTeichStickelbergerSetup


-- @@ L136-136 verbatim
end Furtwaengler


-- @@ L138-138 verbatim
end BernoulliRegular


-- @@ L140-140 verbatim
end
