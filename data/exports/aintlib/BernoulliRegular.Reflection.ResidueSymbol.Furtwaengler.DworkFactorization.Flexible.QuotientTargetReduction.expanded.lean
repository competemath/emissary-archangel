module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Flexible.ArtinHasseExpInverseNormalization


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped NumberField


-- @@ L11-11 verbatim
namespace BernoulliRegular


-- @@ L13-13 verbatim
namespace Furtwaengler


-- @@ L15-15 verbatim
universe u v w


-- @@ L17-17 verbatim
namespace ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L19-19 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L20-20 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L21-21 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L22-22 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']


-- @@ L24-24 verbatim
variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')


-- @@ L26-32 verbatim
/-- The finite product of Artin-Hasse theta truncations with precision-indexed
coefficient representatives. -/
noncomputable def artinHasseThetaTruncProductAtTo (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    𝓞 R' :=
  dworkThetaFrobeniusProduct ℓ F.concrete.f N
    (F.concrete.dworkCoeffArtinHasseAtTo γ N)
    (F.teichUnitFullVal (F.traceScale * y))


-- @@ L34-41 verbatim
/-- The finite multi-index sum for precision-indexed Artin-Hasse coefficient
representatives. -/
noncomputable def artinHasseDworkMultiIndexSumAtTo (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    𝓞 R' :=
  ∑ m ∈ Furtwaengler.multiIndexLE F.concrete.f N,
    dworkMultiIndexTerm ℓ
      (F.concrete.dworkCoeffArtinHasseAtTo γ N)
      (F.teichUnitFullVal (F.traceScale * y)) m


-- @@ L43-93 verbatim
/-- Quotient normal form for the precision-indexed flexible Artin-Hasse theta
product. -/
theorem quotient_mk_artinHasseThetaTruncProductAtTo_eq_prod_trunc_eval
    (γ : 𝓞 R') (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n ↦ artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.concrete.rIntegralRatToQuotient N)
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (F.artinHasseThetaTruncProductAtTo γ N y) =
      ∏ i : Fin F.concrete.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          (Ideal.Quotient.mk (F.Q ^ (N + 1))
            (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
  classical
  dsimp only
  let S0 : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' := F.concrete
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n ↦ artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (S0.rIntegralRatToQuotient N)
  let u : Fin F.concrete.f → 𝓞 R' := fun i ↦
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (F.artinHasseThetaTruncProductAtTo γ N y)
        = ∏ i : Fin F.concrete.f,
            Ideal.Quotient.mk (F.Q ^ (N + 1))
              (dworkThetaTrunc (S0.dworkCoeffArtinHasseAtTo γ N) N (u i)) := by
            simp [artinHasseThetaTruncProductAtTo, dworkThetaFrobeniusProduct,
              S0, u, map_prod]
    _ = ∏ i : Fin F.concrete.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          (Ideal.Quotient.mk (F.Q ^ (N + 1)) (γ * u i)) := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            show Ideal.Quotient.mk (F.Q ^ (N + 1))
                (dworkThetaTrunc (S0.dworkCoeffArtinHasseAtTo γ N) N (u i)) =
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (Ideal.Quotient.mk (F.Q ^ (N + 1)) (γ * u i))
            exact S0.quotient_mk_dworkThetaTrunc_artinHasseAtTo_eq_trunc_eval
                γ (u i) N
    _ = ∏ i : Fin F.concrete.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          (Ideal.Quotient.mk (F.Q ^ (N + 1))
            (γ * (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
            rfl


-- @@ L95-157 verbatim
/-- Quotient normal form for the corrected theta product, with the parameter
replaced by the finite inverse-series evaluation at `π`. -/
theorem quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_prod_inverse_trunc_eval
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n ↦ artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.concrete.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.concrete.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y) =
      ∏ i : Fin F.concrete.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
            Ideal.Quotient.mk (F.Q ^ (N + 1))
              ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
  classical
  dsimp only
  let S0 : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' := F.concrete
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n ↦ artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (S0.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (S0.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let γ : 𝓞 R' := S0.artinHasseDworkParameterApproxTo N
  let u : Fin F.concrete.f → 𝓞 R' := fun i ↦
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  have hγ :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) γ =
        (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar :=
    S0.quotient_mk_artinHasseDworkParameterApproxTo_eq_trunc_eval N
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (F.artinHasseThetaTruncProductAtTo γ N y)
        = ∏ i : Fin F.concrete.f,
            (PowerSeries.trunc (N + 1) Eps).eval₂
              (RingHom.id A)
              (Ideal.Quotient.mk (F.Q ^ (N + 1)) (γ * u i)) := by
            simpa [Eps, hE, S0, γ, u, A] using
              F.quotient_mk_artinHasseThetaTruncProductAtTo_eq_prod_trunc_eval
                γ N y
    _ = ∏ i : Fin F.concrete.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂
          (RingHom.id A)
          ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
            Ideal.Quotient.mk (F.Q ^ (N + 1)) (u i)) := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            have harg :
                Ideal.Quotient.mk (F.Q ^ (N + 1)) (γ * u i) =
                  (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
                    Ideal.Quotient.mk (F.Q ^ (N + 1)) (u i) := by
              rw [map_mul, hγ]
            rw [harg]


-- @@ L159-180 verbatim
/-- Exact quotient normal form for the conductor-flexible trace-form additive
character. -/
theorem quotient_mk_psiInt_eq_one_add_pi_pow_trace (N : ℕ) (y : kˣ) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k)) =
      (1 + Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π) ^
        (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val := by
  let t : ℕ :=
    (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hpsi :
      F.psiInt (y : k) = F.zeta_ell_int ^ t := by
    simpa [t] using
      F.toConductorFlexibleTraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace
        (y : k)
  have hzeta : F.zeta_ell_int = 1 + F.π := by
    rw [F.hπ]
    ring
  calc
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k))
        = Ideal.Quotient.mk (F.Q ^ (N + 1)) ((1 + F.π) ^ t) := by
            rw [hpsi, hzeta]
    _ = (1 + Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π) ^ t := by
            simp


-- @@ L182-182 verbatim
/-! ### Named flexible quotient target for the all-order Dwork endpoint -/


-- @@ L184-206 verbatim
/-- The normalized quotient product identity for the conductor-flexible
Artin-Hasse Dwork approximation.  This is the statement supplied by the later
finite-log proof: the Frobenius-orbit product of the truncated Artin-Hasse
evaluations equals `(1 + π)^Tr`. -/
def artinHasseApproxDworkOneAddPiProductIdentity (N : ℕ) (y : kˣ) : Prop :=
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n ↦ artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.concrete.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.concrete.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  (1 + πbar) ^
      (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val =
    ∏ i : Fin F.concrete.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id A)
        (δ *
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))


-- @@ L208-278 verbatim
/-- Flexible quotient target for the all-order Artin-Hasse splitting: the
membership theorem is equivalent to the named normalized product identity. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n ↦ artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.concrete.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.concrete.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    F.psiInt (y : k) -
        F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y ∈
      F.Q ^ (N + 1) ↔
      (1 + πbar) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val =
        ∏ i : Fin F.concrete.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂
            (RingHom.id A)
            ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
              Ideal.Quotient.mk (F.Q ^ (N + 1))
                ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ)))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n ↦ artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo (F.concrete.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.concrete.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let theta : 𝓞 R' :=
    F.artinHasseThetaTruncProductAtTo
      (F.concrete.artinHasseDworkParameterApproxTo N) N y
  let target : A :=
    ∏ i : Fin F.concrete.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂
        (RingHom.id A)
        ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar *
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            ((F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))))
  have hpsi :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k)) =
        (1 + πbar) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val := by
    simpa [πbar, A] using F.quotient_mk_psiInt_eq_one_add_pi_pow_trace N y
  have htheta :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) theta = target := by
    simpa [theta, target, Eps, Ips, πbar, hE, A] using
      F.quotient_mk_artinHasseThetaTruncProductAtTo_approx_eq_prod_inverse_trunc_eval
        N y
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k) - theta) = 0 ↔
      (1 + πbar) ^
          (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val =
        target
  rw [map_sub]
  constructor
  · intro h
    have heq :
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.psiInt (y : k)) =
          Ideal.Quotient.mk (F.Q ^ (N + 1)) theta := sub_eq_zero.mp h
    simpa [hpsi, htheta] using heq
  · intro h
    rw [hpsi, htheta, h]
    simp


-- @@ L280-289 verbatim
/-- Named flexible quotient target for the all-order Dwork endpoint. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff_oneAddPiProductIdentity
    (N : ℕ) (y : kˣ) :
    F.psiInt (y : k) -
        F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y ∈
      F.Q ^ (N + 1) ↔
      F.artinHasseApproxDworkOneAddPiProductIdentity N y := by
  simpa [artinHasseApproxDworkOneAddPiProductIdentity] using
    F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff N y


-- @@ L291-301 verbatim
/-- Forward wrapper: proving the normalized quotient product identity is enough
to close the conductor-flexible all-order Dwork membership theorem. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_of_oneAddPiProductIdentity
    {N : ℕ} {y : kˣ}
    (h : F.artinHasseApproxDworkOneAddPiProductIdentity N y) :
    F.psiInt (y : k) -
        F.artinHasseThetaTruncProductAtTo
          (F.concrete.artinHasseDworkParameterApproxTo N) N y ∈
      F.Q ^ (N + 1) :=
  (F.psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_iff_oneAddPiProductIdentity
    N y).2 h


-- @@ L303-303 verbatim
end ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L305-305 verbatim
end Furtwaengler


-- @@ L307-307 verbatim
end BernoulliRegular


-- @@ L309-309 verbatim
end


-- @@ L311-311 verbatim
end
