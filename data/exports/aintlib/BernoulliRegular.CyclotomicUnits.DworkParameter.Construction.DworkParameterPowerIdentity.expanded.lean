module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Construction.ArtinHasseTailUnit


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace BernoulliRegular

-- @@ L10-10 verbatim
namespace CyclotomicUnits

-- @@ L11-11 verbatim
namespace PadicLogSetup

-- @@ L12-12 verbatim
namespace DworkParameter


-- @@ L14-14 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L15-15 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L17-18 verbatim
local instance : CharZero (ValuedCompletion p K) :=
  algebraRat.charZero (ValuedCompletion p K)


-- @@ L20-42 verbatim
theorem dworkParameter_mul_pow_pred_add_p_mul_tailUnit_eq_zero
    (hp_two : 2 < p) :
    dworkParameter p K *
        (dworkParameter p K ^ (p - 1) +
          (p : DworkCompleteIntegerRing p K) *
            artinHasseTailUnit (p := p) (K := K) hp_two) = 0 := by
  apply AdicCompletion.ext_evalₐ
  intro n
  cases n with
  | zero =>
      exact quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _
  | succ N =>
      cases N with
      | zero =>
          rw [map_mul, dworkParameter_evalₐ_one]
          simp
      | succ N =>
          have hfinite :=
            dworkParameterFinite_corrected_factor_eq_zero
              (p := p) (K := K) (N := N + 1) (Nat.succ_pos N)
          rw [map_mul, map_add, map_pow, map_mul, map_natCast,
            dworkParameter_evalₐ, artinHasseTailUnit_evalₐ_succ]
          exact hfinite


-- @@ L44-56 verbatim
theorem dworkParameter_pow_pred_eq_neg_p_mul_tailUnit
    (hp_two : 2 < p) :
    dworkParameter p K ^ (p - 1) =
      -(p : DworkCompleteIntegerRing p K) *
        artinHasseTailUnit (p := p) (K := K) hp_two := by
  have hinside :
      dworkParameter p K ^ (p - 1) +
        (p : DworkCompleteIntegerRing p K) *
          artinHasseTailUnit (p := p) (K := K) hp_two = 0 :=
    dworkParameter_mul_eq_zero (p := p) (K := K)
      (dworkParameter_mul_pow_pred_add_p_mul_tailUnit_eq_zero
        (p := p) (K := K) hp_two)
  simpa [neg_mul] using eq_neg_of_add_eq_zero_left hinside


-- @@ L58-87 verbatim
theorem dworkParameterExpApprox_smodEq
    {M N : ℕ} (hMN : M ≤ N) :
    dworkParameterExpApprox p K M ≡ dworkParameterExpApprox p K N
      [SMOD (lambdaIdeal p K) ^ M •
        (⊤ : Submodule (ValuedIntegerRing p K) (ValuedIntegerRing p K))] := by
  let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
  have hM :
      Ideal.Quotient.mk (I ^ M) (dworkParameterExpApprox p K M) =
        Ideal.Quotient.mk (I ^ M) (valuedCyclotomicZetaInteger p K) := by
    simpa [I] using
      quotient_mk_dworkParameterExpApprox_eq_zeta (p := p) (K := K) M
  have hNpow :
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
          (dworkParameterExpApprox p K N) =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
          (valuedCyclotomicZetaInteger p K) :=
    quotient_mk_dworkParameterExpApprox_eq_zeta (p := p) (K := K) N
  have hN :
      Ideal.Quotient.mk (I ^ M) (dworkParameterExpApprox p K N) =
        Ideal.Quotient.mk (I ^ M) (valuedCyclotomicZetaInteger p K) := by
    have hfactor :=
      congrArg (Ideal.Quotient.factor (Ideal.pow_le_pow_right hMN)) hNpow
    simpa [I] using hfactor
  rw [SModEq.sub_mem]
  have hquot :
      Ideal.Quotient.mk (I ^ M) (dworkParameterExpApprox p K M) =
        Ideal.Quotient.mk (I ^ M) (dworkParameterExpApprox p K N) :=
    hM.trans hN.symm
  exact (mem_ideal_smul_top_iff_self (I ^ M)).mpr
    (Ideal.Quotient.eq.mp hquot)


-- @@ L89-96 verbatim
/-- The Cauchy sequence of finite Artin-Hasse exponential approximants at
`G_p(lambda)`. -/
def dworkParameterExpCauchySeq :
    AdicCompletion.AdicCauchySequence (lambdaIdeal p K) (ValuedIntegerRing p K) where
  val N := dworkParameterExpApprox p K N
  property := by
    intro M N hMN
    exact dworkParameterExpApprox_smodEq (p := p) (K := K) hMN


-- @@ L98-101 verbatim
/-- The specialized completed Artin-Hasse evaluation `E_p(G_p(lambda))`,
defined as the limit of finite truncation evaluations. -/
def dworkParameterExp : DworkCompleteIntegerRing p K :=
  AdicCompletion.mkₐ (lambdaIdeal p K) (dworkParameterExpCauchySeq p K)


-- @@ L103-109 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem dworkParameterExp_evalₐ (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N (dworkParameterExp p K) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (dworkParameterExpApprox p K N) := by
  simp [dworkParameterExp, dworkParameterExpCauchySeq]


-- @@ L111-118 verbatim
theorem dworkParameterExp_eq_zeta :
    dworkParameterExp p K =
      AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [dworkParameterExp_evalₐ, AdicCompletion.evalₐ_of]
  exact quotient_mk_dworkParameterExpApprox_eq_zeta (p := p) (K := K) N


-- @@ L120-133 verbatim
theorem evalIntegralPowerSeriesMod_exp_dworkParameter (N : ℕ) :
    evalIntegralPowerSeriesMod p K (integralExpSeries p K) (dworkParameter p K) N =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (valuedCyclotomicZetaInteger p K) := by
  calc
    evalIntegralPowerSeriesMod p K (integralExpSeries p K) (dworkParameter p K) N =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
          (dworkParameterExpApprox p K N) := by
      rw [evalIntegralPowerSeriesMod, dworkParameter_evalₐ]
      exact (quotient_mk_dworkParameterExpApprox_eq_trunc_eval
        (p := p) (K := K) N).symm
    _ = Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (valuedCyclotomicZetaInteger p K) :=
      quotient_mk_dworkParameterExpApprox_eq_zeta (p := p) (K := K) N


-- @@ L135-143 verbatim
theorem dworkParameter_eval_exp :
    evalIntegralPowerSeries p K (integralExpSeries p K) (dworkParameter p K)
        (dworkParameter_evalₐ_one (p := p) (K := K)) =
      AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalIntegralPowerSeries_evalₐ, AdicCompletion.evalₐ_of]
  exact evalIntegralPowerSeriesMod_exp_dworkParameter (p := p) (K := K) N


-- @@ L145-166 verbatim
/-- Uniqueness of the completed inverse-series construction: a completed
element with the same finite coordinates as `G_p(lambda)` is the constructed
Dwork parameter. -/
theorem dworkParameter_unique
    {x : DworkCompleteIntegerRing p K}
    (hx :
      ∀ N,
        AdicCompletion.evalₐ (lambdaIdeal p K) N x =
          (PowerSeries.trunc N
            (PowerSeries.map
              (Ideal.Quotient.mk ((lambdaIdeal p K) ^ N))
              (integralInverseSeries p K))).eval₂
            (RingHom.id
              (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N))
            (Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
              (valuedCyclotomicLambdaInteger p K))) :
    x = dworkParameter p K := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [hx N, dworkParameter_evalₐ]
  exact (quotient_mk_dworkParameterApprox_eq_trunc_eval
    (p := p) (K := K) N).symm



-- @@ L169-169 verbatim
end DworkParameter

-- @@ L170-170 verbatim
end PadicLogSetup

-- @@ L171-171 verbatim
end CyclotomicUnits

-- @@ L172-172 verbatim
end BernoulliRegular


-- @@ L174-174 verbatim
end
