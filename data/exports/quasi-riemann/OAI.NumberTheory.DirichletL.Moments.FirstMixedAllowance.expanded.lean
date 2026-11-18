import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPaidScales
import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstMixedAllowance

-- @@ L10-10 verbatim
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst

-- @@ L11-11 verbatim
open CenteredMomentRankinRadical CenteredMomentFirstCanonicalAllowance

-- @@ L12-12 verbatim
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstScale CenteredMomentSectorLocalization

-- @@ L13-13 verbatim
open CenteredMomentDescentLedger CenteredMomentFirstExceptionalPaidScales

-- @@ L14-14 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L16-18 verbatim
def allowance (C D:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z (C.absNorm:ℝ)-5*Real.logb Z (D.absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6


-- @@ L20-23 verbatim
def extractedAllowance (I J:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6


-- @@ L25-26 verbatim
lemma allowance_nonneg (C D:Ideal O)(Z:ℝ):0≤allowance C D Z:=by
  unfold allowance;positivity


-- @@ L28-36 verbatim
lemma actual_allowance_sum (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(Z:ℝ)(hZ:1<Z):
    allowance C D Z+
      max (3*Real.logb Z (D.absNorm:ℝ)-5*Real.logb Z (C.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=
  actual_canonical_common_support_allowance C D hC hD hCD Z hZ


-- @@ L38-72 verbatim
theorem first_saving_with_allowance {Z:ℝ}(hZ:1<Z)(s:Branch Z):
    let c:=Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)
    let e:=Real.logb Z (s.E.absNorm:ℝ)
    let D₀:=d+Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-
      Real.logb Z (dyadicScale s.n)
    2*(c+s.w)/3-loss s≤
      firstSaving c D₀ s.w (s.q+R+e) s.wo (extractedAllowance s.I s.J Z)
        (max (D₀-c-2*s.w+s.wo) 0+s.kind*s.σ) s.ell:=by
  have hC:(1:ℝ)≤((commonPart s.I s.J).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero s.I s.J))
  have hR:(1:ℝ)≤((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have hE:(1:ℝ)≤(s.E.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr s.hE)
  have hc:=Real.logb_nonneg hZ hC
  have hr:=Real.logb_nonneg hZ hR
  have he:=Real.logb_nonneg hZ hE
  have hd:=retained_deficit s.I s.J s.E s.hE Z s.H s.X s.Tsec s.Csec s.ξ
    hZ s.hH s.hX (zero_lt_one.trans_le s.hCsec) s.hsec s.n s.hn
  have hh:=firstSaving_lower _ _ _ s.w
    (s.q+Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)+Real.logb Z (s.E.absNorm:ℝ))
    _ s.wo (extractedAllowance s.I s.J Z)
    (max (Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)+
      Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-Real.logb Z (dyadicScale s.n)-
      Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)-2*s.w+s.wo) 0+s.kind*s.σ)
    s.ell s.σ (frequencyLoss Z s.Csec s.ξ)
    hc s.hw (by linarith [s.hq]) s.hwo (by unfold extractedAllowance;positivity)
    s.hσ (frequencyLoss_nonneg Z s.Csec s.ξ hZ s.hCsec s.hξ)
    (by linarith [s.hq]) (le_refl _) hd (by nlinarith [s.hkind,s.hσ]) s.hell s.hwσ
  dsimp only at hh ⊢
  simpa only [loss,sub_add_eq_sub_sub] using hh


-- @@ L74-79 verbatim
def columnSaving {Z:ℝ}(s:Branch Z):ℝ:=
  saving s-(Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)+
    Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)-
    2*Real.logb Z ((commonRadical s.I s.J).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ))+
    extractedAllowance s.I s.J Z


-- @@ L81-86 verbatim
lemma column_saving {Z:ℝ}(hZ:1<Z)(s:Branch Z):
    2*removedWidth s/3-loss s≤columnSaving s:=by
  have hh:=first_saving_with_allowance hZ s
  dsimp only [columnSaving,saving,removedWidth] at hh ⊢
  unfold firstSaving at hh ⊢
  linarith


-- @@ L88-88 verbatim
end SevenEighths.CenteredMomentFirstMixedAllowance


-- @@ L90-90 verbatim
end


-- @@ L92-92 verbatim
end OAI
