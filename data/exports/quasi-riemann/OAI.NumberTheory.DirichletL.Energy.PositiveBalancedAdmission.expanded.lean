import OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters
import OAI.NumberTheory.DirichletL.Energy.NaturalSourceAdmission
import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

-- @@ L11-11 verbatim
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound

-- @@ L12-12 verbatim
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy

-- @@ L13-13 verbatim
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands

-- @@ L14-14 verbatim
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource

-- @@ L15-15 verbatim
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl

-- @@ L16-16 verbatim
open CenteredMomentEnergyOriginalHighReflectionSymmetric

-- @@ L17-17 verbatim
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry

-- @@ L18-18 verbatim
open CenteredMomentCommonRadialData CenteredMomentSourceRow

-- @@ L19-19 verbatim
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform

-- @@ L20-20 verbatim
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily

-- @@ L21-21 verbatim
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass

-- @@ L22-22 verbatim
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot

-- @@ L23-23 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L24-24 verbatim
variable {α:Type*}[Fintype α]

-- @@ L25-25 verbatim
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _

-- @@ L26-26 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L27-27 verbatim
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L28-28 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

-- @@ L29-29 verbatim
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)

-- @@ L30-30 verbatim
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)

-- @@ L31-31 verbatim
variable (hWs:Function.support W⊆Set.Icc aslot bslot)

-- @@ L32-32 verbatim
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)

-- @@ L33-33 verbatim
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)

-- @@ L34-34 verbatim
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)


-- @@ L36-37 verbatim
local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂


-- @@ L39-39 verbatim
open CenteredMomentEnergyPositiveHighParameters

-- @@ L40-40 verbatim
open CenteredMomentEnergyNaturalInputMatches CenteredMomentAmplificationChildInput


-- @@ L42-51 verbatim
theorem fixed_fields :
    (balancedSource).lower=aslot ∧ (balancedSource).upper=bslot ∧
    (balancedSource).b₁=b ∧ (balancedSource).b₂=b ∧
    (balancedSource).W₁=p.profile 0 ∧ (balancedSource).W₂=p.profile 1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧ (balancedSource).t=t ∧
    (∀i,(balancedSource).lo i=aslot) ∧ (∀i,(balancedSource).hi i=bslot) ∧
    (∀i,(balancedSource).M i=profileBound W hW aslot bslot lo hi haslot hWs) ∧
    (∀i,(balancedSource).P i=Z^(w i)) := by
  repeat' constructor
  all_goals intro i;rfl


-- @@ L53-58 verbatim
theorem fixed_lower_product (N:ℕ)(hN:Fintype.card α≤N) :
    0<(min 1 aslot)^N*a*a ∧
    (min 1 aslot)^N*a*a≤(∏i,(balancedSource).lo i)*a*a := by
  have hh:=CenteredMomentEnergyOriginalProfileControl.lower_product balancedSource N aslot haslot hN
    (fun _=>le_rfl)
  exact ⟨by positivity,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le⟩


-- @@ L60-65 verbatim
lemma exact_log_volume (hZ:1<Z) :
    Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+∑i,w i := by
  have hh:=CenteredMomentEnergyInputParentCapacity.input_volume_log balancedSource Z
  change Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+
    ∑i,Real.logb Z (Z^(w i)) at hh
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh


-- @@ L67-87 verbatim
theorem four_upper_scales (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤L) :
    (balancedSource).X₁≤Z^L ∧ (balancedSource).X₂≤Z^L ∧
    (balancedSource).Y₁≤Z^L ∧ (balancedSource).Y₂≤Z^L := by
  have hp:0<Z:=zero_lt_one.trans hZ
  have hx:=CenteredMomentEnergyNaturalSourceAdmission.original_scale_caps w hZ hX₁ hX₂ hw
    (by linarith : (1/6:ℝ)≤κ) hcap hs
  have hv:=balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs
  have hprod:1≤∏i,Z^(w i):=by
    rw [←Real.rpow_sum_of_pos hp]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=>hw i))
  have hxy:X₁*X₂≤volume balancedSource:=by
    change X₁*X₂≤X₁*X₂*(∏i,Z^(w i))
    exact le_mul_of_one_le_right (mul_pos hX₁ hX₂).le hprod
  have hY:1≤comparisonFirst Z s.width:=Real.one_le_rpow hZ.le (div_nonneg s.width_nonneg (by norm_num))
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change Z^(s.width/4)≤Z^L
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [s.width_nonneg])
  · change X₁*X₂/comparisonFirst Z s.width≤Z^L
    exact (div_le_self (mul_pos hX₁ hX₂).le hY).trans (hxy.trans hv)


-- @@ L89-94 verbatim
theorem four_lower_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤min (length Z X₁) (length Z X₂)) :
    Z^(s.width/4)≤(balancedSource).X₁ ∧ Z^(s.width/4)≤(balancedSource).X₂ ∧
    Z^(s.width/4)≤(balancedSource).Y₁ ∧ Z^(s.width/4)≤(balancedSource).Y₂ := by
  have hh:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩


-- @@ L96-112 verbatim
theorem state_capacity_packet (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤L) :
    1≤s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧
    length Z (balancedSource).X₁+length Z (balancedSource).X₂+6*κ*(∑i,w i)≤s.width ∧
    Real.logb Z s.radial.scale+Real.logb Z ((balancedSource).η.modulus.absNorm:ℝ)≤s.width ∧
    volume balancedSource≤Z^s.width ∧ Real.logb Z (volume balancedSource)≤s.width ∧
    volume balancedSource≤Z^L ∧
    (s.puncture.absNorm:ℝ)≤Z^Bmask := by
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨hr.1,hr.2.1,rfl,rfl,hcap,actual_width_le s hZ,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl,
    balanced_log_volume M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ hZ hw hκ hcap,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs,s.puncture_bound⟩


-- @@ L114-114 verbatim
end SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission


-- @@ L116-116 verbatim
end


-- @@ L118-118 verbatim
end OAI
