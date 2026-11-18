import OAI.NumberTheory.DirichletL.Energy.PositiveHighSource
import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentEnergyPositiveHighParameters

-- @@ L10-10 verbatim
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound

-- @@ L11-11 verbatim
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy

-- @@ L12-12 verbatim
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands

-- @@ L13-13 verbatim
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource

-- @@ L14-14 verbatim
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl

-- @@ L15-15 verbatim
open CenteredMomentEnergyOriginalHighReflectionSymmetric

-- @@ L16-16 verbatim
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry

-- @@ L17-17 verbatim
open CenteredMomentCommonRadialData CenteredMomentSourceRow

-- @@ L18-18 verbatim
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform

-- @@ L19-19 verbatim
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily

-- @@ L20-20 verbatim
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass

-- @@ L21-21 verbatim
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot

-- @@ L22-22 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L23-23 verbatim
variable {α:Type*}[Fintype α][DecidableEq α]

-- @@ L24-24 verbatim
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _

-- @@ L25-25 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L26-26 verbatim
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L27-27 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

-- @@ L28-28 verbatim
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)

-- @@ L29-29 verbatim
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)

-- @@ L30-30 verbatim
variable (hWs:Function.support W⊆Set.Icc aslot bslot)

-- @@ L31-31 verbatim
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)

-- @@ L32-32 verbatim
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)

-- @@ L33-33 verbatim
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)


-- @@ L35-36 verbatim
local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂


-- @@ L38-45 verbatim
lemma actual_width_le (hZ:1<Z):
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.width:=by
  have hn:0<(s.character.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.character.modulus_ne_bot)
  have hc:Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.characterWidth:=
    (Real.logb_le_iff_le_rpow hZ hn).mpr s.modulus_bound
  rw [s.scale_eq,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  exact add_le_add_right hc _


-- @@ L47-50 verbatim
lemma actual_conductor_scale (hZ:1<Z):
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width:=by
  rw [s.scale_eq,NaturalState.width,Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left s.modulus_bound (Real.rpow_nonneg (by linarith) _)


-- @@ L52-61 verbatim
omit [DecidableEq α] in
lemma balanced_log_volume (κ:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width):
    Real.logb Z (CenteredMomentAmplificationChildInput.volume balancedSource)≤s.width:=by
  have hv:0<CenteredMomentAmplificationChildInput.volume balancedSource:=by
    rw [balanced_volume]
    exact mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (by linarith) _))
  exact (Real.logb_le_iff_le_rpow hZ hv).mpr
    (balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl)


-- @@ L63-73 verbatim
omit [DecidableEq α] in
lemma balanced_actual_four_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤min (length Z X₁) (length Z X₂)):
    let M0:=Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ);
    Z^(M0/4)≤(balancedSource).X₁ ∧ Z^(M0/4)≤(balancedSource).X₂ ∧
    Z^(M0/4)≤(balancedSource).Y₁ ∧ Z^(M0/4)≤(balancedSource).Y₂:=by
  have hf:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  have hm:=actual_width_le s hZ
  have hp:Z^((Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ))/4)≤
      Z^(s.width/4):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  exact ⟨hp.trans hf.1,hp.trans hf.2.1,hp.trans hf.2.2.1,hp.trans hf.2.2.2.1⟩


-- @@ L75-82 verbatim
omit [DecidableEq α] in
lemma balanced_control (N:ℕ)(hN:Fintype.card α≤N)(S:Finset (ℕ×ℕ)):
    (plainControl balancedSource (p.profile 0) (p.profile 1))^2≤
      (CenteredMomentEnergyNaturalInputMatches.profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2:=by
  apply plain_control_sq_le balancedSource p S N _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    hN (fun _=>le_rfl)


-- @@ L84-98 verbatim
omit [DecidableEq α] in
lemma balanced_source_cost (N:ℕ)(hN:Fintype.card α≤N)(hZ:1<Z):
    CenteredMomentFirstReferenceEnergy.sourceFactor balancedSource a a s.radial.scale≤
      (Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a))*Z^s.width:=by
  have hK:0<s.radial.scale:=by rw [s.scale_eq]; positivity
  have hc:=source_factor_le balancedSource N aslot a s.radial.scale haslot ha hK hN (fun _=>le_rfl)
  have hconst:0≤Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a):=by
    have hp:=CenteredMomentFirstPhysicalSource.fixedPresentationCost_pos
    positivity
  have he:(balancedSource).η=s.character:=rfl
  rw [he] at hc
  apply hc.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (actual_conductor_scale s hZ) hconst


-- @@ L100-100 verbatim
end SevenEighths.CenteredMomentEnergyPositiveHighParameters


-- @@ L102-102 verbatim
end


-- @@ L104-104 verbatim
end OAI
