import OAI.NumberTheory.DirichletL.Energy.Bands
import OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentEnergySlotHeight

-- @@ L9-9 verbatim
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy

-- @@ L10-10 verbatim
open CenteredMomentHeckeSlots CenteredMomentCommonMaskEnergy

-- @@ L11-11 verbatim
open HeckePrimeAnnular CenteredMomentPrimeSlotShift

-- @@ L12-12 verbatim
local notation "O"=>HeckeFamily.O


-- @@ L14-14 verbatim
variable {α:Type*}[Fintype α]


-- @@ L16-27 verbatim
lemma height_coefficient (ν:Ideal O→ℂ)(W:ℝ→ℂ)(P σ freq t:ℝ)(hP:0<P)
    (I:Ideal O)(hI:I≠0):
    heightCoefficient (fun J=>ν J*annularWeight W P σ freq J) t I=
      (P:ℂ)^(Complex.I*t)*(ν I*annularWeight W P σ (t+freq) I):=by
  have hN:0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh:=norm_height_split (I.absNorm:ℝ) P σ t freq hN hP
  unfold heightCoefficient annularWeight
  calc
    _=(ν I*W ((I.absNorm:ℝ)/P))*
      (((((I.absNorm:ℝ)/P:ℝ):ℂ)^(-HeckeDyadic.shift σ freq))*(I.absNorm:ℂ)^(Complex.I*t)):=by ring
    _=_:=by rw [show (I.absNorm:ℂ)=((I.absNorm:ℝ):ℂ) by simp,hh];ring


-- @@ L29-37 verbatim
lemma row_slot_phase (η:Character)(m A z:O)(pool:Finset (Ideal O))
    (β γ:Ideal O→ℂ)(phase:ℂ)(t:ℝ)(he:∀I∈pool,β I=phase*γ I):
    rowSlot η m A z pool β t=phase*rowSlot η m A z pool γ t:=by
  unfold rowSlot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [he I hI]
  ring


-- @@ L39-50 verbatim
lemma positive_row_phase (η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(he:∀i I,I∈pool i→β i I=phase i*γ i I):
    positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      (∏i,phase i)*positiveSlotRow η m A z W₁ W₂ pool γ P t X₁ X₂:=by
  have hs (i:α):rowSlot η m A z (pool i) (β i) t=
      phase i*rowSlot η m A z (pool i) (γ i) t:=
    row_slot_phase η m A z (pool i) (β i) (γ i) (phase i) t (he i)
  unfold positiveSlotRow
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  ring


-- @@ L52-63 verbatim
theorem energy_phase (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (he:∀i I,I∈pool i→β i I=phase i*γ i I)(hp:∀i,‖phase i‖=1):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool γ P X₁ X₂ keep Φ K:=by
  have hprod:‖∏i,phase i‖=1:=by rw [norm_prod];simp only [hp,Finset.prod_const_one]
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row_phase η m A z W₁ W₂ pool β γ phase P t X₁ X₂ he]
  simp only [norm_mul,hprod,one_mul]


-- @@ L65-79 verbatim
theorem inherited_height_energy (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(ν:α→Ideal O→ℂ)(W:α→ℝ→ℂ)
    (P σ freq:α→ℝ)(hP:∀i,0<P i)(hpool:∀i I,I∈pool i→I≠0)
    (t rowt X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A rowt W₁ W₂ pool
      (fun i=>heightCoefficient (fun I=>ν i I*annularWeight (W i) (P i) (σ i) (freq i) I) t)
      P X₁ X₂ keep Φ K=
    energy η m A rowt W₁ W₂ pool
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+freq i) I)
      P X₁ X₂ keep Φ K:=by
  apply energy_phase η m A W₁ W₂ pool _ _ (fun i=>(P i:ℂ)^(Complex.I*t)) P rowt X₁ X₂ keep Φ K
  · intro i I hi
    exact height_coefficient (ν i) (W i) (P i) (σ i) (freq i) t (hP i) I (hpool i I hi)
  · intro i
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (hP i) (Complex.I*t)


-- @@ L81-81 verbatim
end SevenEighths.CenteredMomentEnergySlotHeight


-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end OAI
