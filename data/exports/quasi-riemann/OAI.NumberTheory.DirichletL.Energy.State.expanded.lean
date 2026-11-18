import OAI.NumberTheory.DirichletL.Moments.NaturalMaskedFloor
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentEnergyState

-- @@ L9-9 verbatim
open HeckeFamily CenteredMomentSecondHeightFamily CenteredExceptionalProfile

-- @@ L10-10 verbatim
open CenteredMomentRadialEligibleEnergy (Radial)

-- @@ L11-11 verbatim
open CenteredMomentFiniteProfileExceptional

-- @@ L12-12 verbatim
open CenteredMomentInductionEnergy QuadraticInitialBound

-- @@ L13-13 verbatim
local notation "O"=>HeckeFamily.O


-- @@ L15-33 verbatim
structure NaturalState (Z Bmask bΦ:ℝ) where
  character : Character
  fixedModulus : Ideal O
  puncture : Ideal O
  radial : Radial
  rowWidth : ℝ
  characterWidth : ℝ
  base_ge_one : 1≤Z
  row_nonneg : 0≤rowWidth
  character_nonneg : 0≤characterWidth
  scale_eq : radial.scale=Z^rowWidth
  modulus_bound : (character.modulus.absNorm:ℝ)≤Z^characterWidth
  puncture_ne_zero : puncture≠0
  puncture_bound : (puncture.absNorm:ℝ)≤Z^Bmask
  radial_support : Function.support (radial.profile:ℝ→ℂ)⊆Set.Iic bΦ
  row_ne_zero : ∀z,radial.keep z→z≠0
  nonexceptional : ∀z,radial.keep z→
    ¬FixedInducingRow character fixedModulus
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator puncture) 1 z


-- @@ L35-35 verbatim
namespace NaturalState

-- @@ L36-36 verbatim
variable {Z Bmask bΦ:ℝ}

-- @@ L37-37 verbatim
def width (s:NaturalState Z Bmask bΦ):ℝ := s.rowWidth+s.characterWidth

-- @@ L38-39 verbatim
lemma width_nonneg (s:NaturalState Z Bmask bΦ):0≤s.width :=
  add_nonneg s.row_nonneg s.character_nonneg


-- @@ L41-42 verbatim
def mask (s:NaturalState Z Bmask bΦ):O :=
  fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture


-- @@ L44-48 verbatim
def plainEnergy (s:NaturalState Z Bmask bΦ) {a b:ℝ} (p:Profiles a b)
    (t X₁ X₂:ℝ):ℝ :=
  energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
    X₁ X₂ s.radial.keep s.radial.profile s.radial.scale


-- @@ L50-54 verbatim
lemma plainEnergy_eq_zero (s:NaturalState Z Bmask bΦ) {a b:ℝ} (p:Profiles a b)
    (t X₁ X₂:ℝ):
    s.plainEnergy p t X₁ X₂=CenteredMomentCoreFloor.zeroEnergy s.character s.mask 1 t
      (p.profile 0) (p.profile 1) X₁ X₂ s.radial :=
  (CenteredMomentCoreFloor.zero_energy_eq _ _ _ _ _ _ _ _ _).symm


-- @@ L56-61 verbatim
lemma radical_bound (s:NaturalState Z Bmask bΦ):
    (s.puncture.radical.absNorm:ℝ)≤Z^Bmask :=by
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=s.puncture))))

-- @@ L62-62 verbatim
end NaturalState


-- @@ L64-69 verbatim
def ZeroBound (Q:Ideal O) (a b bΦ Bmask M ε:ℝ)(degree:ℕ)(S:Finset (ℕ×ℕ))(C Z₀:ℝ):Prop :=
  ∀Z:ℝ,Z₀≤Z→∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→
    s.plainEnergy p t X₁ X₂≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree*
        Z^(s.width+ε)


-- @@ L71-71 verbatim
end SevenEighths.CenteredMomentEnergyState


-- @@ L73-73 verbatim
end


-- @@ L75-75 verbatim
end OAI
