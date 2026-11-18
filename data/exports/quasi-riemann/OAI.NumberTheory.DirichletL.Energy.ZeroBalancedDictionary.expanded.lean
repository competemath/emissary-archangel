import OAI.NumberTheory.DirichletL.Energy.ZeroReferencePhysical
import OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters
import OAI.NumberTheory.DirichletL.Moments.FirstAnnularInput


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentEnergyZeroBalancedDictionary

-- @@ L11-11 verbatim
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound

-- @@ L12-12 verbatim
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy

-- @@ L13-13 verbatim
open CenteredMomentEnergyReferenceState CenteredMomentFiniteProfileExceptional

-- @@ L14-14 verbatim
open CenteredMomentCommonRadialData CenteredMomentSourceRow

-- @@ L15-15 verbatim
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyNaturalInputMatches

-- @@ L16-16 verbatim
open CenteredMomentAmplificationChildInput CenteredMomentFirstSourceReduction

-- @@ L17-17 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L18-18 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L19-19 verbatim
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L20-20 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

-- @@ L21-21 verbatim
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)

-- @@ L22-22 verbatim
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

-- @@ L23-23 verbatim
local notation "zeroInput"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂


-- @@ L25-28 verbatim
theorem balanced_matches (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)
    (w σ freq:Fin 0→ℝ)(W:ℝ→ℂ)(bslot:ℝ):
    CenteredMomentAllocatedRayDictionary.Matches M H hH zeroInput η₀ θ w σ freq W bslot Z:=by
  constructor <;> intro i <;> exact Fin.elim0 i


-- @@ L30-38 verbatim
theorem balanced_eq_positive_empty (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)
    (w σ freq:Fin 0→ℝ):
    zeroInput=CenteredMomentEnergyPositiveHighSource.balancedInput M H hH η₀ θ
      (fun _=>0) continuous_const 1 1 0 0 (by norm_num)
      (by simp [Function.support]) w σ freq (fun i=>Fin.elim0 i)
      s p ha t X₁ X₂ hX₁ hX₂:=by
  unfold CenteredMomentEnergyZeroReferencePhysical.balancedInput
    CenteredMomentEnergyPositiveHighSource.balancedInput input naturalInput naturalData completeInput
  congr 5 <;> exact Subsingleton.elim _ _


-- @@ L40-40 verbatim
variable (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)(w σ freq:Fin 0→ℝ)

-- @@ L41-45 verbatim
def positiveEmptyInput : Input (Fin 0):=
  CenteredMomentEnergyPositiveHighSource.balancedInput M H hH η₀ θ
  (fun _=>0) continuous_const 1 1 0 0 (by norm_num)
  (by simp [Function.support]) w σ freq (fun i=>Fin.elim0 i)
  s p ha t X₁ X₂ hX₁ hX₂


-- @@ L47-47 verbatim
local notation "positiveInput"=>positiveEmptyInput M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq


-- @@ L49-50 verbatim
lemma balanced_pools_eq : (zeroInput).pools=(positiveInput).pools:=
  congrArg Input.pools (balanced_eq_positive_empty M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq)


-- @@ L52-55 verbatim
lemma balanced_normalized_gauss_eq (R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ):
    normalizedGaussSource zeroInput R seed W K=normalizedGaussSource positiveInput R seed W K:=
  congrArg (fun inp=>normalizedGaussSource inp R seed W K)
    (balanced_eq_positive_empty M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq)


-- @@ L57-60 verbatim
lemma balanced_physical_mass_eq (R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z₀ ξ:ℝ):
    physicalMass zeroInput R seed m A Φ K Z₀ ξ=physicalMass positiveInput R seed m A Φ K Z₀ ξ:=
  congrArg (fun inp=>physicalMass inp R seed m A Φ K Z₀ ξ)
    (balanced_eq_positive_empty M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq)


-- @@ L62-67 verbatim
lemma balanced_current_source :
    (zeroInput).η=s.character ∧ (zeroInput).m=s.mask ∧ (zeroInput).t=t ∧
    (zeroInput).X₁=X₁ ∧ (zeroInput).X₂=X₂ ∧
    (zeroInput).Y₁=comparisonFirst Z s.width ∧
    (zeroInput).Y₂=comparisonSecond Z s.width X₁ X₂:=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


-- @@ L69-85 verbatim
theorem declared_capacity (hZ:1<Z):
    let Mdecl:=max s.width (length Z X₁+length Z X₂);
    Real.logb Z (volume zeroInput)≤Mdecl ∧
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.width ∧
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width ∧
    volume zeroInput≤Z^Mdecl:=by
  have hlog (X:ℝ)(hX:0<X):Real.logb Z X≤length Z X:=by
    rw [CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX]
    exact le_max_right _ _
  have hV:Real.logb Z (volume zeroInput)≤length Z X₁+length Z X₂:=by
    rw [CenteredMomentEnergyZeroReferencePhysical.balanced_volume,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact add_le_add (hlog X₁ hX₁) (hlog X₂ hX₂)
  have hdecl:=hV.trans (le_max_right s.width (length Z X₁+length Z X₂))
  refine ⟨hdecl,CenteredMomentEnergyPositiveHighParameters.actual_width_le s hZ,
    CenteredMomentEnergyPositiveHighParameters.actual_conductor_scale s hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos zeroInput)).mp hdecl


-- @@ L87-93 verbatim
theorem balanced_four_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤min (length Z X₁) (length Z X₂)):
    Z^(s.width/4)≤(zeroInput).X₁ ∧ Z^(s.width/4)≤(zeroInput).X₂ ∧
    Z^(s.width/4)≤(zeroInput).Y₁ ∧ Z^(s.width/4)≤(zeroInput).Y₂:=by
  have h:=CenteredMomentEnergyOriginalHighReflectionSymmetric.balanced_four_scale_gates
    Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩


-- @@ L95-102 verbatim
lemma declared_capacity_upper (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal):
    max s.width (length Z X₁+length Z X₂)≤max Mcap (2*Lgoal):=by
  have hlen (X:ℝ)(hcap:X≤Z^Lgoal):length Z X≤Lgoal:=by
    unfold length
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mpr
      (max_le (Real.one_le_rpow hZ.le hL) hcap)
  exact max_le_max hs (by linarith [hlen X₁ hc₁,hlen X₂ hc₂])


-- @@ L104-104 verbatim
end SevenEighths.CenteredMomentEnergyZeroBalancedDictionary


-- @@ L106-106 verbatim
end


-- @@ L108-108 verbatim
end OAI
