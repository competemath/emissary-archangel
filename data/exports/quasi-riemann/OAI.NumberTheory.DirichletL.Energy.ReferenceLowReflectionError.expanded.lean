import OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflection
import OAI.NumberTheory.DirichletL.Energy.ReferenceLowError


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
open Filter


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentEnergyReferenceLowReflectionError

-- @@ L11-11 verbatim
open HeckeFamily HeckeDyadic ConcreteTraceCRT

-- @@ L12-12 verbatim
open CenteredMomentEnergyState CenteredMomentEnergyBands

-- @@ L13-13 verbatim
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState

-- @@ L14-14 verbatim
open CenteredMomentEnergyReferenceLowMoments CenteredMomentEnergyReferenceLowWindow

-- @@ L15-15 verbatim
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentNaturalRowSource

-- @@ L16-16 verbatim
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy

-- @@ L17-17 verbatim
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound

-- @@ L18-18 verbatim
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion

-- @@ L19-19 verbatim
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial

-- @@ L20-20 verbatim
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization

-- @@ L21-21 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L22-22 verbatim
variable {α:Type*}[Fintype α][DecidableEq α]

-- @@ L23-23 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L24-24 verbatim
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L25-25 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)


-- @@ L27-27 verbatim
open CenteredMomentEnergyReferenceLowReflection CenteredMomentEnergyReferenceLowError

-- @@ L28-95 verbatim
theorem reference_from_low_with_error
    (Fmax:Finset α)(Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask L Lslot Mcap ε κ:ℝ)
        (η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      0≤Bmask →
      ∀(F:Finset α),F⊆Fmax → ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(along bshort:ℝ),s.width≤Lreflect+along →
      max 0 (s.width-along+xi)≤L → bshort≤L →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+6*κ*(∑i∈F,w i)≤s.width →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+(∑i∈F,w i)≤5*s.width/6 →
      let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε);
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^bshort)*∏i∈F,Z^(w i) :=by
  obtain ⟨Cerr,hCerr,herr⟩:=relative_slot_error Fmax Wslot aslot bslot lo hi b haslot hsSlot hcSlot
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low (α:=α) M H hH
    a b bΦ epsilon xi saving Lreflect ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cerr,hC,mul_pos hD hCerr,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask
    F hF θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity hsmall
  dsimp only
  have hh:=hZ.2 Wslot bslot Bmask L Lslot lo hi Mcap ε κ η₀ Q K hK hlow hBmask
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity hsmall
  dsimp only at hh
  have he:=herr F hF Wshort (fun x hx=>(hsShort hx).2)
    (naturalCharacter s.character) (fun i=>relativeCharacter M H hH η₀ (θ i))
    (fun i=>primePool M H bslot (Z^(w i))) (fun i=>Z^(w i)) σ freq t
    (Z^bshort) s.radial.scale s.radial.profile (effectiveState s).radial.keep
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) s.radial.scale_pos
    (fun i _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
    (fun i _=>hσlo i) (fun i _=>hσhi i)
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1) s.radial.nonneg
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hcoeff:0≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
      (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving):=by positivity
  apply hh.trans
  apply add_le_add le_rfl
  convert mul_le_mul_of_nonneg_left he hcoeff using 1 ; ring


-- @@ L97-97 verbatim
end SevenEighths.CenteredMomentEnergyReferenceLowReflectionError


-- @@ L99-99 verbatim
end


-- @@ L101-101 verbatim
end OAI
