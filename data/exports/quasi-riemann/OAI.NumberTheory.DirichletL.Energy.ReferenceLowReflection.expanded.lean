import OAI.NumberTheory.DirichletL.Energy.ReferenceLowMoments
import OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
import OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneous


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L9-9 verbatim
open Filter


-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentEnergyReferenceLowReflection

-- @@ L12-12 verbatim
open HeckeFamily HeckeDyadic ConcreteTraceCRT

-- @@ L13-13 verbatim
open CenteredMomentEnergyState CenteredMomentEnergyBands

-- @@ L14-14 verbatim
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState

-- @@ L15-15 verbatim
open CenteredMomentEnergyReferenceLowMoments CenteredMomentEnergyReferenceLowWindow

-- @@ L16-16 verbatim
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentNaturalRowSource

-- @@ L17-17 verbatim
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy

-- @@ L18-18 verbatim
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound

-- @@ L19-19 verbatim
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion

-- @@ L20-20 verbatim
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial

-- @@ L21-21 verbatim
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization

-- @@ L22-22 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L23-23 verbatim
variable {α:Type*}[Fintype α][DecidableEq α]

-- @@ L24-24 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L25-25 verbatim
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L26-26 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)


-- @@ L28-92 verbatim
theorem reference_from_low
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Wslot:ℝ→ℂ)(bslot Bmask L Lslot lo hi Mcap ε κ:ℝ)
        (η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      0≤Bmask →
      ∀(F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
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
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=reflected_child_uniform_from_low (α:=α) M H hH a b ha hlo hhi degree S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Wslot bslot Bmask L Lslot lo hi Mcap ε κ η₀ Q K hK hlow hBmask
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity hsmall
  dsimp only
  apply hZ.2 Bmask s Wlong Wshort hsLong hsShort α F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t)
    (fun i=>Z^(w i)) t along bshort _ hlength
  · have hz:0<Z:=zero_lt_one.trans hZ.1
    have hd:0≤diagonalControl s.radial.profile:=by unfold diagonalControl; positivity
    positivity
  · intro v j k x hx
    have hwindow:=reflection_window_length Z (max 0 (s.width-along+xi)) x hZ.1 (le_max_left _ _) hx
    exact hchild Wslot bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q K hK hlow hBmask
      F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs Wshort hsShort
      j k v (Real.exp x) (Z^bshort) (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
      (hwindow.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hL))
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hbshort)
      (by linarith [hwindow.1]) (by linarith [hwindow.1])


-- @@ L94-94 verbatim
end SevenEighths.CenteredMomentEnergyReferenceLowReflection


-- @@ L96-96 verbatim
end


-- @@ L98-98 verbatim
end OAI
