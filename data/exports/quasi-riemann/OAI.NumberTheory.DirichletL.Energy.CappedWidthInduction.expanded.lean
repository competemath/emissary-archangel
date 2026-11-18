import OAI.NumberTheory.DirichletL.Energy.WidthInduction
import OAI.NumberTheory.DirichletL.Energy.WidthFloor
import OAI.NumberTheory.DirichletL.Energy.StageReserveSchedule
import OAI.NumberTheory.DirichletL.Energy.BandMonotonicity


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff

-- @@ L10-10 verbatim
open Filter


-- @@ L12-12 verbatim
namespace SevenEighths.CenteredMomentEnergyCappedWidthInduction

-- @@ L13-13 verbatim
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands

-- @@ L14-14 verbatim
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

-- @@ L15-15 verbatim
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity

-- @@ L16-16 verbatim
open CenteredMomentEnergyWidthFloor CenteredMomentFiniteProfileExceptional

-- @@ L17-17 verbatim
open CenteredMomentNaturalFixedRaySource

-- @@ L18-18 verbatim
local notation "O"=>HeckeFamily.O


-- @@ L20-20 verbatim
open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)


-- @@ L22-22 verbatim
def bandWidth (M B ε:ℝ)(k:ℕ):ℝ:=min M (width M B ε k)

-- @@ L23-23 verbatim
lemma bandWidth_le (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤M:=min_le_left _ _

-- @@ L24-24 verbatim
lemma bandWidth_le_schedule (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤width M B ε k:=min_le_right _ _

-- @@ L25-30 verbatim
lemma bandWidth_nonneg (M B ε:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε)(k:ℕ):
    0≤bandWidth M B ε k:=by
  have hr:0<reserve M B ε:=(bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.1
  have hs:0<amplification ε:=(bounds M B 0 ε hM hB (by norm_num) hε).1
  unfold bandWidth width
  positivity

-- @@ L31-35 verbatim
lemma bandWidth_terminal (M B ε:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε):
    bandWidth M B ε (count M ε)=M:=by
  have hh: M<width M B ε (count M ε):=
    (bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.2.2.2.2.2.1
  exact min_eq_left hh.le

-- @@ L36-42 verbatim
lemma actual_child_band (M B ε parent child:ℝ)(hε:0<ε)(k:ℕ)
    (hp:parent≤bandWidth M B ε (k+1))(hc:child≤parent-amplification ε/2):
    child≤bandWidth M B ε k:=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  apply le_min
  · have hh:=hp.trans (bandWidth_le M B ε (k+1));linarith
  · exact child_band M B ε parent child k (hp.trans (bandWidth_le_schedule M B ε (k+1))) hc


-- @@ L44-44 verbatim
variable {α:Type*}[Fintype α][DecidableEq α]

-- @@ L45-45 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L46-46 verbatim
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L47-47 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)


-- @@ L49-61 verbatim
def CertifiedBand (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)(k:ℕ):Prop:=
  ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
    internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k)
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z degree S Czero ∧
      PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi
        (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
        (stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q degree S Cpositive


-- @@ L63-91 verbatim
theorem certified_floor (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (ha:0<a)(hb:0≤b)(hrad:0<radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ0:0≤κ)(hε:0<ε)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε 0:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have ha0:=lowerAt_pos a b Mcap ε ha 0
  obtain ⟨degree,S,Czero,Cpositive,hCzero,hCpositive,hfloor⟩:=
    actual_joint_floor (α:=α) M H hH Mcap Bs κ ε hMcap hBs hκ0 hε W aslot bslot
      haslot hWs hW (lowerAt a b Mcap ε 0) b radial Bmask (lengthAt Mcap Bmask L ε 0)
      lo hi ha0 hb hrad hmask hbeta hκ
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM _ _ _
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hfloor η₀] with Z hZ
  have hh:=hZ.2 Q hQM
  have hloss:loss Mcap Bs ε 0≤stageLoss Mcap Bs ε 0:=by
    unfold stageLoss
    linarith
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      le_rfl (bandWidth_le_schedule Mcap Bs ε 0) hloss le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hh.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl (bandWidth_le_schedule Mcap Bs ε 0) hloss le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hh.2


-- @@ L93-129 verbatim
omit [Fintype α] [DecidableEq α] in
theorem certified_terminal (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ0:0≤κ)(hε:0<ε)
    (h:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε)):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z η₀ Q degree S Cpositive:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  obtain ⟨hs,hs1,hse,hr,hm,hmm,hκm,h20,hcover,hloss⟩:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have he:stageLoss Mcap Bs ε (count Mcap ε)≤ε:=by
    have hh:=stageLoss_final Mcap Bs κ ε hMcap hBs hκ0 hε (count Mcap ε) le_rfl
    linarith
  obtain ⟨degree,S,hbound⟩:=h
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero,Cpositive,hCzero,hCpositive,hcert⟩:=hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hcert] with Z hZ
  have hz:=hZ.2.1
  have hp:=hZ.2.2
  simp only [lowerAt,lengthAt,remaining,Nat.sub_self,CenteredMomentEnergyProfiles.lower,range] at hz hp
  have hterminal:=bandWidth_terminal Mcap Bs ε hMcap hBs hε
  change bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (count Mcap ε)=Mcap at hterminal
  rw [hterminal] at hz hp
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      (le_max_right _ _) le_rfl he le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hz
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl (le_max_right _ _) le_rfl he le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hp


-- @@ L131-131 verbatim
end SevenEighths.CenteredMomentEnergyCappedWidthInduction


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
end OAI
