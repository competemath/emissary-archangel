import OAI.NumberTheory.DirichletL.Energy.ReferenceLowEmpty


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentEnergyLowBandEmpty

-- @@ L9-9 verbatim
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands

-- @@ L10-10 verbatim
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource

-- @@ L11-11 verbatim
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy

-- @@ L12-12 verbatim
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound

-- @@ L13-13 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L14-14 verbatim
variable {α:Type*}[Fintype α][DecidableEq α]

-- @@ L15-15 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L16-16 verbatim
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L17-17 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)


-- @@ L19-48 verbatim
omit [Fintype α] [DecidableEq α] in
theorem positive_low_zero
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C):
    ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  let T:Finset α:=∅
  let θ:T→RayQuotient.Characters M H:=fun i=>False.elim (Finset.notMem_empty _ i.property)
  let w:T→ℝ:=fun _=>0
  have hcap:length Z X₁+length Z X₂+6*κ*(∑i:T,w i)≤s.width:=by
    simp only [T,w,Finset.sum_const_zero,mul_zero,add_zero]
    linarith [s.width_nonneg]
  have hl:length Z X₁+length Z X₂+(∑i:T,w i)≤5*s.width/6:=by
    simpa only [w,Finset.sum_const_zero,add_zero] using hsmall
  have hh:=h T θ w w w t 0 (fun _=>le_rfl)
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property)) le_rfl
    (fun _=>by simp [w]) s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hl
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (w i) (w i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [T,energy,positiveSlotRow,NaturalState.plainEnergy,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid] at hh
  simpa only [add_zero,Real.norm_eq_abs] using hh


-- @@ L50-50 verbatim
end SevenEighths.CenteredMomentEnergyLowBandEmpty


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
end OAI
