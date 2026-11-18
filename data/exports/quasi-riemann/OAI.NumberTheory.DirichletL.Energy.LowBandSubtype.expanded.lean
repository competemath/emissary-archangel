import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
import OAI.NumberTheory.DirichletL.Energy.Reindex


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentEnergyLowBandSubtype

-- @@ L10-10 verbatim
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentEnergyReferenceLowBands

-- @@ L11-11 verbatim
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy

-- @@ L12-12 verbatim
open CenteredMomentPrimeSlot CenteredMomentEnergyReindex

-- @@ L13-13 verbatim
local notation "O" => HeckeFamily.O

-- @@ L14-14 verbatim
variable {α β : Type*} [Fintype α] [Fintype β]

-- @@ L15-15 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L16-16 verbatim
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L17-17 verbatim
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


-- @@ L19-56 verbatim
omit [Fintype α] [Fintype β] in
theorem positiveLowAt_embedding (e : β↪α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=β) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C := by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
  let E : T≃T.map e := Finset.equivMap e T
  let θ' : T.map e→RayQuotient.Characters M H := θ∘E.symm
  let w' : T.map e→ℝ := w∘E.symm
  let σ' : T.map e→ℝ := σ∘E.symm
  let v' : T.map e→ℝ := v∘E.symm
  have hsum : (∑i:T.map e,w' i)=∑i:T,w i := E.symm.sum_comp w
  have hh := h (T.map e) θ' w' σ' v' t height
    (fun i=>hw (E.symm i)) (fun i=>hwL (E.symm i))
    (fun i=>hσlo (E.symm i)) (fun i=>hσhi (E.symm i))
    hheight (fun i=>hv (E.symm i)) s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
    (by rw [hsum];exact hcapacity) (by rw [hsum];exact hlow)
  have he := energy_reindex E s.character s.mask 1 (p.profile 0) (p.profile 1)
    (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
    (fun (i:T.map e) I=>idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
    (fun i:T.map e=>Z^(w' i)) t X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have he' : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>primePool M H bslot (Z^(w i)))
      (fun (i:T) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:T=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
      (fun (i:T.map e) I=>idealCoeff (relativeCharacter M H hH η₀ (θ' i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
      (fun i:T.map e=>Z^(w' i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
    simpa only [Function.comp_def,θ',w',σ',v',Equiv.symm_apply_apply] using he
  exact he'.le.trans hh


-- @@ L58-67 verbatim
omit [Fintype α] in
theorem positiveLowAt_subtype (T : Finset α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=T) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C :=
  positiveLowAt_embedding M H hH ⟨Subtype.val,Subtype.val_injective⟩ W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε κ Z η₀ Q degree S C h


-- @@ L69-69 verbatim
end SevenEighths.CenteredMomentEnergyLowBandSubtype


-- @@ L71-71 verbatim
end


-- @@ L73-73 verbatim
end OAI
