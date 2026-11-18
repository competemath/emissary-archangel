import OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseMoment

-- @@ L6-6 verbatim
open scoped BigOperators Classical

-- @@ L7-7 verbatim
open InverseSecondFibers

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L10-11 verbatim
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]


-- @@ L13-15 verbatim
theorem actualSecondChild_outer_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).1 = (actualSecondChild p 1 1 x).1 := rfl


-- @@ L17-19 verbatim
theorem actualSecondChild_label_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).2.1 = (actualSecondChild p 1 1 x).2.1 := rfl


-- @@ L21-23 verbatim
theorem actualSecondTriples_units {Jo Jn : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn)) :
    actualSecondTriples p u v source = actualSecondTriples p 1 1 source := rfl


-- @@ L25-33 verbatim
theorem assigned_second_triples_subset {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂) ⊆
      actualSecondTriples p 1 1 source := by
  intro γ hγ
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
  exact Finset.mem_image.mpr ⟨y,hy,rfl⟩


-- @@ L35-42 verbatim
theorem assigned_second_mass_le_original {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (K : ℕ) :
    (∑ γ∈actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),tripleDivisorWeight K γ) ≤
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (assigned_second_triples_subset p u v source J₁ J₂ L₁ L₂)
    (fun γ _ _ => tripleDivisorWeight_nonneg K γ)


-- @@ L44-44 verbatim
end

-- @@ L45-45 verbatim
end SevenEighths.InverseMoment


-- @@ L47-47 verbatim
end OAI
