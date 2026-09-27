/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.Cost


-- @@ L10-12 verbatim
/-!
# Transport of language families, witnesses, and width along equivalences
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace GenLimit.FiniteWitness


-- @@ L18-18 verbatim
variable {α β : Type*}


-- @@ L20-22 verbatim
/-- Transport a language family along an equivalence of universes. -/
def transportClass (e : α ≃ β) (H : Set (Set α)) : Set (Set β) :=
  {K | e ⁻¹' K ∈ H}


-- @@ L24-26 verbatim
/-- Transport finite witnesses along an equivalence of universes. -/
noncomputable def transportAssignment (e : α ≃ β) (T : Set α → Finset α)
    (K : Set β) : Finset β := (T (e ⁻¹' K)).map e.toEmbedding


-- @@ L28-33 verbatim
@[simp] theorem transportClass_inverse (e : α ≃ β) (H : Set (Set α)) :
    transportClass e.symm (transportClass e H) = H := by
  ext L
  change (e ⁻¹' (e.symm ⁻¹' L) ∈ H) ↔ L ∈ H
  have he : e ⁻¹' (e.symm ⁻¹' L) = L := by ext x; simp
  rw [he]


-- @@ L35-58 verbatim
theorem Valid.transport {H : Set (Set α)} {T : Set α → Finset α}
    (hT : Valid H T) (e : α ≃ β) :
    Valid (transportClass e H) (transportAssignment e T) := by
  classical
  refine ⟨?_, ?_⟩
  · intro K hK x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hT.1 (e ⁻¹' K) hK hy
  · intro S hS
    let S' := S.map e.symm.toEmbedding
    have ha {K} (hK : K ∈ active (transportClass e H) (transportAssignment e T) S) :
        e ⁻¹' K ∈ active H T S' := by
      refine ⟨hK.1, ?_, ?_⟩
      · intro y hy
        have hes : e y ∈ S := hK.2.1 (Finset.mem_map.mpr ⟨y, hy, rfl⟩)
        exact Finset.mem_map.mpr ⟨e y, hes, e.symm_apply_apply y⟩
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
        change e (e.symm x) ∈ K
        simpa using hK.2.2 hx
    obtain ⟨K, hK⟩ := hS
    apply ((hT.2 S' ⟨e ⁻¹' K, ha hK⟩).image e.injective.injOn).mono
    rintro _ ⟨y, hy, rfl⟩ L hL
    exact hy (e ⁻¹' L) (ha hL)


-- @@ L60-66 verbatim
theorem HasBoundedWitnesses.transport {H : Set (Set α)} {d : ℕ}
    (h : HasBoundedWitnesses H d) (e : α ≃ β) :
    HasBoundedWitnesses (transportClass e H) d := by
  obtain ⟨T, hT, hb⟩ := h
  refine ⟨transportAssignment e T, hT.transport e, ?_⟩
  intro K hK
  simpa [transportAssignment] using hb (e ⁻¹' K) hK


-- @@ L68-73 verbatim
theorem bounded_transport_iff (e : α ≃ β) (H : Set (Set α)) (d : ℕ) :
    HasBoundedWitnesses (transportClass e H) d ↔ HasBoundedWitnesses H d := by
  constructor
  · intro h
    simpa using h.transport e.symm
  · exact fun h => h.transport e


-- @@ L75-79 verbatim
theorem finiteWitnesses_transport {H : Set (Set α)}
    (h : HasFiniteWitnesses H) (e : α ≃ β) :
    HasFiniteWitnesses (transportClass e H) := by
  obtain ⟨T, hT⟩ := h
  exact (Valid.transport hT e).hasFiniteWitnesses


-- @@ L81-86 verbatim
theorem finiteWitnesses_transport_iff (e : α ≃ β) (H : Set (Set α)) :
    HasFiniteWitnesses (transportClass e H) ↔ HasFiniteWitnesses H := by
  constructor
  · intro h
    simpa using finiteWitnesses_transport h e.symm
  · exact fun h => finiteWitnesses_transport h e


-- @@ L88-99 verbatim
theorem width_le_of_witness_imp {F : Set (Set α)} {G : Set (Set β)}
    (hb : ∀ d, HasBoundedWitnesses G d → HasBoundedWitnesses F d)
    (hf : HasFiniteWitnesses G → HasFiniteWitnesses F) :
    separationWidth F ≤ separationWidth G := by
  classical
  by_cases h : ∃ d, HasBoundedWitnesses G d
  · rw [show separationWidth G = finiteValue (Nat.find h) by simp [separationWidth, h]]
    exact (width_le_finite_iff F _).mpr (hb _ (Nat.find_spec h))
  · by_cases hw : HasFiniteWitnesses G
    · rw [show separationWidth G = omegaValue by simp [separationWidth, h, hw]]
      exact (width_le_omega_iff F).mpr (hf hw)
    · simp [separationWidth, h, hw]


-- @@ L101-106 verbatim
theorem width_eq_of_thresholds {H : Set (Set α)} {K : Set (Set β)}
    (hb : ∀ d, HasBoundedWitnesses H d ↔ HasBoundedWitnesses K d)
    (hf : HasFiniteWitnesses H ↔ HasFiniteWitnesses K) :
    separationWidth H = separationWidth K := by
  exact le_antisymm (width_le_of_witness_imp (fun d => (hb d).mpr) hf.mpr)
    (width_le_of_witness_imp (fun d => (hb d).mp) hf.mp)


-- @@ L108-110 verbatim
theorem width_transport (e : α ≃ β) (H : Set (Set α)) :
    separationWidth (transportClass e H) = separationWidth H :=
  width_eq_of_thresholds (bounded_transport_iff e H) (finiteWitnesses_transport_iff e H)


-- @@ L112-117 verbatim
theorem uus_transport {H : Set (Set α)} (hH : Generic.UUS H) (e : α ≃ β) :
    Generic.UUS (transportClass e H) := by
  intro K hK
  apply ((hH _ hK).image e.injective.injOn).mono
  rintro _ ⟨y, hy, rfl⟩
  exact hy


-- @@ L119-119 verbatim
end GenLimit.FiniteWitness
