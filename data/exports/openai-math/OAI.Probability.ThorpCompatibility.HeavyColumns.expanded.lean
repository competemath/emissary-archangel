import Mathlib
import OAI.Probability.ThorpCompatibility.HeavyEntries
import OAI.Probability.ThorpCompatibility.UniformSupport


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace ThorpCompatibility

-- @@ L9-9 verbatim
open Finset

-- @@ L10-11 verbatim
noncomputable def remainingValues {A : ℕ} (σ : Equiv.Perm (Fin A)) (i : Fin A) : Finset (Fin A) :=
  (Finset.Ici i).map σ.toEmbedding


-- @@ L13-14 verbatim
lemma card_remainingValues {A : ℕ} (σ : Equiv.Perm (Fin A)) (i : Fin A) :
    (remainingValues σ i).card = A - (i : ℕ) := by simp [remainingValues]


-- @@ L16-23 verbatim
lemma mem_remainingValues {A : ℕ} (σ : Equiv.Perm (Fin A)) (i w : Fin A) :
    w ∈ remainingValues σ i ↔ i ≤ σ.symm w := by
  simp only [remainingValues, Finset.mem_map, Finset.mem_Ici, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨h, hi, hw⟩
    rwa [← hw, σ.symm_apply_apply]
  · intro h
    exact ⟨σ.symm w, h, σ.apply_symm_apply w⟩


-- @@ L25-29 verbatim
lemma remainingValues_nonempty {A : ℕ} (σ : Equiv.Perm (Fin A)) (i : Fin A) :
    (remainingValues σ i).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_remainingValues]
  exact Nat.sub_pos_of_lt i.isLt


-- @@ L31-41 verbatim
lemma columnPrediction_unused {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) (i : Fin A)
    (a : Grid A D) (hQa : 0 < Q.mass a) (w : Fin A) (hw : w ∉ remainingValues (a.2 k) i) :
    (columnPrediction Q k i (colHistory k i a)).mass w = 0 := by
  apply Q.predict_mass_zero _ _ (Q.map_mass_pos _ hQa)
  intro b _ hprev hvalue
  have hlt : (a.2 k).symm w < i := lt_of_not_ge (by simpa [mem_remainingValues] using hw)
  have he := (Law.history_eq_iff _ _ b a).mp hprev ((a.2 k).symm w) hlt
  change b.2 k ((a.2 k).symm w) = a.2 k ((a.2 k).symm w) at he
  rw [(a.2 k).apply_symm_apply] at he
  have hi : (a.2 k).symm w = i := (b.2 k).injective (he.trans hvalue.symm)
  exact (ne_of_lt hlt) hi


-- @@ L43-52 verbatim
lemma entry_heavy_mass_bound {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) (i : Fin A)
    (a : Grid A D) (hQa : 0 < Q.mass a) {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * entryHeavyMass Q H k i a ≤
      Real.log ((A - (i : ℕ) : ℕ) : ℝ) -
        (columnPrediction Q k i (colHistory k i a)).entropy := by
  have h := (columnPrediction Q k i (colHistory k i a)).heavy_mass_uniformOn
    (remainingValues (a.2 k) i) (remainingValues_nonempty (a.2 k) i)
    (fun w hw => columnPrediction_unused Q k i a hQa w hw) hH
  rw [card_remainingValues] at h
  simpa only [entryHeavyMass, columnLight, not_le] using h


-- @@ L54-63 verbatim
lemma mean_entry_heavy_bound {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) (i : Fin A)
    {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * Q.mean (entryHeavyMass Q H k i) ≤
      Real.log ((A - (i : ℕ) : ℕ) : ℝ) -
        Q.condEntropy (fun a => a.2 k i) (colHistory k i) := by
  have h := Q.mean_mono_support (fun a ha => entry_heavy_mass_bound Q k i a ha hH)
  rw [Law.mean_const_mul, Law.mean_sub, Law.mean_const] at h
  change _ ≤ _ - Q.mean (fun a => (Q.predict (fun b => b.2 k i)
    (colHistory k i) (colHistory k i a)).entropy) at h
  rwa [Q.mean_prediction_entropy] at h


-- @@ L65-73 verbatim
lemma column_heavy_bound {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D)
    {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * (∑ i : Fin A, Q.mean (entryHeavyMass Q H k i)) ≤
      (Q.map (fun a => a.2 k)).uniformDeficit := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin A))) =>
    mean_entry_heavy_bound Q k i hH)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_log_sub, grid_base_chain] at h
  simpa only [Law.uniformDeficit, Law.entropy, Law.mean, Fintype.card_perm,
    Fintype.card_fin, sub_neg_eq_add] using h


-- @@ L75-75 verbatim
end ThorpCompatibility


-- @@ L77-77 verbatim
end OAI
