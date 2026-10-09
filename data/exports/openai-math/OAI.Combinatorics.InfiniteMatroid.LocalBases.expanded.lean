import OAI.Combinatorics.InfiniteMatroid.SparsePerturbation
import OAI.Combinatorics.InfiniteMatroid.Interpolation


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
section


-- @@ L8-8 verbatim
open Set Filter

-- @@ L9-9 verbatim
open scoped Topology symmDiff


-- @@ L11-11 verbatim
namespace InfiniteMatroidCounterexample


-- @@ L13-15 verbatim
instance d_infinite : Infinite D :=
  Infinite.of_injective (fun m : ℕ ↦ (⟨m, fun _ ↦ false⟩ : D))
    (fun _ _ h ↦ congrArg Sigma.fst h)


-- @@ L17-17 verbatim
instance e0_infinite : Infinite E0 := inferInstance

-- @@ L18-18 verbatim
instance d_countable : Countable D := inferInstance

-- @@ L19-19 verbatim
instance e0_countable : Countable E0 := inferInstance


-- @@ L21-23 verbatim
noncomputable def labelEquiv : E0 ≃ ℕ := by
  letI := Classical.choice (nonempty_denumerable E0)
  exact Denumerable.eqv E0


-- @@ L25-26 verbatim
noncomputable def natProbe (T : Set E0) (n : ℕ) (A : Set ℕ) : ℝ :=
  fProbe T n (labelEquiv ⁻¹' A)


-- @@ L28-48 verbatim
lemma natProbe_cylinder {T I Y : Set E0} (hI : SameClass T I) (hY : SameClass T Y) :
    CylinderContinuous (natProbe T) (labelEquiv.symm ⁻¹' I) (labelEquiv.symm ⁻¹' Y) := by
  classical
  intro j ε hε
  obtain ⟨N, _, hN⟩ := fProbe_block_continuity hI hY j hε
  refine ⟨(blockPrefix N).sup labelEquiv + 1, ?_⟩
  intro X Z hIX hXY hIZ hZY hagree n hnj
  apply hN (labelEquiv ⁻¹' X) (labelEquiv ⁻¹' Z)
  · intro x hx
    exact hIX (by simpa using hx)
  · intro x hx
    simpa using hXY hx
  · intro x hx
    exact hIZ (by simpa using hx)
  · intro x hx
    simpa using hZY hx
  · intro x hx
    apply hagree (labelEquiv x)
    have hle := Finset.le_sup (f := labelEquiv) ((mem_prefix x N).mpr hx)
    omega
  · exact hnj.le


-- @@ L50-62 verbatim
lemma natProbe_shift (T : Set E0) (I Y : Set ℕ) :
    IntervalFiniteShift (natProbe T) I Y := by
  intro A B _ hAB _ hfin
  have hf : (labelEquiv ⁻¹' B \ labelEquiv ⁻¹' A).Finite := by
    rw [← Set.preimage_sdiff]
    exact Set.Finite.preimage labelEquiv.injective.injOn hfin
  have he := finite_change_eventually (T := T) (Set.preimage_mono hAB) hf
  have hc : (labelEquiv ⁻¹' B \ labelEquiv ⁻¹' A).ncard = (B \ A).ncard := by
    rw [← Set.preimage_sdiff]
    exact Set.ncard_preimage_of_injective_subset_range labelEquiv.injective
      (by rw [labelEquiv.surjective.range_eq]; exact subset_univ _)
  rw [hc] at he
  simpa only [probeLiminf, natProbe, EReal.coe_natCast] using probeLiminf_finite_change he


-- @@ L64-95 verbatim
lemma fProbe_interpolation {T I Y : Set E0} (hI : SameClass T I) (hY : SameClass T Y)
    (hIY : I ⊆ Y) (hlow : probeLiminf (fProbe T) I ≤ -1)
    (hhigh : 0 < probeLiminf (fProbe T) Y) :
    ∃ B, I ⊆ B ∧ B ⊆ Y ∧ SameClass T B ∧ LowerBasis (fProbe T) B := by
  have hpre (X : Set E0) : labelEquiv ⁻¹' (labelEquiv.symm ⁻¹' X) = X := by
    ext x
    simp
  have hlim (X : Set E0) : probeLiminf (natProbe T) (labelEquiv.symm ⁻¹' X) =
      probeLiminf (fProbe T) X := by
    simp only [probeLiminf, natProbe, hpre]
  obtain ⟨B, hIB, hBY, hB⟩ := local_interpolation (Set.preimage_mono (f := labelEquiv.symm) hIY)
    (natProbe_cylinder hI hY)
    (fun n A B _ hAB _ ↦ fProbe_mono T (Set.preimage_mono hAB) n)
    (fun n A B _ _ _ h ↦ by
      obtain ⟨e, he⟩ := h
      calc
        natProbe T n B ≤ fProbe T n (insert (labelEquiv.symm e) (labelEquiv ⁻¹' A)) := by
          apply fProbe_mono
          intro x hx
          rcases he hx with heq | hxA
          · left
            exact labelEquiv.injective (by simpa using heq)
          · exact Or.inr hxA
        _ ≤ natProbe T n A + 1 := fProbe_insert_le _ _ _ _)
    (natProbe_shift T _ _) (by rw [hlim]; exact hlow) (by rw [hlim]; exact hhigh)
  have hi : I ⊆ labelEquiv ⁻¹' B := by
    intro x hx
    exact hIB (by simpa using hx)
  have hy : labelEquiv ⁻¹' B ⊆ Y := by
    intro x hx
    simpa using hBY hx
  exact ⟨labelEquiv ⁻¹' B, hi, hy, sameClass_interval hI hY hi hy, hB⟩


-- @@ L97-98 verbatim
def LocalLower (T : Set E0) : Set (Set E0) :=
  {X | SameClass T X ∧ LowerBasis (fProbe T) X}


-- @@ L100-120 verbatim
lemma localLower_antichain (T : Set E0) :
    ∀ ⦃X Y⦄, X ∈ LocalLower T → Y ∈ LocalLower T → X ⊆ Y → X = Y := by
  intro X Y hX hY hXY
  by_contra hne
  obtain ⟨e, heY, heX⟩ := Set.not_subset.mp (fun hYX ↦ hne (Subset.antisymm hXY hYX))
  have hs : probeLiminf (fProbe T) (insert e X) = probeLiminf (fProbe T) X + 1 := by
    have heq : insert e X \ X = {e} := by ext x; simp [heX]
    have he := finite_change_eventually (T := T) (subset_insert e X)
      (show (insert e X \ X).Finite by rw [heq]; exact finite_singleton e)
    simp only [heq, ncard_singleton, Nat.cast_one] at he
    simpa using probeLiminf_finite_change he
  have hm := probeLiminf_mono (fun n ↦ fProbe_mono T (Set.insert_subset heY hXY) n)
  rw [hs] at hm
  have : (0 : EReal) < probeLiminf (fProbe T) X + 1 := by
    have hh := EReal.add_lt_add_right_coe hX.2.1 1
    have hz : (-1 : EReal) + 1 = 0 := by
      change ((-1 : ℝ) : EReal) + ((1 : ℝ) : EReal) = 0
      rw [← EReal.coe_add]
      norm_num
    simpa only [EReal.coe_one, hz] using hh
  exact (this.trans_le hm).not_ge hY.2.2


-- @@ L122-122 verbatim
end InfiniteMatroidCounterexample

-- @@ L123-123 verbatim
end


-- @@ L125-125 verbatim
end OAI
