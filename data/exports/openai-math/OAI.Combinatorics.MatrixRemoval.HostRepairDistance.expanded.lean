import OAI.Combinatorics.MatrixRemoval.HostSampledSelection
import OAI.Combinatorics.MatrixRemoval.HostSamplingCompatibility


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-14 verbatim
/-!
# Arbitrary-repair lower bound for the actual canonical host

The concrete common-leaf selection satisfies both independent certificates:
its guarded path is valid, and its chosen coordinates bound each guard cell's
sampling multiplicity.
Together these prove the integer repair lower bound. No assumption
about preservation of arbitrary variable-variable cells is made.
-/


-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
namespace Problem348.Construction.SampledSelection


-- @@ L19-19 verbatim
open HostSampledPath HostSampling TreeSampling


-- @@ L21-33 verbatim
/-- The actual constant-offset anchor frame is chosen by its row/column seeds. -/
theorem frame_chosen {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (s : Seeds (2 ^ h)) (t : Mode h) :
    FrameChosen er ec s (frame er ec ha t s.2.1 s.2.2) := by
  constructor
  · intro u
    simp [frame, SelectedAnchor.frame, sampleDepth]
  · intro v
    simp [frame, SelectedAnchor.frame, sampleDepth]
  · intro u
    exact rowChosen_path_anchor er s t u
  · intro v
    exact colChosen_path_anchor ec s t v


-- @@ L35-64 verbatim
/-- Every actual path point and anchor frame obeys the uniform sampler's
coordinate equations. This is separate from all matrix-entry claims. -/
theorem selection_chosen {h n : ℕ} (hh : 1 ≤ h) (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (s : Seeds (2 ^ h)) :
    PathChosen er ec s (selection hh er ec ha s.1 s.2.1 s.2.2) := by
  constructor
  · intro i hi
    simpa only [selection, path_of_le hi] using rowChosen_path er i hi true s
  · intro i hi
    simpa only [selection, path_of_le hi] using rowChosen_path er i hi false s
  · intro i hi
    simpa only [selection, path_of_le hi] using colChosen_path ec i hi true s
  · intro i hi
    simpa only [selection, path_of_le hi] using colChosen_path ec i hi false s
  · exact rowChosen_path_dummy er s
  · exact colChosen_path_dummy ec s
  · simp [selection, HostSampledPath.dummy, sampleDepth]
  · simp [selection, HostSampledPath.dummy, sampleDepth]
  · simpa only [selection, Equiv.symm_apply_apply, path_of_le (Nat.zero_le h)] using
      protected_path_roots h true true s.1 s.2.1 s.2.2
  · simpa only [selection, Equiv.symm_apply_apply, path_of_le (Nat.zero_le h)] using
      protected_path_roots h false false s.1 s.2.1 s.2.2
  · intro i hi
    exact frame_chosen er ec ha s _
  · intro i hi
    exact frame_chosen er ec ha s _
  · intro i hi
    exact frame_chosen er ec ha s _
  · intro i hi
    exact frame_chosen er ec ha s _


-- @@ L66-76 verbatim
/-- Each fixed guarded cell occupies at most the prescribed `1/m²` fraction
of the three-seed sample space, for the actual selected paths. -/
theorem selection_guard_frequency {h n : ℕ} (hh : 1 ≤ h)
    (er ec : Position h ≃ Fin n) (ha : AxisConditions er ec)
    (rc : Fin n × Fin n) :
    (Finset.univ.filter fun s : Seeds (2 ^ h) =>
      rc ∈ (selection hh er ec ha s.1 s.2.1 s.2.2).guards h).card * (2 ^ h) ^ 2 ≤
        Fintype.card (Seeds (2 ^ h)) :=
  path_guard_frequency er ec
    (fun s => selection hh er ec ha s.1 s.2.1 s.2.2)
    (fun s => selection_chosen hh er ec ha s) rc


-- @@ L78-98 verbatim
/-- The arbitrary-repair lower bound for the literal canonical host.
The independent axis enumerations satisfy `AxisConditions`: increasing anchor
groups precede all nonanchors, variable rows precede dummy rows, dummy columns
precede variable columns, and sampled parent/child pairs obey the four signed
tree-order inequalities. No entry-preservation condition is imposed on repairs. -/
theorem hammingDistance_ge {h n : ℕ} (hh : 1 ≤ h)
    (er ec : Position h ≃ Fin n) (ha : AxisConditions er ec)
    (B : BinaryMatrix n) (hfree : HFree fixedH B) :
    (2 ^ h) ^ 2 ≤ hammingDistance (SelectedAnchor.matrix er ec) B := by
  classical
  apply Sampling.hammingDistance_ge_of_guard_sampling fixedH
    (SelectedAnchor.matrix er ec) B
    (fun s : Seeds (2 ^ h) => (selection hh er ec ha s.1 s.2.1 s.2.2).guards h)
    (2 ^ h)
  · rw [card_seeds]
    positivity
  · exact selection_guard_frequency hh er ec ha
  · intro s hag
    exact GuardedPath.Selection.not_HFree_of_agree
      (selection_valid hh er ec ha s.1 s.2.1 s.2.2) hag
  · exact hfree


-- @@ L100-100 verbatim
end Problem348.Construction.SampledSelection


-- @@ L102-102 verbatim
end


-- @@ L104-104 verbatim
end OAI
