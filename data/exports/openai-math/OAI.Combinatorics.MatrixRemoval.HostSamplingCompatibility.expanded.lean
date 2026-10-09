import OAI.Combinatorics.MatrixRemoval.HostSampling
import OAI.Combinatorics.MatrixRemoval.HostSampledPath
import OAI.Combinatorics.MatrixRemoval.GuardContainment


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-12 verbatim
/-!
# Compatibility of the path sampler and protected-cell sampler

The quotient/remainder formula and `finProdFinEquiv` select the same
coordinate, identifying path samples with the uniform-fiber sampler.
-/


-- @@ L14-14 verbatim
namespace Problem348.TreeSampling


-- @@ L16-22 verbatim
/-- The equivalence-based and arithmetic mixers select identical coordinates. -/
theorem atLevel_eq_mixFin (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    atLevel h i hi z u = SampledPath.mixFin h i hi z u := by
  apply Fin.ext
  change u.val % (2 ^ (h - i)) + (2 ^ (h - i)) * (z.val / (2 ^ (h - i))) =
    z.val / (2 ^ (h - i)) * (2 ^ (h - i)) + u.val % (2 ^ (h - i))
  ac_rfl


-- @@ L24-24 verbatim
end Problem348.TreeSampling


-- @@ L26-26 verbatim
namespace Problem348.Construction.HostSampling


-- @@ L28-39 verbatim
/-- An actual sampled variable path point is selected by the marginal sampler. -/
theorem coordinate_path_position (h i : ℕ) (hi : i ≤ h) (sign : Bool)
    (z u : Fin (2 ^ h)) :
    coordinate z u (HostSampledPath.position h i hi sign z u) =
      offset (HostSampledPath.position h i hi sign z u) := by
  change TreeSampling.atLevel h (depth (SampledPath.sample h i hi sign z u))
    (depth_le _) z u =
    (SampledPath.sample h i hi sign z u).2
  have hd : depth (SampledPath.sample h i hi sign z u) = i :=
    (HostSampledPath.sample_atLevel h i hi sign z u).1
  simp only [hd]
  exact TreeSampling.atLevel_eq_mixFin h i hi z u


-- @@ L41-44 verbatim
/-- Anchor representatives use the corresponding independent axis seed. -/
@[simp] theorem coordinate_anchor (h : ℕ) (t : Mode h) (v : Fin 64)
    (z u : Fin (2 ^ h)) :
    coordinate z u (Sum.inl (t, v, u)) = offset (Sum.inl (t, v, u)) := rfl


-- @@ L46-49 verbatim
/-- The selected dummy position uses the same independent axis seed. -/
@[simp] theorem coordinate_path_dummy (h : ℕ) (z u : Fin (2 ^ h)) :
    coordinate z u (HostSampledPath.dummy h u) =
      offset (HostSampledPath.dummy h u) := rfl


-- @@ L51-58 verbatim
/-- Every pair of path samples, not just the protected pairs, is selected.
The two axes use different offset seeds but the same leaf seed. -/
theorem selected_path_positions (h i j : ℕ) (hi : i ≤ h) (hj : j ≤ h)
    (s t : Bool) (z u v : Fin (2 ^ h)) :
    Selected (z, u, v) (HostSampledPath.position h i hi s z u)
      (HostSampledPath.position h j hj t z v) := by
  exact Prod.ext (coordinate_path_position h i hi s z u)
    (coordinate_path_position h j hj t z v)


-- @@ L60-67 verbatim
/-- A path-row / selected-anchor-column pair is a selected protected cell. -/
theorem protected_selected_path_anchor (h i : ℕ) (hi : i ≤ h) (sign : Bool)
    (t : Mode h) (a : Fin 64) (z u v : Fin (2 ^ h)) :
    Protected (HostSampledPath.position h i hi sign z u) (Sum.inl (t, a, v)) ∧
      Selected (z, u, v) (HostSampledPath.position h i hi sign z u)
        (Sum.inl (t, a, v)) := by
  exact ⟨protected_anchor_right _ _,
    Prod.ext (coordinate_path_position h i hi sign z u) rfl⟩


-- @@ L69-76 verbatim
/-- A selected-anchor-row / path-column pair is a selected protected cell. -/
theorem protected_selected_anchor_path (h i : ℕ) (hi : i ≤ h) (sign : Bool)
    (t : Mode h) (a : Fin 64) (z u v : Fin (2 ^ h)) :
    Protected (Sum.inl (t, a, u)) (HostSampledPath.position h i hi sign z v) ∧
      Selected (z, u, v) (Sum.inl (t, a, u))
        (HostSampledPath.position h i hi sign z v) := by
  exact ⟨protected_anchor_left _ _,
    Prod.ext rfl (coordinate_path_position h i hi sign z v)⟩


-- @@ L78-83 verbatim
/-- Direct row-field adapter for the geometric guarded-path certificate. -/
theorem rowChosen_path {h n : ℕ} (er : Position h ≃ Fin n)
    (i : ℕ) (hi : i ≤ h) (sign : Bool) (s : TreeSampling.Seeds (2 ^ h)) :
    RowChosen er s (er (HostSampledPath.position h i hi sign s.1 s.2.1)) := by
  simp only [RowChosen, Equiv.symm_apply_apply]
  exact coordinate_path_position h i hi sign s.1 s.2.1


-- @@ L85-90 verbatim
/-- Direct column-field adapter for the geometric guarded-path certificate. -/
theorem colChosen_path {h n : ℕ} (ec : Position h ≃ Fin n)
    (i : ℕ) (hi : i ≤ h) (sign : Bool) (s : TreeSampling.Seeds (2 ^ h)) :
    ColChosen ec s (ec (HostSampledPath.position h i hi sign s.1 s.2.2)) := by
  simp only [ColChosen, Equiv.symm_apply_apply]
  exact coordinate_path_position h i hi sign s.1 s.2.2


-- @@ L92-96 verbatim
@[simp] theorem rowChosen_path_dummy {h n : ℕ} (er : Position h ≃ Fin n)
    (s : TreeSampling.Seeds (2 ^ h)) :
    RowChosen er s (er (HostSampledPath.dummy h s.2.1)) := by
  simp only [RowChosen, Equiv.symm_apply_apply]
  rfl


-- @@ L98-102 verbatim
@[simp] theorem colChosen_path_dummy {h n : ℕ} (ec : Position h ≃ Fin n)
    (s : TreeSampling.Seeds (2 ^ h)) :
    ColChosen ec s (ec (HostSampledPath.dummy h s.2.2)) := by
  simp only [ColChosen, Equiv.symm_apply_apply]
  rfl


-- @@ L104-108 verbatim
@[simp] theorem rowChosen_path_anchor {h n : ℕ} (er : Position h ≃ Fin n)
    (s : TreeSampling.Seeds (2 ^ h)) (t : Mode h) (a : Fin 64) :
    RowChosen er s (er (Sum.inl (t, a, s.2.1))) := by
  simp only [RowChosen, Equiv.symm_apply_apply]
  rfl


-- @@ L110-114 verbatim
@[simp] theorem colChosen_path_anchor {h n : ℕ} (ec : Position h ≃ Fin n)
    (s : TreeSampling.Seeds (2 ^ h)) (t : Mode h) (a : Fin 64) :
    ColChosen ec s (ec (Sum.inl (t, a, s.2.2))) := by
  simp only [ColChosen, Equiv.symm_apply_apply]
  rfl


-- @@ L116-122 verbatim
/-- Both sampled roots belong to protected classes, regardless of sign. -/
theorem protected_path_roots (h : ℕ) (s t : Bool) (z u v : Fin (2 ^ h)) :
    Protected (HostSampledPath.position h 0 (Nat.zero_le h) s z u)
      (HostSampledPath.position h 0 (Nat.zero_le h) t z v) := by
  apply protected_roots
  · exact (HostSampledPath.sample_atLevel h 0 (Nat.zero_le h) s z u).1
  · exact (HostSampledPath.sample_atLevel h 0 (Nat.zero_le h) t z v).1


-- @@ L124-124 verbatim
end Problem348.Construction.HostSampling


-- @@ L126-126 verbatim
end OAI
