import OAI.Analysis.LipschitzEquivalence.FreeSpace


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uH uIndex


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace LipschitzCounterexample


-- @@ L10-10 verbatim
namespace NullSequences


-- @@ L12-12 verbatim
open Filter

-- @@ L13-13 verbatim
open scoped Topology

-- @@ L14-14 verbatim
variable {H : Type uH} [NormedAddCommGroup H]


-- @@ L16-16 verbatim
abbrev C0 := ZeroAtInftyContinuousMap ℕ H


-- @@ L18-21 verbatim
def ofTendsto (s : ℕ → H) (hs : Tendsto s atTop (𝓝 0)) : C0 (H := H) where
  toFun := s
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by simpa [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using hs


-- @@ L23-24 verbatim
theorem tendsto_zero (s : C0 (H := H)) : Tendsto s atTop (𝓝 0) := by
  simpa [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using zero_at_infty s


-- @@ L26-27 verbatim
theorem norm_apply_le (s : C0 (H := H)) (i : ℕ) : ‖s i‖ ≤ ‖s‖ :=
  BoundedContinuousFunction.norm_coe_le_norm s.toBCF i


-- @@ L29-31 verbatim
theorem norm_le {s : C0 (H := H)} {c : ℝ} (hc : 0 ≤ c) :
    ‖s‖ ≤ c ↔ ∀ i, ‖s i‖ ≤ c :=
  BoundedContinuousFunction.norm_le hc


-- @@ L33-36 verbatim
def evalAddHom (i : ℕ) : C0 (H := H) →+ H where
  toFun := fun s => s i
  map_zero' := rfl
  map_add' := fun _ _ => rfl


-- @@ L38-39 verbatim
@[simp] theorem sum_apply {ι : Type uIndex} (f : ι → C0 (H := H)) (S : Finset ι) (i : ℕ) :
    (∑ j ∈ S, f j) i = ∑ j ∈ S, f j i := map_sum (evalAddHom i) _ _


-- @@ L41-45 verbatim
def single (i : ℕ) (x : H) : C0 (H := H) :=
  ofTendsto (fun j => if j = i then x else 0) (by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with j hj
    simp [ne_of_gt hj])


-- @@ L47-48 verbatim
@[simp] theorem single_apply (i j : ℕ) (x : H) :
    single i x j = if j = i then x else 0 := rfl


-- @@ L50-52 verbatim
@[simp] theorem single_zero (i : ℕ) : single i (0 : H) = 0 := by
  ext j
  simp


-- @@ L54-57 verbatim
@[simp] theorem single_sub (i : ℕ) (x y : H) :
    single i (x - y) = single i x - single i y := by
  ext j
  by_cases hj : j = i <;> simp [hj]


-- @@ L59-64 verbatim
@[simp] theorem norm_single (i : ℕ) (x : H) : ‖single i x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (norm_le (norm_nonneg x)).2
    intro j
    by_cases hj : j = i <;> simp [hj]
  · simpa using norm_apply_le (single i x) i


-- @@ L66-69 verbatim
theorem isometry_single (i : ℕ) : Isometry (single (H := H) i) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← single_sub, norm_single, dist_eq_norm]


-- @@ L71-72 verbatim
def trunc (N : ℕ) (s : C0 (H := H)) : C0 (H := H) :=
  ∑ i ∈ Finset.range N, single i (s i)


-- @@ L74-76 verbatim
@[simp] theorem trunc_apply (N i : ℕ) (s : C0 (H := H)) :
    trunc N s i = if i < N then s i else 0 := by
  simp [trunc, sum_apply, single_apply]


-- @@ L78-84 verbatim
theorem norm_sub_trunc_le (s : C0 (H := H)) (N : ℕ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i ≥ N, ‖s i‖ ≤ c) : ‖s - trunc N s‖ ≤ c := by
  apply (norm_le hc).2
  intro i
  by_cases hi : i < N
  · simp [hi, hc]
  · simpa [hi] using h i (Nat.le_of_not_gt hi)


-- @@ L86-97 verbatim
theorem tendsto_trunc (s : C0 (H := H)) : Tendsto (fun N => trunc N s) atTop (𝓝 s) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hs := (tendsto_zero s).norm
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hs (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_comm, dist_eq_norm]
  apply lt_of_le_of_lt (norm_sub_trunc_le s n (le_of_lt (half_pos hε)) ?_)
    (half_lt_self hε)
  intro i hi
  have h := hN i (hn.trans hi)
  simpa only [norm_zero, Real.dist_eq, sub_zero, abs_norm] using h.le


-- @@ L99-99 verbatim
variable [NormedSpace ℝ H]


-- @@ L101-105 verbatim
def evalCLM (i : ℕ) : C0 (H := H) →L[ℝ] H :=
  ({ toFun := fun s => s i
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : C0 (H := H) →ₗ[ℝ] H).mkContinuous
    1 (fun s => by simpa using norm_apply_le s i)


-- @@ L107-122 verbatim
instance [TopologicalSpace.SeparableSpace H] : TopologicalSpace.SeparableSpace (C0 (H := H)) := by
  let S : Set (C0 (H := H)) := ⋃ i : ℕ, Set.range (single (H := H) i)
  have hs : TopologicalSpace.IsSeparable S :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (isometry_single i).continuous)
  have hd : Dense (Submodule.span ℝ S : Set (C0 (H := H))) := by
    intro s
    apply isClosed_closure.mem_of_tendsto (tendsto_trunc s)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    exact Set.mem_iUnion.2 ⟨i, ⟨s i, rfl⟩⟩
  exact hd.isSeparable_iff.mp hs.span


-- @@ L124-124 verbatim
end NullSequences


-- @@ L126-126 verbatim
end LipschitzCounterexample

-- @@ L127-127 verbatim
end


-- @@ L129-129 verbatim
end OAI
