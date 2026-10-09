import OAI.Analysis.LipschitzEquivalence.SupportedDuality


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uM uE


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators InnerProductSpace Topology ENNReal

-- @@ L9-9 verbatim
open scoped Topology ENNReal NNReal

-- @@ L10-10 verbatim
open scoped Classical ENNReal NNReal InnerProductSpace Topology

-- @@ L11-11 verbatim
open Filter Set

-- @@ L12-12 verbatim
open scoped NNReal Topology

-- @@ L13-13 verbatim
open Filter Set


-- @@ L15-15 verbatim
namespace LipschitzCounterexample.FreeSpace

-- @@ L16-16 verbatim
open scoped NNReal Topology

-- @@ L17-17 verbatim
open Filter Set LocalizedLinearization

-- @@ L18-18 verbatim
variable {M : Type uM} [MetricSpace M] [Zero M]


-- @@ L20-21 verbatim
def multiplier (φ : M → ℝ) : Space M →L[ℝ] Space M :=
  linearize (fun x => φ x • point x)


-- @@ L23-31 verbatim
theorem multiplier_lipschitz (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) :
    LipschitzWith (A+B*R) (fun x => φ x • point x) := by
  simpa only [mul_one] using lipschitz_effective_smul point φ isometry_point.lipschitzWith hφ hA
    (fun x hx => by
      have he : ‖point x‖ = dist x 0 := by simpa only [point_zero,dist_zero_right] using isometry_point.dist_eq x 0
      rw [he]
      exact hR x hx)


-- @@ L33-37 verbatim
theorem multiplier_point (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) (x : M) :
    multiplier φ (point x) = φ x • point x :=
  linearize_point _ (multiplier_lipschitz φ hφ hA hR) (by simp) x


-- @@ L39-43 verbatim
theorem norm_multiplier_le (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) :
    ‖multiplier φ‖ ≤ A+B*R :=
  norm_linearize_le _ (multiplier_lipschitz φ hφ hA hR) (by simp)


-- @@ L45-54 verbatim
theorem supported_map {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Space M →L[ℝ] E) (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    {K : Set M} (hT : ∀ x ∈ K, T (point x) ∈ S) :
    ∀ μ ∈ supported K, T μ ∈ S := by
  have hsub : supported K ≤ S.comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal _ _ (hS.preimage T.continuous)
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact hT x hx
  exact fun μ hμ => hsub hμ


-- @@ L56-64 verbatim
theorem supported_univ : supported (Set.univ : Set M) = ⊤ := by
  apply top_unique
  intro μ _
  have hd := dense_combinations μ
  have hs : Set.range (Finsupp.linearCombination ℝ (point : M → Space M)) ⊆
      (↑(supported (M := M) Set.univ) : Set (Space M)) := by
    rintro _ ⟨a,rfl⟩
    exact combination_mem_supported a (by simp)
  exact (supported_isClosed Set.univ).closure_subset (closure_mono hs hd)


-- @@ L66-76 verbatim
theorem multiplier_supported (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) {K S : Set M}
    (hS : ∀ x ∈ K, φ x ≠ 0 → x ∈ S) {μ : Space M} (hμ : μ ∈ supported K) :
    multiplier φ μ ∈ supported S := by
  apply supported_map (multiplier φ) (supported S) (supported_isClosed S) (K := K) ?_ μ hμ
  intro x hx
  rw [multiplier_point φ hφ hA hR]
  by_cases hz : φ x = 0
  · simp [hz]
  · exact Submodule.smul_mem _ _ (point_mem_supported (hS x hx hz))


-- @@ L78-89 verbatim
theorem multiplier_identity_on (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) {K : Set M}
    (hK : ∀ x ∈ K, φ x = 1) {μ : Space M} (hμ : μ ∈ supported K) :
    multiplier φ μ = μ := by
  have hker : supported K ≤ (multiplier φ-ContinuousLinearMap.id ℝ (Space M)).ker := by
    apply Submodule.topologicalClosure_minimal _ _ (ContinuousLinearMap.isClosed_ker _)
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change multiplier φ (point x)-point x = 0
    rw [multiplier_point φ hφ hA hR,hK x hx,one_smul,sub_self]
  exact sub_eq_zero.mp (hker hμ)


-- @@ L91-91 verbatim
end LipschitzCounterexample.FreeSpace

-- @@ L92-92 verbatim
namespace LipschitzCounterexample.FreeSpace

-- @@ L93-93 verbatim
open scoped NNReal Topology

-- @@ L94-94 verbatim
open Filter Set LocalizedLinearization

-- @@ L95-95 verbatim
variable {M : Type uM} [MetricSpace M] [Zero M]


-- @@ L97-98 verbatim
def Approximable (μ : Space M) (K : Set M) (ε : ℝ) : Prop :=
  ∃ ν : Space M, ν ∈ supported K ∧ ‖μ-ν‖ < ε


-- @@ L100-101 verbatim
theorem supported_mono {K S : Set M} (h : K ⊆ S) : supported K ≤ supported S :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono h))


-- @@ L103-106 verbatim
theorem Approximable.mono {μ : Space M} {K S : Set M} {ε : ℝ}
    (h : Approximable μ K ε) (hKS : K ⊆ S) : Approximable μ S ε := by
  obtain ⟨ν,hν,hn⟩ := h
  exact ⟨ν,supported_mono hKS hν,hn⟩


-- @@ L108-113 verbatim
theorem finite_bounded {A : Finset M} : ∃ R : ℝ, 0 < R ∧ ∀ x ∈ A, dist x 0 ≤ R := by
  classical
  refine ⟨1+∑ x ∈ A, dist x 0,by positivity,?_⟩
  intro x hx
  have h := Finset.single_le_sum (fun y (_hy : y ∈ A) => dist_nonneg (x := y) (y := 0)) hx
  linarith


-- @@ L115-120 verbatim
theorem exists_radius_approx (μ : Space M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ Approximable μ (Metric.closedBall 0 R) ε := by
  obtain ⟨a,ha⟩ := exists_finite_approx μ hε
  obtain ⟨R,hR,hA⟩ := finite_bounded (A := a.support)
  refine ⟨R,hR,Finsupp.linearCombination ℝ point a,?_,ha⟩
  exact combination_mem_supported a (fun x hx => hA x hx)


-- @@ L122-135 verbatim
theorem prefix_radius_approx (μ : ℕ → Space M) {ε : ℝ} (hε : 0 < ε)
    (N : ℕ) (r : ℝ) : ∃ R : ℝ, r ≤ R ∧ 0 < R ∧
      ∀ i < N, Approximable (μ i) (Metric.closedBall 0 R) ε := by
  induction N with
  | zero => exact ⟨max (r+1) 1,by exact (le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _),
      lt_of_lt_of_le zero_lt_one (le_max_right _ _),by simp⟩
  | succ N ih =>
    obtain ⟨R,hr,hR,hN⟩ := ih
    obtain ⟨S,hS,hμ⟩ := exists_radius_approx (μ N) hε
    refine ⟨max R S,hr.trans (le_max_left _ _),hR.trans_le (le_max_left _ _),?_⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · exact (hN i hi).mono (Metric.closedBall_subset_closedBall (le_max_left _ _))
    · exact hμ.mono (Metric.closedBall_subset_closedBall (le_max_right _ _))


-- @@ L137-146 verbatim
theorem test_eq_of_agree {K : Set M} (h0 : (0 : M) ∈ K)
    (f g : M → ℝ) {C D : ℝ≥0} (hf : LipschitzWith C f) (hg : LipschitzWith D g)
    (he : ∀ x ∈ K, f x = g x) {ν : Space M} (hν : ν ∈ supported K) :
    test (normalized f hf) ν = test (normalized g hg) ν := by
  have hker : supported K ≤ (test (normalized f hf)-test (normalized g hg)).ker := by
    apply supported_le_ker
    intro x hx
    change (f x-f 0)-(g x-g 0) = 0
    rw [he x hx,he 0 h0,sub_self]
  exact sub_eq_zero.mp (hker hν)


-- @@ L148-163 verbatim
theorem pairing_difference_le {K : Set M} (h0 : (0 : M) ∈ K)
    (f g : M → ℝ) {C D : ℝ≥0} (hf : LipschitzWith C f) (hg : LipschitzWith D g)
    (he : ∀ x ∈ K, f x = g x) (μ ν : Space M) (hν : ν ∈ supported K) :
    |test (normalized f hf) μ-test (normalized g hg) μ| ≤ (C+D)*‖μ-ν‖ := by
  have heq := test_eq_of_agree h0 f g hf hg he hν
  have hid : test (normalized f hf) μ-test (normalized g hg) μ =
      test (normalized f hf) (μ-ν)-test (normalized g hg) (μ-ν) := by
    rw [map_sub,map_sub,heq]
    ring
  rw [hid]
  apply (abs_sub _ _).trans
  have hf' := (norm_test_apply_le (normalized f hf) (μ-ν)).trans
    (mul_le_mul_of_nonneg_right (norm_normalized_le f hf) (norm_nonneg _))
  have hg' := (norm_test_apply_le (normalized g hg) (μ-ν)).trans
    (mul_le_mul_of_nonneg_right (norm_normalized_le g hg) (norm_nonneg _))
  simpa only [Real.norm_eq_abs,NNReal.coe_add,add_mul] using add_le_add hf' hg'


-- @@ L165-165 verbatim
end LipschitzCounterexample.FreeSpace


-- @@ L167-167 verbatim
end


-- @@ L169-169 verbatim
end OAI
