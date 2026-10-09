import OAI.Combinatorics.CliqueFree.Lottery
import OAI.Combinatorics.CliqueFree.Optimizer


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Finset


-- @@ L11-11 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L13-13 verbatim
namespace CliqueFreeIndependence

-- @@ L14-14 verbatim
universe u

-- @@ L15-15 verbatim
namespace WeightedGraph

-- @@ L16-16 verbatim
open Lottery

-- @@ L17-17 verbatim
variable {V : Type u} [Fintype V]


-- @@ L19-20 verbatim
/-- A weight vector restricted to a vertex set. -/
noncomputable def restrict (A : Finset V) (w : V → ℝ) : V → ℝ := fun v ↦ if v ∈ A then w v else 0


-- @@ L22-34 verbatim
lemma edgeMass_smul (G : SimpleGraph V) (w : V → ℝ) (a : ℝ) :
    edgeMass G (fun v ↦ a*w v) = a^2 * edgeMass G w := by
  have h : edgeForm G (fun v ↦ a*w v) (fun v ↦ a*w v) = a^2*edgeForm G w w := by
    unfold edgeForm
    rw [mul_sum]
    apply sum_congr rfl
    intro u _
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    split_ifs <;> ring
  rw [edgeForm_self,edgeForm_self] at h
  linarith


-- @@ L36-57 verbatim
lemma edgeMass_restrict (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    edgeMass G (restrict A w) = crossMass G w A A / 2 := by
  classical
  unfold edgeMass crossMass restrict
  congr 1
  calc
    _ = ∑ u, ∑ v, if u ∈ A ∧ v ∈ A then (if G.Adj u v then w u*w v else 0) else 0 := by
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp [hu,hv]
    _ = _ := by
      simp only [ite_and]
      simp_rw [sum_ite_irrel]
      simp only [sum_const_zero]
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter]
      apply sum_congr rfl
      intro u hu
      rw [← sum_filter]
      simp


-- @@ L59-60 verbatim
lemma crossMass_restrict (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w A A = ∑ v ∈ A, w v * mass w (A ∩ neighbors G v) := crossMass_factor G w A A


-- @@ L62-69 verbatim
lemma edgeMass_restrict_le (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A : Finset V) {t : ℝ} (hA : ∀ v ∈ A, mass w (A ∩ neighbors G v) ≤ t) :
    edgeMass G (restrict A w) ≤ t * mass w A / 2 := by
  rw [edgeMass_restrict,crossMass_restrict]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ v ∈ A, w v*t := sum_le_sum fun v hv ↦ mul_le_mul_of_nonneg_left (hA v hv) (hw v)
    _ = _ := by rw [← sum_mul]; exact mul_comm _ _


-- @@ L71-73 verbatim
/-- Bounded multipliers supported on A, regardless of the lottery weight of the entry. -/
def BoundedOn (L : Law (V → ℝ)) (A : Finset V) (b : ℝ) : Prop :=
  ∀ z ∈ L, (∀ v, 0 ≤ z.2 v ∧ z.2 v ≤ b) ∧ (∀ v, v ∉ A → z.2 v = 0)


-- @@ L75-76 verbatim
noncomputable def expectedEdges (G : SimpleGraph V) (w : V → ℝ) (L : Law (V → ℝ)) : ℝ :=
  expect L (fun m ↦ edgeMass G (fun v ↦ w v*m v))


-- @@ L78-89 verbatim
lemma expectedEdges_transform (G : SimpleGraph V) (w : V → ℝ) (L : Law (V → ℝ)) (p k : ℝ) :
    expectedEdges G w (transform p (fun m v ↦ k*m v) L) = p*k^2*expectedEdges G w L := by
  unfold expectedEdges
  rw [expect_transform]
  have he (m : V → ℝ) : edgeMass G (fun v ↦ w v*(k*m v)) = k^2*edgeMass G (fun v ↦ w v*m v) := by
    convert edgeMass_smul G (fun v ↦ w v*m v) k using 2
    ext v
    ring
  change p * expect L (fun m ↦ edgeMass G (fun v ↦ w v*(k*m v))) = _
  simp_rw [he]
  rw [expect_mul]
  ring


-- @@ L91-97 verbatim
omit [Fintype V] in
lemma mean_transform (L : Law (V → ℝ)) (p k : ℝ) (v : V) :
    expect (transform p (fun m v ↦ k*m v) L) (fun m ↦ m v) = p*k*expect L (fun m ↦ m v) := by
  rw [expect_transform]
  change p * expect L (fun m ↦ k*m v) = _
  rw [expect_mul]
  ring


-- @@ L99-107 verbatim
omit [Fintype V] in
lemma bounded_transform {L : Law (V → ℝ)} {A : Finset V} {b B k : ℝ}
    (hL : BoundedOn L A b) (hk : 0 ≤ k) (hkb : k*b ≤ B) (p : ℝ) :
    BoundedOn (transform p (fun m v ↦ k*m v) L) A B := by
  intro z hz
  obtain ⟨y,hy,rfl⟩ := List.mem_map.1 hz
  obtain ⟨hby,hsy⟩ := hL y hy
  exact ⟨fun v ↦ ⟨mul_nonneg hk (hby v).1,(mul_le_mul_of_nonneg_left (hby v).2 hk).trans hkb⟩,
    fun v hv ↦ by simp [hsy v hv]⟩


-- @@ L109-116 verbatim
omit [Fintype V] in
lemma bounded_append {L K : Law (V → ℝ)} {A B S : Finset V} {b : ℝ}
    (hL : BoundedOn L A b) (hK : BoundedOn K B b) (hA : A ⊆ S) (hB : B ⊆ S) :
    BoundedOn (L++K) S b := by
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · exact ⟨(hL z hz).1,fun v hv ↦ (hL z hz).2 v (fun h ↦ hv (hA h))⟩
  · exact ⟨(hK z hz).1,fun v hv ↦ (hK z hz).2 v (fun h ↦ hv (hB h))⟩


-- @@ L118-137 verbatim
lemma normalize_subprob (G : SimpleGraph V) (w : V → ℝ) {L : Law (V → ℝ)}
    (hL : Positive L) (hsum : total L ≤ 1) {A : Finset V} {b : ℝ} (hb : 0 ≤ b)
    (hbL : BoundedOn L A b) :
    ∃ K : Law (V → ℝ), IsProb K ∧ BoundedOn K A b ∧
      (∀ v, expect K (fun m ↦ m v) = expect L (fun m ↦ m v)) ∧
      expectedEdges G w K = expectedEdges G w L := by
  let K : Law (V → ℝ) := (1-total L,0)::L
  refine ⟨K,⟨?_,?_⟩,?_,?_,?_⟩
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact sub_nonneg.2 hsum
    · exact hL z hz
  · simp [K,total,expect_cons]
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨fun _ ↦ ⟨le_rfl,hb⟩,fun _ _ ↦ rfl⟩
    · exact hbL z hz
  · intro v
    simp [K]
  · simp [K,expectedEdges,edgeMass,crossMass]


-- @@ L139-139 verbatim
end WeightedGraph

-- @@ L140-140 verbatim
end CliqueFreeIndependence


-- @@ L142-142 verbatim
end


-- @@ L144-144 verbatim
end OAI
