import OAI.Combinatorics.CliqueFree.Reach
import OAI.Combinatorics.CliqueFree.FiniteKernel


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
namespace CliqueFreeIndependence.WeightedGraph


-- @@ L15-15 verbatim
universe u v


-- @@ L17-17 verbatim
variable {V : Type u} [Fintype V]


-- @@ L19-19 verbatim
attribute [local instance 10000] edgeStateDecEq


-- @@ L21-21 verbatim
namespace LocalWalk

-- @@ L22-22 verbatim
open FiniteEntropy FiniteKernel

-- @@ L23-23 verbatim
variable (G : SimpleGraph V) (w : V → ℝ)


-- @@ L25-29 verbatim
/-- The disjoint union of the neighborhood transition kernels. -/
noncomputable def transition : Kernel (EdgeState G) := fun e f ↦
  if e.src = f.src then
    if G.Adj e.dst f.dst then w f.dst / commonMass G w e.src e.dst else 0
  else 0


-- @@ L31-32 verbatim
noncomputable def normalizer : ℝ :=
  ∑ e : EdgeState G, w e.src * w e.dst * commonMass G w e.src e.dst


-- @@ L34-35 verbatim
noncomputable def law : EdgeState G → ℝ := fun e ↦
  (w e.src * w e.dst * commonMass G w e.src e.dst) / normalizer G w


-- @@ L37-37 verbatim
noncomputable def vertexWeight : EdgeState G → ℝ := fun e ↦ w e.dst


-- @@ L39-41 verbatim
noncomputable def fiber (u : V) : Finset (EdgeState G) := by
  classical
  exact univ.filter (fun e ↦ e.src = u)


-- @@ L43-45 verbatim
@[simp] lemma mem_fiber (e : EdgeState G) (u : V) : e ∈ fiber G u ↔ e.src = u := by
  classical
  simp [fiber]


-- @@ L47-49 verbatim
lemma fiber_mass (u : V) : (∑ e ∈ fiber G u, vertexWeight G w e) = neighborMass G w u := by
  classical
  simp only [fiber, sum_filter, vertexWeight, EdgeState.sum_fiber, neighborMass, mass]


-- @@ L51-54 verbatim
lemma normalizer_eq : normalizer G w = 6 * triangleMass G w := by
  rw [normalizer, EdgeState.sum_eq (fun u v ↦ w u * w v * commonMass G w u v),
    triangleMass_eq_sum]
  simp only [triangleAt, mul_sum, mul_assoc]


-- @@ L56-56 verbatim
variable {G w}

-- @@ L57-75 verbatim
lemma transition_stochastic (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : Stochastic (transition G w) := by
  classical
  intro e
  constructor
  · intro f
    dsimp [transition]
    split_ifs
    · exact (div_pos (hw _) (hc _ _ e.adj)).le
    all_goals exact le_rfl
  · change (∑ f : EdgeState G, if e.src = f.src then
        (if G.Adj e.dst f.dst then w f.dst / commonMass G w e.src e.dst else 0) else 0) = 1
    rw [EdgeState.sum_fiber' e.src (fun z ↦
      if G.Adj e.dst z then w z / commonMass G w e.src e.dst else 0)]
    have hid (z : V) : (if G.Adj e.dst z then w z / commonMass G w e.src e.dst else 0) =
        (if G.Adj e.dst z then w z else 0) / commonMass G w e.src e.dst := by
      split_ifs <;> simp
    simp_rw [hid]
    rw [← sum_div, ← commonMass_eq_sum, div_self (hc _ _ e.adj).ne']


-- @@ L77-79 verbatim
lemma normalizer_pos [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : 0 < normalizer G w := by
  exact sum_pos (fun e _ ↦ mul_pos (mul_pos (hw _) (hw _)) (hc _ _ e.adj)) univ_nonempty


-- @@ L81-89 verbatim
lemma law_isProb [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : IsProb (law G w) := by
  have hZ := normalizer_pos hw hc
  constructor
  · intro e
    exact (div_pos (mul_pos (mul_pos (hw _) (hw _)) (hc _ _ e.adj)) hZ).le
  · unfold law
    rw [← sum_div]
    exact div_self hZ.ne'


-- @@ L91-104 verbatim
lemma transition_reversible [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) :
    Reversible (law G w) (transition G w) := by
  classical
  intro e f
  by_cases hsrc : e.src = f.src
  · by_cases hadj : G.Adj e.dst f.dst
    · simp only [transition, hsrc, ite_true, hadj, hadj.symm, law]
      have he := (hc _ _ e.adj).ne'
      have hf := (hc _ _ f.adj).ne'
      rw [hsrc] at he
      field_simp [he, hf, (normalizer_pos hw hc).ne']
    · simp [transition, hsrc, hadj, G.adj_comm f.dst]
  · simp [transition, hsrc, Ne.symm hsrc]


-- @@ L106-107 verbatim
lemma transition_fixed_src (e f : EdgeState G) (h : e.src ≠ f.src) :
    transition G w e f = 0 := by simp [transition, h]


-- @@ L109-120 verbatim
lemma transition_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v) :
    ∀ e f, transition G w e f ≤ x * vertexWeight G w f := by
  classical
  intro e f
  have hc0 : 0 < commonMass G w e.src e.dst := (one_div_pos.2 hx).trans_le (hc _ _ e.adj)
  dsimp [transition, vertexWeight]
  split_ifs
  · apply (div_le_iff₀ hc0).2
    have h := (div_le_iff₀ hx).1 (hc _ _ e.adj)
    nlinarith [mul_le_mul_of_nonneg_left h (hw f.dst).le]
  all_goals exact (mul_pos hx (hw _)).le


-- @@ L122-124 verbatim
lemma smoothed_fixed_src (n : ℕ) (e f : EdgeState G) (h : e.src ≠ f.src) :
    smoothed (transition G w) n e f = 0 :=
  preserves_smoothed (label := EdgeState.src) transition_fixed_src n e f h


-- @@ L126-131 verbatim
lemma smoothed_supported (n : ℕ) (e f : EdgeState G) (h : f ∉ fiber G e.src) :
    smoothed (transition G w) n e f = 0 := by
  apply smoothed_fixed_src
  intro he
  apply h
  exact (mem_fiber G f e.src).2 he.symm


-- @@ L133-138 verbatim
lemma smoothed_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v) (n : ℕ) :
    ∀ e f, smoothed (transition G w) n e f ≤ x * vertexWeight G w f := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  exact FiniteKernel.smoothed_density (transition_stochastic hw hc0) (transition_density hw hx hc) n


-- @@ L140-153 verbatim
lemma entropy_bounds [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) (n : ℕ) (e : EdgeState G) :
    -Real.log x ≤ entropy (vertexWeight G w) (smoothed (transition G w) n e) ∧
      entropy (vertexWeight G w) (smoothed (transition G w) n e) ≤ x := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hp := stochastic_smoothed (transition_stochastic hw hc0) n e
  constructor
  · exact entropy_ge_neg_log_of_density (w := vertexWeight G w) (fun f ↦ hw f.dst) hp hx
      (smoothed_density hw hx hc n e)
  · have h := entropy_supported_le_log (w := vertexWeight G w) (fiber G e.src) (fun f _ ↦ hw f.dst) hp
      (smoothed_supported n e) (Real.exp_pos x) (by rw [fiber_mass]; exact hL e.src)
    simpa only [Real.log_exp] using h


-- @@ L155-155 verbatim
end LocalWalk


-- @@ L157-157 verbatim
end CliqueFreeIndependence.WeightedGraph


-- @@ L159-159 verbatim
end


-- @@ L161-161 verbatim
end OAI
