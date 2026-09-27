/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import LeanPool.Feige.ConditionalTwoPointCalibration
import LeanPool.Feige.BoundaryNull
import LeanPool.Feige.StrictLocalInsertion


-- @@ L12-14 verbatim
/-!
# Removing strict positivity from the finite two-point bound
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Filter Topology


-- @@ L20-20 verbatim
namespace Feige


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-25 verbatim
/-- A positive perturbation parameter tending to zero. -/
def boundaryEpsilon (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)


-- @@ L27-29 verbatim
/-- A strictly positive approximation to a nonnegative lower displacement. -/
def strictGammaApprox {m : ℕ} (γ : Fin m → ℝ) (n : ℕ) (i : Fin m) : ℝ :=
  (1 - boundaryEpsilon n) * γ i + boundaryEpsilon n / 2


-- @@ L31-33 verbatim
theorem boundaryEpsilon_pos (n : ℕ) : 0 < boundaryEpsilon n := by
  unfold boundaryEpsilon
  positivity


-- @@ L35-37 verbatim
theorem boundaryEpsilon_le_one (n : ℕ) : boundaryEpsilon n ≤ 1 := by
  unfold boundaryEpsilon
  exact (div_le_one (by positivity)).2 (by norm_num)


-- @@ L39-45 verbatim
theorem strictGammaApprox_pos {m : ℕ} {γ : Fin m → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (n : ℕ) (i : Fin m) :
    0 < strictGammaApprox γ n i := by
  unfold strictGammaApprox
  have he := boundaryEpsilon_pos n
  have he1 := boundaryEpsilon_le_one n
  nlinarith [hγ i]


-- @@ L47-54 verbatim
theorem strictGammaApprox_le_one {m : ℕ} {γ : Fin m → ℝ}
    (hγ1 : ∀ i, γ i ≤ 1)
    (n : ℕ) (i : Fin m) :
    strictGammaApprox γ n i ≤ 1 := by
  unfold strictGammaApprox
  have he := boundaryEpsilon_pos n
  have he1 := boundaryEpsilon_le_one n
  nlinarith [hγ1 i]


-- @@ L56-59 verbatim
theorem tendsto_boundaryEpsilon :
    Tendsto boundaryEpsilon atTop (𝓝 0) := by
  unfold boundaryEpsilon
  exact tendsto_one_div_add_atTop_nhds_zero_nat


-- @@ L61-68 verbatim
theorem tendsto_strictGammaApprox {m : ℕ} (γ : Fin m → ℝ) :
    Tendsto (strictGammaApprox γ) atTop (𝓝 γ) := by
  rw [tendsto_pi_nhds]
  intro i
  unfold strictGammaApprox
  convert (((tendsto_const_nhds.sub tendsto_boundaryEpsilon).mul
    tendsto_const_nhds).add (tendsto_boundaryEpsilon.div_const 2)) using 1
  ring_nf


-- @@ L70-84 verbatim
theorem tendsto_twoPointKFinset_strictGammaApprox
    {m : ℕ} (γ β : Fin m → ℝ) (S : Finset (Fin m)) :
    Tendsto (fun n => twoPointKFinset (strictGammaApprox γ n) β S)
      atTop (𝓝 (twoPointKFinset γ β S)) := by
  unfold twoPointKFinset twoPointK
  apply continuous_dirichletK.continuousAt.tendsto.comp
  rw [tendsto_pi_nhds]
  intro i
  classical
  unfold twoPointVector
  by_cases hi : i ∈ S
  · simp [hi]
  · simp only [SetLike.mem_coe, hi, ite_false, lowValue]
    exact tendsto_const_nhds.sub
      ((tendsto_strictGammaApprox γ).apply_nhds i)


-- @@ L86-96 verbatim
theorem tendsto_twoPointHighProbability_strictGammaApprox
    {m : ℕ} (γ β : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 < β i)
    (i : Fin m) :
    Tendsto
      (fun n => twoPointHighProbability (strictGammaApprox γ n) β i)
      atTop (𝓝 (twoPointHighProbability γ β i)) := by
  unfold twoPointHighProbability highProbability
  have ht := (tendsto_strictGammaApprox γ).apply_nhds i
  apply ht.div (ht.add tendsto_const_nhds)
  linarith [hγ i, hβ i]


-- @@ L98-112 verbatim
theorem tendsto_highSetMass_strictGammaApprox
    {m : ℕ} (γ β : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 < β i)
    (S : Finset (Fin m)) :
    Tendsto
      (fun n => highSetMass
        (twoPointHighProbability (strictGammaApprox γ n) β) S)
      atTop (𝓝 (highSetMass (twoPointHighProbability γ β) S)) := by
  unfold highSetMass
  apply (tendsto_finsetProd S fun i _ =>
    tendsto_twoPointHighProbability_strictGammaApprox γ β hγ hβ i).mul
  apply tendsto_finsetProd (Finset.univ \ S)
  intro i hi
  exact tendsto_const_nhds.sub
    (tendsto_twoPointHighProbability_strictGammaApprox γ β hγ hβ i)


-- @@ L114-134 verbatim
/-- Every state rejected at the limiting parameter is, uniformly over the
finite Boolean state space, eventually rejected at threshold `α + δ` by the
strict approximants. -/
theorem eventually_rejectionFinset_subset_strictApprox
    {m : ℕ} (γ β : Fin m → ℝ) (α δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      ∀ S ∈ Finset.univ.filter
          (fun S : Finset (Fin m) => twoPointKFinset γ β S ≤ α),
        twoPointKFinset (strictGammaApprox γ n) β S ≤ α + δ := by
  apply (eventually_all_finset _).2
  intro S hS
  have hK : twoPointKFinset γ β S ≤ α := by
    simpa using hS
  have ht := tendsto_twoPointKFinset_strictGammaApprox γ β S
  have hev :
      ∀ᶠ n in atTop,
        twoPointKFinset (strictGammaApprox γ n) β S <
          twoPointKFinset γ β S + δ :=
    (tendsto_order.1 ht).2 _ (lt_add_of_pos_right _ hδ)
  filter_upwards [hev] with n hn
  linarith


-- @@ L136-179 verbatim
theorem twoPointRejectionMass_le_add_delta
    {m : ℕ} (γ β : Fin m → ℝ)
    (hγ0 : ∀ i, 0 ≤ γ i) (hγ1 : ∀ i, γ i ≤ 1)
    (hβ : ∀ i, 0 < β i) {α δ : ℝ}
    (hα : 0 ≤ α) (hδ : 0 < δ) :
    twoPointRejectionMass γ β α ≤ α + δ := by
  classical
  let T : Finset (Finset (Fin m)) :=
    Finset.univ.filter (fun S => twoPointKFinset γ β S ≤ α)
  let massN : ℕ → ℝ := fun n =>
    ∑ S ∈ T, highSetMass
      (twoPointHighProbability (strictGammaApprox γ n) β) S
  have hlim : Tendsto massN atTop
      (𝓝 (twoPointRejectionMass γ β α)) := by
    unfold massN T twoPointRejectionMass
    simpa only [Finset.powerset_univ] using
      tendsto_finsetSum (Finset.univ.filter
        (fun S : Finset (Fin m) => twoPointKFinset γ β S ≤ α))
        (fun S _ => tendsto_highSetMass_strictGammaApprox γ β hγ0 hβ S)
  apply le_of_tendsto hlim
  have hinc := eventually_rejectionFinset_subset_strictApprox
    γ β α δ hδ
  filter_upwards [hinc] with n hn
  have hsubset : T ⊆ Finset.univ.filter
      (fun S => twoPointKFinset (strictGammaApprox γ n) β S ≤ α + δ) := by
    intro S hS
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact hn S (by simpa [T] using hS)
  calc
    massN n ≤ twoPointRejectionMass (strictGammaApprox γ n) β (α + δ) := by
      unfold massN twoPointRejectionMass
      simp only [Finset.powerset_univ]
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro S hS hnot
      exact highSetMass_nonneg
        (twoPointHighProbability_nonneg
          (fun i => (strictGammaApprox_pos hγ0 n i).le) hβ)
        (twoPointHighProbability_le_one
          (fun i => (strictGammaApprox_pos hγ0 n i).le) hβ) S
    _ ≤ α + δ := strictTwoPoint_rejectionMass_le_alpha
      (strictGammaApprox γ n) β
      (strictGammaApprox_pos hγ0 n)
      (strictGammaApprox_le_one hγ1 n)
      hβ (by linarith)


-- @@ L181-190 verbatim
/-- Closed-boundary two-point rejection estimate. -/
theorem twoPointRejectionMass_le_alpha
    {m : ℕ} (γ β : Fin m → ℝ)
    (hγ0 : ∀ i, 0 ≤ γ i) (hγ1 : ∀ i, γ i ≤ 1)
    (hβ : ∀ i, 0 < β i) {α : ℝ} (hα : 0 ≤ α) :
    twoPointRejectionMass γ β α ≤ α := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  exact twoPointRejectionMass_le_add_delta
    γ β hγ0 hγ1 hβ hα hδ


-- @@ L192-196 verbatim
/-- The fully discharged finite two-point rejection hypothesis used by the
conditional-mixture calibration theorem. -/
theorem twoPointRejectionBound : TwoPointRejectionBound := by
  intro m γ β hγ0 hγ1 hβ α hα
  exact twoPointRejectionMass_le_alpha γ β hγ0 hγ1 hβ hα


-- @@ L198-198 verbatim
end


-- @@ L200-200 verbatim
end Feige
