import OAI.Analysis.MetricEntropy.PartitionGraph
import OAI.Analysis.MetricEntropy.LogProfile
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Linarith


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
universe uX uι uLabel


-- @@ L10-17 verbatim
/-!
# The actual logarithmic graph matrix

Columns retain both their vertex and their admissible partition set. The graph
metric takes values in ENat, so disconnected vertices have profile zero.
The row separation proof uses an actual coordinate of this matrix; the finite
field construction supplies its graph-separation hypothesis separately.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace MetricEntropyDuality.GraphProfile


-- @@ L23-23 verbatim
open scoped BigOperators


-- @@ L25-25 verbatim
variable {X : Type uX} {ι : Type uι} {Label : ι → Type uLabel}


-- @@ L27-29 verbatim
/-- Actual column indices, including the choice of partition graph. -/
abbrev Columns (X : Type uX) (𝒯 : Finset (Finset ι)) :=
  X × {T : Finset ι // T ∈ 𝒯}


-- @@ L31-34 verbatim
/-- The graph-distance column function. -/
def column (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι)) (h : ℕ)
    (y : Columns X 𝒯) (x : X) : ℝ :=
  LogProfile.phi h (PartitionGraph.distance L y.2.val x y.1)


-- @@ L36-38 verbatim
/-- The actual row vector has one coordinate for every actual column. -/
def row (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι)) (h : ℕ)
    (x : X) : Columns X 𝒯 → ℝ := fun y => column L 𝒯 h y x


-- @@ L40-43 verbatim
theorem column_nonneg (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (_hh : 0 < h) (y : Columns X 𝒯) (x : X) :
    0 ≤ column L 𝒯 h y x :=
  LogProfile.phi_nonneg h _


-- @@ L45-48 verbatim
theorem column_le_one (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (hh : 0 < h) (y : Columns X 𝒯) (x : X) :
    column L 𝒯 h y x ≤ 1 :=
  LogProfile.phi_le_one hh _


-- @@ L50-55 verbatim
theorem column_self (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (_hh : 0 < h) (x : X) (T : {T : Finset ι // T ∈ 𝒯}) :
    column L 𝒯 h (x, T) x = 1 := by
  unfold column
  rw [PartitionGraph.distance_self]
  exact LogProfile.phi_zero h


-- @@ L57-62 verbatim
theorem column_eq_zero_of_le (L : (i : ι) → X → Label i)
    (𝒯 : Finset (Finset ι)) {h : ℕ} (hh : 0 < h)
    (y : Columns X 𝒯) (x : X)
    (hd : (h : ℕ∞) ≤ PartitionGraph.distance L y.2.val x y.1) :
    column L 𝒯 h y x = 0 :=
  LogProfile.phi_eq_zero_of_le hh hd


-- @@ L64-70 verbatim
/-- Exact finite-ball expansion, with no finite-distance assumption. -/
theorem column_eq_sum (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (hh : 0 < h) (y : Columns X 𝒯) (x : X) :
    column L 𝒯 h y x = ∑ j ∈ Finset.range h,
      if PartitionGraph.distance L y.2.val x y.1 ≤ (j : ℕ∞)
      then LogProfile.gamma h j else 0 :=
  LogProfile.phi_eq_sum hh _


-- @@ L72-86 verbatim
/-- The concrete coordinate witness consumed by the convex-body construction. -/
theorem exists_column_abs_eq_one (L : (i : ι) → X → Label i)
    (𝒯 : Finset (Finset ι)) {h : ℕ} (hh : 0 < h) (x z : X)
    (hsep : ∃ T ∈ 𝒯, (h : ℕ∞) < PartitionGraph.distance L T x z) :
    ∃ y : Columns X 𝒯, |column L 𝒯 h y x - column L 𝒯 h y z| = 1 := by
  obtain ⟨T, hT, hd⟩ := hsep
  let c : Columns X 𝒯 := (x, ⟨T, hT⟩)
  have hx : column L 𝒯 h c x = 1 := column_self L 𝒯 hh x ⟨T, hT⟩
  have hz : column L 𝒯 h c z = 0 := by
    apply column_eq_zero_of_le L 𝒯 hh c z
    change (h : ℕ∞) ≤ PartitionGraph.distance L T z x
    rw [PartitionGraph.distance_comm]
    exact hd.le
  refine ⟨c, ?_⟩
  rw [hx, hz, sub_zero, abs_one]


-- @@ L88-98 verbatim
/-- All row coordinates lie in the common unit interval. -/
theorem abs_row_sub_le_one (L : (i : ι) → X → Label i)
    (𝒯 : Finset (Finset ι)) {h : ℕ} (hh : 0 < h)
    (x z : X) (y : Columns X 𝒯) :
    |row L 𝒯 h x y - row L 𝒯 h z y| ≤ 1 := by
  have hx0 := column_nonneg L 𝒯 hh y x
  have hx1 := column_le_one L 𝒯 hh y x
  have hz0 := column_nonneg L 𝒯 hh y z
  have hz1 := column_le_one L 𝒯 hh y z
  change |column L 𝒯 h y x - column L 𝒯 h y z| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩


-- @@ L100-124 verbatim
/-- The column `(x,T)` certifies exact unit separation, including when the
chosen graph disconnects x from z. -/
theorem norm_row_sub_eq_one [Fintype X]
    (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (hh : 0 < h) (x z : X)
    (hsep : ∃ T ∈ 𝒯, (h : ℕ∞) < PartitionGraph.distance L T x z) :
    ‖row L 𝒯 h x - row L 𝒯 h z‖ = 1 := by
  classical
  obtain ⟨T, hT, hd⟩ := hsep
  let c : Columns X 𝒯 := (x, ⟨T, hT⟩)
  have hx : column L 𝒯 h c x = 1 := column_self L 𝒯 hh x ⟨T, hT⟩
  have hz : column L 𝒯 h c z = 0 := by
    apply column_eq_zero_of_le L 𝒯 hh c z
    change (h : ℕ∞) ≤ PartitionGraph.distance L T z x
    rw [PartitionGraph.distance_comm]
    exact hd.le
  have hc : (row L 𝒯 h x - row L 𝒯 h z) c = 1 := by
    change column L 𝒯 h c x - column L 𝒯 h c z = 1
    rw [hx, hz, sub_zero]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro y
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using abs_row_sub_le_one L 𝒯 hh x z y
  · have hb := norm_le_pi_norm (row L 𝒯 h x - row L 𝒯 h z) c
    simpa only [hc, norm_one] using hb


-- @@ L126-133 verbatim
/-- The norm equality also gives the usual finite-product metric equality. -/
theorem dist_row_eq_one [Fintype X]
    (L : (i : ι) → X → Label i) (𝒯 : Finset (Finset ι))
    {h : ℕ} (hh : 0 < h) (x z : X)
    (hsep : ∃ T ∈ 𝒯, (h : ℕ∞) < PartitionGraph.distance L T x z) :
    dist (row L 𝒯 h x) (row L 𝒯 h z) = 1 := by
  rw [dist_eq_norm]
  exact norm_row_sub_eq_one L 𝒯 hh x z hsep


-- @@ L135-135 verbatim
end MetricEntropyDuality.GraphProfile


-- @@ L137-137 verbatim
end


-- @@ L139-139 verbatim
end OAI
