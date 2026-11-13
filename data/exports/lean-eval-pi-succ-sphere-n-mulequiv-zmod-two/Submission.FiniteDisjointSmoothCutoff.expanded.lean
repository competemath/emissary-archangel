import Mathlib
import Submission.MorsePerturb


-- @@ L4-11 verbatim
/-!
# Pairwise disjoint smooth cutoffs around finitely many interior centers

Distinct points in a finite subset of the ambient Euclidean space admit
pairwise disjoint open neighborhoods.  Intersecting those neighborhoods with
the open middle slab and shrinking to metric balls gives concrete smooth
cutoffs whose supports cannot interfere with another center's core.
-/


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
open Set Function Metric

-- @@ L16-16 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L18-18 verbatim
namespace Submission


-- @@ L20-20 verbatim
variable {n : ℕ}


-- @@ L22-22 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L24-36 verbatim
/-- A finite family of ball cutoffs, all supported in the middle slab and with
pairwise disjoint support balls. -/
structure FiniteDisjointMiddleCutoffs {ι : Type*} [Fintype ι]
    (center : ι → E') where
  radius : ι → ℝ
  radius_pos : ∀ i, 0 < radius i
  support_subset_middle : ∀ i,
    ball (center i) (radius i) ⊆
      tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ)
  pairwise_disjoint_support : Pairwise fun i j =>
    Disjoint (ball (center i) (radius i)) (ball (center j) (radius j))
  cutoff : ∀ i, SmoothCutoff
    (closedBall (center i) (radius i / 2)) (ball (center i) (radius i))


-- @@ L38-38 verbatim
namespace FiniteDisjointMiddleCutoffs


-- @@ L40-41 verbatim
variable {ι : Type*} [Fintype ι]
  {center : ι → EuclideanSpace ℝ (Fin (n + 2))}


-- @@ L43-51 verbatim
/-- Every point of a cutoff core lies in its open support ball. -/
theorem core_subset_support
    (D : FiniteDisjointMiddleCutoffs (n := n) center) (i : ι) :
    closedBall (center i) (D.radius i / 2) ⊆ ball (center i) (D.radius i) := by
  intro v hv
  rw [mem_closedBall] at hv
  rw [mem_ball]
  have hr := D.radius_pos i
  linarith


-- @@ L53-67 verbatim
/-- A different cutoff is zero throughout the current cutoff's core. -/
theorem cutoff_eq_zero_of_mem_core
    (D : FiniteDisjointMiddleCutoffs (n := n) center)
    (i : ι) {v : EuclideanSpace ℝ (Fin (n + 2))}
    (hv : v ∈ closedBall (center i) (D.radius i / 2))
    (j : ι) (hji : j ≠ i) :
    D.cutoff j v = 0 := by
  exact (D.cutoff j).eq_zero v (by
    intro hvj
    have hvi : v ∈ ball (center i) (D.radius i) :=
      D.core_subset_support i hv
    have hd : Disjoint (ball (center j) (D.radius j))
        (ball (center i) (D.radius i)) :=
      D.pairwise_disjoint_support hji
    exact Set.disjoint_left.1 hd hvj hvi)


-- @@ L69-79 verbatim
/-- Consequently any raw jet localized by another cutoff vanishes on this
core. -/
theorem localized_eq_zero_of_mem_core
    (D : FiniteDisjointMiddleCutoffs (n := n) center)
    (h : ι → EuclideanSpace ℝ (Fin (n + 2)) → ℝ)
    (i : ι) {v : EuclideanSpace ℝ (Fin (n + 2))}
    (hv : v ∈ closedBall (center i) (D.radius i / 2))
    (j : ι) (hji : j ≠ i) :
    (D.cutoff j).localize (h j) v = 0 := by
  rw [SmoothCutoff.localize, D.cutoff_eq_zero_of_mem_core i hv j hji]
  exact zero_mul _


-- @@ L81-92 verbatim
/-- Each localized jet has compact support and vanishes on both collars. -/
theorem localized_properties
    (D : FiniteDisjointMiddleCutoffs (n := n) center)
    (h : ι → EuclideanSpace ℝ (Fin (n + 2)) → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (h i)) (i : ι) :
    ContDiff ℝ ∞ ((D.cutoff i).localize (h i)) ∧
      HasCompactSupport ((D.cutoff i).localize (h i)) ∧
      (∀ v, tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v →
        (D.cutoff i).localize (h i) v = 0) :=
  ⟨(D.cutoff i).contDiff_localize (hsmooth i),
    (D.cutoff i).hasCompactSupport_localize (h i),
    (D.cutoff i).localize_collar_zero (D.support_subset_middle i) (h i)⟩


-- @@ L94-131 verbatim
/-- Existence of disjoint middle-slab cutoffs around any finite injective
family of interior centers. -/
theorem exists_of_injective_interior
    (center : ι → EuclideanSpace ℝ (Fin (n + 2)))
    (hinj : Injective center)
    (hinterior : ∀ i,
      1 / 4 < tcoord (center i) ∧ tcoord (center i) < 3 / 4) :
    Nonempty (FiniteDisjointMiddleCutoffs (n := n) center) := by
  classical
  let middle : Set (EuclideanSpace ℝ (Fin (n + 2))) :=
    tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ)
  have hmiddleOpen : IsOpen middle :=
    isOpen_Ioo.preimage contDiff_vertC.continuous
  have hcenterMiddle : ∀ i, center i ∈ middle := by
    intro i
    exact hinterior i
  obtain ⟨U, hU, hUdisjoint⟩ := (Set.finite_range center).t2_separation
  let V : ι → Set E' := fun i => U (center i) ∩ middle
  have hVopen : ∀ i, IsOpen (V i) := fun i => (hU (center i)).2.inter hmiddleOpen
  have hVmem : ∀ i, center i ∈ V i := fun i =>
    ⟨(hU (center i)).1, hcenterMiddle i⟩
  have hexRadius : ∀ i, ∃ r > 0, ball (center i) r ⊆ V i := by
    intro i
    exact Metric.isOpen_iff.1 (hVopen i) (center i) (hVmem i)
  choose r hr hball using hexRadius
  refine ⟨{
    radius := r
    radius_pos := hr
    support_subset_middle := fun i => (hball i).trans inter_subset_right
    pairwise_disjoint_support := ?_
    cutoff := fun i => (SmoothCutoff.exists_ball (center i) (hr i)).some
  }⟩
  intro i j hij
  have hcij : center i ≠ center j := fun h => hij (hinj h)
  have hdU : Disjoint (U (center i)) (U (center j)) :=
    hUdisjoint (mem_range_self i) (mem_range_self j) hcij
  exact hdU.mono ((hball i).trans inter_subset_left)
    ((hball j).trans inter_subset_left)


-- @@ L133-133 verbatim
end FiniteDisjointMiddleCutoffs


-- @@ L135-135 verbatim
end Submission
