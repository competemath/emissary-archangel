import Mathlib
import Submission.MorseSharedAffineHeight
import Submission.FiniteIFTSurfaceCover


-- @@ L5-13 verbatim
/-!
# One shared Morse covector for a finite IFT cover

The ambient covector is updated one chart at a time.  Sard supplies an
arbitrarily small chart tilt for the current chart, while compact openness of
the Morse jet preserves every chart core processed earlier.  Finite induction
therefore produces one genuinely shared ambient covector which is Morse-good
on every compact core, and it can be kept inside any prescribed ball.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function Filter Metric

-- @@ L18-18 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
variable {n : ℕ}


-- @@ L24-24 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L25-25 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L26-26 verbatim
local notation "Cov" => E' →L[ℝ] ℝ


-- @@ L28-28 verbatim
namespace FiniteIFTSurfaceCover


-- @@ L30-30 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]


-- @@ L32-36 verbatim
/-- One ambient covector is Morse-good on every compact chart core indexed by
`s`. -/
def SharedAffineMorseOnIndices (B : FiniteIFTSurfaceCover C ι)
    (A : Cov) (s : Finset ι) : Prop :=
  ∀ i ∈ s, (B.chart i).SharedAffineMorseOn A (B.core i)


-- @@ L38-78 verbatim
/-- One sequential Sard step: process chart `i`, retaining all earlier compact
cores and staying in the prescribed open neighborhood of the current ambient
covector. -/
theorem exists_sharedAffineMorse_update
    (B : FiniteIFTSurfaceCover C ι) (s : Finset ι) (i : ι)
    (A : Cov) (hs : B.SharedAffineMorseOnIndices A s)
    {U : Set Cov} (hU : IsOpen U) (hAU : A ∈ U) :
    ∃ A' ∈ U,
      (B.chart i).SharedAffineMorseOn A' (B.core i) ∧
      B.SharedAffineMorseOnIndices A' s := by
  have hprevious :
      ∀ᶠ A' in 𝓝 A, B.SharedAffineMorseOnIndices A' s := by
    change ∀ᶠ A' in 𝓝 A, ∀ j ∈ s,
      (B.chart j).SharedAffineMorseOn A' (B.core j)
    rw [eventually_all_finset]
    intro j hj
    exact (B.chart j).eventually_sharedAffineMorseOn
      (B.compact_core j) A (hs j hj)
  have hstay : ∀ᶠ A' in 𝓝 A, A' ∈ U := hU.mem_nhds hAU
  have hgood :
      ∀ᶠ A' in 𝓝 A,
        A' ∈ U ∧ B.SharedAffineMorseOnIndices A' s :=
    hstay.and hprevious
  let update : E₂ → Cov := (B.chart i).updateSharedCovector A
  have hupdate : Tendsto update (𝓝 0) (𝓝 A) := by
    have hcont : ContinuousAt update 0 :=
      ((B.chart i).continuous_updateSharedCovector A).continuousAt
    rw [← (B.chart i).updateSharedCovector_zero A]
    exact hcont
  have hpre :
      {q | update q ∈ U ∧ B.SharedAffineMorseOnIndices (update q) s} ∈
        𝓝 (0 : E₂) :=
    hupdate hgood
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨q, hqball, hqreg⟩ :=
    exists_small_regular_chartGradient
      ((B.chart i).contDiff_sharedAffineHeight A) hδ
  have hpreserved := hball hqball
  refine ⟨update q, hpreserved.1, ?_, hpreserved.2⟩
  exact (B.chart i).sharedAffineMorseOn_update_of_regularValue
    (B.domain_open i) A q hqreg (B.core_subset_domain i)


-- @@ L80-110 verbatim
/-- Every ball about zero contains one ambient covector whose shared affine
height is Morse-good on all compact cores of the finite IFT cover. -/
theorem exists_sharedAffineMorseCovector_in_ball
    (B : FiniteIFTSurfaceCover C ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ ball (0 : Cov) ε,
      ∀ i, (B.chart i).SharedAffineMorseOn A (B.core i) := by
  classical
  have hind : ∀ s : Finset ι,
      ∃ A ∈ ball (0 : Cov) ε, B.SharedAffineMorseOnIndices A s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨0, ?_, ?_⟩
        · simpa using hε
        · intro i hi
          simp at hi
    | @insert i s hi ih =>
        obtain ⟨A, hAball, hAs⟩ := ih
        obtain ⟨A', hA'ball, hAi, hA's⟩ :=
          B.exists_sharedAffineMorse_update s i A hAs
            Metric.isOpen_ball hAball
        refine ⟨A', hA'ball, ?_⟩
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact hAi
        · exact hA's j hj
  obtain ⟨A, hAball, hAall⟩ := hind Finset.univ
  refine ⟨A, hAball, ?_⟩
  intro i
  exact hAall i (Finset.mem_univ i)


-- @@ L112-120 verbatim
/-- Neighborhood form of the finite sequential construction. -/
theorem exists_sharedAffineMorseCovector_mem_nhds
    (B : FiniteIFTSurfaceCover C ι) {V : Set Cov}
    (hV : V ∈ 𝓝 (0 : Cov)) :
    ∃ A ∈ V, ∀ i, (B.chart i).SharedAffineMorseOn A (B.core i) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨A, hA, hMorse⟩ :=
    B.exists_sharedAffineMorseCovector_in_ball hε
  exact ⟨A, hball hA, hMorse⟩


-- @@ L122-122 verbatim
end FiniteIFTSurfaceCover


-- @@ L124-124 verbatim
end Submission
