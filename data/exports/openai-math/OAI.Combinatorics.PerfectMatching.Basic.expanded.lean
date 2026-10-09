import OAI.Combinatorics.PerfectMatching.Model
import OAI.Combinatorics.PerfectMatching.Simplex


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-10 verbatim
/-!
Finite loopless multigraphs, perfect matching indicators, and their convex hull.
The edge type distinguishes parallel edges. Feasible laws are probability vectors
on perfect matchings with a prescribed mean.
-/


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
open scoped BigOperators Topology

-- @@ L15-15 verbatim
open Filter


-- @@ L17-17 verbatim
namespace MatchingEntropy


-- @@ L19-19 verbatim
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]


-- @@ L21-21 verbatim
namespace LooplessGraph


-- @@ L23-24 verbatim
instance incidentDecidable (G : LooplessGraph V E) (v : V) (e : E) :
    Decidable (G.Incident v e) := inferInstanceAs (Decidable (G.left e = v ∨ G.right e = v))


-- @@ L26-27 verbatim
def indicator (G : LooplessGraph V E) (M : G.Matching) (e : E) : ℝ :=
  if e ∈ M.val then 1 else 0


-- @@ L29-30 verbatim
def polytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  convexHull ℝ (Set.range G.indicator)


-- @@ L32-33 verbatim
def mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (e : E) : ℝ :=
  ∑ M, p M * G.indicator M e


-- @@ L35-36 verbatim
def feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) : Set (G.Matching → ℝ) :=
  {p | p ∈ probabilitySimplex G.Matching ∧ G.mean p = y}


-- @@ L38-42 verbatim
omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_nonneg (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    0 ≤ G.indicator M e := by
  simp only [indicator]
  split <;> norm_num


-- @@ L44-48 verbatim
omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_le_one (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    G.indicator M e ≤ 1 := by
  simp only [indicator]
  split <;> norm_num


-- @@ L50-53 verbatim
omit [Fintype V] [DecidableEq V] in
theorem continuous_mean (G : LooplessGraph V E) : Continuous G.mean := by
  unfold mean
  fun_prop


-- @@ L55-62 verbatim
def meanLinear (G : LooplessGraph V E) : (G.Matching → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := G.mean
  map_add' p q := by
    ext e
    simp [mean, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by
    ext e
    simp [mean, mul_assoc, Finset.mul_sum]


-- @@ L64-73 verbatim
omit [Fintype V] [DecidableEq V] in
theorem mean_mem_polytope (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) : G.mean p ∈ G.polytope := by
  have h := (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
    (fun M _ ↦ hp.1 M) hp.2 (fun M _ ↦ subset_convexHull ℝ _ (Set.mem_range_self M))
  have he : G.mean p = ∑ M, p M • G.indicator M := by
    ext e
    simp [mean]
  rw [he]
  exact h


-- @@ L75-80 verbatim
omit [Fintype V] [DecidableEq V] in
@[simp] theorem mean_single (G : LooplessGraph V E) (M : G.Matching) :
    G.mean (Pi.single M 1) = G.indicator M := by
  classical
  ext e
  simp [mean, Pi.single_apply, ite_mul]


-- @@ L82-97 verbatim
omit [Fintype V] [DecidableEq V] in
/-- Exact equivalence between the convex hull of matching indicators and feasible finite laws. -/
theorem mem_polytope_iff (G : LooplessGraph V E) (y : E → ℝ) :
    y ∈ G.polytope ↔ (G.feasibleLaws y).Nonempty := by
  classical
  constructor
  · intro hy
    have hc : Convex ℝ (G.mean '' probabilitySimplex G.Matching) :=
      (convex_probabilitySimplex G.Matching).linear_image G.meanLinear
    have hs : Set.range G.indicator ⊆ G.mean '' probabilitySimplex G.Matching := by
      rintro _ ⟨M, rfl⟩
      exact ⟨Pi.single M 1, single_mem_probabilitySimplex M, G.mean_single M⟩
    obtain ⟨p, hp, rfl⟩ := convexHull_min hs hc hy
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact G.mean_mem_polytope hp


-- @@ L99-103 verbatim
omit [Fintype V] [DecidableEq V] in
theorem compact_feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) :
    IsCompact (G.feasibleLaws y) := by
  exact (isCompact_probabilitySimplex G.Matching).inter_right
    (isClosed_eq G.continuous_mean continuous_const)


-- @@ L105-112 verbatim
omit [Fintype V] [DecidableEq V] in
theorem compact_polytope (G : LooplessGraph V E) : IsCompact G.polytope := by
  have heq : G.polytope = G.mean '' probabilitySimplex G.Matching := by
    ext y
    rw [G.mem_polytope_iff]
    rfl
  rw [heq]
  exact (isCompact_probabilitySimplex G.Matching).image G.continuous_mean



-- @@ L115-115 verbatim
end LooplessGraph


-- @@ L117-117 verbatim
end MatchingEntropy


-- @@ L119-119 verbatim
end


-- @@ L121-121 verbatim
end OAI
