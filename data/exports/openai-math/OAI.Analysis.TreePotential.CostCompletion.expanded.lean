import OAI.Analysis.TreePotential.Coordinates


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set

-- @@ L7-7 verbatim
open scoped ENNReal

-- @@ L8-8 verbatim
namespace BoundedTreePotentials


-- @@ L10-10 verbatim
namespace CostHeads

-- @@ L11-11 verbatim
open TreeCalculus BlockCalculus ForestCoordinates Filter Topology

-- @@ L12-12 verbatim
open scoped Classical


-- @@ L14-16 verbatim
lemma linear_coefficient_head (A : FiniteOuterHead) (x : LinearOuter) (s : ForestNode) :
    coefficient (fun n => linearBlockHilbertEquiv (n+1)) (linearOuterHead A.nodes A.initial x) s =
    if s.2.val ∈ A.nodes s.1 then coefficient (fun n => linearBlockHilbertEquiv (n+1)) x s else 0 := rfl


-- @@ L18-32 verbatim
lemma linear_head_eq_self_iff (A : FiniteOuterHead) (x : LinearOuter) :
    linearOuterHead A.nodes A.initial x = x ↔ ∀ s : ForestNode,
      s.2.val ∉ A.nodes s.1 → coefficient (fun n => linearBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => linearBlockHilbertEquiv (n+1)) z s) h
    rw [linear_coefficient_head, ite_eq_right hs] at he
    exact he.symm
  · intro h
    apply coefficient_ext (fun n => linearBlockHilbertEquiv (n+1))
    intro s
    rw [linear_coefficient_head]
    split_ifs with hs
    · rfl
    · exact (h s hs).symm


-- @@ L34-48 verbatim
lemma linear_head_eq_zero_iff (A : FiniteOuterHead) (x : LinearOuter) :
    linearOuterHead A.nodes A.initial x = 0 ↔ ∀ s : ForestNode,
      s.2.val ∈ A.nodes s.1 → coefficient (fun n => linearBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => linearBlockHilbertEquiv (n+1)) z s) h
    rw [linear_coefficient_head, ite_eq_left hs, coefficient_zero] at he
    exact he
  · intro h
    apply coefficient_ext (fun n => linearBlockHilbertEquiv (n+1))
    intro s
    rw [linear_coefficient_head, coefficient_zero]
    split_ifs with hs
    · exact h s hs
    · rfl


-- @@ L50-53 verbatim
lemma linear_finite_head_approx (x : LinearOuter) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : LinearOuter, ∃ A : FiniteOuterHead, ‖x-p‖ < ε ∧ linearOuterHead A.nodes A.initial p = p := by
  obtain ⟨p,A,hd,hp⟩ := exists_finite_head_approx (fun n => linearBlockHilbertEquiv (n+1)) x hε
  exact ⟨p,A,hd,(linear_head_eq_self_iff A p).mpr hp⟩


-- @@ L55-56 verbatim
def linearCoordinateTail (A : FiniteOuterHead) : ClosedFiniteCodim LinearOuter :=
  ForestCoordinates.coordinateTail (fun n => linearBlockHilbertEquiv (n+1)) A


-- @@ L58-61 verbatim
lemma mem_linearCoordinateTail (A : FiniteOuterHead) (x : LinearOuter) :
    x ∈ (linearCoordinateTail A).space ↔ linearOuterHead A.nodes A.initial x = 0 := by
  exact (ForestCoordinates.mem_coordinateTail (fun n => linearBlockHilbertEquiv (n+1)) A x).trans
    (linear_head_eq_zero_iff A x).symm


-- @@ L63-66 verbatim
lemma linear_head_ker (A : FiniteOuterHead) :
    (linearOuterHead A.nodes A.initial).ker = (linearCoordinateTail A).space := by
  ext x
  exact (mem_linearCoordinateTail A x).symm


-- @@ L68-74 verbatim
instance linear_head_finiteRank (A : FiniteOuterHead) :
    Module.Finite ℝ (linearOuterHead A.nodes A.initial).range := by
  have h : Module.Finite ℝ (LinearOuter ⧸ (linearOuterHead A.nodes A.initial).ker) := by
    rw [linear_head_ker]
    exact (linearCoordinateTail A).finiteCodim
  let := h
  exact Module.Finite.equiv (linearOuterHead A.nodes A.initial).toLinearMap.quotKerEquivRange


-- @@ L76-88 verbatim
lemma linear_head_weaklyNull {y : ℕ → LinearOuter} (hy : WeaklyNull y) (A : FiniteOuterHead) :
    Tendsto (fun j => ‖linearOuterHead A.nodes A.initial (y j)‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := hy.approximable (linearCoordinateTail A) hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N, ?_⟩
  intro j hj
  obtain ⟨w,hw,hd⟩ := hN j hj
  have hw0 := (mem_linearCoordinateTail A w).mp hw
  have hh := linearOuterHead_contract A.nodes A.initial (y j-w)
  rw [map_sub, hw0, sub_zero] at hh
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hh.trans_lt hd


-- @@ L90-92 verbatim
lemma quadratic_coefficient_head (A : FiniteOuterHead) (x : QuadraticOuter) (s : ForestNode) :
    coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) (quadraticOuterHead A.nodes A.initial x) s =
    if s.2.val ∈ A.nodes s.1 then coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) x s else 0 := rfl


-- @@ L94-108 verbatim
lemma quadratic_head_eq_self_iff (A : FiniteOuterHead) (x : QuadraticOuter) :
    quadraticOuterHead A.nodes A.initial x = x ↔ ∀ s : ForestNode,
      s.2.val ∉ A.nodes s.1 → coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) z s) h
    rw [quadratic_coefficient_head, ite_eq_right hs] at he
    exact he.symm
  · intro h
    apply coefficient_ext (fun n => quadraticBlockHilbertEquiv (n+1))
    intro s
    rw [quadratic_coefficient_head]
    split_ifs with hs
    · rfl
    · exact (h s hs).symm


-- @@ L110-124 verbatim
lemma quadratic_head_eq_zero_iff (A : FiniteOuterHead) (x : QuadraticOuter) :
    quadraticOuterHead A.nodes A.initial x = 0 ↔ ∀ s : ForestNode,
      s.2.val ∈ A.nodes s.1 → coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) z s) h
    rw [quadratic_coefficient_head, ite_eq_left hs, coefficient_zero] at he
    exact he
  · intro h
    apply coefficient_ext (fun n => quadraticBlockHilbertEquiv (n+1))
    intro s
    rw [quadratic_coefficient_head, coefficient_zero]
    split_ifs with hs
    · exact h s hs
    · rfl


-- @@ L126-129 verbatim
lemma quadratic_finite_head_approx (x : QuadraticOuter) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : QuadraticOuter, ∃ A : FiniteOuterHead, ‖x-p‖ < ε ∧ quadraticOuterHead A.nodes A.initial p = p := by
  obtain ⟨p,A,hd,hp⟩ := exists_finite_head_approx (fun n => quadraticBlockHilbertEquiv (n+1)) x hε
  exact ⟨p,A,hd,(quadratic_head_eq_self_iff A p).mpr hp⟩


-- @@ L131-132 verbatim
def quadraticCoordinateTail (A : FiniteOuterHead) : ClosedFiniteCodim QuadraticOuter :=
  ForestCoordinates.coordinateTail (fun n => quadraticBlockHilbertEquiv (n+1)) A


-- @@ L134-137 verbatim
lemma mem_quadraticCoordinateTail (A : FiniteOuterHead) (x : QuadraticOuter) :
    x ∈ (quadraticCoordinateTail A).space ↔ quadraticOuterHead A.nodes A.initial x = 0 := by
  exact (ForestCoordinates.mem_coordinateTail (fun n => quadraticBlockHilbertEquiv (n+1)) A x).trans
    (quadratic_head_eq_zero_iff A x).symm


-- @@ L139-142 verbatim
lemma quadratic_head_ker (A : FiniteOuterHead) :
    (quadraticOuterHead A.nodes A.initial).ker = (quadraticCoordinateTail A).space := by
  ext x
  exact (mem_quadraticCoordinateTail A x).symm


-- @@ L144-150 verbatim
instance quadratic_head_finiteRank (A : FiniteOuterHead) :
    Module.Finite ℝ (quadraticOuterHead A.nodes A.initial).range := by
  have h : Module.Finite ℝ (QuadraticOuter ⧸ (quadraticOuterHead A.nodes A.initial).ker) := by
    rw [quadratic_head_ker]
    exact (quadraticCoordinateTail A).finiteCodim
  let := h
  exact Module.Finite.equiv (quadraticOuterHead A.nodes A.initial).toLinearMap.quotKerEquivRange


-- @@ L152-164 verbatim
lemma quadratic_head_weaklyNull {y : ℕ → QuadraticOuter} (hy : WeaklyNull y) (A : FiniteOuterHead) :
    Tendsto (fun j => ‖quadraticOuterHead A.nodes A.initial (y j)‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := hy.approximable (quadraticCoordinateTail A) hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N, ?_⟩
  intro j hj
  obtain ⟨w,hw,hd⟩ := hN j hj
  have hw0 := (mem_quadraticCoordinateTail A w).mp hw
  have hh := quadraticOuterHead_contract A.nodes A.initial (y j-w)
  rw [map_sub, hw0, sub_zero] at hh
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hh.trans_lt hd


-- @@ L166-166 verbatim
end CostHeads


-- @@ L168-177 verbatim
lemma sqrt_shift {r R d c : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hc : 0 ≤ c) (hh : r ≤ R+d) :
    Real.sqrt (r^2+c) ≤ Real.sqrt (R^2+c)+d := by
  have hs := Real.sq_sqrt (show 0 ≤ R^2+c by positivity)
  have hn := Real.sqrt_nonneg (R^2+c)
  have hRT : R ≤ Real.sqrt (R^2+c) := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hrhs : r^2 ≤ (R+d)^2 := by nlinarith [mul_nonneg (show 0 ≤ R+d-r by linarith) (show 0 ≤ R+d+r by positivity)]
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hRT)]


-- @@ L179-179 verbatim
section FiniteRankCompactness

-- @@ L180-180 verbatim
open Filter Topology

-- @@ L181-182 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L184-203 verbatim
lemma finiteRank_close_pair (P : E →L[ℝ] F) [Module.Finite ℝ P.range]
    (y : ℕ → E) {R ε : ℝ} (hR : ∀ j, ‖y j‖ ≤ R) (hε : 0 < ε) :
    ∃ i j : ℕ, i ≠ j ∧ ‖P (y i)-P (y j)‖ < ε := by
  let z : ℕ → P.range := fun j => ⟨P (y j), ⟨y j,rfl⟩⟩
  have hz : ∀ j, z j ∈ Metric.closedBall (0 : P.range) (‖P‖*R) := by
    intro j
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hR j) (norm_nonneg P))
  obtain ⟨a,ha,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : P.range) (‖P‖*R)).tendsto_subseq hz
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (by positivity)
  refine ⟨φ N, φ (N+1), (hφ (Nat.lt_succ_self N)).ne, ?_⟩
  have h1 := hN N le_rfl
  have h2 := hN (N+1) (Nat.le_succ N)
  have ht := dist_triangle (z (φ N)) a (z (φ (N+1)))
  rw [dist_comm a] at ht
  rw [dist_eq_norm] at ht
  change ‖P (y (φ N))-P (y (φ (N+1)))‖ ≤ _ at ht
  change dist (z (φ N)) a < ε/2 at h1
  change dist (z (φ (N+1))) a < ε/2 at h2
  linarith


-- @@ L205-205 verbatim
end FiniteRankCompactness


-- @@ L207-207 verbatim
namespace CostHeads

-- @@ L208-208 verbatim
open TreeCalculus BlockCalculus ForestCoordinates Filter Topology

-- @@ L209-209 verbatim
open scoped Classical


-- @@ L211-236 verbatim
/-- Transfer from finite centers to arbitrary completed centers, uniformly on
an entire closed finite-codimensional tail. -/
theorem linear_completed_tail_bound (x : LinearOuter) (hx : ‖x‖ = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ F : ClosedFiniteCodim LinearOuter, ∀ y, y ∈ F.space → 1 ≤ ‖y‖ →
      Real.sqrt (1+t^2/16)-1-ε ≤ (‖x+t • y‖+‖x-t • y‖)/2-1 := by
  obtain ⟨p,A,hp,hA⟩ := linear_finite_head_approx x (show 0 < ε/2 by positivity)
  refine ⟨linearCoordinateTail A, ?_⟩
  intro y hy hyn
  have hy0 := (mem_linearCoordinateTail A y).mp hy
  have he := linearOuter_midpoint A.nodes A.initial p (t • y) hA
  rw [map_smul, hy0, smul_zero, sub_zero, norm_smul, Real.norm_of_nonneg ht.le] at he
  have hnorm : 1 ≤ ‖p‖+‖x-p‖ := by
    have hh := norm_sub_norm_le x p
    rw [hx] at hh
    linarith
  have hs := sqrt_shift zero_le_one (norm_nonneg p) (norm_nonneg (x-p))
    (show 0 ≤ t^2/16 by positivity) hnorm
  norm_num only [one_pow] at hs
  have hyb : Real.sqrt (‖p‖^2+t^2/16) ≤ Real.sqrt (‖p‖^2+(t*‖y‖)^2/16) := by
    apply Real.sqrt_le_sqrt
    have hh : t ≤ t*‖y‖ := by nlinarith
    nlinarith [norm_nonneg y]
  have hppert := midpoint_center_perturbation x p y t
  rw [norm_sub_rev p x] at hppert
  linarith


-- @@ L238-242 verbatim
theorem linear_averaged_modulus {t : ℝ} (ht : 0 < t) :
    ((Real.sqrt (1+t^2/16)-1 : ℝ) : EReal) ≤ averagedModulus LinearOuter t := by
  apply averagedModulus_lower_bound
  intro x hx ε hε
  exact linear_completed_tail_bound x hx ht hε


-- @@ L244-269 verbatim
/-- Transfer from finite centers to arbitrary completed centers, uniformly on
an entire closed finite-codimensional tail. -/
theorem quadratic_completed_tail_bound (x : QuadraticOuter) (hx : ‖x‖ = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ F : ClosedFiniteCodim QuadraticOuter, ∀ y, y ∈ F.space → 1 ≤ ‖y‖ →
      Real.sqrt (1+t^2/16)-1-ε ≤ (‖x+t • y‖+‖x-t • y‖)/2-1 := by
  obtain ⟨p,A,hp,hA⟩ := quadratic_finite_head_approx x (show 0 < ε/2 by positivity)
  refine ⟨quadraticCoordinateTail A, ?_⟩
  intro y hy hyn
  have hy0 := (mem_quadraticCoordinateTail A y).mp hy
  have he := quadraticOuter_midpoint A.nodes A.initial p (t • y) hA
  rw [map_smul, hy0, smul_zero, sub_zero, norm_smul, Real.norm_of_nonneg ht.le] at he
  have hnorm : 1 ≤ ‖p‖+‖x-p‖ := by
    have hh := norm_sub_norm_le x p
    rw [hx] at hh
    linarith
  have hs := sqrt_shift zero_le_one (norm_nonneg p) (norm_nonneg (x-p))
    (show 0 ≤ t^2/16 by positivity) hnorm
  norm_num only [one_pow] at hs
  have hyb : Real.sqrt (‖p‖^2+t^2/16) ≤ Real.sqrt (‖p‖^2+(t*‖y‖)^2/16) := by
    apply Real.sqrt_le_sqrt
    have hh : t ≤ t*‖y‖ := by nlinarith
    nlinarith [norm_nonneg y]
  have hppert := midpoint_center_perturbation x p y t
  rw [norm_sub_rev p x] at hppert
  linarith


-- @@ L271-275 verbatim
theorem quadratic_averaged_modulus {t : ℝ} (ht : 0 < t) :
    ((Real.sqrt (1+t^2/16)-1 : ℝ) : EReal) ≤ averagedModulus QuadraticOuter t := by
  apply averagedModulus_lower_bound
  intro x hx ε hε
  exact quadratic_completed_tail_bound x hx ht hε


-- @@ L277-277 verbatim
end CostHeads



-- @@ L280-280 verbatim
end BoundedTreePotentials


-- @@ L282-282 verbatim
end


-- @@ L284-284 verbatim
end OAI
