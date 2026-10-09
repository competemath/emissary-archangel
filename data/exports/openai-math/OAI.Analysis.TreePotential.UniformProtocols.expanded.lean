import OAI.Analysis.TreePotential.EndpointTransfer


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set

-- @@ L7-7 verbatim
open scoped ENNReal

-- @@ L8-8 verbatim
open Set Filter Topology

-- @@ L9-9 verbatim
open scoped Classical


-- @@ L11-11 verbatim
namespace BoundedTreePotentials.BlockCalculus

-- @@ L12-12 verbatim
open TreeCalculus


-- @@ L14-24 verbatim
/-- Component trimming with constant 242. Empty heads and roots use the same literal
coordinate projection as in the outer sum. -/

theorem linear_block_trimming_242 {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x=x) (hy : head D y=0) :
    (linearBlockCost n y)^2≤242*((linearBlockCost n (x+y))^2+
      (linearBlockCost n (x-y))^2-2*(linearBlockCost n x)^2) := by
  have hh := linear_block_midpoint_sq hD x y hx
  rw [hy,sub_zero] at hh
  have he := scalar_midpoint_energy hh
  nlinarith [sq_nonneg (linearBlockCost n y)]


-- @@ L26-26 verbatim
end BoundedTreePotentials.BlockCalculus


-- @@ L28-28 verbatim
namespace BoundedTreePotentials.CostHeads

-- @@ L29-29 verbatim
open _root_.OAI.BoundedTreePotentials.Dyadic


-- @@ L31-39 verbatim
/-- The variation-energy estimate for terminal bound 2. -/
theorem linear_variation_energy_1008 {m : ℕ} {W : List Bool → LinearOuter}
    {P : List Bool → FiniteOuterHead} (hW : IsMartingale m W)
    (hP : PredictableLinearHeads m W P)
    (hC : ∀ w,w.length=m → ‖W w‖≤2) :
    (∑ i ∈ Finset.range m,average (i+1) (fun w => ‖linearLayer P W w‖^2))≤1008 := by
  have hh := linear_variation_energy_252 hW hP hC
  norm_num at hh
  exact hh


-- @@ L41-41 verbatim
end BoundedTreePotentials.CostHeads


-- @@ L43-43 verbatim
namespace BoundedTreePotentials.Dyadic

-- @@ L44-44 verbatim
section ConditionalAverages

-- @@ L45-45 verbatim
variable {E : Type*} [AddCommGroup E] [Module ℝ E]


-- @@ L47-51 verbatim
/-- Exact finite conditional expectation over k future fair bits. Histories
are chronological from the right, as in the energy theorems. -/
def conditionalMean (W : List Bool → E) : ℕ → List Bool → E
  | 0,w => W w
  | k+1,w => (1/2 : ℝ) • (conditionalMean W k (false::w)+conditionalMean W k (true::w))


-- @@ L53-59 verbatim
lemma conditionalMean_succ_front (W : List Bool → E) (k : ℕ) (w : List Bool) :
    conditionalMean W (k+1) w=
      conditionalMean (fun v => (1/2:ℝ) • (W (false::v)+W (true::v))) k w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    exact congrArg ((1/2 : ℝ) • ·) (congrArg₂ (·+·) (ih (false::w)) (ih (true::w)))


-- @@ L61-70 verbatim
/-- The local dyadic martingale identity is exactly the assertion that each
value is its finite conditional terminal average. -/
lemma martingale_conditionalMean {m : ℕ} {W : List Bool → E} (hW : IsMartingale m W)
    (k : ℕ) (w : List Bool) (hw : w.length+k≤ m) : conditionalMean W k w=W w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [conditionalMean,ih (false::w) (by simp only [List.length_cons]; omega),
      ih (true::w) (by simp only [List.length_cons]; omega)]
    exact (hW w (by omega)).symm


-- @@ L72-83 verbatim
lemma isMartingale_iff_terminal_averages (m : ℕ) (W : List Bool → E) :
    IsMartingale m W ↔ ∀ w,w.length≤ m → W w=conditionalMean W (m-w.length) w := by
  constructor
  · intro h w hw
    exact (martingale_conditionalMean h _ _ (by omega)).symm
  · intro h w hw
    have he : m-w.length=(m-(w.length+1))+1 := by omega
    rw [h w hw.le,he,conditionalMean]
    have hf := h (false::w) (by simp only [List.length_cons]; omega)
    have ht := h (true::w) (by simp only [List.length_cons]; omega)
    simp only [List.length_cons] at hf ht
    rw [← hf,← ht]


-- @@ L85-85 verbatim
end ConditionalAverages


-- @@ L87-96 verbatim
lemma conditionalMean_eq_average (W : List Bool → ℝ) (k : ℕ) :
    conditionalMean W k []=average k W := by
  induction k generalizing W with
  | zero => simp only [conditionalMean,average_zero]
  | succ k ih =>
    rw [conditionalMean_succ_front,ih,average_succ]
    congr 1
    funext w
    simp only [smul_eq_mul]
    ring


-- @@ L98-98 verbatim
end BoundedTreePotentials.Dyadic


-- @@ L100-100 verbatim
end


-- @@ L102-102 verbatim
end OAI
