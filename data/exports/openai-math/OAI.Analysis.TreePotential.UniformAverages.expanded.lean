import OAI.Analysis.TreePotential.NormIdentities


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
namespace BoundedTreePotentials.CostHeads


-- @@ L13-24 verbatim
/-- The optimized square-root clipping bound. -/
theorem linear_head_tail_clipping_optimized (A : FiniteOuterHead) (x y : LinearOuter)
    (hx : linearOuterHead A.nodes A.initial x=x)
    (hy : linearOuterHead A.nodes A.initial y=0) :
    Real.sqrt (‖x‖^2+‖y‖^2/16) ≤ max ‖x+y‖ ‖x-y‖ := by
  have he := linearOuter_midpoint_sq A.nodes A.initial x y hx
  rw [hy,sub_zero] at he
  have hh := scalar_avg_sq_le (norm_nonneg (x+y)) (norm_nonneg (x-y))
    (le_max_left ‖x+y‖ ‖x-y‖) (le_max_right ‖x+y‖ ‖x-y‖)
  have hs := Real.sq_sqrt (show 0≤‖x‖^2+‖y‖^2/16 by positivity)
  have hn : 0 ≤ max ‖x+y‖ ‖x-y‖ := (norm_nonneg (x+y)).trans (le_max_left _ _)
  nlinarith [Real.sqrt_nonneg (‖x‖^2+‖y‖^2/16)]


-- @@ L26-26 verbatim
end BoundedTreePotentials.CostHeads


-- @@ L28-28 verbatim
namespace BoundedTreePotentials.Dyadic


-- @@ L30-30 verbatim
section


-- @@ L32-35 verbatim
lemma histories_length (k : ℕ) : (histories k).length=2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [histories,List.length_flatMap,ih,pow_succ]


-- @@ L37-37 verbatim
variable {E : Type*} [AddCommGroup E] [Module ℝ E]


-- @@ L39-40 verbatim
def uniformVectorAverage (k : ℕ) (f : List Bool → E) : E :=
  ((2:ℝ)^k)⁻¹ • ((histories k).map f).sum


-- @@ L42-56 verbatim
lemma uniformVectorAverage_succ (k : ℕ) (f : List Bool → E) :
    uniformVectorAverage (k+1) f=
      uniformVectorAverage k (fun w => (1/2:ℝ) • (f (false::w)+f (true::w))) := by
  have he (l : List (List Bool)) :
      ((l.flatMap (fun w => [false::w,true::w])).map f).sum =
      (2:ℝ) • ((l.map (fun w => (1/2:ℝ) • (f (false::w)+f (true::w)))).sum) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,
        List.map_nil,List.sum_cons,List.sum_nil,add_zero,ih]
      module
  simp only [uniformVectorAverage,histories,he,pow_succ,mul_inv_rev,smul_smul]
  congr 1
  ring


-- @@ L58-67 verbatim
/-- An explicit average with exactly 2^k equally weighted future branches. -/
theorem conditionalMean_eq_uniform (W : List Bool → E) (k : ℕ) (w : List Bool) :
    conditionalMean W k w=
      ((2:ℝ)^k)⁻¹ • (((histories k).map (fun v => W (v++w))).sum) := by
  change conditionalMean W k w=uniformVectorAverage k (fun v => W (v++w))
  induction k generalizing W w with
  | zero => simp [uniformVectorAverage,histories,conditionalMean]
  | succ k ih =>
    rw [conditionalMean_succ_front,ih,uniformVectorAverage_succ]
    rfl


-- @@ L69-69 verbatim
end


-- @@ L71-78 verbatim
lemma histories_nodup (k : ℕ) : (histories k).Nodup := by
  induction k with
  | zero => simp [histories]
  | succ k ih =>
    rw [histories,List.nodup_flatMap]
    refine ⟨fun w _ => by simp,ih.imp ?_⟩
    intro a b hab
    simp [Function.onFun,List.disjoint_left,hab]

-- @@ L79-79 verbatim
end BoundedTreePotentials.Dyadic


-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
end OAI
