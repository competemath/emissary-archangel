import OAI.Analysis.SegmentLenses.TreeGeometry


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-7 verbatim
/-!
# Finite probability laws and joint square-root budgets
-/


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open Finset


-- @@ L14-14 verbatim
namespace SegmentLenses





-- @@ L19-31 verbatim
theorem joint_sqrt_bound {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 ≤ θ) :
    Real.sqrt η + Real.sqrt (η + 2 * θ) ≤ 2 * Real.sqrt (η + θ) := by
  have hηθ : 0 ≤ η + θ := by positivity
  have hη2θ : 0 ≤ η + 2 * θ := by positivity
  have h0 := Real.sqrt_nonneg η
  have h1 := Real.sqrt_nonneg (η + 2 * θ)
  have h2 := Real.sqrt_nonneg (η + θ)
  have hs0 := Real.sq_sqrt hη
  have hs1 := Real.sq_sqrt hη2θ
  have hs2 := Real.sq_sqrt hηθ
  have hprod : Real.sqrt η * Real.sqrt (η + 2 * θ) ≤ η + θ := by
    nlinarith [sq_nonneg (Real.sqrt (η + 2 * θ) - Real.sqrt η)]
  nlinarith



-- @@ L34-43 verbatim
theorem joint_budget_tail {η θ R r t : ℝ}
    (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    (hbudget : η + θ ≤ R ^ 2 - r ^ 2)
    (htail : t ≤ Real.sqrt η + Real.sqrt (η + 2 * θ)) :
    t ≤ 2 * Real.sqrt (R ^ 2 - r ^ 2) := by
  calc
    t ≤ Real.sqrt η + Real.sqrt (η + 2 * θ) := htail
    _ ≤ 2 * Real.sqrt (η + θ) := joint_sqrt_bound hη hθ
    _ ≤ 2 * Real.sqrt (R ^ 2 - r ^ 2) := by
      gcongr



-- @@ L46-49 verbatim
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1


-- @@ L51-51 verbatim
namespace FiniteLaw

-- @@ L52-52 verbatim
variable {Ω : Type*} [Fintype Ω]


-- @@ L54-54 verbatim
def mean (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω


-- @@ L56-57 verbatim
@[simp] theorem mean_const (μ : FiniteLaw Ω) (c : ℝ) : μ.mean (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, μ.total]


-- @@ L59-61 verbatim
@[simp] theorem mean_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.mean (fun ω => f ω + g ω) = μ.mean f + μ.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]


-- @@ L63-65 verbatim
@[simp] theorem mean_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.mean (fun ω => f ω - g ω) = μ.mean f - μ.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]


-- @@ L67-69 verbatim
@[simp] theorem mean_mul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.mean (fun ω => c * f ω) = c * μ.mean f := by
  simp [mean, Finset.mul_sum, mul_left_comm]


-- @@ L71-72 verbatim
theorem mean_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.mean f := Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω)


-- @@ L74-76 verbatim
theorem mean_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.mean f ≤ μ.mean g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω)



-- @@ L79-91 verbatim
theorem sq_mean_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.mean f ^ 2 ≤ μ.mean (fun ω => f ω ^ 2) := by
  have h := μ.mean_nonneg (fun ω => sq_nonneg (f ω - μ.mean f))
  have he : μ.mean (fun ω => (f ω - μ.mean f) ^ 2) =
      μ.mean (fun ω => f ω ^ 2) - μ.mean f ^ 2 := by
    have hfun : (fun ω => (f ω - μ.mean f) ^ 2) =
        fun ω => f ω ^ 2 - (2 * μ.mean f) * f ω + μ.mean f ^ 2 := by
      funext ω
      ring
    rw [hfun, mean_add, mean_sub, mean_mul, mean_const]
    ring
  rw [he] at h
  linarith





-- @@ L96-112 verbatim
theorem joint_identity (μ : FiniteLaw Ω) {ι : Ω → Type*}
    [∀ ω, Fintype (ι ω)] (a b : (ω : Ω) → ι ω → ℝ) (r : ℝ)
    (hpair : μ.mean (fun ω => ∑ i, a ω i * b ω i) = r ^ 2) :
    μ.mean (fun ω => ∑ i, (a ω i - b ω i) ^ 2) +
      μ.mean (fun ω => r ^ 2 - ∑ i, b ω i ^ 2) =
      μ.mean (fun ω => ∑ i, a ω i ^ 2) - r ^ 2 := by
  rw [← mean_add]
  have he : (fun ω => (∑ i, (a ω i - b ω i) ^ 2) +
        (r ^ 2 - ∑ i, b ω i ^ 2)) =
      fun ω => (∑ i, a ω i ^ 2) - 2 * (∑ i, a ω i * b ω i) + r ^ 2 := by
    funext ω
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring
  rw [he, mean_add, mean_sub, mean_mul, mean_const, hpair]
  ring


-- @@ L114-114 verbatim
end FiniteLaw




-- @@ L118-118 verbatim
end SegmentLenses



-- @@ L121-121 verbatim
end


-- @@ L123-123 verbatim
end OAI
