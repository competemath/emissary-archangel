import OAI.Combinatorics.ExpectationThreshold.Basic
import OAI.Combinatorics.ExpectationThreshold.ProbabilitySubsetProduct
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-15 verbatim
/-!
# The upper expectation bound for rounding

The score sums over nonempty subsets of the original ground set. Its moments
come from the actual coordinate product law. Nonemptiness saves a factor of
one fifth in the fractional-cover cost.
-/


-- @@ L17-17 verbatim
open scoped BigOperators


-- @@ L19-19 verbatim
namespace TalagrandThreshold


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L25-27 verbatim
/-- The nonnegative subset-product score used by the rounding argument. -/
def productScore (g : Finset α → ℝ) (Y : α → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)), g S * ∏ x ∈ S, Y x


-- @@ L29-32 verbatim
theorem productScore_nonneg {g : Finset α → ℝ} {Y : α → ℝ}
    (hg : ∀ S, 0 ≤ g S) (hY : ∀ x, 0 ≤ Y x) : 0 ≤ productScore g Y := by
  exact Finset.sum_nonneg fun S _ =>
    mul_nonneg (hg S) (Finset.prod_nonneg fun x _ => hY x)


-- @@ L34-34 verbatim
variable {Ω : Type*} [Fintype Ω]


-- @@ L36-53 verbatim
/-- Independence of the coordinates gives the full subset-product expectation. -/
theorem expectation_productScore (ν : FiniteLaw Ω) (g : Finset α → ℝ) (Y : Ω → ℝ) :
    (FiniteLaw.pi (fun _ : α => ν)).expectation
        (fun ω => productScore g (fun x => Y (ω x))) =
      ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
        g S * (ν.expectation Y) ^ S.card := by
  classical
  calc
    _ = ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
        (FiniteLaw.pi (fun _ : α => ν)).expectation
          (fun ω => g S * ∏ x ∈ S, Y (ω x)) := by
      unfold FiniteLaw.expectation productScore
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      rw [FiniteLaw.expectation_smul, FiniteLaw.expectation_pi_subset_product_const]


-- @@ L55-65 verbatim
/-- A nonempty product gains at least one factor of one fifth. -/
theorem one_fifth_pow_le {r : ℝ} (hr : 0 ≤ r) {k : ℕ} (hk : 0 < k) :
    (r / 5) ^ k ≤ (1 / 5) * r ^ k := by
  have hsmall : (1 / 5 : ℝ) ^ k ≤ 1 / 5 :=
    pow_le_of_le_one (by norm_num) (by norm_num) (Nat.ne_of_gt hk)
  calc
    (r / 5) ^ k = (1 / 5 : ℝ) ^ k * r ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ (1 / 5) * r ^ k := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hr k)


-- @@ L67-99 verbatim
/-- The product score costs at most one fifth of the fractional-cover cost. -/
theorem expectation_productScore_le (ν : FiniteLaw Ω) (g : Finset α → ℝ)
    (Y : Ω → ℝ) {r : ℝ} (hg : ∀ S, 0 ≤ g S) (hY : ∀ ω, 0 ≤ Y ω)
    (hr : 0 ≤ r) (hmean : ν.expectation Y ≤ r / 5) :
    (FiniteLaw.pi (fun _ : α => ν)).expectation
        (fun ω => productScore g (fun x => Y (ω x))) ≤
      (1 / 5) * fracCost r g := by
  classical
  have hmean0 := ν.expectation_nonneg hY
  rw [expectation_productScore]
  calc
    (∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
        g S * (ν.expectation Y) ^ S.card) ≤
        ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
          (1 / 5) * (g S * r ^ S.card) := by
      apply Finset.sum_le_sum
      intro S hS
      have hne : S.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
      have hpower : (ν.expectation Y) ^ S.card ≤ (1 / 5) * r ^ S.card :=
        (pow_le_pow_left₀ hmean0 hmean S.card).trans
          (one_fifth_pow_le hr (Finset.card_pos.mpr hne))
      calc
        g S * (ν.expectation Y) ^ S.card ≤ g S * ((1 / 5) * r ^ S.card) :=
          mul_le_mul_of_nonneg_left hpower (hg S)
        _ = (1 / 5) * (g S * r ^ S.card) := by ring
    _ = (1 / 5) * ∑ S ∈ (Finset.univ.erase ∅ : Finset (Finset α)),
        g S * r ^ S.card := (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / 5) * fracCost r g := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 5)
      unfold fracCost
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun S _ _ => mul_nonneg (hg S) (pow_nonneg hr S.card))


-- @@ L101-111 verbatim
/-- The budget one half gives the upper bound one tenth for the same score. -/
theorem expectation_productScore_le_tenth (ν : FiniteLaw Ω) (g : Finset α → ℝ)
    (Y : Ω → ℝ) {r : ℝ} (hg : ∀ S, 0 ≤ g S) (hY : ∀ ω, 0 ≤ Y ω)
    (hr : 0 ≤ r) (hmean : ν.expectation Y ≤ r / 5) (hcost : fracCost r g ≤ 1 / 2) :
    (FiniteLaw.pi (fun _ : α => ν)).expectation
        (fun ω => productScore g (fun x => Y (ω x))) ≤ 1 / 10 := by
  calc
    _ ≤ (1 / 5) * fracCost r g := expectation_productScore_le ν g Y hg hY hr hmean
    _ ≤ (1 / 5 : ℝ) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 1 / 5)
    _ = 1 / 10 := by norm_num


-- @@ L113-113 verbatim
end

-- @@ L114-114 verbatim
end TalagrandThreshold


-- @@ L116-116 verbatim
end OAI
