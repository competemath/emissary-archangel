import OAI.Geometry.PinnedDistances.Variance


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3 u4 u5 u6 u7


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open NumberField

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open MeasureTheory

-- @@ L13-13 verbatim
open scoped Topology

-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory

-- @@ L16-16 verbatim
open scoped Topology ENNReal

-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
open MeasureTheory NumberField

-- @@ L19-19 verbatim
open scoped BigOperators

-- @@ L20-20 verbatim
noncomputable section

-- @@ L21-21 verbatim
open scoped BigOperators

-- @@ L22-22 verbatim
open MeasureTheory


-- @@ L24-24 verbatim
namespace WeakPinned.Global

-- @@ L25-25 verbatim
open Hierarchy

-- @@ L26-26 verbatim
variable {P : Type u1} [Fintype P] [DecidableEq P]

-- @@ L27-27 verbatim
variable {K : Type u2} [Field K] [NumberField K]

-- @@ L28-28 verbatim
variable (Z : P → K) (hZ : Function.Injective Z)


-- @@ L30-32 verbatim
def cellMass (C : Finset P) : ℝ :=
  (∑ v : InfinitePlace K, Arithmetic.archWeight v * ∫ ω, (arch Z v ω).mass C ∂Grid.fullLaw) +
    (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).mass C


-- @@ L34-38 verbatim
lemma cellMass_nonneg (C : Finset P) : 0 ≤ cellMass Z hZ C := by
  exact add_nonneg
    (Finset.sum_nonneg (fun v _ => mul_nonneg (Arithmetic.archWeight_nonneg v)
      (integral_nonneg (fun ω => (arch Z v ω).mass_nonneg C))))
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => (finite Z hZ v).mass_nonneg C)))


-- @@ L40-41 verbatim
lemma cellMass_singleton (C : Finset P) (hC : C.card ≤ 1) : cellMass Z hZ C = 0 := by
  simp only [cellMass, Depth.mass_singleton _ C hC, integral_zero, mul_zero, Finset.sum_const_zero, add_zero]


-- @@ L43-58 verbatim
lemma cellMass_overlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∑ C, cellMass Z hZ C * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) = L Z hZ x y hxy := by
  simp only [cellMass, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
    mul_assoc, L]
  rw [← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.mul_sum, Depth.averaged_mass_overlap (arch Z v) (arch_measurable Z hZ v)
      (arch_integrable Z hZ v) hn x y hxy]
  · congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    exact (finite Z hZ v).mass_overlap hn x y hxy


-- @@ L60-60 verbatim
end WeakPinned.Global


-- @@ L62-62 verbatim
namespace WeakPinned.Variance

-- @@ L63-63 verbatim
variable {P : Type u3} [Fintype P] [DecidableEq P]


-- @@ L65-67 verbatim
/-- Finite linear model of the actual occurrence integral on expressions
    vanishing on singleton and empty cells. Multiplicities are in m. -/
def weightedIntegral (m : Finset P → ℝ) (f : Finset P → ℝ) : ℝ := ∑ C, m C * f C


-- @@ L69-70 verbatim
def weightedOverlap (m : Finset P → ℝ) (x y : P) : ℝ :=
  weightedIntegral m (fun C => if x ∈ C ∧ y ∈ C then 1 else 0)


-- @@ L72-95 verbatim
lemma weighted_cancel (m : Finset P → ℝ) (b : ℝ) (S : P → ℝ)
    (hL : ∀ x y, x ≠ y → weightedOverlap m x y = b+S x+S y)
    (B : Finset P) (hB : 2 ≤ B.card) : weightedIntegral m (signedCell B) = 0 := by
  have he : weightedIntegral m (signedCell B) =
      ∑ x, ∑ y, signedPair B x y * weightedOverlap m x y := by
    simp only [weightedIntegral, signedCell_eq]
    have hc (C : Finset P) : (∑ x ∈ C, ∑ y ∈ C, signedPair B x y) =
        ∑ x, ∑ y, signedPair B x y * (if x ∈ C ∧ y ∈ C then (1:ℝ) else 0) := by
      simp only [mul_ite, mul_one, mul_zero, ite_and]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
      simp
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp only [weightedOverlap, weightedIntegral, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  rw [he]
  exact variance_cancel B hB _ b S hL


-- @@ L97-143 verbatim
lemma weighted_variance {I : Type u4} [Fintype I]
    (m : Finset P → ℝ) (hm : ∀ C, 0 ≤ m C) (b : ℝ) (S : P → ℝ)
    (hL : ∀ x y, x ≠ y → weightedOverlap m x y = b+S x+S y)
    (w : I → ℝ) (B : I → Finset P) (T M ε τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1)
    (hT : 1 ≤ T) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hτ : 0 < τ)
    (hscale : τ * Fintype.card P ≤ T)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M * prob Finset.univ x) :
    weightedIntegral m (varianceCell w B T) ≤
      (2*ε*(M+1)/τ)*weightedIntegral m (pairCell Finset.univ) +
      4*M*weightedIntegral m (fun C => if (C.card : ℝ) ≤ T then pairCell Finset.univ C else 0) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun C _ =>
    mul_le_mul_of_nonneg_left
      (varianceCell_bound w B T M ε τ hw hW hT hM hε hτ hscale hB hk hn hdom C) (hm C))
  simp only [mul_add, Finset.sum_add_distrib] at hh
  have hz : (∑ C, m C * ∑ i, w i * signedCell (B i) C) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hi (i : I) : (∑ C, m C * (w i * signedCell (B i) C)) = 0 := by
      calc
        _ = w i * weightedIntegral m (signedCell (B i)) := by
          simp only [weightedIntegral, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro C _
          ring
        _ = 0 := by rw [weighted_cancel m b S hL _ (hB i),mul_zero]
    simp_rw [hi]
    exact Finset.sum_const_zero
  rw [hz,zero_add] at hh
  simp only [← mul_add] at hh
  change weightedIntegral m (varianceCell w B T) ≤ _ at hh
  have he₁ : (∑ C, m C * (2*ε*(M+1)/τ * pairCell Finset.univ C)) =
      (2*ε*(M+1)/τ)*weightedIntegral m (pairCell Finset.univ) := by
    simp only [weightedIntegral, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  have he₂ : (∑ C, m C * (4*M*(if (C.card : ℝ) ≤ T then pairCell Finset.univ C else 0))) =
      4*M*weightedIntegral m (fun C => if (C.card : ℝ) ≤ T then pairCell Finset.univ C else 0) := by
    simp only [weightedIntegral, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  rwa [he₁,he₂] at hh

-- @@ L144-144 verbatim
end WeakPinned.Variance


-- @@ L146-146 verbatim
namespace WeakPinned.Global

-- @@ L147-147 verbatim
open Hierarchy Variance

-- @@ L148-148 verbatim
variable {P : Type u5} [Fintype P] [DecidableEq P]

-- @@ L149-149 verbatim
variable {K : Type u6} [Field K] [NumberField K]

-- @@ L150-150 verbatim
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)


-- @@ L152-152 verbatim
def totalMass (C : Finset P) : ℝ := cellMass Z₁ h₁ C + cellMass Z₂ h₂ C


-- @@ L154-154 verbatim
def totalPotential (x : P) : ℝ := S Z₁ h₁ x + S Z₂ h₂ x


-- @@ L156-156 verbatim
def baseConstant : ℝ := 2*Grid.kappa - M Z₁ h₁ - M Z₂ h₂


-- @@ L158-159 verbatim
lemma totalMass_nonneg (C : Finset P) : 0 ≤ totalMass Z₁ Z₂ h₁ h₂ C :=
  add_nonneg (cellMass_nonneg Z₁ h₁ C) (cellMass_nonneg Z₂ h₂ C)


-- @@ L161-162 verbatim
lemma totalPotential_nonneg (x : P) : 0 ≤ totalPotential Z₁ Z₂ h₁ h₂ x :=
  add_nonneg (S_nonneg Z₁ h₁ x) (S_nonneg Z₂ h₂ x)


-- @@ L164-171 verbatim
lemma totalMass_overlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    weightedOverlap (totalMass Z₁ Z₂ h₁ h₂) x y =
      baseConstant Z₁ Z₂ h₁ h₂ + totalPotential Z₁ Z₂ h₁ h₂ x + totalPotential Z₁ Z₂ h₁ h₂ y := by
  simp only [weightedOverlap,weightedIntegral,totalMass,add_mul,Finset.sum_add_distrib]
  rw [cellMass_overlap Z₁ h₁ hn x y hxy,cellMass_overlap Z₂ h₂ hn x y hxy,
    coordinate_overlap_identity Z₁ h₁ hn x y hxy,coordinate_overlap_identity Z₂ h₂ hn x y hxy]
  simp only [baseConstant,totalPotential]
  ring


-- @@ L173-191 verbatim
/-- Unconditional arithmetic-hierarchy instance of the quantitative variance
    bound. The overlap identity follows from the product formula, and the
    family hypotheses are exactly finite sampling data. -/
theorem arithmetic_variance {I : Type u7} [Fintype I]
    (hnP : 2 ≤ Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (T M₀ ε τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1)
    (hT : 1 ≤ T) (hM : 0 ≤ M₀) (hε : 0 ≤ ε) (hτ : 0 < τ)
    (hscale : τ * Fintype.card P ≤ T)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M₀ * prob Finset.univ x) :
    weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (varianceCell w B T) ≤
      (2*ε*(M₀+1)/τ)*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (pairCell Finset.univ) +
      4*M₀*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂)
        (fun C => if (C.card : ℝ) ≤ T then pairCell Finset.univ C else 0) :=
  weighted_variance _ (totalMass_nonneg Z₁ Z₂ h₁ h₂) _ _
    (totalMass_overlap Z₁ Z₂ h₁ h₂ hnP) w B T M₀ ε τ hw hW hT hM hε hτ hscale hB hk hn hdom

-- @@ L192-192 verbatim
end WeakPinned.Global


-- @@ L194-194 verbatim
end

-- @@ L195-195 verbatim
end

-- @@ L196-196 verbatim
end

-- @@ L197-197 verbatim
end

-- @@ L198-198 verbatim
end

-- @@ L199-199 verbatim
end


-- @@ L201-201 verbatim
end OAI
