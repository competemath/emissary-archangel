import OAI.NumberTheory.DirichletL.Reflection.Extraction


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L11-11 verbatim
def extractedRowFactor (D1 D2 K : Ideal Eis) : ℂ := quadraticRow K (primaryGenerator (D1*D2))

-- @@ L12-13 verbatim
def extractedSlotFactor (D1 D2 P : Ideal Eis) : ℂ :=
  inverseCubicKernel P D1 * (if IsCoprime P D2 then 1 else 0)


-- @@ L15-16 verbatim
lemma extractedRowFactor_norm_le_one (D1 D2 K : Ideal Eis) : ‖extractedRowFactor D1 D2 K‖ ≤ 1 :=
  quadraticRow_norm_le_one K _


-- @@ L18-22 verbatim
lemma extractedSlotFactor_norm_le_one (D1 D2 P : Ideal Eis) : ‖extractedSlotFactor D1 D2 P‖ ≤ 1 := by
  unfold extractedSlotFactor
  split_ifs
  · simpa only [mul_one] using inverseCubicKernel_norm_le_one P D1
  · simp


-- @@ L24-34 verbatim
lemma coprime_product_mask (P D b : Ideal Eis) :
    (if IsCoprime P (D*b) then (1:ℂ) else 0) =
      (if IsCoprime P D then 1 else 0)*(if IsCoprime P b then 1 else 0) := by
  by_cases hD : IsCoprime P D <;> by_cases hb : IsCoprime P b
  · simp [hD,hb,hD.mul_right hb]
  · have hn : ¬IsCoprime P (D*b) := fun h => hb (h.of_isCoprime_of_dvd_right (dvd_mul_left _ _))
    simp [hD,hb,hn]
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (dvd_mul_right _ _))
    simp [hD,hb,hn]
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (dvd_mul_right _ _))
    simp [hD,hb,hn]


-- @@ L36-47 verbatim
theorem forced_dual_kernel_factor (D1 D2 K P n b : Ideal Eis)
    (hK : Admissible K) (hP : primaryGenerator P ≠ 0) :
    quadraticRow K (primaryGenerator ((D1*n)*(D2*b)))*inverseCubicKernel P (D1*n)*
      (if IsCoprime P (D2*b) then 1 else 0)*(if IsCoprime K P then 1 else 0) =
      (extractedRowFactor D1 D2 K*extractedSlotFactor D1 D2 P)*
        quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*
        (if IsCoprime P b then 1 else 0)*(if IsCoprime K P then 1 else 0) := by
  rw [show (D1*n)*(D2*b)=(D1*D2)*(n*b) by ring,primaryGenerator_mul,
    canonical_quadraticRow_argument_mul K hK,inverseCubicKernel_mul_right P D1 n hP,
    coprime_product_mask]
  unfold extractedRowFactor extractedSlotFactor
  ring


-- @@ L49-51 verbatim
def extractedFrozenColumn {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  normalizedFrozenColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)


-- @@ L53-56 verbatim
lemma extractedFrozenColumn_norm_le_one {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ)
    (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) : ‖extractedFrozenColumn F jF e A n b‖ ≤ 1 :=
  normalizedFrozenColumn_norm_le_one F jF e A hA _ _


-- @@ L58-58 verbatim
end

-- @@ L59-59 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L61-61 verbatim
end OAI
