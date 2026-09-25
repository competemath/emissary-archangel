/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.ModularForms.Eisenstein
public import SpherePacking.MagicFunction.IntegralParametrisations


-- @@ L12-16 verbatim
/-!
# The Function `a`

Defines Viazovska's function `a` via its integral representations.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
local notation "V" => EuclideanSpace ℝ (Fin 8)


-- @@ L22-22 verbatim
open Set Complex Real MagicFunction.Parametrisations

-- @@ L23-23 verbatim
open scoped UpperHalfPlane


-- @@ L25-25 verbatim
noncomputable section Integrands


-- @@ L27-27 verbatim
variable (r : ℝ)


-- @@ L29-29 verbatim
namespace MagicFunction.a.ComplexIntegrands


-- @@ L31-31 verbatim
def Φ₁' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))


-- @@ L33-33 verbatim
def Φ₂' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))


-- @@ L35-35 verbatim
def Φ₃' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))


-- @@ L37-37 verbatim
def Φ₄' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))


-- @@ L39-39 verbatim
def Φ₅' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * r * (z : ℂ))


-- @@ L41-41 verbatim
def Φ₆' : ℂ → ℂ := fun z ↦ φ₀'' (z) * cexp (π * I * r * (z : ℂ))


-- @@ L43-45 verbatim
section Def

-- We write some API that allows us to express the `(Φᵢ' r)` as functions when needed.


-- @@ L47-48 verbatim
lemma Φ₁'_def : Φ₁' r = fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ)) :=
  rfl


-- @@ L50-51 verbatim
lemma Φ₂'_def : Φ₂' r = fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ)) :=
  rfl


-- @@ L53-54 verbatim
lemma Φ₃'_def : Φ₃' r = fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ)) :=
  rfl


-- @@ L56-57 verbatim
lemma Φ₄'_def : Φ₄' r = fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ)) :=
  rfl


-- @@ L59-60 verbatim
lemma Φ₅'_def : Φ₅' r = fun z ↦ φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * r * (z : ℂ)) :=
  rfl


-- @@ L62-63 verbatim
lemma Φ₆'_def : Φ₆' r = fun z ↦ φ₀'' (z) * cexp (π * I * r * (z : ℂ)) :=
  rfl


-- @@ L65-65 verbatim
end Def


-- @@ L67-67 verbatim
end MagicFunction.a.ComplexIntegrands


-- @@ L69-69 verbatim
namespace MagicFunction.a.RealIntegrands


-- @@ L71-71 verbatim
open MagicFunction.a.ComplexIntegrands


-- @@ L73-73 verbatim
def Φ₁ : ℝ → ℂ := fun t ↦ I * Φ₁' r (z₁' t)


-- @@ L75-75 verbatim
def Φ₂ : ℝ → ℂ := fun t ↦ Φ₂' r (z₂' t)


-- @@ L77-77 verbatim
def Φ₃ : ℝ → ℂ := fun t ↦ I * Φ₃' r (z₃' t)


-- @@ L79-79 verbatim
def Φ₄ : ℝ → ℂ := fun t ↦ -1 * Φ₄' r (z₄' t)


-- @@ L81-81 verbatim
def Φ₅ : ℝ → ℂ := fun t ↦ I * Φ₅' r (z₅' t)


-- @@ L83-83 verbatim
def Φ₆ : ℝ → ℂ := fun t ↦ I * Φ₆' r (z₆' t)


-- @@ L85-87 verbatim
section Def

-- We write some API that allows us to express the `(Φᵢ r)` as functions when needed.


-- @@ L89-90 verbatim
lemma Φ₁_def : Φ₁ r = fun t ↦ I * Φ₁' r (z₁' t) :=
  rfl


-- @@ L92-93 verbatim
lemma Φ₂_def : Φ₂ r = fun t ↦ Φ₂' r (z₂' t) :=
  rfl


-- @@ L95-96 verbatim
lemma Φ₃_def : Φ₃ r = fun t ↦ I * Φ₃' r (z₃' t) :=
  rfl


-- @@ L98-99 verbatim
lemma Φ₄_def : Φ₄ r = fun t ↦ -1 * Φ₄' r (z₄' t) :=
  rfl


-- @@ L101-102 verbatim
lemma Φ₅_def : Φ₅ r = fun t ↦ I * Φ₅' r (z₅' t) :=
  rfl


-- @@ L104-105 verbatim
lemma Φ₆_def : Φ₆ r = fun t ↦ I * Φ₆' r (z₆' t) :=
  rfl


-- @@ L107-107 verbatim
end Def


-- @@ L109-109 verbatim
end MagicFunction.a.RealIntegrands


-- @@ L111-111 verbatim
end Integrands


-- @@ L113-113 verbatim
namespace MagicFunction.a.RealIntegrals


-- @@ L115-115 verbatim
noncomputable section Real_Input


-- @@ L117-117 verbatim
open MagicFunction.a.RealIntegrands


-- @@ L119-119 verbatim
def I₁' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₁ x t


-- @@ L121-121 verbatim
def I₂' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₂ x t


-- @@ L123-123 verbatim
def I₃' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₃ x t


-- @@ L125-125 verbatim
def I₄' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₄ x t


-- @@ L127-127 verbatim
def I₅' : ℝ → ℂ := fun x ↦ -2 * ∫ t in (0 : ℝ)..1, Φ₅ x t


-- @@ L129-129 verbatim
def I₆' : ℝ → ℂ := fun x ↦ 2 * ∫ t in Ici (1 : ℝ), Φ₆ x t


-- @@ L131-131 verbatim
def a' : ℝ → ℂ := fun x ↦ I₁' x + I₂' x + I₃' x + I₄' x + I₅' x + I₆' x


-- @@ L133-133 verbatim
end Real_Input


-- @@ L135-135 verbatim
end MagicFunction.a.RealIntegrals


-- @@ L137-137 verbatim
open MagicFunction.a.RealIntegrals


-- @@ L139-139 verbatim
namespace MagicFunction.a.RadialFunctions


-- @@ L141-141 verbatim
noncomputable section Vector_Input


-- @@ L143-143 expanded
def I₁ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₁' (‖x‖ ^ 2)


-- @@ L145-145 expanded
def I₂ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₂' (‖x‖ ^ 2)


-- @@ L147-147 expanded
def I₃ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₃' (‖x‖ ^ 2)


-- @@ L149-149 expanded
def I₄ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₄' (‖x‖ ^ 2)


-- @@ L151-151 expanded
def I₅ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₅' (‖x‖ ^ 2)


-- @@ L153-153 expanded
def I₆ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₆' (‖x‖ ^ 2)


-- @@ L155-155 expanded
def a : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ a' (‖x‖ ^ 2)


-- @@ L157-157 verbatim
end Vector_Input


-- @@ L159-159 verbatim
open intervalIntegral


-- @@ L161-161 verbatim
section Eq


-- @@ L163-163 verbatim
open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands


-- @@ L165-165 expanded
lemma a_eq (x : EuclideanSpace ℝ (Fin 8)) : a x = I₁ x + I₂ x + I₃ x + I₄ x + I₅ x + I₆ x :=
  rfl


-- @@ L167-167 expanded
lemma I₁_eq (x : EuclideanSpace ℝ (Fin 8)) : I₁ x = I₁' (‖x‖ ^ 2) :=
  rfl


-- @@ L169-169 expanded
lemma I₂_eq (x : EuclideanSpace ℝ (Fin 8)) : I₂ x = I₂' (‖x‖ ^ 2) :=
  rfl


-- @@ L171-171 expanded
lemma I₃_eq (x : EuclideanSpace ℝ (Fin 8)) : I₃ x = I₃' (‖x‖ ^ 2) :=
  rfl


-- @@ L173-173 expanded
lemma I₄_eq (x : EuclideanSpace ℝ (Fin 8)) : I₄ x = I₄' (‖x‖ ^ 2) :=
  rfl


-- @@ L175-175 expanded
lemma I₅_eq (x : EuclideanSpace ℝ (Fin 8)) : I₅ x = I₅' (‖x‖ ^ 2) :=
  rfl


-- @@ L177-177 expanded
lemma I₆_eq (x : EuclideanSpace ℝ (Fin 8)) : I₆ x = I₆' (‖x‖ ^ 2) :=
  rfl


-- @@ L179-204 verbatim
lemma I₁'_eq (r : ℝ) : I₁' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  simp only [I₁', Φ₁, Φ₁']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₁'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * r * (I + t)) := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      conv_lhs => rw [mul_assoc]
      congr 2 <;> ring_nf
      rw [I_sq]
      ring_nf
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * I * r) * cexp (-π * r * t) := by
      conv_rhs => rw [mul_assoc]
      rw [← Complex.exp_add]
      congr
      ring_nf
  _ = _ := by
      rw [mul_pow, I_sq]
      ring_nf


-- @@ L206-216 verbatim
lemma I₁'_eq' (r : ℝ) : I₁' r = -I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  rw [I₁'_eq r]
  rw [← smul_eq_mul (-I), ← integral_smul]
  simp only [smul_eq_mul (-I), neg_mul]
  congr
  ext x
  ring


-- @@ L218-223 verbatim
lemma I₁'_eq_Ioc (r : ℝ) : I₁' r = ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  rw [I₁'_eq, integral_of_le zero_le_one]


-- @@ L225-230 verbatim
lemma I₁'_eq'_Ioc (r : ℝ) : I₁' r = -I * ∫ t in (0 : ℝ)..1,
      φ₀'' (-1 / (I * t))
      * t ^ 2
      * cexp (-π * I * r)
      * cexp (-π * r * t) := by
    simp [I₁'_eq', intervalIntegral_eq_integral_uIoc]


-- @@ L232-253 verbatim
lemma I₂'_eq (r : ℝ) : I₂' r = ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (t + I))
    * (t + I) ^ 2
    * cexp (-π * I * r)
    * cexp (π * I * r * t)
    * cexp (-π * r) := by
  simp only [I₂', Φ₂, Φ₂']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₂'_eq_of_mem hmem]
  calc
  _ = φ₀'' (-1 / (t + I)) * (t + I) ^ 2 * cexp (π * I * r * (-1 + t + I)) := by
      congr 2 <;> ring_nf
  _ = _ := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr
      ring_nf
      rw [I_sq]
      ring_nf


-- @@ L255-280 verbatim
lemma I₃'_eq (r : ℝ) : I₃' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  simp only [I₃', Φ₃, Φ₃']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₃'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * r * (-I + t)) := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      conv_lhs => rw [mul_assoc]
      congr 2 <;> ring_nf
      rw [I_sq]
      ring_nf
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (π * I * r) * cexp (-π * r * t) := by
    conv_rhs => rw [mul_assoc]
    rw [← Complex.exp_add]
    congr
    ring_nf
  _ = _ := by
    rw [mul_pow, I_sq]
    ring_nf


-- @@ L282-292 verbatim
lemma I₃'_eq' (r : ℝ) : I₃' r = -I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  rw [I₃'_eq r]
  rw [← smul_eq_mul (-I), ← integral_smul]
  simp only [smul_eq_mul (-I), neg_mul]
  congr
  ext x
  ring


-- @@ L294-299 verbatim
lemma I₃'_eq_Ioc (r : ℝ) : I₃' r = ∫ (t : ℝ) in Ioc 0 1, -I
  * φ₀'' (-1 / (I * t))
  * t ^ 2
  * cexp (π * I * r)
  * cexp (-π * r * t) := by
    rw [I₃'_eq, integral_of_le zero_le_one]


-- @@ L301-306 verbatim
lemma I₃'_eq'_Ioc (r : ℝ) : I₃' r = -I * ∫ (t : ℝ) in Ioc 0 1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  rw [I₃'_eq', integral_of_le zero_le_one]


-- @@ L308-327 verbatim
lemma I₄'_eq (r : ℝ) : I₄' r = ∫ t in (0 : ℝ)..1, -1
    * φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2
    * cexp (π * I * r)
    * cexp (-π * I * r * t)
    * cexp (-π * r) := by
  simp only [I₄', Φ₄, Φ₄']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₄'_eq_of_mem hmem]
  calc
  _ = -1 * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2 * cexp (π * I * r * (1 - t + I)) := by ring_nf
  _ = _ := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      rw [← Complex.exp_add, ← Complex.exp_add]
      ring_nf
      rw [I_sq]
      ring_nf


-- @@ L329-349 verbatim
lemma I₅'_eq (r : ℝ) : I₅' r = -2 * ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  simp only [I₅', Φ₅, Φ₅']; congr 1
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  have hmem : t ∈ Icc 0 1 := ⟨ht₀, ht₁⟩
  simp only [z₅'_eq_of_mem hmem]
  calc
  _ = I * φ₀'' (-1 / (I * t)) * (I * t) ^ 2 * cexp (-π * r * t) := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      conv_lhs => rw [mul_assoc]
      congr 2
      ring_nf
      rw [I_sq]
      ring_nf
  _ = _ := by
    rw [mul_pow, I_sq]
    ring_nf


-- @@ L351-360 verbatim
lemma I₅'_eq' (r : ℝ) : I₅' r = 2 * I * ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  rw [I₅'_eq r]
  simp only [neg_mul, integral_neg, mul_neg, neg_neg, mul_assoc, ← smul_eq_mul I]
  rw [← integral_smul]
  congr; ext x
  simp only [smul_eq_mul I]
  ring_nf


-- @@ L362-366 verbatim
lemma I₅'_eq_Ioc (r : ℝ) : I₅' r = -2 * ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  rw [I₅'_eq, integral_of_le zero_le_one]


-- @@ L368-372 verbatim
lemma I₅'_eq'_Ioc (r : ℝ) : I₅' r = 2 * I * ∫ (t : ℝ) in Ioc 0 1,
    φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  rw [I₅'_eq', integral_of_le zero_le_one]


-- @@ L374-387 verbatim
lemma I₆'_eq (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), I
    * φ₀'' (I * t)
    * cexp (-π * r * t) := by
  simp only [I₆', Φ₆, Φ₆']
  congr 1
  apply MeasureTheory.setIntegral_congr_fun (X := ℝ) (E := ℂ) (measurableSet_Ici)
  simp only [EqOn, neg_mul]
  intro t ht
  rw [z₆'_eq_of_mem ht]
  conv_rhs => rw [mul_assoc]
  congr
  ring_nf
  rw [I_sq]
  ring_nf


-- @@ L389-397 verbatim
lemma I₆'_eq' (r : ℝ) : I₆' r = 2 * I * ∫ t in Ici (1 : ℝ),
  φ₀'' (I * t)
  * cexp (-π * r * t) := by
  rw [I₆'_eq r]
  simp only [mul_assoc, ← smul_eq_mul I]
  rw [← MeasureTheory.integral_smul]
  congr; ext t
  simp only [smul_eq_mul I]
  ring_nf


-- @@ L399-399 verbatim
end Eq


-- @@ L401-401 verbatim
end MagicFunction.a.RadialFunctions
