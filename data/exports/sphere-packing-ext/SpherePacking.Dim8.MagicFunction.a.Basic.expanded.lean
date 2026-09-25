/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan

M4R File
-/

module
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.MagicFunction.IntegralParametrisations



-- @@ L14-26 verbatim
/-!
# Integral representation of the magic function `a`

We define the complex integrands and real reparametrizations used to build the scalar integrals
`I₁'`, ..., `I₆'` and their radial versions on `V = EuclideanSpace ℝ (Fin 8)`. The resulting sum
is the function `a`.

## Main definitions
* `MagicFunction.a.RealIntegrals.a'` and `MagicFunction.a.RadialFunctions.a`

## Main statements
* `MagicFunction.a.RadialFunctions.a_eq`
-/



-- @@ L29-29 verbatim
local notation "V" => EuclideanSpace ℝ (Fin 8)


-- @@ L31-31 verbatim
open scoped UpperHalfPlane

-- @@ L32-32 verbatim
open Set Complex Real MagicFunction.Parametrisations


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
variable (r : ℝ)


-- @@ L38-38 verbatim
namespace MagicFunction.a.ComplexIntegrands


-- @@ L40-44 verbatim
/-- The first complex integrand used to define the magic function `a`.

The prime indicates this is a complex-variable integrand, before reparametrizing to `Φ₁`. -/
@[expose] public def Φ₁' : ℂ → ℂ := fun z ↦
  φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))


-- @@ L46-49 verbatim
/-- A copy of `Φ₁'` used for uniform indexing.

The prime indicates this is a complex-variable integrand, before reparametrizing to `Φ₂`. -/
@[expose] public def Φ₂' : ℂ → ℂ := Φ₁' r


-- @@ L51-55 verbatim
/-- The third complex integrand used to define the magic function `a`.

The prime indicates this is a complex-variable integrand, before reparametrizing to `Φ₃`. -/
@[expose] public def Φ₃' : ℂ → ℂ := fun z ↦
  φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))


-- @@ L57-60 verbatim
/-- A copy of `Φ₃'` used for uniform indexing.

The prime indicates this is a complex-variable integrand, before reparametrizing to `Φ₄`. -/
@[expose] public def Φ₄' : ℂ → ℂ := Φ₃' r


-- @@ L62-66 verbatim
/-- The fifth complex integrand used to define the magic function `a`.

The prime indicates this is a complex-variable integrand, before reparametrizing to `Φ₅`. -/
@[expose] public def Φ₅' : ℂ → ℂ := fun z ↦
  φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * r * (z : ℂ))


-- @@ L68-72 verbatim
/-- The sixth complex integrand used to define the magic function `a`.

The prime indicates this is a complex-variable integrand, before reparametrizing to `Φ₆`. -/
@[expose] public def Φ₆' : ℂ → ℂ := fun z ↦
  φ₀'' (z) * cexp (π * I * r * (z : ℂ))


-- @@ L74-74 verbatim
end MagicFunction.a.ComplexIntegrands


-- @@ L76-76 verbatim
namespace MagicFunction.a.RealIntegrands


-- @@ L78-78 verbatim
open MagicFunction.a.ComplexIntegrands


-- @@ L80-81 verbatim
/-- The first real-variable integrand, obtained from `Φ₁'` by the parametrization `z₁'`. -/
@[expose] public def Φ₁ : ℝ → ℂ := fun t ↦ I * Φ₁' r (z₁' t)


-- @@ L83-84 verbatim
/-- The second real-variable integrand, obtained from `Φ₂'` by the parametrization `z₂'`. -/
@[expose] public def Φ₂ : ℝ → ℂ := fun t ↦ Φ₂' r (z₂' t)


-- @@ L86-87 verbatim
/-- The third real-variable integrand, obtained from `Φ₃'` by the parametrization `z₃'`. -/
@[expose] public def Φ₃ : ℝ → ℂ := fun t ↦ I * Φ₃' r (z₃' t)


-- @@ L89-90 verbatim
/-- The fourth real-variable integrand, obtained from `Φ₄'` by the parametrization `z₄'`. -/
@[expose] public def Φ₄ : ℝ → ℂ := fun t ↦ -1 * Φ₄' r (z₄' t)


-- @@ L92-93 verbatim
/-- The fifth real-variable integrand, obtained from `Φ₅'` by the parametrization `z₅'`. -/
@[expose] public def Φ₅ : ℝ → ℂ := fun t ↦ I * Φ₅' r (z₅' t)


-- @@ L95-96 verbatim
/-- The sixth real-variable integrand, obtained from `Φ₆'` by the parametrization `z₆'`. -/
@[expose] public def Φ₆ : ℝ → ℂ := fun t ↦ I * Φ₆' r (z₆' t)


-- @@ L98-100 verbatim
section Def

-- We write some API that allows us to express the `(Φᵢ r)` as functions when needed.


-- @@ L102-104 verbatim
/-- Unfolding lemma for `Φ₁`. -/
public lemma Φ₁_def : Φ₁ r = fun t ↦ I * Φ₁' r (z₁' t) :=
  rfl


-- @@ L106-108 verbatim
/-- Unfolding lemma for `Φ₂`. -/
public lemma Φ₂_def : Φ₂ r = fun t ↦ Φ₂' r (z₂' t) :=
  rfl


-- @@ L110-112 verbatim
/-- Unfolding lemma for `Φ₃`. -/
public lemma Φ₃_def : Φ₃ r = fun t ↦ I * Φ₃' r (z₃' t) :=
  rfl


-- @@ L114-116 verbatim
/-- Unfolding lemma for `Φ₄`. -/
public lemma Φ₄_def : Φ₄ r = fun t ↦ -1 * Φ₄' r (z₄' t) :=
  rfl


-- @@ L118-120 verbatim
/-- Unfolding lemma for `Φ₅`. -/
public lemma Φ₅_def : Φ₅ r = fun t ↦ I * Φ₅' r (z₅' t) :=
  rfl


-- @@ L122-124 verbatim
/-- Unfolding lemma for `Φ₆`. -/
public lemma Φ₆_def : Φ₆ r = fun t ↦ I * Φ₆' r (z₆' t) :=
  rfl


-- @@ L126-126 verbatim
end Def


-- @@ L128-128 verbatim
end MagicFunction.a.RealIntegrands

-- @@ L129-129 verbatim
namespace MagicFunction.a.RealIntegrals


-- @@ L131-131 verbatim
open MagicFunction.a.RealIntegrands


-- @@ L133-136 verbatim
/-- The first scalar integral entering the definition of `a'`.

The prime indicates the input is the scalar parameter `r`, before radializing to `I₁`. -/
@[expose] public def I₁' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₁ x t


-- @@ L138-141 verbatim
/-- The second scalar integral entering the definition of `a'`.

The prime indicates the input is the scalar parameter `r`, before radializing to `I₂`. -/
@[expose] public def I₂' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₂ x t


-- @@ L143-146 verbatim
/-- The third scalar integral entering the definition of `a'`.

The prime indicates the input is the scalar parameter `r`, before radializing to `I₃`. -/
@[expose] public def I₃' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₃ x t


-- @@ L148-151 verbatim
/-- The fourth scalar integral entering the definition of `a'`.

The prime indicates the input is the scalar parameter `r`, before radializing to `I₄`. -/
@[expose] public def I₄' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₄ x t


-- @@ L153-156 verbatim
/-- The fifth scalar integral entering the definition of `a'`.

The prime indicates the input is the scalar parameter `r`, before radializing to `I₅`. -/
@[expose] public def I₅' : ℝ → ℂ := fun x ↦ -2 * ∫ t in (0 : ℝ)..1, Φ₅ x t


-- @@ L158-161 verbatim
/-- The sixth scalar integral entering the definition of `a'`.

The prime indicates the input is the scalar parameter `r`, before radializing to `I₆`. -/
@[expose] public def I₆' : ℝ → ℂ := fun x ↦ 2 * ∫ t in Ici (1 : ℝ), Φ₆ x t


-- @@ L163-166 verbatim
/-- The scalar version of the magic function `a`, defined as the sum of `I₁'`, ..., `I₆'`.

The prime indicates the input is the scalar parameter `r`, before radializing to `a`. -/
@[expose] public def a' : ℝ → ℂ := fun x ↦ I₁' x + I₂' x + I₃' x + I₄' x + I₅' x + I₆' x


-- @@ L168-168 verbatim
end MagicFunction.a.RealIntegrals

-- @@ L169-169 verbatim
open MagicFunction.a.RealIntegrals


-- @@ L171-171 verbatim
namespace MagicFunction.a.RadialFunctions


-- @@ L173-174 expanded
/-- The radial function on `V` induced by `I₁'` via `r = ‖x‖ ^ 2`. -/
@[expose]
public def I₁ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₁' (‖x‖ ^ 2)


-- @@ L176-177 expanded
/-- The radial function on `V` induced by `I₂'` via `r = ‖x‖ ^ 2`. -/
@[expose]
public def I₂ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₂' (‖x‖ ^ 2)


-- @@ L179-180 expanded
/-- The radial function on `V` induced by `I₃'` via `r = ‖x‖ ^ 2`. -/
@[expose]
public def I₃ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₃' (‖x‖ ^ 2)


-- @@ L182-183 expanded
/-- The radial function on `V` induced by `I₄'` via `r = ‖x‖ ^ 2`. -/
@[expose]
public def I₄ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₄' (‖x‖ ^ 2)


-- @@ L185-186 expanded
/-- The radial function on `V` induced by `I₅'` via `r = ‖x‖ ^ 2`. -/
@[expose]
public def I₅ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₅' (‖x‖ ^ 2)


-- @@ L188-189 expanded
/-- The radial function on `V` induced by `I₆'` via `r = ‖x‖ ^ 2`. -/
@[expose]
public def I₆ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ I₆' (‖x‖ ^ 2)


-- @@ L191-192 expanded
/-- The magic function `a` as a radial function on `V`. -/
@[expose]
public def a : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ a' (‖x‖ ^ 2)


-- @@ L194-194 verbatim
open intervalIntegral


-- @@ L196-196 verbatim
section Eq


-- @@ L198-198 verbatim
open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands


-- @@ L200-201 expanded
/-- Unfolding lemma expressing `a` as the sum of the six radial integrals `I₁`, ..., `I₆`. -/
public lemma a_eq (x : EuclideanSpace ℝ (Fin 8)) : a x = I₁ x + I₂ x + I₃ x + I₄ x + I₅ x + I₆ x :=
  rfl


-- @@ L203-204 expanded
/-- Unfolding lemma for `I₁` in terms of `I₁'`. -/
public lemma I₁_eq (x : EuclideanSpace ℝ (Fin 8)) : I₁ x = I₁' (‖x‖ ^ 2) :=
  rfl


-- @@ L206-207 expanded
/-- Unfolding lemma for `I₂` in terms of `I₂'`. -/
public lemma I₂_eq (x : EuclideanSpace ℝ (Fin 8)) : I₂ x = I₂' (‖x‖ ^ 2) :=
  rfl


-- @@ L209-210 expanded
/-- Unfolding lemma for `I₃` in terms of `I₃'`. -/
public lemma I₃_eq (x : EuclideanSpace ℝ (Fin 8)) : I₃ x = I₃' (‖x‖ ^ 2) :=
  rfl


-- @@ L212-213 expanded
/-- Unfolding lemma for `I₄` in terms of `I₄'`. -/
public lemma I₄_eq (x : EuclideanSpace ℝ (Fin 8)) : I₄ x = I₄' (‖x‖ ^ 2) :=
  rfl


-- @@ L215-216 expanded
/-- Unfolding lemma for `I₅` in terms of `I₅'`. -/
public lemma I₅_eq (x : EuclideanSpace ℝ (Fin 8)) : I₅ x = I₅' (‖x‖ ^ 2) :=
  rfl


-- @@ L218-219 expanded
/-- Unfolding lemma for `I₆` in terms of `I₆'`. -/
public lemma I₆_eq (x : EuclideanSpace ℝ (Fin 8)) : I₆ x = I₆' (‖x‖ ^ 2) :=
  rfl


-- @@ L221-246 verbatim
/-- An explicit integral expression for `I₁'` after rewriting `Φ₁` and the parametrization `z₁'`. -/
public lemma I₁'_eq (r : ℝ) : I₁' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by
  simp only [I₁', Φ₁, Φ₁']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  simp only [z₁'_eq_of_mem (t := t) ⟨ht₀, ht₁⟩]
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


-- @@ L248-253 verbatim
/-- Rewrite `I₁'` as an integral over `Ioc 0 1`. -/
public lemma I₁'_eq_Ioc (r : ℝ) : I₁' r = ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * I * r)
    * cexp (-π * r * t) := by simp [I₁'_eq, intervalIntegral_eq_integral_uIoc]


-- @@ L255-276 verbatim
/-- An explicit integral expression for `I₂'` after rewriting `Φ₂` and the parametrization `z₂'`. -/
public lemma I₂'_eq (r : ℝ) : I₂' r = ∫ t in (0 : ℝ)..1,
    φ₀'' (-1 / (t + I))
    * (t + I) ^ 2
    * cexp (-π * I * r)
    * cexp (π * I * r * t)
    * cexp (-π * r) := by
  simp only [I₂', Φ₂, Φ₂', Φ₁']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  simp only [z₂'_eq_of_mem (t := t) ⟨ht₀, ht₁⟩]
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


-- @@ L278-303 verbatim
/-- An explicit integral expression for `I₃'` after rewriting `Φ₃` and the parametrization `z₃'`. -/
public lemma I₃'_eq (r : ℝ) : I₃' r = ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (π * I * r)
    * cexp (-π * r * t) := by
  simp only [I₃', Φ₃, Φ₃']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  simp only [z₃'_eq_of_mem (t := t) ⟨ht₀, ht₁⟩]
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


-- @@ L305-324 verbatim
/-- An explicit integral expression for `I₄'` after rewriting `Φ₄` and the parametrization `z₄'`. -/
public lemma I₄'_eq (r : ℝ) : I₄' r = ∫ t in (0 : ℝ)..1, -1
    * φ₀'' (-1 / (-t + I))
    * (-t + I) ^ 2
    * cexp (π * I * r)
    * cexp (-π * I * r * t)
    * cexp (-π * r) := by
  simp only [I₄', Φ₄, Φ₄', Φ₃']
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  simp only [z₄'_eq_of_mem (t := t) ⟨ht₀, ht₁⟩]
  calc
  _ = -1 * φ₀'' (-1 / (-t + I)) * (-t + I) ^ 2 * cexp (π * I * r * (1 - t + I)) := by ring_nf
  _ = _ := by
      conv_rhs => rw [mul_assoc, mul_assoc]
      rw [← Complex.exp_add, ← Complex.exp_add]
      ring_nf
      rw [I_sq]
      ring_nf


-- @@ L326-346 verbatim
/-- An explicit integral expression for `I₅'` after rewriting `Φ₅` and the parametrization `z₅'`. -/
public lemma I₅'_eq (r : ℝ) : I₅' r = -2 * ∫ t in (0 : ℝ)..1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by
  simp only [I₅', Φ₅, Φ₅']; congr 1
  apply integral_congr
  simp only [EqOn, zero_le_one, uIcc_of_le, mem_Icc, neg_mul, and_imp]
  intro t ht₀ ht₁
  simp only [z₅'_eq_of_mem (t := t) ⟨ht₀, ht₁⟩]
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


-- @@ L348-352 verbatim
/-- Rewrite `I₅'` as an integral over `Ioc 0 1`. -/
public lemma I₅'_eq_Ioc (r : ℝ) : I₅' r = -2 * ∫ (t : ℝ) in Ioc 0 1, -I
    * φ₀'' (-1 / (I * t))
    * t ^ 2
    * cexp (-π * r * t) := by simp [I₅'_eq, intervalIntegral_eq_integral_uIoc]


-- @@ L354-365 verbatim
/-- An explicit integral expression for `I₆'` after rewriting `Φ₆` and the parametrization `z₆'`. -/
public lemma I₆'_eq (r : ℝ) : I₆' r = 2 * ∫ t in Ici (1 : ℝ), I
    * φ₀'' (I * t)
    * cexp (-π * r * t) := by
  simp only [I₆', Φ₆, Φ₆']
  congr 1
  apply MeasureTheory.setIntegral_congr_fun (X := ℝ) (E := ℂ) (measurableSet_Ici)
  simp only [EqOn, neg_mul]
  intro t ht
  simp [z₆'_eq_of_mem ht]
  ring_nf
  simp [I_sq]


-- @@ L367-380 verbatim
attribute [simp]
  MagicFunction.a.RealIntegrands.Φ₁_def
  MagicFunction.a.RealIntegrands.Φ₂_def
  MagicFunction.a.RealIntegrands.Φ₃_def
  MagicFunction.a.RealIntegrands.Φ₄_def
  MagicFunction.a.RealIntegrands.Φ₅_def
  MagicFunction.a.RealIntegrands.Φ₆_def
  MagicFunction.a.RadialFunctions.a_eq
  MagicFunction.a.RadialFunctions.I₁_eq
  MagicFunction.a.RadialFunctions.I₂_eq
  MagicFunction.a.RadialFunctions.I₃_eq
  MagicFunction.a.RadialFunctions.I₄_eq
  MagicFunction.a.RadialFunctions.I₅_eq
  MagicFunction.a.RadialFunctions.I₆_eq


-- @@ L382-382 verbatim
end MagicFunction.a.RadialFunctions.Eq


-- @@ L384-384 verbatim
end
