/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module


public import SpherePacking.MagicFunction.b.psi
public import SpherePacking.MagicFunction.IntegralParametrisations


-- @@ L12-16 verbatim
/-!
# The Function `b`

This file defines Viazovska's function `b` via its integral representations.
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
namespace MagicFunction.b.ComplexIntegrands


-- @@ L31-31 verbatim
def Ψ₁' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)


-- @@ L33-33 verbatim
def Ψ₂' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)


-- @@ L35-35 verbatim
def Ψ₃' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)


-- @@ L37-37 verbatim
def Ψ₄' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)


-- @@ L39-39 verbatim
def Ψ₅' : ℂ → ℂ := fun z ↦ (ψI' z) * cexp (π * I * r * z)


-- @@ L41-41 verbatim
def Ψ₆' : ℂ → ℂ := fun z ↦ (ψS' z) * cexp (π * I * r * z)


-- @@ L43-45 verbatim
section Def

-- We write some API that allows us to express the `(Ψᵢ' r)` as functions when needed.


-- @@ L47-48 verbatim
lemma Ψ₁'_def : Ψ₁' r = fun z ↦ (ψT' z) * cexp (π * I * r * z) :=
  rfl


-- @@ L50-51 verbatim
lemma Ψ₂'_def : Ψ₂' r = fun z ↦ (ψT' z) * cexp (π * I * r * z) :=
  rfl


-- @@ L53-54 verbatim
lemma Ψ₃'_def : Ψ₃' r = fun z ↦ (ψT' z) * cexp (π * I * r * z) :=
  rfl


-- @@ L56-57 verbatim
lemma Ψ₄'_def : Ψ₄' r = fun z ↦ (ψT' z) * cexp (π * I * r * z) :=
  rfl


-- @@ L59-60 verbatim
lemma Ψ₅'_def : Ψ₅' r = fun z ↦ (ψI' z) * cexp (π * I * r * z) :=
  rfl


-- @@ L62-63 verbatim
lemma Ψ₆'_def : Ψ₆' r = fun z ↦ (ψS' z) * cexp (π * I * r * z) :=
  rfl


-- @@ L65-65 verbatim
end Def


-- @@ L67-67 verbatim
end MagicFunction.b.ComplexIntegrands


-- @@ L69-69 verbatim
namespace MagicFunction.b.RealIntegrands


-- @@ L71-71 verbatim
open MagicFunction.b.ComplexIntegrands


-- @@ L73-73 verbatim
def Ψ₁ : ℝ → ℂ := fun t ↦ I * Ψ₁' r (z₁' t)


-- @@ L75-75 verbatim
def Ψ₂ : ℝ → ℂ := fun t ↦ Ψ₂' r (z₂' t)


-- @@ L77-77 verbatim
def Ψ₃ : ℝ → ℂ := fun t ↦ I * Ψ₃' r (z₃' t)


-- @@ L79-79 verbatim
def Ψ₄ : ℝ → ℂ := fun t ↦ -1 * Ψ₄' r (z₄' t)


-- @@ L81-81 verbatim
def Ψ₅ : ℝ → ℂ := fun t ↦ I * Ψ₅' r (z₅' t)


-- @@ L83-83 verbatim
def Ψ₆ : ℝ → ℂ := fun t ↦ I * Ψ₆' r (z₆' t)


-- @@ L85-87 verbatim
section Def

-- We write some API that allows us to express the `(Ψᵢ r)` as functions when needed.


-- @@ L89-90 verbatim
lemma Ψ₁_def : Ψ₁ r = fun t ↦ I * Ψ₁' r (z₁' t) :=
  rfl


-- @@ L92-93 verbatim
lemma Ψ₂_def : Ψ₂ r = fun t ↦ Ψ₂' r (z₂' t) :=
  rfl


-- @@ L95-96 verbatim
lemma Ψ₃_def : Ψ₃ r = fun t ↦ I * Ψ₃' r (z₃' t) :=
  rfl


-- @@ L98-99 verbatim
lemma Ψ₄_def : Ψ₄ r = fun t ↦ -1 * Ψ₄' r (z₄' t) :=
  rfl


-- @@ L101-102 verbatim
lemma Ψ₅_def : Ψ₅ r = fun t ↦ I * Ψ₅' r (z₅' t) :=
  rfl


-- @@ L104-105 verbatim
lemma Ψ₆_def : Ψ₆ r = fun t ↦ I * Ψ₆' r (z₆' t) :=
  rfl


-- @@ L107-107 verbatim
end Def


-- @@ L109-109 verbatim
end MagicFunction.b.RealIntegrands


-- @@ L111-111 verbatim
end Integrands


-- @@ L113-113 verbatim
namespace MagicFunction.b.RealIntegrals


-- @@ L115-115 verbatim
noncomputable section Real_Input


-- @@ L117-117 verbatim
open MagicFunction.b.RealIntegrands


-- @@ L119-119 verbatim
def J₁' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₁ x t


-- @@ L121-121 verbatim
def J₂' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₂ x t


-- @@ L123-123 verbatim
def J₃' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₃ x t


-- @@ L125-125 verbatim
def J₄' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₄ x t


-- @@ L127-127 verbatim
def J₅' : ℝ → ℂ := fun x ↦ -2 * ∫ t in (0 : ℝ)..1, Ψ₅ x t


-- @@ L129-129 verbatim
def J₆' : ℝ → ℂ := fun x ↦ 2 * ∫ t in Ici (1 : ℝ), Ψ₆ x t


-- @@ L131-131 verbatim
def b' : ℝ → ℂ := fun x ↦ J₁' x + J₂' x + J₃' x + J₄' x + J₅' x + J₆' x


-- @@ L133-133 verbatim
end Real_Input


-- @@ L135-135 verbatim
end MagicFunction.b.RealIntegrals


-- @@ L137-137 verbatim
open MagicFunction.b.RealIntegrals


-- @@ L139-139 verbatim
namespace MagicFunction.b.RadialFunctions


-- @@ L141-141 verbatim
noncomputable section Vector_Input


-- @@ L143-143 expanded
def J₁ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ J₁' (‖x‖ ^ 2)


-- @@ L145-145 expanded
def J₂ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ J₂' (‖x‖ ^ 2)


-- @@ L147-147 expanded
def J₃ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ J₃' (‖x‖ ^ 2)


-- @@ L149-149 expanded
def J₄ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ J₄' (‖x‖ ^ 2)


-- @@ L151-151 expanded
def J₅ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ J₅' (‖x‖ ^ 2)


-- @@ L153-153 expanded
def J₆ : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ J₆' (‖x‖ ^ 2)


-- @@ L155-155 expanded
def b : EuclideanSpace ℝ (Fin 8) → ℂ := fun x ↦ b' (‖x‖ ^ 2)


-- @@ L157-157 verbatim
end Vector_Input


-- @@ L159-160 verbatim
open intervalIntegral MagicFunction.b.ComplexIntegrands MagicFunction.b.RealIntegrands
  MagicFunction.b.RealIntegrals


-- @@ L162-162 verbatim
section Eq₀


-- @@ L164-169 expanded
lemma b_eq (x : EuclideanSpace ℝ (Fin 8)) : b x = J₁ x + J₂ x + J₃ x + J₄ x + J₅ x + J₆ x :=
  rfl


-- @@ L171-171 verbatim
private lemma aux_I :  I ≠ 0 := by norm_num


-- @@ L173-181 verbatim
lemma J₁'_eq₀ (r : ℝ) : J₁' r = ∫ t in (0 : ℝ)..1,
    I * ψS' (-1 / ((z₁' t) + (1 : ℂ))) * ((z₁' t) + (1 : ℂ)) ^ 2 * cexp (π * I * r * (z₁' t)) := by
  rw [J₁', Ψ₁_def r, Ψ₁'_def r]
  apply integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₁ ht]
  ac_rfl


-- @@ L183-189 verbatim
lemma J₂'_eq₀ (r : ℝ) : J₂' r = ∫ t in (0 : ℝ)..1,
    ψS' (-1 / ((z₂' t) + (1 : ℂ))) * ((z₂' t) + (1 : ℂ)) ^ 2 * cexp (π * I * r * (z₂' t)) := by
  rw [J₂', Ψ₂_def r, Ψ₂'_def r]
  apply integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₂ ht]


-- @@ L191-199 verbatim
lemma J₃'_eq₀ (r : ℝ) : J₃' r = ∫ t in (0 : ℝ)..1,
    I * ψS' (-1 / ((z₃' t) + (1 : ℂ))) * ((z₃' t) + (1 : ℂ)) ^ 2 * cexp (π * I * r * (z₃' t)) := by
  rw [J₃', Ψ₃_def r, Ψ₃'_def r]
  apply integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₃ ht]
  ac_rfl


-- @@ L201-208 verbatim
lemma J₄'_eq₀ (r : ℝ) : J₄' r = ∫ t in (0 : ℝ)..1,
    -1 * ψS' (-1 / ((z₄' t) + (1 : ℂ))) * ((z₄' t) + (1 : ℂ)) ^ 2 * cexp (π * I * r * (z₄' t)) := by
  rw [J₄', Ψ₄_def r, Ψ₄'_def r]
  apply integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [ψS_slash_ST_explicit₄ ht]
  ac_rfl


-- @@ L210-219 verbatim
lemma J₅'_eq₀ (r : ℝ) : J₅' r = -2 * ∫ t in (0 : ℝ)..1,
    I * ψS' (-1 / (z₅' t)) * (z₅' t) ^ 2 * cexp (π * I * r * (z₅' t)) := by
  rw [J₅', Ψ₅_def r, Ψ₅'_def r]
  congr 1
  apply integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [ψS_slash_S_explicit₅ ht]
  ac_rfl


-- @@ L221-224 verbatim
lemma J₆'_eq₀ (r : ℝ) : J₆' r = 2 * ∫ t in Ici (1 : ℝ),
    I * ψS' (z₆' t) * cexp (π * I * r * (z₆' t)) := by
  rw [J₆', Ψ₆_def r, Ψ₆'_def r]
  ring_nf


-- @@ L226-226 verbatim
end Eq₀


-- @@ L228-228 verbatim
end MagicFunction.b.RadialFunctions
