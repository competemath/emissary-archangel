/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.Basic

-- @@ L9-17 verbatim
/-!

## Modules associated with complex Lorentz vectors

We define the modules underlying complex Lorentz vectors.
These definitions are preludes to the definitions of
`Lorentz.complexContr` and `Lorentz.complexCo`.

-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace Lorentz


-- @@ L23-23 verbatim
noncomputable section

-- @@ L24-24 verbatim
open Matrix

-- @@ L25-25 verbatim
open MatrixGroups

-- @@ L26-26 verbatim
open Complex


-- @@ L28-31 verbatim
/-- The module for contravariant (up-index) complex Lorentz vectors. -/
structure ContrℂModule where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin 3 → ℂ`. -/
  val : Fin 1 ⊕ Fin 3 → ℂ


-- @@ L33-33 verbatim
namespace ContrℂModule


-- @@ L35-40 verbatim
/-- The equivalence between `ContrℂModule` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
def toFin13ℂFun : ContrℂModule ≃ (Fin 1 ⊕ Fin 3 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L42-44 verbatim
/-- The instance of `AddCommMonoid` on `ContrℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommMonoid ContrℂModule := Equiv.addCommMonoid toFin13ℂFun


-- @@ L46-48 verbatim
/-- The instance of `AddCommGroup` on `ContrℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommGroup ContrℂModule := Equiv.addCommGroup toFin13ℂFun


-- @@ L50-52 verbatim
/-- The instance of `Module` on `ContrℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : Module ℂ ContrℂModule := Equiv.module ℂ toFin13ℂFun


-- @@ L54-59 verbatim
@[ext]
lemma ext (ψ ψ' : ContrℂModule) (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl


-- @@ L61-62 verbatim
@[simp]
lemma val_add (ψ ψ' : ContrℂModule) : (ψ + ψ').val = ψ.val + ψ'.val := rfl


-- @@ L64-65 verbatim
@[simp]
lemma val_smul (r : ℂ) (ψ : ContrℂModule) : (r • ψ).val = r • ψ.val := rfl


-- @@ L67-70 verbatim
/-- The linear equivalence between `ContrℂModule` and `(Fin 1 ⊕ Fin 3 → ℂ)`. -/
@[simps!]
def toFin13ℂEquiv : ContrℂModule ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) :=
  Equiv.linearEquiv ℂ toFin13ℂFun


-- @@ L72-74 verbatim
/-- The underlying element of `Fin 1 ⊕ Fin 3 → ℂ` of a element in `ContrℂModule` defined
  through the linear equivalence `toFin13ℂEquiv`. -/
abbrev toFin13ℂ (ψ : ContrℂModule) := toFin13ℂEquiv ψ


-- @@ L76-91 verbatim
/-- The representation of the Lorentz group on `ContrℂModule`. -/
def lorentzGroupRep : Representation ℂ (LorentzGroup 3) ContrℂModule where
  toFun M := {
      toFun := fun v => toFin13ℂEquiv.symm (LorentzGroup.toComplex M *ᵥ v.toFin13ℂ),
      map_add' := by
        intro ψ ψ'
        simp [mulVec_add]
      map_smul' := by
        intro r ψ
        simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' M N := by
    ext i
    simp


-- @@ L93-96 verbatim
/-- The representation of the SL(2, ℂ) on `ContrℂModule` induced by the representation of the
  Lorentz group. -/
def SL2CRep : Representation ℂ SL(2, ℂ) ContrℂModule :=
  MonoidHom.comp lorentzGroupRep Lorentz.SL2C.toLorentzGroup


-- @@ L98-98 verbatim
end ContrℂModule


-- @@ L100-103 verbatim
/-- The module for covariant (up-index) complex Lorentz vectors. -/
structure CoℂModule where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin 3 → ℂ`. -/
  val : Fin 1 ⊕ Fin 3 → ℂ


-- @@ L105-105 verbatim
namespace CoℂModule


-- @@ L107-112 verbatim
/-- The equivalence between `CoℂModule` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
def toFin13ℂFun : CoℂModule ≃ (Fin 1 ⊕ Fin 3 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L114-116 verbatim
/-- The instance of `AddCommMonoid` on `CoℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommMonoid CoℂModule := Equiv.addCommMonoid toFin13ℂFun


-- @@ L118-120 verbatim
/-- The instance of `AddCommGroup` on `CoℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommGroup CoℂModule := Equiv.addCommGroup toFin13ℂFun


-- @@ L122-124 verbatim
/-- The instance of `Module` on `CoℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : Module ℂ CoℂModule := Equiv.module ℂ toFin13ℂFun


-- @@ L126-131 verbatim
@[ext]
lemma ext (ψ ψ' : CoℂModule) (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl


-- @@ L133-134 verbatim
@[simp]
lemma val_add (ψ ψ' : CoℂModule) : (ψ + ψ').val = ψ.val + ψ'.val := rfl


-- @@ L136-137 verbatim
@[simp]
lemma val_smul (r : ℂ) (ψ : CoℂModule) : (r • ψ).val = r • ψ.val := rfl


-- @@ L139-142 verbatim
/-- The linear equivalence between `CoℂModule` and `(Fin 1 ⊕ Fin 3 → ℂ)`. -/
@[simps!]
def toFin13ℂEquiv : CoℂModule ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) :=
  Equiv.linearEquiv ℂ toFin13ℂFun


-- @@ L144-146 verbatim
/-- The underlying element of `Fin 1 ⊕ Fin 3 → ℂ` of a element in `CoℂModule` defined
  through the linear equivalence `toFin13ℂEquiv`. -/
abbrev toFin13ℂ (ψ : CoℂModule) := toFin13ℂEquiv ψ


-- @@ L148-168 verbatim
/-- The representation of the Lorentz group on `CoℂModule`. -/
def lorentzGroupRep : Representation ℂ (LorentzGroup 3) CoℂModule where
  toFun M := {
      toFun := fun v => toFin13ℂEquiv.symm ((LorentzGroup.toComplex M)⁻¹ᵀ *ᵥ v.toFin13ℂ),
      map_add' := by
        intro ψ ψ'
        simp [mulVec_add]
      map_smul' := by
        intro r ψ
        simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' M N := by
    ext1 x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    simp only [_root_.map_mul]
    rw [Matrix.mul_inv_rev]
    exact transpose_mul _ _


-- @@ L170-173 verbatim
/-- The representation of the SL(2, ℂ) on `ContrℂModule` induced by the representation of the
  Lorentz group. -/
def SL2CRep : Representation ℂ SL(2, ℂ) CoℂModule :=
  MonoidHom.comp lorentzGroupRep Lorentz.SL2C.toLorentzGroup


-- @@ L175-175 verbatim
end CoℂModule


-- @@ L177-177 verbatim
end

-- @@ L178-178 verbatim
end Lorentz
