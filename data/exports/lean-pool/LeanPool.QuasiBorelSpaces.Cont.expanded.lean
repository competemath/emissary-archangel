/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.OmegaHom
import LeanPool.QuasiBorelSpaces.Basic


-- @@ L11-15 verbatim
/-!
# LeanPool.QuasiBorelSpaces.Cont

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Cont`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open QuasiBorelSpace

-- @@ L20-20 verbatim
open OmegaCompletePartialOrder


-- @@ L22-22 verbatim
namespace OmegaQuasiBorelSpace


-- @@ L24-27 expanded
/-- The continuation monad in the category of `OmegaQuasiBorelSpace`s. -/
structure Cont (R A : Type*) [OmegaQuasiBorelSpace R] [OmegaQuasiBorelSpace A] where
  /-- The underlying morphism. -/
  apply : OmegaQuasiBorelHom (OmegaQuasiBorelHom A R) R


-- @@ L29-29 verbatim
namespace Cont


-- @@ L31-31 verbatim
variable {R A B : Type*} [OmegaQuasiBorelSpace R] [OmegaQuasiBorelSpace A]


-- @@ L33-36 verbatim
@[ext]
lemma ext {x y : Cont R A} (h : x.apply = y.apply) : x = y := by
  cases x
  simp_all


-- @@ L38-41 verbatim
instance : PartialOrder (Cont R A) :=
  PartialOrder.lift apply (by
    rintro ⟨x⟩ ⟨y⟩
    simp only [mk.injEq, imp_self])


-- @@ L43-46 expanded
/-- The underlying continuation as an order homomorphism. -/
def applyOrderHom : Cont R A →o (OmegaQuasiBorelHom (OmegaQuasiBorelHom A R) R)
    where
  toFun := apply
  monotone' _ _ h := h


-- @@ L48-54 verbatim
instance : OmegaCompletePartialOrder (Cont R A) := by
  refine OmegaCompletePartialOrder.lift applyOrderHom
    (fun c ↦ ⟨ωSup (c.map applyOrderHom)⟩) ?_ ?_
  · intro ⟨x⟩ ⟨y⟩
    exact id
  · intro c
    rfl


-- @@ L56-57 verbatim
instance : QuasiBorelSpace (Cont R A) :=
  QuasiBorelSpace.lift apply


-- @@ L59-62 verbatim
@[local fun_prop]
lemma isHom_val : IsHom (apply (R := R) (A := A)) := by
  rw [← isHom_to_lift]
  simp only [isHom_id']


-- @@ L64-68 verbatim
@[fun_prop]
lemma isHom_val'
    [QuasiBorelSpace B] {f : B → Cont R A} (hf : IsHom f)
    : IsHom (fun x ↦ (f x).apply) := by
  fun_prop


-- @@ L70-72 verbatim
@[simp, local fun_prop]
lemma isHom_mk : IsHom (mk (R := R) (A := A)) := by
  apply isHom_of_lift


-- @@ L74-78 expanded
@[fun_prop]
lemma isHom_mk' [QuasiBorelSpace B] {f : B → OmegaQuasiBorelHom (OmegaQuasiBorelHom A R) R}
    (hf : IsHom f) : IsHom (fun x ↦ mk (f x)) := by fun_prop


-- @@ L80-85 verbatim
@[simp, local fun_prop]
lemma ωScottContinuous_mk : ωScottContinuous (mk (R := R) (A := A)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y h k ↦ ?_, fun c ↦ ?_⟩
  · apply h
  · rfl


-- @@ L87-91 expanded
@[fun_prop]
lemma ωScottContinuous_mk' [OmegaCompletePartialOrder B]
    {f : B → OmegaQuasiBorelHom (OmegaQuasiBorelHom A R) R} (hf : ωScottContinuous f) :
    ωScottContinuous (fun x ↦ mk (f x)) := by fun_prop


-- @@ L93-98 verbatim
@[simp, local fun_prop]
lemma ωScottContinuous_val : ωScottContinuous (apply (R := R) (A := A)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y h k ↦ ?_, fun c ↦ ?_⟩
  · apply h
  · rfl


-- @@ L100-104 verbatim
@[fun_prop]
lemma ωScottContinuous_val'
    [OmegaCompletePartialOrder B] {f : B → Cont R A} (hf : ωScottContinuous f)
    : ωScottContinuous (fun x ↦ (f x).apply) := by
  fun_prop


-- @@ L106-120 verbatim
instance : OmegaQuasiBorelSpace (Cont R A) where
  isHom_ωSup := by
    change IsHom fun x ↦ mk _
    apply isHom_comp' isHom_mk
    apply isHom_ωSup'
    simp only [
      Chain.isHom_iff, Chain.coe_map, Function.comp_apply, OmegaQuasiBorelHom.isHom_iff]
    intro i
    apply isHom_comp'
        (f := fun x : Cont R A × _ ↦ x.1.apply x.2)
        (g := fun x : Chain (Cont R A) × _ ↦ (x.1 i, x.2))
        (by fun_prop)
    apply Prod.isHom_mk
    · apply isHom_comp' (Chain.isHom_apply i) Prod.isHom_fst
    · apply Prod.isHom_snd


-- @@ L122-125 expanded
/-- The `unit` operator (i.e., pure values) for the continuation monad. -/
@[simps]
def unit : OmegaQuasiBorelHom A (Cont R A) where toFun x := ⟨{ toFun k := k x }⟩


-- @@ L127-130 expanded
/-- The `bind` operator (i.e., sequential composition) for the continuation monad. -/
@[simps]
def bind [OmegaQuasiBorelSpace B] :
    OmegaQuasiBorelHom (OmegaQuasiBorelHom A (Cont R B)) (OmegaQuasiBorelHom (Cont R A) (Cont R B))
    where toFun f := { toFun x := ⟨{ toFun k := x.apply { toFun y := (f y).apply k } }⟩ }


-- @@ L132-133 expanded
@[simp]
lemma bind_unit [OmegaQuasiBorelSpace B] (f : OmegaQuasiBorelHom A (Cont R B)) (x : A) :
    bind f (unit x) = f x :=
  rfl


-- @@ L135-136 verbatim
@[simp]
lemma unit_bind : bind (unit (R := R) (A := A)) = .id := rfl


-- @@ L138-143 expanded
@[simp]
lemma bind_bind {C : Type*} [OmegaQuasiBorelSpace B] [OmegaQuasiBorelSpace C]
    (f : OmegaQuasiBorelHom B (Cont R C)) (g : OmegaQuasiBorelHom A (Cont R B)) :
    (bind f).comp (bind g) = bind ((bind f).comp g) :=
  rfl


-- @@ L145-145 verbatim
end Cont


-- @@ L147-147 verbatim
end OmegaQuasiBorelSpace
