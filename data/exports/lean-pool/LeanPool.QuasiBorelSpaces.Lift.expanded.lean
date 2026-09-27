/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.Defs
import LeanPool.QuasiBorelSpaces.Basic


-- @@ L11-15 verbatim
/-!
# LeanPool.QuasiBorelSpaces.Lift

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Lift`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]


-- @@ L21-21 verbatim
namespace QuasiBorelSpace.ULift


-- @@ L23-23 verbatim
instance : QuasiBorelSpace (ULift A) := lift ULift.down


-- @@ L25-27 verbatim
@[simp]
lemma isHom_def {φ : A → ULift B} : IsHom φ ↔ IsHom (fun x ↦ (φ x).down) := by
  simp only [isHom_to_lift]


-- @@ L29-31 verbatim
@[fun_prop]
lemma isHom_up {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ ULift.up (f x)) := by
  simp only [isHom_def, hf]


-- @@ L33-35 verbatim
@[fun_prop]
lemma isHom_down {f : A → ULift B} (hf : IsHom f) : IsHom (fun x ↦ ULift.down (f x)) := by
  simp_all


-- @@ L37-37 verbatim
end QuasiBorelSpace.ULift


-- @@ L39-39 verbatim
namespace QuasiBorelSpace.PLift


-- @@ L41-41 verbatim
instance : QuasiBorelSpace (PLift A) := lift PLift.down


-- @@ L43-45 verbatim
@[simp]
lemma isHom_def {φ : A → PLift B} : IsHom φ ↔ IsHom (fun x ↦ (φ x).down) := by
  simp only [isHom_to_lift]


-- @@ L47-49 verbatim
@[fun_prop]
lemma isHom_up {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ PLift.up (f x)) := by
  simp only [isHom_def, hf]


-- @@ L51-53 verbatim
@[fun_prop]
lemma isHom_down {f : A → PLift B} (hf : IsHom f) : IsHom (fun x ↦ PLift.down (f x)) := by
  simp_all


-- @@ L55-55 verbatim
end QuasiBorelSpace.PLift
