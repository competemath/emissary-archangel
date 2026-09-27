/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.IsHomDiagonal
public import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Option
import LeanPool.QuasiBorelSpaces.Basic
import LeanPool.QuasiBorelSpaces.Nat
import LeanPool.QuasiBorelSpaces.Prop


-- @@ L14-18 verbatim
/-!
# LeanPool.QuasiBorelSpaces.Option

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Option`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace QuasiBorelSpace.Option


-- @@ L24-24 verbatim
variable {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]


-- @@ L26-30 verbatim
/--
We derive the `QuasiBorelSpace` instance for `Option A`s from their encoding as
`Unit ⊕ A`.
-/
abbrev Encoding (A : Type*) := Unit ⊕ A


-- @@ L32-32 verbatim
namespace Encoding


-- @@ L34-35 verbatim
/-- The encoded version of `Option.none`. -/
def none : Encoding A := .inl ()


-- @@ L37-38 verbatim
/-- The encoded version of `Option.some`. -/
def some (x : A) : Encoding A := .inr x


-- @@ L40-42 verbatim
/-- The encoded version of `Option.elim`. -/
def elim (x : B) (f : A → B) : Encoding A → B :=
  Sum.elim (fun _ ↦ x) f


-- @@ L44-47 verbatim
@[fun_prop, simp]
lemma isHom_some : IsHom (some (A := A)) := by
  unfold some
  fun_prop


-- @@ L49-56 verbatim
@[fun_prop]
lemma isHom_elim
    {f : A → C} (hf : IsHom f)
    {g : A → B → C} (hg : IsHom fun (x, y) ↦ g x y)
    {h : A → Encoding B} (hh : IsHom h)
    : IsHom (fun x ↦ elim (f x) (g x) (h x)) := by
  unfold elim
  fun_prop


-- @@ L58-58 verbatim
end Encoding


-- @@ L60-62 verbatim
/-- Encodes an `Option A` as an `Encoding A`. -/
def encode (x : Option A) : Unit ⊕ A :=
  Option.elim x Encoding.none Encoding.some


-- @@ L64-64 verbatim
instance : QuasiBorelSpace (Option A) := lift encode


-- @@ L66-68 verbatim
@[fun_prop, simp]
lemma isHom_encode : IsHom (encode (A := A)) := by
  apply isHom_of_lift


-- @@ L70-73 verbatim
@[fun_prop]
lemma isHom_some {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ some (f x)) := by
  simp only [isHom_to_lift (A := Option _), encode, Option.elim_some]
  fun_prop


-- @@ L75-86 verbatim
@[fun_prop]
lemma isHom_elim
    {f : A → Option B} (hf : IsHom f)
    {g : A → C} (hg : IsHom g)
    {h : A → B → C} (hh : IsHom fun (x, y) ↦ h x y)
    : IsHom (fun x ↦ Option.elim (f x) (g x) (h x)) := by
  have {x}
      : Option.elim (f x) (g x) (h x)
      = Encoding.elim (g x) (h x) (encode (f x)) := by
    cases f x <;> rfl
  simp only [this]
  fun_prop


-- @@ L88-96 verbatim
@[fun_prop]
lemma isHom_map
    {f : A → B → C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : IsHom g)
    : IsHom (fun x ↦ Option.map (f x) (g x)) := by
  have {x} : Option.map (f x) (g x) = Option.elim (g x) .none (.some ∘ f x) := by
    cases g x <;> rfl
  simp only [this]
  fun_prop


-- @@ L98-106 verbatim
@[fun_prop]
lemma isHom_bind
    {f : A → B → Option C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : IsHom g)
    : IsHom (fun x ↦ Option.bind (g x) (f x)) := by
  have {x} : Option.bind (g x) (f x) = Option.elim (g x) .none (f x) := by
    cases g x <;> rfl
  simp only [this]
  fun_prop


-- @@ L108-115 verbatim
@[fun_prop]
lemma isHom_bind'
    {C : Type _} [QuasiBorelSpace C]
    {f : A → B → Option C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : IsHom g)
    : IsHom (fun x ↦ g x >>= f x) := by
  simp only [Option.bind_eq_bind]
  fun_prop


-- @@ L117-125 verbatim
@[fun_prop]
lemma isHom_getD
    {f : A → Option B} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ (f x).getD (g x)) := by
  have {x} : Option.getD (f x) (g x) = Option.elim (f x) (g x) id := by
    cases f x <;> rfl
  simp only [this]
  fun_prop


-- @@ L127-132 verbatim
@[simp, fun_prop]
lemma isHom_isSome : IsHom (fun x : Option A ↦ x.isSome) := by
  have (x : Option A) : x.isSome = x.elim false (fun _ ↦ true) := by
    cases x <;> rfl
  simp only [this]
  fun_prop


-- @@ L134-139 verbatim
@[simp, fun_prop]
lemma isHom_isNone : IsHom (fun x : Option A ↦ x.isNone) := by
  have (x : Option A) : x.isNone = x.elim true (fun _ ↦ false) := by
    cases x <;> rfl
  simp only [this]
  fun_prop


-- @@ L141-149 verbatim
instance [IsHomDiagonal A] : IsHomDiagonal (Option A) where
  isHom_eq := by
    have {x y : Option A}
        : x = y
        ↔ x.elim (y.elim True (fun _ ↦ False)) (fun x ↦ y.elim False (x = ·)) := by
      cases x <;> cases y <;>
        simp only [reduceCtorEq, Option.elim_none, Option.elim_some, Option.some.injEq]
    simp only [this]
    fun_prop


-- @@ L151-151 verbatim
end QuasiBorelSpace.Option


-- @@ L153-153 verbatim
namespace OmegaQuasiBorelSpace.Option


-- @@ L155-155 verbatim
open QuasiBorelSpace

-- @@ L156-156 verbatim
open OmegaCompletePartialOrder


-- @@ L158-158 verbatim
variable {A B : Type*}


-- @@ L160-177 verbatim
@[fun_prop]
lemma isHom_project
    [QuasiBorelSpace A] [QuasiBorelSpace B] [Preorder B]
    {f : A → Chain (Option B)} (hf : IsHom f)
    (g : ∀ x, ∃ n, (f x n).isSome)
    : IsHom (fun x ↦ Chain.Option.project (f x) (g x)) := by
  simp only [Chain.isHom_iff, Chain.Option.project_coe]
  intro i
  apply Option.isHom_getD
  · apply isHom_cases (f := fun n x ↦ f x n)
    · apply Nat.isHom_add'
      · apply Nat.isHom_find fun n ↦ ?_
        apply isHom_eq'
        · exact isHom_comp' Option.isHom_isSome (isHom_comp' (Chain.isHom_apply n) hf)
        · fun_prop
      · fun_prop
    · simp_all
  · fun_prop


-- @@ L179-191 verbatim
@[fun_prop]
lemma isHom_distrib [QuasiBorelSpace A] [Preorder A] : IsHom (Chain.Option.distrib (A := A)) := by
  classical
  rw [isHom_def]
  intro φ hφ
  simp only [Chain.Option.distrib]
  apply Prop.isHom_dite
  · apply Prop.isHom_exists fun i ↦ ?_
    apply isHom_eq'
    · exact isHom_comp' Option.isHom_isSome (isHom_comp' (Chain.isHom_apply i) hφ)
    · fun_prop
  · fun_prop
  · fun_prop


-- @@ L193-197 verbatim
noncomputable instance [OmegaQuasiBorelSpace A] : OmegaQuasiBorelSpace (Option A) where
  isHom_ωSup := by
    change IsHom fun r ↦ ωSup _
    simp only [ωSup]
    fun_prop


-- @@ L199-199 verbatim
end OmegaQuasiBorelSpace.Option
