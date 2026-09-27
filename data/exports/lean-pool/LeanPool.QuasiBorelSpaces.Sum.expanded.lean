/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.Lift
public import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Sum
public import LeanPool.QuasiBorelSpaces.Sigma
import LeanPool.QuasiBorelSpaces.Basic
import LeanPool.QuasiBorelSpaces.Hom


-- @@ L14-21 verbatim
/-!
# Binary Coproducts of Quasi-Borel Spaces

This file defines binary coproducts of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `· ⊕ ·` type.

See [HeunenKSY17], Proposition 17.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace QuasiBorelSpace.Sum


-- @@ L27-27 verbatim
universe u v


-- @@ L29-34 verbatim
variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {D : Type*} [QuasiBorelSpace D]
  {E : Type*} [QuasiBorelSpace E]


-- @@ L36-41 verbatim
/--
We derive the `QuasiBorelSpace` instance for `A ⊕ B` via `Sigma (Encoding A B)`.
-/
def Encoding (A : Type u) (B : Type v) : Bool → Type (max u v)
  | true => ULift A
  | false => ULift B


-- @@ L43-43 verbatim
namespace Encoding


-- @@ L45-46 verbatim
/-- The encoded version of `Sum.inl`. -/
def inl (x : A) : Sigma (Encoding A B) := ⟨true, ⟨x⟩⟩


-- @@ L48-49 verbatim
/-- The encoded version of `Sum.inr`. -/
def inr (x : B) : Sigma (Encoding A B) := ⟨false, ⟨x⟩⟩


-- @@ L51-54 verbatim
/-- The encoded version of `Sum.elim`. -/
def elim (f : A → C) (g : B → C) : Sigma (Encoding A B) → C
  | ⟨true, x⟩ => f x.down
  | ⟨false, x⟩ => g x.down


-- @@ L56-59 verbatim
instance {b : Bool} : QuasiBorelSpace (Encoding A B b) := by
  cases b <;>
  · dsimp only [Encoding]
    infer_instance


-- @@ L61-64 verbatim
@[fun_prop]
lemma isHom_inl : IsHom (inl (A := A) (B := B)) := by
  unfold inl
  fun_prop


-- @@ L66-69 verbatim
@[fun_prop]
lemma isHom_inr : IsHom (inr (A := A) (B := B)) := by
  unfold inr
  fun_prop


-- @@ L71-76 verbatim
@[fun_prop]
lemma isHom_elim {f : A → C} (hf : IsHom f) {g : B → C} (hg : IsHom g) : IsHom (elim f g) := by
  apply Sigma.isHom_elim fun b ↦ ?_
  cases b <;>
  · simp only [elim]
    fun_prop


-- @@ L78-78 verbatim
end Encoding


-- @@ L80-82 verbatim
/-- Encodes an `A ⊕ B` as a `Sigma (Encoding A B)`. -/
def encode : A ⊕ B → Sigma (Encoding A B) :=
  Sum.elim Encoding.inl Encoding.inr


-- @@ L84-84 verbatim
instance : QuasiBorelSpace (A ⊕ B) := lift encode


-- @@ L86-88 verbatim
@[fun_prop]
lemma isHom_encode : IsHom (encode (A := A) (B := B)) := by
  apply isHom_of_lift


-- @@ L90-93 verbatim
@[simp]
lemma isHom_inl : IsHom (Sum.inl : A → A ⊕ B) := by
  simp only [isHom_to_lift, encode, Sum.elim_inl]
  fun_prop


-- @@ L95-97 verbatim
@[fun_prop]
lemma isHom_inl' {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ Sum.inl (f x) : A → B ⊕ C) :=
  isHom_comp isHom_inl hf


-- @@ L99-102 verbatim
@[simp]
lemma isHom_inr : IsHom (Sum.inr : B → A ⊕ B) := by
  simp only [isHom_to_lift, encode, Sum.elim_inr]
  fun_prop


-- @@ L104-106 verbatim
@[fun_prop]
lemma isHom_inr' {f : A → C} (hf : IsHom f) : IsHom (fun x ↦ Sum.inr (f x) : A → B ⊕ C) :=
  isHom_comp isHom_inr hf


-- @@ L108-117 verbatim
@[local fun_prop]
lemma isHom_elim
    {f : A → C} (hf : IsHom f)
    {g : B → C} (hg : IsHom g)
    : IsHom (Sum.elim f g) := by
  have : Sum.elim f g = fun x ↦ Encoding.elim f g (encode x) := by
    ext x
    cases x <;> rfl
  rw [this]
  fun_prop


-- @@ L119-130 expanded
@[fun_prop]
lemma isHom_elim' {f : A → B → D} (hf : IsHom (fun x : A × B ↦ f x.1 x.2)) {g : A → C → D}
    (hg : IsHom (fun x : A × C ↦ g x.1 x.2)) {h : A → B ⊕ C} (hh : IsHom h) :
    IsHom (fun x ↦ Sum.elim (f x) (g x) (h x)) :=
  by
  have {x} :
    Sum.elim (f x) (g x) (h x) =
      Sum.elim (γ := QuasiBorelHom A D) (fun x ↦ .mk (f · x)) (fun x ↦ .mk (g · x)) (h x) x :=
    by cases h x <;> rfl
  simp only [this]
  fun_prop


-- @@ L132-139 verbatim
@[fun_prop]
lemma isHom_map
    {f : A → B → D} (hf : IsHom fun x : A × B ↦ f x.1 x.2)
    {g : A → C → E} (hg : IsHom fun x : A × C ↦ g x.1 x.2)
    {h : A → B ⊕ C} (hh : IsHom h)
    : IsHom (fun x ↦ Sum.map (f x) (g x) (h x)) := by
  change IsHom fun x ↦ Sum.elim (Sum.inl ∘ f x) (Sum.inr ∘ g x) (h x)
  fun_prop


-- @@ L141-147 verbatim
@[fun_prop, simp]
lemma isHom_isLeft : IsHom (Sum.isLeft : A ⊕ B → Bool) := by
  have : (Sum.isLeft : A ⊕ B → Bool) = Sum.elim (fun _ ↦ true) (fun _ ↦ false) := by
    ext x
    cases x <;> rfl
  rw [this]
  fun_prop


-- @@ L149-149 verbatim
end QuasiBorelSpace.Sum


-- @@ L151-151 verbatim
namespace OmegaQuasiBorelSpace.Sum


-- @@ L153-153 verbatim
open QuasiBorelSpace

-- @@ L154-154 verbatim
open OmegaCompletePartialOrder


-- @@ L156-156 verbatim
variable {A B C : Type*}


-- @@ L158-168 verbatim
@[fun_prop]
lemma isHom_projl
    [Preorder A] [QuasiBorelSpace A]
    [Preorder B] [QuasiBorelSpace B]
    [QuasiBorelSpace C]
    {f : C → Chain (A ⊕ B)} (hf : IsHom f)
    {g : C → A} (hg : IsHom g)
    : IsHom (fun x ↦ Chain.Sum.projl (hA := ⟨g x⟩) (f x)) := by
  simp only [Chain.isHom_iff, Chain.Sum.projl_coe]
  intro i
  exact Sum.isHom_elim' (by fun_prop) (by fun_prop) (isHom_comp' (Chain.isHom_apply i) hf)


-- @@ L170-180 verbatim
@[fun_prop]
lemma isHom_projr
    [Preorder A] [QuasiBorelSpace A]
    [Preorder B] [QuasiBorelSpace B]
    [QuasiBorelSpace C]
    {f : C → Chain (A ⊕ B)} (hf : IsHom f)
    {g : C → B} (hb : IsHom g)
    : IsHom (fun x ↦ Chain.Sum.projr (hB := ⟨g x⟩) (f x)) := by
  simp only [Chain.isHom_iff, Chain.Sum.projr_coe]
  intro i
  exact Sum.isHom_elim' (by fun_prop) (by fun_prop) (isHom_comp' (Chain.isHom_apply i) hf)


-- @@ L182-188 verbatim
@[fun_prop, simp]
lemma isHom_distrib
    [Preorder A] [QuasiBorelSpace A]
    [Preorder B] [QuasiBorelSpace B]
    : IsHom (Chain.Sum.distrib (A := A) (B := B)) := by
  simp (unfoldPartialApp := true) only [Chain.Sum.distrib]
  fun_prop


-- @@ L190-196 verbatim
/-- Coproduct of omega quasi-borel spaces is again an omega quasi-borel space. -/
noncomputable instance
    [OmegaQuasiBorelSpace A] [OmegaQuasiBorelSpace B] :
    OmegaQuasiBorelSpace (A ⊕ B) where
  isHom_ωSup := by
    simp only [ωSup]
    fun_prop


-- @@ L198-198 verbatim
end OmegaQuasiBorelSpace.Sum
