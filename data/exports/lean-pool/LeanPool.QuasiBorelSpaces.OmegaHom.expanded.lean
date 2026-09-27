/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.Hom
public import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import LeanPool.QuasiBorelSpaces.Basic


-- @@ L12-18 verbatim
/-!
# Exponentials for ω-quasi-borel spaces

This file defines the function space `OmegaQuasiBorelHom X Y` (written
`X →ω𝒒 Y`) of Scott-continuous QBS morphisms. It proves that this space is
itself an ωQBS.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open QuasiBorelSpace

-- @@ L23-23 verbatim
open OmegaQuasiBorelSpace

-- @@ L24-24 verbatim
open OmegaCompletePartialOrder


-- @@ L26-35 verbatim
/--
Exponential objects: functions that are both Scott-Continuous and Measurable (QBS Morphisms)
-/
structure OmegaQuasiBorelHom
    (X Y : Type*)
    [OmegaQuasiBorelSpace X] [OmegaQuasiBorelSpace Y] where
  /-- The underlying function of an ω-quasi-borel morphism. -/
  toFun : X → Y
  isHom' : IsHom toFun := by fun_prop
  ωScottContinuous' : ωScottContinuous toFun := by fun_prop


-- @@ L37-37 verbatim
@[inherit_doc] infixr:25 " →ω𝒒 " => OmegaQuasiBorelHom


-- @@ L39-39 verbatim
namespace OmegaQuasiBorelHom


-- @@ L41-41 verbatim
variable {X Y Z : Type*} [OmegaQuasiBorelSpace X] [OmegaQuasiBorelSpace Y] [OmegaQuasiBorelSpace Z]


-- @@ L43-47 expanded
instance : FunLike (OmegaQuasiBorelHom X Y) X Y
    where
  coe f := (f.1 : X → Y)
  coe_injective f g
    h := by
    cases f
    simp_all


-- @@ L49-49 verbatim
namespace Simps


-- @@ L51-52 expanded
/-- A simps projection for function coercion. -/
def coe (f : OmegaQuasiBorelHom X Y) : X → Y :=
  f


-- @@ L54-54 verbatim
end Simps


-- @@ L56-56 verbatim
initialize_simps_projections OmegaQuasiBorelHom (toFun → coe)


-- @@ L58-59 expanded
@[ext]
lemma ext {f g : OmegaQuasiBorelHom X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h


-- @@ L61-68 expanded
/-- Copy of a `OmegaQuasiBorelHom` with a new `toFun` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (f : OmegaQuasiBorelHom X Y) (f' : X → Y) (h : f' = ⇑f) : OmegaQuasiBorelHom X Y
    where
  toFun := f'
  isHom' := h.symm ▸ f.isHom'
  ωScottContinuous' := h.symm ▸ f.ωScottContinuous'


-- @@ L70-71 verbatim
@[simp]
lemma coe_mk {f : X → Y} (hf₁ : IsHom f) (hf₂ : ωScottContinuous f) : ⇑(mk f hf₁ hf₂) = f := rfl


-- @@ L73-74 expanded
@[simp]
lemma eta (f : OmegaQuasiBorelHom X Y) : mk f f.isHom' f.ωScottContinuous' = f :=
  rfl


-- @@ L76-77 expanded
@[simp]
lemma toFun_eq_coe (f : OmegaQuasiBorelHom X Y) : toFun f = ⇑f :=
  rfl


-- @@ L79-80 expanded
@[simp, fun_prop]
lemma isHom_coe (f : OmegaQuasiBorelHom X Y) : IsHom (f : X → Y) :=
  f.2


-- @@ L82-83 expanded
@[simp, fun_prop]
lemma ωScottContinuous_coe (f : OmegaQuasiBorelHom X Y) : ωScottContinuous (f : X → Y) :=
  f.3


-- @@ L85-86 expanded
@[simp]
lemma monotone_coe (f : OmegaQuasiBorelHom X Y) : Monotone (f : X → Y) :=
  f.3.monotone


-- @@ L88-89 expanded
instance : PartialOrder (OmegaQuasiBorelHom X Y) :=
  PartialOrder.lift DFunLike.coe DFunLike.coe_injective


-- @@ L91-95 expanded
/-- Converts an ωQBS Hom to a Poset Hom. -/
@[simps, coe]
def toOrderHom (f : OmegaQuasiBorelHom X Y) : X →o Y
    where
  toFun := f
  monotone' := f.monotone_coe


-- @@ L97-102 expanded
/-- Converts a ωQBS Hom to an ωCPO Hom. -/
@[simps, coe]
def toContinuousHom (f : OmegaQuasiBorelHom X Y) : X →𝒄 Y
    where
  toFun := f
  monotone' := f.monotone_coe
  map_ωSup' := f.ωScottContinuous_coe.map_ωSup


-- @@ L104-107 expanded
/-- Converts a ωQBS Hom to a quasi-Borel Hom. -/
@[simps, coe]
def toQuasiBorelHom (f : OmegaQuasiBorelHom X Y) : QuasiBorelHom X Y where toFun := f


-- @@ L109-112 expanded
/-- The underlying pointwise function as an order homomorphism. -/
def coeOrderHom : (OmegaQuasiBorelHom X Y) →o (X → Y)
    where
  toFun f := f
  monotone' _ _ h := h


-- @@ L114-115 expanded
@[simp]
private lemma coeOrderHom_apply (f : OmegaQuasiBorelHom X Y) (x : X) : coeOrderHom f x = f x :=
  rfl


-- @@ L117-143 expanded
/-- The ωCPO structure on the exponential is the pointwise order. -/
@[simps!]
instance : OmegaCompletePartialOrder (OmegaQuasiBorelHom X Y) :=
  OmegaCompletePartialOrder.lift coeOrderHom
    (fun c ↦
      { toFun := ωSup (c.map coeOrderHom)
        isHom' := by
          apply isHom_ωSup'
          simp only [Chain.isHom_iff, Chain.coe_map, Pi.evalOrderHom_coe, Function.comp_apply,
            Function.eval, coeOrderHom_apply]
          intro i
          exact (c i).isHom'
        ωScottContinuous' :=
          by
          let c' : Chain (X →𝒄 Y) :=
            { toFun n := (c n).toContinuousHom
              monotone' i j h := c.monotone h }
          change ωScottContinuous (DFunLike.coe (ωSup c'))
          apply ContinuousHom.ωScottContinuous })
    (fun _ _ h ↦ h)
    (by
      intro c
      funext x
      rfl)


-- @@ L145-161 expanded
/-- The QBS structure on the ωHoms is identical to normal QBS Homs. -/
instance : QuasiBorelSpace (OmegaQuasiBorelHom X Y)
    where
  IsVar φ := IsHom (fun x : ℝ × X ↦ φ x.1 x.2)
  isVar_const f := by fun_prop
  isVar_comp hf
    hφ := by
    rw [← isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' {ix} {φ} hix
    hφ := by
    rw [← isHom_iff_measurable] at hix
    let ix' := fun (p : ℝ × X) ↦ ix p.1
    have hix' : IsHom ix' := by
      apply isHom_comp (hf := hix)
      exact Prod.isHom_fst
    let branches := fun n (p : ℝ × X) ↦ (φ n p.1) p.2
    apply isHom_cases (ix := ix') (f := branches)
    · exact hix'
    · exact hφ


-- @@ L163-163 expanded
instance : MeasurableSpace (OmegaQuasiBorelHom X Y) :=
  toMeasurableSpace


-- @@ L165-169 expanded
@[local simp]
lemma isHom_def (φ : ℝ → OmegaQuasiBorelHom X Y) : IsHom φ ↔ IsHom (fun x : ℝ × X ↦ φ x.1 x.2) :=
  by
  rw [← isVar_iff_isHom]
  rfl


-- @@ L171-179 expanded
@[simp]
lemma isHom_eval : IsHom (fun p : (OmegaQuasiBorelHom X Y) × X ↦ p.1 p.2) :=
  by
  rw [QuasiBorelSpace.isHom_def]
  intro φ hφ
  have h_func : IsHom (fun r ↦ (φ r).1) := isHom_comp Prod.isHom_fst hφ
  have h_arg : IsHom (fun r ↦ (φ r).2) := isHom_comp Prod.isHom_snd hφ
  rw [isHom_def] at h_func
  have h_input : IsHom (fun r : ℝ ↦ (r, (φ r).2)) := Prod.isHom_mk isHom_id h_arg
  apply isHom_comp (hf := h_func) (hg := h_input)


-- @@ L181-210 expanded
@[simp]
lemma ωScottContinuous_eval : ωScottContinuous (fun p : (OmegaQuasiBorelHom X Y) × X ↦ p.1 p.2) :=
  by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y ⟨h₁, h₂⟩ ↦ ?_, fun c ↦ ?_⟩
  · exact (h₁ _).trans (y.1.monotone_coe h₂)
  · simp only [Prod.ωSup_fst, Prod.ωSup_snd, ωSup_coe]
    apply le_antisymm
    · simp only [ωSup, ωSup_le_iff, Chain.coe_map, Pi.evalOrderHom_coe, Function.comp_apply,
        Function.eval, OrderHom.fst_coe]
      intro i
      change (c i).1 (ωSup (c.map OrderHom.snd)) ≤ _
      rw [(c i).1.ωScottContinuous_coe.map_ωSup]
      simp only [ωSup_le_iff, Chain.coe_map, OrderHom.coe_mk, Function.comp_apply, OrderHom.snd_coe]
      intro j
      apply le_ωSup_of_le (i ⊔ j)
      simp only [Chain.coe_map, Function.comp_apply]
      trans
      · apply (c.monotone (by grind : i ≤ i ⊔ j)).1
      · apply (c (i ⊔ j)).1.monotone_coe
        apply (c.monotone (by grind : j ≤ i ⊔ j)).2
    · simp only [ωSup_le_iff, Chain.coe_map, Function.comp_apply]
      intro i
      apply le_ωSup_of_le i
      simp only [Chain.coe_map, Pi.evalOrderHom_coe, Function.comp_apply, Function.eval,
        OrderHom.fst_coe]
      apply (c i).1.monotone_coe
      apply le_ωSup_of_le i
      simp only [Chain.coe_map, Function.comp_apply, OrderHom.snd_coe, le_refl]


-- @@ L212-218 expanded
omit [OmegaQuasiBorelSpace X] in
@[fun_prop]
lemma isHom_eval' [QuasiBorelSpace X] {f : X → OmegaQuasiBorelHom Y Z} (hf : IsHom f) {g : X → Y}
    (hg : IsHom g) : IsHom (fun x ↦ f x (g x)) := by
  exact isHom_comp' (f := fun x ↦ x.1 x.2) (g := fun x ↦ (f x, g x)) isHom_eval (by fun_prop)


-- @@ L220-226 expanded
@[fun_prop]
lemma ωScottContinuous_eval' {f : X → OmegaQuasiBorelHom Y Z} (hf : ωScottContinuous f) {g : X → Y}
    (hg : ωScottContinuous g) : ωScottContinuous (fun x ↦ f x (g x)) := by
  exact
    ωScottContinuous.comp (g := fun x ↦ x.1 x.2) (f := fun x ↦ (f x, g x)) ωScottContinuous_eval
      (by fun_prop)


-- @@ L228-243 expanded
omit [OmegaQuasiBorelSpace X] in
@[simp]
lemma isHom_iff [QuasiBorelSpace X] (f : X → OmegaQuasiBorelHom Y Z) :
    IsHom f ↔ IsHom (fun x : X × Y ↦ f x.1 x.2) :=
  by
  apply Iff.intro
  · intro hf
    rw [QuasiBorelSpace.isHom_def]
    simp only [Prod.isHom_iff, and_imp]
    intro φ hφ₁ hφ₂
    fun_prop
  · intro hf
    rw [QuasiBorelSpace.isHom_def]
    intro φ hφ
    simp only [isHom_def]
    fun_prop


-- @@ L245-251 verbatim
@[fun_prop]
lemma isHom_mk
    {f : X → Y → Z}
    (h₁ : IsHom fun x : X × Y ↦ f x.1 x.2)
    (h₂ : ∀x, ωScottContinuous (f x))
    : IsHom fun x ↦ mk (f x) (by fun_prop) (h₂ x) := by
  simp only [isHom_iff, coe_mk, h₁]


-- @@ L253-273 verbatim
@[fun_prop]
lemma ωScottContinuous_mk
    {f : X → Y → Z}
    (h₁ : ∀ x, IsHom (f x))
    (h₂ : ωScottContinuous fun x : X × Y ↦ f x.1 x.2)
    : ωScottContinuous fun x ↦ mk (f x) (h₁ x) (by fun_prop) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y h z ↦ ?_, fun c ↦ ?_⟩
  · have : (x, z) ≤ (y, z) := ⟨h, le_rfl⟩
    exact h₂.monotone this
  · ext x
    simp only [coe_mk, ωSup]
    rw [(by simp only [ωSup_const] : x = ωSup (Chain.const x))]
    change f (ωSup (Chain.zip c (Chain.const x))).1 (ωSup (Chain.zip c (Chain.const x))).2 = _
    rw [h₂.map_ωSup]
    congr 1
    ext n
    simp only [
      Chain.coe_map, OrderHom.coe_mk, Function.comp_apply, Chain.zip_apply,
      Chain.const_apply, ωSup_const, Pi.evalOrderHom_coe, Function.eval]
    rfl


-- @@ L275-290 expanded
/-- The exponential object is an ωQBS. -/
instance : OmegaQuasiBorelSpace (OmegaQuasiBorelHom X Y) where
  isHom_ωSup := by
    simp only [ωSup, isHom_iff, coe_mk]
    apply isHom_ωSup'
    simp only [Chain.isHom_iff, Chain.coe_map, Pi.evalOrderHom_coe, Function.comp_apply,
      Function.eval]
    intro i
    apply
      isHom_comp' (f := fun x : (OmegaQuasiBorelHom X Y) × X ↦ x.1 x.2) (g :=
        fun x : Chain (OmegaQuasiBorelHom X Y) × X ↦ (x.1 i, x.2))
    · fun_prop
    · apply Prod.isHom_mk
      · apply isHom_comp' (Chain.isHom_apply i) Prod.isHom_fst
      · fun_prop


-- @@ L292-292 verbatim
/-! ### Operations -/


-- @@ L294-297 expanded
/-- Identity `OmegaQuasiBorelHom`s. -/
@[simps]
def id : OmegaQuasiBorelHom X X where toFun x := x


-- @@ L299-302 expanded
/-- Function composition for `OmegaQuasiBorelHom`s. -/
@[simps coe]
def comp (f : OmegaQuasiBorelHom Y Z) (g : OmegaQuasiBorelHom X Y) : OmegaQuasiBorelHom X Z where
  toFun x := f (g x)


-- @@ L304-307 expanded
/-- Product construction as an `OmegaQuasiBorelHom`. -/
@[simps coe]
def Prod.mk (f : OmegaQuasiBorelHom X Y) (g : OmegaQuasiBorelHom X Z) : OmegaQuasiBorelHom X (Y × Z)
    where toFun x := (f x, g x)


-- @@ L309-312 expanded
/-- First product projection. -/
@[simps coe]
def Prod.fst : OmegaQuasiBorelHom (X × Y) X where toFun x := x.1


-- @@ L314-317 expanded
/-- Second product projection. -/
@[simps coe]
def Prod.snd : OmegaQuasiBorelHom (X × Y) Y where toFun x := x.2


-- @@ L319-322 expanded
/-- Currying for `OmegaQuasiBorelHom`s. -/
@[simps coe]
def curry (f : OmegaQuasiBorelHom (Z × X) Y) : OmegaQuasiBorelHom Z (OmegaQuasiBorelHom X Y) where
  toFun x := { toFun y := f (x, y) }


-- @@ L324-327 expanded
/-- Function application is an `OmegaQuasiBorelHom`. -/
@[simps coe]
def eval : OmegaQuasiBorelHom ((OmegaQuasiBorelHom X Y) × X) Y where toFun x := x.1 x.2


-- @@ L329-332 expanded
/-- Uncurrying for `OmegaQuasiBorelHom`s. -/
@[simps!]
def uncurry (f : OmegaQuasiBorelHom X (OmegaQuasiBorelHom Y Z)) : OmegaQuasiBorelHom (X × Y) Z :=
  eval.comp (Prod.mk (comp f Prod.fst) Prod.snd)


-- @@ L334-335 expanded
@[simp]
lemma curry_uncurry (f : OmegaQuasiBorelHom Z (OmegaQuasiBorelHom X Y)) : curry (uncurry f) = f :=
  rfl


-- @@ L337-338 expanded
@[simp]
lemma uncurry_curry (f : OmegaQuasiBorelHom (Z × X) Y) : uncurry (curry f) = f :=
  rfl


-- @@ L340-340 verbatim
end OmegaQuasiBorelHom
