/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.UnitInterval


-- @@ L14-18 verbatim
/-!
# LeanPool.WhiteheadTheorem.Exponential

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Exponential`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open CategoryTheory

-- @@ L23-23 verbatim
open scoped Topology



-- @@ L26-26 verbatim
variable {X Y Y' Z : Type*}

-- @@ L27-27 verbatim
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z]


-- @@ L29-31 verbatim
/-- `uncurry_curry` -/
lemma ContinuousMap.uncurry_curry [LocallyCompactSpace Y]
  (f : C(X × Y, Z)) : f = f.curry.uncurry := rfl


-- @@ L33-35 verbatim
/-- `curry_uncurry` -/
lemma ContinuousMap.curry_uncurry [LocallyCompactSpace Y]
  (f : C(X, C(Y, Z))) : f = f.uncurry.curry := rfl


-- @@ L37-40 verbatim
/-- An auxiliary lemma only used for showing the naturality of `topBinProdRightAdjExp` -/
lemma TopCat.exp_homEquiv_naturality_right [LocallyCompactSpace X]
    (f : C(Y', Y)) (g : C(Y, C(X, Z))) :
  (g.comp f).uncurry = g.uncurry.comp (f.prodMap (ContinuousMap.id X)) := rfl




-- @@ L44-44 verbatim
namespace TopCat


-- @@ L46-50 verbatim
/-- The functor `TopCat.of (· × X)` (taking the topological binary product, with `X` on the right)
from `TopCat` to `TopCat` -/
abbrev topBinProdRight (X : TopCat.{u}) : TopCat ⥤ TopCat where
  obj Y := TopCat.of (Y × X)
  map {Y Z} f := TopCat.ofHom (f.hom.prodMap (ContinuousMap.id X))


-- @@ L52-55 verbatim
/-- The exponentiation functor `C(X, ·)` from `TopCat` to `TopCat` -/
abbrev exp (X : TopCat.{u}) : TopCat ⥤ TopCat where
  obj Y := TopCat.of C(X, Y)
  map {Y Z} f := TopCat.ofHom ⟨fun g ↦ f.hom.comp g, f.hom.continuous_postcomp⟩


-- @@ L57-69 verbatim
/-- `topBinProdRightAdjExp` -/
noncomputable def topBinProdRightAdjExp (X : TopCat.{u}) [LocallyCompactSpace X] :
    topBinProdRight X ⊣ exp X :=
  Adjunction.mkOfHomEquiv
  { homEquiv Y Z :=
    { toFun f := TopCat.ofHom f.hom.curry
      invFun f := TopCat.ofHom f.hom.uncurry
      left_inv _ := by simp only [hom_ofHom, ← ContinuousMap.uncurry_curry _, ofHom_hom]
      right_inv _ := by simp only [hom_ofHom, ← ContinuousMap.curry_uncurry _, ofHom_hom] }
    homEquiv_naturality_left_symm {Y' Y Z} f g := by
      simp only [Equiv.coe_fn_symm_mk, hom_comp, TopCat.exp_homEquiv_naturality_right, ofHom_comp]
    homEquiv_naturality_right {Y Z Z'} f g := by
      simp only [Equiv.coe_fn_mk, hom_comp]; rfl }


-- @@ L71-75 verbatim
/-- Same as `topBinProdRight`, except that `X` is not an object in `TopCat`,
but simply a topological space -/
abbrev topBinProdRight' (X : Type u) [TopologicalSpace X] : TopCat ⥤ TopCat where
  obj Y := TopCat.of (Y × X)
  map {Y Z} f := ofHom (f.hom.prodMap (ContinuousMap.id X))


-- @@ L77-80 verbatim
/-- `topBinProdLeft'` -/
abbrev topBinProdLeft' (X : Type u) [TopologicalSpace X] : TopCat ⥤ TopCat where
  obj Y := TopCat.of (X × Y)
  map {Y Z} f := ofHom ((ContinuousMap.id X).prodMap f.hom)


-- @@ L82-85 verbatim
/-- Same as `exp`, except that `X` is not an object in `TopCat`, but simply a topological space -/
abbrev exp' (X : Type u) [TopologicalSpace X] : TopCat ⥤ TopCat where
  obj Y := TopCat.of C(X, Y)
  map {Y Z} f := TopCat.ofHom ⟨fun g ↦ f.hom.comp g, f.hom.continuous_postcomp⟩


-- @@ L87-101 verbatim
/-- Same as `topBinProdRightAdjExp`,
except that `X` is not an object in `TopCat`, but simply a topological space -/
noncomputable def topBinProdRightAdjExp'
    (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] :
    topBinProdRight' X ⊣ exp' X :=
  Adjunction.mkOfHomEquiv
  { homEquiv Y Z :=
    { toFun f := TopCat.ofHom f.hom.curry
      invFun f := TopCat.ofHom f.hom.uncurry
      left_inv _ := by simp only [hom_ofHom, ← ContinuousMap.uncurry_curry _, ofHom_hom]
      right_inv _ := by simp only [hom_ofHom, ← ContinuousMap.curry_uncurry _, ofHom_hom] }
    homEquiv_naturality_left_symm {Y' Y Z} f g := by
      simp only [Equiv.coe_fn_symm_mk, hom_comp, TopCat.exp_homEquiv_naturality_right, ofHom_comp]
    homEquiv_naturality_right {Y Z Z'} f g := by
      simp only [Equiv.coe_fn_mk, hom_comp]; rfl }


-- @@ L103-124 verbatim
/-- `topBinProdLeftAdjExp'` -/
noncomputable def topBinProdLeftAdjExp'
    (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] :
    topBinProdLeft' X ⊣ exp' X :=
  Adjunction.mkOfHomEquiv
  { homEquiv Y Z :=
      let i : TopCat.of (X × Y) ≅ TopCat.of (Y × X) := isoOfHomeo (Homeomorph.prodComm X Y)
      { toFun f := TopCat.ofHom (i.inv ≫ f).hom.curry
        invFun f := i.hom ≫ TopCat.ofHom f.hom.uncurry
        left_inv _ := by
          simp only [hom_comp, hom_ofHom, ← ContinuousMap.uncurry_curry _, ofHom_comp, ofHom_hom,
            Iso.hom_inv_id_assoc]
        right_inv _ := by
          simp only [Iso.inv_hom_id_assoc, hom_ofHom, ← ContinuousMap.curry_uncurry _, ofHom_hom] }
    homEquiv_naturality_left_symm {Y' Y Z} f g := by
      simp only [isoOfHomeo_inv, Homeomorph.prodComm_symm, hom_comp, hom_ofHom, isoOfHomeo_hom,
        Equiv.coe_fn_symm_mk, exp_homEquiv_naturality_right, ofHom_comp]
      rfl
    homEquiv_naturality_right {Y Z Z'} f g := by
      simp only [isoOfHomeo_inv, Homeomorph.prodComm_symm, hom_comp, hom_ofHom, isoOfHomeo_hom,
        Equiv.coe_fn_mk, ContinuousMap.comp_assoc]
      rfl }


-- @@ L126-126 verbatim
end TopCat



-- @@ L129-129 verbatim
namespace ContinuousMap


-- @@ L131-131 verbatim
variable {A B Y : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Y]


-- @@ L133-137 verbatim
/-- `argSwap` -/
@[simp]
def argSwap : C(C(A × B, Y), C(B × A, Y)) where
  toFun f := f.comp ContinuousMap.prodSwap
  continuous_toFun := by fun_prop


-- @@ L139-145 verbatim
/-- `curriedArgSwap` -/
def curriedArgSwap [LocallyCompactSpace A] [LocallyCompactSpace B] :
    C(C(A, C(B, Y)), C(B, C(A, Y))) where
  toFun f := ContinuousMap.curry <| argSwap <| ContinuousMap.uncurry f
  continuous_toFun := by
    refine Continuous.comp continuous_curry ?_
    exact Continuous.comp argSwap.continuous continuous_uncurry


-- @@ L147-148 verbatim
lemma curriedArgSwap_curriedArgSwap [LocallyCompactSpace A] [LocallyCompactSpace B] :
  curriedArgSwap ∘ (curriedArgSwap (A := A) (B := B) (Y := Y)) = id := rfl


-- @@ L150-153 verbatim
/-- `curryLeft` -/
def curryLeft (f : C(A × B, Y)) (b : B) : C(A, Y) where
  toFun a := f ⟨a, b⟩
  continuous_toFun := f.continuous.curry_left


-- @@ L155-158 verbatim
/-- `curryRight` -/
def curryRight (f : C(A × B, Y)) (a : A) : C(B, Y) where
  toFun b := f ⟨a, b⟩
  continuous_toFun := f.continuous.curry_right


-- @@ L160-165 verbatim
lemma eq_of_curry_eq {f g : C(A × B, Y)}
    (e : f.curry = g.curry) : f = g := by
  ext ⟨a, b⟩
  replace e := congrFun (congrArg ContinuousMap.toFun e) a
  replace e := congrFun (congrArg ContinuousMap.toFun e) b
  exact e


-- @@ L167-172 verbatim
lemma eq_of_argSwap_curry_eq {f g : C(A × B, Y)}
    (e : f.argSwap.curry = g.argSwap.curry) : f = g := by
  ext ⟨a, b⟩
  replace e := congrFun (congrArg ContinuousMap.toFun e) b
  replace e := congrFun (congrArg ContinuousMap.toFun e) a
  exact e


-- @@ L174-176 verbatim
end ContinuousMap

---------------------------------------------------------------


-- @@ L178-178 verbatim
open scoped unitInterval


-- @@ L180-180 verbatim
namespace TopCat


-- @@ L182-182 verbatim
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]


-- @@ L184-186 verbatim
lemma hom_eq_of_curry_eq {Y : TopCat} {f g : TopCat.of (A × B) ⟶ Y}
    (e : f.hom.curry = g.hom.curry) : f = g :=
  TopCat.hom_ext_iff.mpr <| ContinuousMap.eq_of_curry_eq e


-- @@ L188-190 verbatim
lemma hom_eq_of_argSwap_curry_eq {Y : TopCat} {f g : TopCat.of (A × B) ⟶ Y}
    (e : f.hom.argSwap.curry = g.hom.argSwap.curry) : f = g :=
  TopCat.hom_ext_iff.mpr <| ContinuousMap.eq_of_argSwap_curry_eq e


-- @@ L192-192 verbatim
end TopCat



-- @@ L195-196 verbatim
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] : ContinuousEval C(X, Y) X Y := by infer_instance

-- @@ L197-197 verbatim
example : LocallyCompactSpace I := by infer_instance

-- @@ L198-198 verbatim
example {Y : Type*} [TopologicalSpace Y] : ContinuousEval C(I, Y) I Y := by infer_instance

-- @@ L199-199 verbatim
example {Y : Type*} [TopologicalSpace Y] : ContinuousEval C(I, Y) _ _ := by infer_instance
