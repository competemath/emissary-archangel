/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CocycleTwist


-- @@ L8-24 verbatim
/-!
# Pullback of a twisted sheaf of modules along a morphism of locally ringed spaces

Let `X` be a scheme, `c` a cocycle on a family of opens `U : ι → X.Opens` covering `X`, and
`f : Y ⟶ X` a morphism of locally ringed spaces. The transition functions of `c` pull back to a
cocycle `f^♯ c` on the family `f⁻¹ Uᵢ` (`LocallyRingedSpace.cocycleComap`), and for every
`𝒪_X`-module `G` there is a natural isomorphism

  `f^* (G ⊗ L_c) ≅ (f^* G) ⊗ L_{f^♯ c}`  (`LocallyRingedSpace.pullbackModulesTwistIso`).

Proof: twisting by `f^♯ c` on `Y` commutes with pushforward on the nose,
`f_* (N ⊗ L_{f^♯ c}) ≅ (f_* N) ⊗ L_c` (`LocallyRingedSpace.pushforwardModTwistIso`; both sides
are the families of sections of `N` over the `f⁻¹ (V ∩ Uᵢ)`). Since twisting by `c` is an
autoequivalence with inverse the twist by `c⁻¹` on both `X` and `Y`, the two functors
`G ↦ f^* (G ⊗ L_c)` and `G ↦ (f^* G) ⊗ L_{f^♯ c}` are left adjoint to isomorphic functors, hence
isomorphic.
-/


-- @@ L26-26 verbatim
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

-- @@ L27-27 verbatim
open AlgebraicGeometry.Scheme.Modules


-- @@ L29-29 verbatim
universe u


-- @@ L31-31 verbatim
namespace AlgebraicGeometry.LocallyRingedSpace


-- @@ L33-35 verbatim
set_option hygiene false in
/-- Sections of the structure sheaf of `Y` over `W`. -/
local notation "Γᵧ(" W ")" => Y.presheaf.obj (op W)


-- @@ L37-38 verbatim
variable {Y : LocallyRingedSpace.{u}} {X : Scheme.{u}} (f : Y ⟶ X.toLocallyRingedSpace)
  {ι : Type} {U : ι → X.Opens}


-- @@ L40-47 verbatim
/-- The **pullback of a cocycle**: the transition functions `f^♯ cᵢⱼ` on the family
`f⁻¹ Uᵢ`. -/
noncomputable def cocycleComap (c : Cocycle U) : ModCocycle (fun i ↦ preimOpen f (U i)) where
  g i j := pbG f c i j
  self i := by
    change pbSec f (c.g i i) = 1
    rw [c.self, pbSec_one]
  mul i j k := pbG_mul (f := f) (c := c) i j k _ le_rfl


-- @@ L49-50 verbatim
lemma cocycleComap_g (c : Cocycle U) (i j : ι) : (cocycleComap f c).g i j = pbSec f (c.g i j) :=
  rfl


-- @@ L52-54 verbatim
/-- Pullback of cocycles commutes with inverses. -/
lemma cocycleComap_inv (c : Cocycle U) : cocycleComap f c⁻¹ = (cocycleComap f c)⁻¹ :=
  ModCocycle.ext fun i j ↦ pbSec_res f _ (c.g j i)


-- @@ L56-58 verbatim
variable {f} in
lemma iSup_preimOpen (hU : ⨆ i, U i = ⊤) : ⨆ i, preimOpen f (U i) = ⊤ :=
  eq_top_iff.2 ((preimOpen_iSup hU ⊤).trans (iSup_mono fun _ ↦ inf_le_right))


-- @@ L60-60 verbatim
variable (c : Cocycle U) (N : SheafOfModules.{u} Y.ringSheaf)


-- @@ L62-83 expanded
/-- The map `f_* (N ⊗ L_{f^♯ c}) ⟶ (f_* N) ⊗ L_c`, the identity on components. -/
noncomputable def pushforwardModTwistHom :
    ((SheafOfModules.pushforward f.toRingSheafHom).obj (modTwist N (cocycleComap f c)) :
        X.Modules) ⟶
      twist ((SheafOfModules.pushforward f.toRingSheafHom).obj N : X.Modules) c :=
  Scheme.Modules.homMk
    (fun V ↦
      { toFun
          s :=
          twistMk (V := V) (c := c) (F :=
            ((SheafOfModules.pushforward f.toRingSheafHom).obj N : X.Modules))
            (fun i ↦ modTwistComp (W := preimOpen f V) s i) fun i j ↦
            by
            refine (modTwistComp_compat (W := preimOpen f V) s i j).trans ?_
            congr 1
            exact (pbSec_res f (inf_le_right : V ⊓ (U i ⊓ U j) ≤ U i ⊓ U j) (c.g i j)).symm
        map_zero' := rfl
        map_add' _ _ := rfl })
    (fun V r s ↦
      twist_ext fun i ↦
        by
        change
          (TopCat.Presheaf.restrictOpen (pbSec f r) (preimOpen f V ⊓ preimOpen f (U i))
                (by order)) •
              modTwistComp (W := preimOpen f V) s i =
            @HSMul.hSMul Γᵧ(preimOpen f V ⊓ preimOpen f (U i))
              (N.val.obj (op (preimOpen f V ⊓ preimOpen f (U i)))) _ _
              (pbSec f (TopCat.Presheaf.restrictOpen r (V ⊓ U i) (by order)))
              (modTwistComp (W := preimOpen f V) s i)
        rw [pbSec_res]
        rfl)
    (fun _ _ _ _ ↦ rfl)


-- @@ L85-110 expanded
/-- The map `(f_* N) ⊗ L_c ⟶ f_* (N ⊗ L_{f^♯ c})`, the identity on components. -/
noncomputable def pushforwardModTwistInv :
    twist ((SheafOfModules.pushforward f.toRingSheafHom).obj N : X.Modules) c ⟶
      ((SheafOfModules.pushforward f.toRingSheafHom).obj (modTwist N (cocycleComap f c)) :
        X.Modules) :=
  Scheme.Modules.homMk
    (fun V ↦
      { toFun
          s :=
          modTwistMk (N := N) (W := preimOpen f V) (c := cocycleComap f c) (fun i ↦ twistComp s i)
            fun i j ↦ by
            refine (twistComp_compat s i j).trans ?_
            change
              @HSMul.hSMul Γᵧ(preimOpen f V ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j)))
                  (N.val.obj (op (preimOpen f V ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))))) _ _
                  (pbSec f (TopCat.Presheaf.restrictOpen (c.g i j) (V ⊓ (U i ⊓ U j)) (by order)))
                  (modRes (N := N) (twistComp s j)
                    (preimOpen f V ⊓ (preimOpen f (U i) ⊓ preimOpen f (U j))) _) =
                _
            rw [pbSec_res]
            rfl
        map_zero' := rfl
        map_add' _ _ := rfl })
    (fun V r s ↦
      modTwist_ext fun i ↦
        by
        change
          @HSMul.hSMul Γᵧ(preimOpen f V ⊓ preimOpen f (U i))
              (N.val.obj (op (preimOpen f V ⊓ preimOpen f (U i)))) _ _
              (pbSec f (TopCat.Presheaf.restrictOpen r (V ⊓ U i) (by order))) (twistComp s i) =
            (TopCat.Presheaf.restrictOpen (pbSec f r) (preimOpen f V ⊓ preimOpen f (U i))
                (by order)) •
              _
        rw [pbSec_res]
        rfl)
    (fun _ _ _ _ ↦ rfl)


-- @@ L112-118 verbatim
/-- **Twisting commutes with pushforward**: `f_* (N ⊗ L_{f^♯ c}) ≅ (f_* N) ⊗ L_c`, the identity
on components. -/
noncomputable def pushforwardModTwistIso :
    ((SheafOfModules.pushforward f.toRingSheafHom).obj (modTwist N (cocycleComap f c)) :
      X.Modules) ≅ twist ((SheafOfModules.pushforward f.toRingSheafHom).obj N : X.Modules) c :=
  Scheme.Modules.isoMk (pushforwardModTwistHom f c N) (pushforwardModTwistInv f c N)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)


-- @@ L120-125 verbatim
/-- `f_* (N ⊗ L_{f^♯ c}) ≅ (f_* N) ⊗ L_c`, naturally in `N`. -/
noncomputable def modTwistFunctorPushforwardIso :
    modTwistFunctor (cocycleComap f c) ⋙ SheafOfModules.pushforward f.toRingSheafHom ≅
      SheafOfModules.pushforward f.toRingSheafHom ⋙ twistFunctor c :=
  NatIso.ofComponents (fun N ↦ pushforwardModTwistIso f c N) fun _ ↦
    Scheme.Modules.Hom.ext_apply fun _ _ ↦ rfl


-- @@ L127-127 verbatim
variable (hU : ⨆ i, U i = ⊤)


-- @@ L129-139 verbatim
/-- **The pullback of a twist is the twist of the pullback**: for a morphism of locally ringed
spaces `f : Y ⟶ X` and a cocycle `c` on an open cover of the scheme `X`,
`f^* (G ⊗ L_c) ≅ (f^* G) ⊗ L_{f^♯ c}`, naturally in `G`. -/
noncomputable def pullbackModulesTwistIso :
    twistFunctor c ⋙ f.pullbackModules ≅
      f.pullbackModules ⋙ modTwistFunctor (cocycleComap f c) :=
  Adjunction.leftAdjointUniq ((twistEquivalence c hU).toAdjunction.comp f.pullbackModulesAdj)
    ((f.pullbackModulesAdj.comp
      (modTwistEquivalence (cocycleComap f c) (iSup_preimOpen hU)).toAdjunction).ofNatIsoRight
      (Functor.isoWhiskerRight (modTwistFunctorCongr (cocycleComap_inv f c).symm) _ ≪≫
        modTwistFunctorPushforwardIso f c⁻¹))


-- @@ L141-141 verbatim
end AlgebraicGeometry.LocallyRingedSpace
