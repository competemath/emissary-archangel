/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.CharacteristicClasses.ProjectiveBundleIntegral
import RiemannRoch.CharacteristicClasses.ProjectiveBundleTautologicalSection


-- @@ L10-25 verbatim
/-!
# The tautological quotient `p^* E ↠ O(1)` of a projective bundle

For an affine frame cover `C` of `p : ℙ(E) = Proj (Sym E) → X`:

* `SchemeProjectiveBundle.AffineFrameCover.tautologicalPushforwardHom : E ⟶ p_* O(1)` is glued on
  the base cover from the frame maps `bᵢₖ ↦ tᵢₖ`, where `tᵢₖ` is the tautological section `bᵢₖ`
  of `O(1)` on the chart `i`. The overlap identity on common basic opens follows from the
  chart-level restriction compatibility of the tautological sections and their linearity.
* `SchemeProjectiveBundle.AffineFrameCover.tautologicalQuotient : p^* E ⟶ O(1)` is its adjoint,
  and it is an epimorphism (`tautologicalQuotient_epi`), because its values generate `O(1)` on the
  literal linear opens.
* `SchemeProjectiveBundle.AffineFrameCover.exists_tautologicalQuotient`.

No positivity hypothesis on the frames is needed.
-/


-- @@ L27-27 verbatim
set_option autoImplicit false


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-32 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
  SchemeKTheory


-- @@ L34-34 verbatim
universe u


-- @@ L36-36 verbatim
namespace SchemeProjectiveBundle

-- @@ L37-37 verbatim
namespace AffineFrameCover


-- @@ L39-39 verbatim
local notation "𝐑[" f "]" => Scheme.Modules.restrictFunctor f



-- @@ L42-49 verbatim
theorem tautQuotient_pre_app' {Y Z W : Scheme.{u}} (s : W ⟶ Y) (q : Z ⟶ Y) (r : W ⟶ Z)
    [IsOpenImmersion s] [IsOpenImmersion q] [IsOpenImmersion r] (h : r ≫ q = s)
    (F : Y.Modules) (V : W.Opens) (x : Γ(F, s ''ᵁ V))
    (ψ : op (s ''ᵁ V) ⟶ op (q ''ᵁ (r ''ᵁ V))) :
    (restrictCompPrefixIso' s q r h F).hom.app V x = F.presheaf.map ψ x := by
  obtain ⟨f, hf⟩ := tensorOverlap_pre_app s q r h F (op V)
  rw [Subsingleton.elim ψ f]
  exact hf x


-- @@ L51-51 verbatim
section Leg


-- @@ L53-63 verbatim
variable {R S M N ι : Type u}
  [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N]
  [Finite ι]
  {b : Module.Basis ι R M} {c : Module.Basis ι S N}
  {q : space S N ⟶ space R M} [IsOpenImmersion q]
  {Xg Z : Scheme.{u}} (ιg : space R M ⟶ Xg) [IsOpenImmersion ιg]
  (p : Z ⟶ Xg) (g : Z ⟶ space R M) (κ : Z ⟶ space S N)
  [IsOpenImmersion p] [IsOpenImmersion g] [IsOpenImmersion κ]
  (hg : g ≫ ιg = p) (hκ : κ ≫ q = g)


-- @@ L65-101 verbatim
omit [Finite ι] in
set_option backward.isDefEq.respectTransparency false in
/-- Elementwise evaluation of a leg on the restriction of a section coming from the chart. -/
theorem tautQuotient_leg_app {d : ℤ} {O : Xg.Modules}
    (ρ : 𝐑[ιg].obj O ≅ twistingSheafOfBasisIndex R M b d)
    (D : TwistingSheafRestrictionData b c d q) (x : Γ(twistingSheafOfBasisIndex R M b d, ⊤))
    (ψ : op (ιg ''ᵁ ⊤) ⟶ op (p ''ᵁ ⊤)) (ψ' : op (⊤ : (space R M).Opens) ⟶ op (q ''ᵁ (κ ''ᵁ ⊤))) :
    (tensorOverlap_leg ιg p g κ hg hκ ρ D).hom.app ⊤ (O.presheaf.map ψ (ρ.inv.app ⊤ x)) =
      D.restrictIso.hom.app (κ ''ᵁ ⊤) ((twistingSheafOfBasisIndex R M b d).presheaf.map ψ' x) := by
  have s1 : (restrictCompPrefixIso' p ιg g hg O).hom.app ⊤ (O.presheaf.map ψ (ρ.inv.app ⊤ x)) =
      (𝐑[ιg].obj O).presheaf.map (homOfLE (le_top : g ''ᵁ ⊤ ≤ ⊤)).op (ρ.inv.app ⊤ x) := by
    obtain ⟨f1, -⟩ := tensorOverlap_pre_app p ιg g hg O (op ⊤)
    rw [tautQuotient_pre_app' p ιg g hg O ⊤ _ f1, Scheme.Modules.restrict_map,
      ← Functor.map_comp_apply]
    rfl
  have s3 : ρ.hom.app (g ''ᵁ ⊤) ((𝐑[ιg].obj O).presheaf.map (homOfLE (le_top : g ''ᵁ ⊤ ≤ ⊤)).op
      (ρ.inv.app ⊤ x)) = (twistingSheafOfBasisIndex R M b d).presheaf.map
        (homOfLE (le_top : g ''ᵁ ⊤ ≤ ⊤)).op x := by
    have hx : ρ.hom.app ⊤ (ρ.inv.app ⊤ x) = x := by
      have h := congrArg (fun f : twistingSheafOfBasisIndex R M b d ⟶
        twistingSheafOfBasisIndex R M b d ↦ f.app ⊤ x) ρ.inv_hom_id
      simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using h
    exact (tautChart_app_map _ _ _).trans (congrArg _ hx)
  have s4 : (restrictCompPrefixIso' g q κ hκ _).hom.app ⊤
      ((twistingSheafOfBasisIndex R M b d).presheaf.map (homOfLE (le_top : g ''ᵁ ⊤ ≤ ⊤)).op x) =
      (twistingSheafOfBasisIndex R M b d).presheaf.map ψ' x := by
    obtain ⟨f2, -⟩ := tensorOverlap_pre_app g q κ hκ (twistingSheafOfBasisIndex R M b d) (op ⊤)
    rw [tautQuotient_pre_app' g q κ hκ _ ⊤ _ f2, ← Functor.map_comp_apply]
    rfl
  unfold tensorOverlap_leg
  simp only [Iso.trans_hom, Functor.mapIso_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [s1]
  change D.restrictIso.hom.app (κ ''ᵁ ⊤) ((restrictCompPrefixIso' g q κ hκ _).hom.app ⊤
    (ρ.hom.app (g ''ᵁ ⊤) _)) = _
  rw [s3, s4]


-- @@ L103-103 verbatim
end Leg


-- @@ L105-105 verbatim
attribute [local instance] transition_isOpenImmersion'


-- @@ L107-107 verbatim
/-! ## Global assembly -/


-- @@ L109-109 verbatim
section Global


-- @@ L111-111 verbatim
variable {X : Scheme.{u}} {E : X.Modules} (C : AffineFrameCover X E)



-- @@ L114-116 verbatim
theorem tautQuotient_chartι_image_top (i : C.I) :
    (C.chartι i) ''ᵁ ⊤ = C.toBase ⁻¹ᵁ C.U i := by
  rw [Scheme.Hom.image_top_eq_opensRange, tautQuotient_chartι_opensRange]


-- @@ L118-120 verbatim
/-- The pushforward of `O(1)` to the base. -/
abbrev tautQuotient_N : X.Modules :=
  (Scheme.Modules.pushforward C.toBase).obj (C.canonicalTwistingSheaf 1)


-- @@ L122-129 verbatim
/-- The tautological section `bₖ` of `O(1)` over the chart `i`, viewed through the chart
restriction isomorphism. -/
def tautQuotient_chartHom (i : C.I) (k : C.basisIndex i) :
    SchemeProjectiveSpace.unitModules (space Γ(X, C.U i) (E.val.obj (op (C.U i)))) ⟶
      (Scheme.Modules.restrictFunctor (tensorOverlap_ιs C i)).obj (C.canonicalTwistingSheaf 1) :=
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  tautChart_tautHom Γ(X, C.U i) (E.val.obj (op (C.U i))) (C.sectionBasis i) (C.sectionBasis i k) ≫
    (C.canonicalTwistingSheafRestrictionIso 1 i).inv


-- @@ L131-136 verbatim
/-- The tautological section `bₖ` of the chart twist. -/
def tautQuotient_chartTaut (i : C.I) (k : C.basisIndex i) : Γ(C.chartTwistingSheaf 1 i, ⊤) :=
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  (tautChart_tautHom Γ(X, C.U i) (E.val.obj (op (C.U i))) (C.sectionBasis i)
    (C.sectionBasis i k)).app ⊤
    (1 : (space Γ(X, C.U i) (E.val.obj (op (C.U i)))).presheaf.obj (op ⊤))


-- @@ L138-141 verbatim
/-- The same section as an element of `O(1)` over the chart range. -/
def tautQuotient_chartSection (i : C.I) (k : C.basisIndex i) :
    (C.canonicalTwistingSheaf 1).val.obj (op ((C.chartι i) ''ᵁ ⊤)) :=
  (C.canonicalTwistingSheafRestrictionIso 1 i).inv.app ⊤ (tautQuotient_chartTaut C i k)


-- @@ L143-146 verbatim
/-- The section `bₖ ↦ tₖ` of `p_* O(1)` over the base chart. -/
def tautQuotient_t (i : C.I) (k : C.basisIndex i) : (tautQuotient_N C).val.obj (op (C.U i)) :=
  (C.canonicalTwistingSheaf 1).val.map (eqToHom (tautQuotient_chartι_image_top C i).symm).op
    (tautQuotient_chartSection C i k)


-- @@ L148-151 verbatim
/-- The local tautological morphism `E|_{Uᵢ} ⟶ (p_* O(1))|_{Uᵢ}`. -/
def tautQuotient_alpha (i : C.I) : E.over (C.U i) ⟶ (tautQuotient_N C).over (C.U i) :=
  (C.frame i).inv ≫ ((tautQuotient_N C).over (C.U i)).freeHomEquiv.symm
    (fun k ↦ Scheme.Modules.overSectionOfElement X (tautQuotient_N C) (C.U i) (tautQuotient_t C i k))


-- @@ L153-162 verbatim
omit C in
/-- An over-site section is the lift of its value on the terminal object. -/
theorem tautQuotient_overSectionOfElement_terminal (M : X.Modules) (U : X.Opens)
    (s : (M.over U).sections) :
    Scheme.Modules.overSectionOfElement X M U (s.eval (op (Over.mk (𝟙 U)))) = s := by
  apply PresheafOfModules.sections_ext
  intro W
  let q : W.unop ⟶ Over.mk (𝟙 U) := Over.homMk W.unop.hom (by rfl)
  change M.val.map W.unop.hom.op (s.eval (op (Over.mk (𝟙 U)))) = s.eval W
  exact PresheafOfModules.sections_property s q.op


-- @@ L164-168 verbatim
theorem tautQuotient_frame_freeSection (i : C.I) (k : C.basisIndex i) :
    SheafOfModules.sectionsMap (C.frame i).hom (SheafOfModules.freeSection k) =
      Scheme.Modules.overSectionOfElement X E (C.U i) (C.sectionBasis i k) := by
  rw [SchemeProjectiveBundle.AffineFrameCover.sectionBasis_apply_overFrame]
  exact (tautQuotient_overSectionOfElement_terminal E (C.U i) _).symm


-- @@ L170-176 verbatim
/-- Value of the local tautological morphism on the frame. -/
theorem tautQuotient_alpha_frame (i : C.I) (k : C.basisIndex i) :
    SheafOfModules.sectionsMap (tautQuotient_alpha C i)
        (Scheme.Modules.overSectionOfElement X E (C.U i) (C.sectionBasis i k)) =
      Scheme.Modules.overSectionOfElement X (tautQuotient_N C) (C.U i) (tautQuotient_t C i k) := by
  rw [← tautQuotient_frame_freeSection, ← SheafOfModules.sectionsMap_comp, tautQuotient_alpha,
    Iso.hom_inv_id_assoc, SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection]


-- @@ L178-203 verbatim
/-- Compatibility of the local tautological morphisms reduces to common basic opens. -/
theorem tautQuotient_alpha_compatible
    (h : ∀ (i j : C.I) (c : C.CommonBasicOpen i j),
      Scheme.Modules.restrictHomOverLE X c.affineOpen_le_left (tautQuotient_alpha C i) =
        Scheme.Modules.restrictHomOverLE X c.affineOpen_le_right (tautQuotient_alpha C j)) :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (fun i ↦ Scheme.Modules.localHomSection X (C.U i) (tautQuotient_alpha C i)) := by
  intro V i j f g
  let H := sheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj E)
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj (tautQuotient_N C))
  have hsep := ((isSheaf_iff_isSheaf_of_type _ H.obj).1 H.property).isSeparated
  let S : Sieve V := Sieve.ofObjects (fun c : C.CommonBasicOpen i j ↦ c.affineOpen.1) V
  have hS : S ∈ Opens.grothendieckTopology X V := by
    intro x hx
    obtain ⟨a, b', hab, hxa⟩ := exists_basicOpen_le_affine_inter (C.isAffine i)
      (C.isAffine j) x ⟨f.le hx, g.le hx⟩
    let c : C.CommonBasicOpen i j := ⟨a, b', hab⟩
    exact ⟨V ⊓ c.affineOpen.1, homOfLE inf_le_left, ⟨c, ⟨homOfLE inf_le_right⟩⟩, ⟨hx, hxa⟩⟩
  refine (hsep S hS).ext ?_
  rintro Z e ⟨c, ⟨q⟩⟩
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  have e1 : f.op ≫ e.op = (homOfLE c.affineOpen_le_left).op ≫ q.op := Subsingleton.elim _ _
  have e2 : g.op ≫ e.op = (homOfLE c.affineOpen_le_right).op ≫ q.op := Subsingleton.elim _ _
  rw [e1, e2, Functor.map_comp_apply, Functor.map_comp_apply,
    Scheme.Modules.sheafHom_map_localHomSection, Scheme.Modules.sheafHom_map_localHomSection,
    h i j c]


-- @@ L205-212 verbatim
omit C in
theorem tautQuotient_sectionsMap_overSection_eval {M N : X.Modules} {U : X.Opens}
    (φ : M.over U ⟶ N.over U) (e : M.val.obj (op U)) :
    (SheafOfModules.sectionsMap φ (Scheme.Modules.overSectionOfElement X M U e)).eval
        (op (Over.mk (𝟙 U))) = φ.val.app (op (Over.mk (𝟙 U))) e := by
  change φ.val.app (op (Over.mk (𝟙 U))) (M.val.map (𝟙 (op U)) e) = _
  rw [M.val.map_id]
  rfl


-- @@ L214-218 verbatim
omit C in
theorem tautQuotient_restrictHomOverLE_app {M N : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (φ : M.over U ⟶ N.over U) (e : M.val.obj (op V)) :
    (Scheme.Modules.restrictHomOverLE X h φ).val.app (op (Over.mk (𝟙 V))) e =
      φ.val.app (op (Over.mk (homOfLE h))) e := rfl


-- @@ L220-226 verbatim
omit C in
theorem tautQuotient_over_naturality {M N : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (φ : M.over U ⟶ N.over U) (e : M.val.obj (op U)) :
    φ.val.app (op (Over.mk (homOfLE h))) (M.val.map (homOfLE h).op e) =
      N.val.map (homOfLE h).op (φ.val.app (op (Over.mk (𝟙 U))) e) := by
  let q : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U) := Over.homMk (homOfLE h) (by rfl)
  exact PresheafOfModules.naturality_apply φ.val q.op e


-- @@ L228-235 verbatim
theorem tautQuotient_alpha_app_frame (i : C.I) (k : C.basisIndex i) :
    (tautQuotient_alpha C i).val.app (op (Over.mk (𝟙 (C.U i)))) (C.sectionBasis i k) =
      tautQuotient_t C i k := by
  rw [← tautQuotient_sectionsMap_overSection_eval, tautQuotient_alpha_frame,
    Scheme.Modules.overSectionOfElement_eval]
  change (tautQuotient_N C).val.map (𝟙 (op (C.U i))) (tautQuotient_t C i k) = _
  rw [(tautQuotient_N C).val.map_id]
  rfl


-- @@ L237-293 verbatim
/-- Local agreement of two chart tautological morphisms, reduced to the section identity. -/
theorem tautQuotient_alpha_local (i j : C.I) (c : C.CommonBasicOpen i j)
    (hkey : ∀ k : C.basisIndex i,
      (tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_left).op (tautQuotient_t C i k) =
        (c.rightSectionBasis.repr (c.leftSectionBasis k)).sum
          (fun l a ↦ a • (tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_right).op
            (tautQuotient_t C j l))) :
    Scheme.Modules.restrictHomOverLE X c.affineOpen_le_left (tautQuotient_alpha C i) =
      Scheme.Modules.restrictHomOverLE X c.affineOpen_le_right (tautQuotient_alpha C j) := by
  rw [← cancel_epi c.leftFrame.hom]
  apply (SheafOfModules.freeHomEquiv _).injective
  funext k
  rw [SheafOfModules.freeHomEquiv_comp_apply, SheafOfModules.freeHomEquiv_comp_apply,
    SheafOfModules.freeHomEquiv_apply]
  have hL : SheafOfModules.sectionsMap c.leftFrame.hom (SheafOfModules.freeSection k) =
      Scheme.Modules.overSectionOfElement X E c.affineOpen.1 (c.leftSectionBasis k) := by
    rw [show c.leftSectionBasis k = _ from
      SchemeProjectiveBundle.AffineFrameCover.restrictedSectionBasis_apply_overFrame C i
        c.affineOpen.1 c.affineOpen_le_left k]
    exact (tautQuotient_overSectionOfElement_terminal E _ _).symm
  rw [hL, ← tautQuotient_overSectionOfElement_terminal (tautQuotient_N C) c.affineOpen.1
      (SheafOfModules.sectionsMap _ _),
    ← tautQuotient_overSectionOfElement_terminal (tautQuotient_N C) c.affineOpen.1
      (SheafOfModules.sectionsMap
        (Scheme.Modules.restrictHomOverLE X c.affineOpen_le_right (tautQuotient_alpha C j)) _),
    tautQuotient_sectionsMap_overSection_eval, tautQuotient_sectionsMap_overSection_eval,
    tautQuotient_restrictHomOverLE_app, tautQuotient_restrictHomOverLE_app]
  congr 1
  have hR : ∀ l, (tautQuotient_alpha C j).val.app (op (Over.mk (homOfLE c.affineOpen_le_right)))
      (c.rightSectionBasis l) = (tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_right).op
        (tautQuotient_t C j l) := by
    intro l
    rw [show c.rightSectionBasis l = _ from
      (SchemeProjectiveBundle.AffineFrameCover.restrictedSectionBasis_eq_restrict C j
        c.affineOpen.1 c.affineOpen_le_right l).symm, tautQuotient_over_naturality,
      tautQuotient_alpha_app_frame]
    rfl
  have hLk : (tautQuotient_alpha C i).val.app (op (Over.mk (homOfLE c.affineOpen_le_left)))
      (c.leftSectionBasis k) = (tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_left).op
        (tautQuotient_t C i k) := by
    rw [show c.leftSectionBasis k = _ from
      (SchemeProjectiveBundle.AffineFrameCover.restrictedSectionBasis_eq_restrict C i
        c.affineOpen.1 c.affineOpen_le_left k).symm, tautQuotient_over_naturality,
      tautQuotient_alpha_app_frame]
    rfl
  rw [hLk, hkey k]
  conv_rhs => rw [← c.rightSectionBasis.linearCombination_repr (c.leftSectionBasis k)]
  rw [Finsupp.linearCombination_apply]
  refine Eq.trans ?_ (map_finsuppSum
    ((tautQuotient_alpha C j).val.app (op (Over.mk (homOfLE c.affineOpen_le_right)))).hom
    (c.rightSectionBasis.repr (c.leftSectionBasis k))
    (fun l a ↦ a • c.rightSectionBasis l)).symm
  apply Finsupp.sum_congr
  intro l _
  erw [(((tautQuotient_alpha C j).val.app (op (Over.mk (homOfLE c.affineOpen_le_right)))).hom).map_smul]
  rw [hR l]
  rfl


-- @@ L295-323 verbatim
omit C in
/-- Generation from a rank-one trivialization (copied from P3C). -/
theorem tautQuotient_generating_of_unitIso {Y S : Scheme.{u}} (j : S ⟶ Y) [IsOpenImmersion j]
    (F : Y.Modules)
    (φ : (Scheme.Modules.restrictFunctor j).obj F ≅ SheafOfModules.unit S.ringCatSheaf)
    {T : Y.Opens} (hT : j.opensRange ≤ T) (t : Γ(F, T))
    (ht : φ.hom.app ⊤ (F.presheaf.map (homOfLE ((j.image_le_opensRange ⊤).trans hT)).op t) =
      (1 : Γ(S, ⊤)))
    (V : S.Opens) (s : Γ(F, j ''ᵁ V)) :
    ∃ a : Γ(Y, j ''ᵁ V), s = a • F.presheaf.map
      (homOfLE ((j.image_le_opensRange V).trans hT)).op t := by
  let x : Γ((Scheme.Modules.restrictFunctor j).obj F, V) :=
    F.presheaf.map (homOfLE ((j.image_le_opensRange V).trans hT)).op t
  have hx : φ.hom.app V x = (1 : Γ(S, V)) := by
    have e : x = ((Scheme.Modules.restrictFunctor j).obj F).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op
        (F.presheaf.map (homOfLE ((j.image_le_opensRange ⊤).trans hT)).op t) := by
      change _ = F.presheaf.map _ (F.presheaf.map _ t)
      rw [← Functor.map_comp_apply]
      rfl
    rw [e, tautChart_app_map, ht]
    exact map_one (S.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
  let w : Γ(S, V) := φ.hom.app V s
  refine ⟨(j.appIso V).inv w, ?_⟩
  change s = w • x
  apply (ConcreteCategory.bijective_of_isIso (φ.hom.app V)).1
  rw [Scheme.Modules.Hom.app_smul, hx]
  change w = w * 1
  rw [mul_one]


-- @@ L325-377 verbatim
omit C in
/-- Epimorphism criterion for an adjoint `p^* E ⟶ F` whose values generate `F` locally
(adapted from P3C's counit criterion). -/
theorem tautQuotient_epi_of_generating {Y : Scheme.{u}} (p : Y ⟶ X) (F : Y.Modules)
    (α : E ⟶ (Scheme.Modules.pushforward p).obj F)
    {ι : Type u} (S : ι → Scheme.{u}) (j : ∀ k, S k ⟶ Y) [∀ k, IsOpenImmersion (j k)]
    (hW : ⨆ k, (j k).opensRange = ⊤) (U : ι → X.Opens)
    (hWU : ∀ k, (j k).opensRange ≤ p ⁻¹ᵁ U k) (e : ∀ k, Γ(E, U k))
    (hgen : ∀ k (V : (S k).Opens) (s : Γ(F, j k ''ᵁ V)),
      ∃ a : Γ(Y, j k ''ᵁ V), s = a • F.presheaf.map
        (homOfLE (((j k).image_le_opensRange V).trans (hWU k))).op (α.app (U k) (e k))) :
    Epi (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm α) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction p
  let σ := (adj.homEquiv _ _).symm α
  have hα : α = adj.unit.app E ≫ (Scheme.Modules.pushforward p).map σ := by
    exact ((adj.homEquiv _ _).apply_symm_apply α).symm.trans (Adjunction.homEquiv_unit _ _ _ _)
  suffices key : ∀ (Z : Y.Modules) (g h : F ⟶ Z), σ ≫ g = σ ≫ h → g = h from
    ⟨fun g h hc => key _ g h hc⟩
  intro Z g h hcomp
  have ht : ∀ k, g.app (p ⁻¹ᵁ U k) (α.app (U k) (e k)) =
      h.app (p ⁻¹ᵁ U k) (α.app (U k) (e k)) := by
    intro k
    have hαk : α.app (U k) (e k) =
        σ.app (p ⁻¹ᵁ U k) ((adj.unit.app E).app (U k) (e k)) := by
      rw [hα]
      rfl
    rw [hαk]
    have := congrArg (fun q => q.app (p ⁻¹ᵁ U k)) hcomp
    have h3 := ConcreteCategory.congr_hom this ((adj.unit.app E).app (U k) (e k))
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h3
    exact h3
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  let V' : ι → Y.Opens := fun k => j k ''ᵁ (j k ⁻¹ᵁ V)
  have hV' : ∀ k, V' k ≤ V := fun k => by
    dsimp only [V']
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_right
  have hcover : V ≤ ⨆ k, V' k := by
    dsimp only [V']
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← iSup_inf_eq, hW, top_inf_eq]
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨Z.presheaf, Z.isSheaf⟩ : TopCat.Sheaf Ab Y)
    V' V (fun k => homOfLE (hV' k)) hcover
  intro k
  change Z.presheaf.map (homOfLE (hV' k)).op (g.app V s) =
    Z.presheaf.map (homOfLE (hV' k)).op (h.app V s)
  rw [← tautChart_app_map, ← tautChart_app_map]
  obtain ⟨a, ha⟩ := hgen k (j k ⁻¹ᵁ V) (F.presheaf.map (homOfLE (hV' k)).op s)
  rw [ha, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, tautChart_app_map,
    tautChart_app_map, ht k]


-- @@ L379-383 verbatim
theorem tautQuotient_toBase_range_le (i : C.I) (k : C.basisIndex i) :
    ((C.literalLinearOpen ⟨i, k⟩).ι ≫ C.chartι i).opensRange ≤ C.toBase ⁻¹ᵁ C.U i := by
  rw [← tautQuotient_chartι_image_top C i, Scheme.Hom.image_top_eq_opensRange]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩


-- @@ L385-410 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem tautQuotient_restrictionIso_taut (i : C.I) (k : C.basisIndex i) {B D : C.scheme.Opens}
    (x : Γ(C.chartTwistingSheaf 1 i, ⊤))
    (ψ1 : op (C.chartι i ''ᵁ ⊤) ⟶ op B) (ψ2 : op B ⟶ op D)
    (ψ3 : op D ⟶ op (C.chartι i ''ᵁ ((C.literalLinearOpen ⟨i, k⟩).ι ''ᵁ ⊤))) :
    ((Scheme.Modules.restrictFunctor (C.literalLinearOpen ⟨i, k⟩).ι).map
        (C.canonicalTwistingSheafRestrictionIso 1 i).hom).app ⊤
      ((C.canonicalTwistingSheaf 1).presheaf.map ψ3 ((C.canonicalTwistingSheaf 1).presheaf.map ψ2
        ((C.canonicalTwistingSheaf 1).presheaf.map ψ1
          ((C.canonicalTwistingSheafRestrictionIso 1 i).inv.app ⊤ x)))) =
      (C.chartTwistingSheaf 1 i).presheaf.map
        (homOfLE (le_top : (C.literalLinearOpen ⟨i, k⟩).ι ''ᵁ ⊤ ≤ ⊤)).op x := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  have hψ : (C.canonicalTwistingSheaf 1).presheaf.map (ψ1 ≫ ψ2 ≫ ψ3) =
      ((Scheme.Modules.restrictFunctor (C.chartι i)).obj
        (C.canonicalTwistingSheaf 1)).presheaf.map
          (homOfLE (le_top : (C.literalLinearOpen ⟨i, k⟩).ι ''ᵁ ⊤ ≤ ⊤)).op := by
    rw [Scheme.Modules.restrict_map]
    congr 1
  rw [hψ]
  change (C.canonicalTwistingSheafRestrictionIso 1 i).hom.app
      ((C.literalLinearOpen ⟨i, k⟩).ι ''ᵁ ⊤) _ = _
  refine (tautChart_app_map (C.canonicalTwistingSheafRestrictionIso 1 i).hom _ _).trans ?_
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id]
  rfl


-- @@ L412-429 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Under the literal-open trivialization of `O(1)`, the tautological section is `1`. -/
theorem tautQuotient_literal_t (i : C.I) (k : C.basisIndex i) :
    (C.canonicalTwistingSheafLiteralLinearOpenIso 1 ⟨i, k⟩).hom.app ⊤
      ((C.canonicalTwistingSheaf 1).presheaf.map
        (homOfLE ((((C.literalLinearOpen ⟨i, k⟩).ι ≫ C.chartι i).image_le_opensRange ⊤).trans
          (tautQuotient_toBase_range_le C i k))).op (tautQuotient_t C i k)) =
      (1 : Γ((C.literalLinearOpen ⟨i, k⟩).toScheme, ⊤)) := by
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  simp only [SchemeProjectiveBundle.AffineFrameCover.canonicalTwistingSheafLiteralLinearOpenIso,
    id_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Iso.app_hom, Functor.mapIso_hom, Scheme.Modules.restrictFunctorComp_hom_app_app]
  rw [tautQuotient_t, tautQuotient_chartSection]
  refine (congrArg (fun z => (SchemeProjectiveBundle.twistingSheafOfBasisIndexLinearOpenIso
    Γ(X, C.U i) (E.val.obj (op (C.U i))) (C.sectionBasis i) 1 k).inv.app ⊤ z)
      (tautQuotient_restrictionIso_taut C i k _ _ _ _)).trans ?_
  exact tautChart_projection_taut _ _ (C.sectionBasis i) k


-- @@ L431-438 verbatim
/-- The overlap identity (KEY): on a common basic open, the chart-`i` tautological section `bᵢₖ`
equals the combination of the chart-`j` ones given by the frame change. -/
def tautQuotient_Key : Prop :=
  ∀ (i j : C.I) (c : C.CommonBasicOpen i j) (k : C.basisIndex i),
    (tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_left).op (tautQuotient_t C i k) =
      (c.rightSectionBasis.repr (c.leftSectionBasis k)).sum
        (fun l a ↦ a • (tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_right).op
          (tautQuotient_t C j l))


-- @@ L440-444 verbatim
/-- The glued tautological morphism `E ⟶ p_* O(1)`. -/
def tautQuotient_alphaGlued (hkey : tautQuotient_Key C) : E ⟶ tautQuotient_N C :=
  Scheme.Modules.glueHom X C.U ((Opens.coversTop_iff (T := X) C.U).2 C.covers)
    (tautQuotient_alpha C)
    (tautQuotient_alpha_compatible C (fun i j c ↦ tautQuotient_alpha_local C i j c (hkey i j c)))


-- @@ L446-453 verbatim
theorem tautQuotient_alphaGlued_app (hkey : tautQuotient_Key C) (i : C.I) (k : C.basisIndex i) :
    (tautQuotient_alphaGlued C hkey).app (C.U i) (C.sectionBasis i k) = tautQuotient_t C i k := by
  have h := Scheme.Modules.glueHom_over X C.U ((Opens.coversTop_iff (T := X) C.U).2 C.covers)
    (tautQuotient_alpha C)
    (tautQuotient_alpha_compatible C (fun i j c ↦ tautQuotient_alpha_local C i j c (hkey i j c))) i
  change ((tautQuotient_alphaGlued C hkey).over (C.U i)).val.app (op (Over.mk (𝟙 (C.U i))))
    (C.sectionBasis i k) = _
  rw [tautQuotient_alphaGlued, h, tautQuotient_alpha_app_frame]


-- @@ L455-467 verbatim
/-- **The leaf, modulo the overlap identity (KEY).** -/
theorem tautQuotient_exists_tautologicalQuotient_of_key (hkey : tautQuotient_Key C) :
    ∃ σ : (Scheme.Modules.pullback C.toBase).obj E ⟶ C.canonicalTwistingSheaf 1, Epi σ := by
  refine ⟨_, tautQuotient_epi_of_generating C.toBase (C.canonicalTwistingSheaf 1)
    (tautQuotient_alphaGlued C hkey)
    (fun ij : Σ i : C.I, C.basisIndex i ↦ (C.literalLinearOpen ij).toScheme)
    (fun ij ↦ (C.literalLinearOpen ij).ι ≫ C.chartι ij.1)
    C.literalLinearOpenCover.iSup_opensRange (fun ij ↦ C.U ij.1)
    (fun ij ↦ tautQuotient_toBase_range_le C ij.1 ij.2) (fun ij ↦ C.sectionBasis ij.1 ij.2) ?_⟩
  intro ij V s
  rw [tautQuotient_alphaGlued_app]
  exact tautQuotient_generating_of_unitIso _ _ (C.canonicalTwistingSheafLiteralLinearOpenIso 1 ij)
    (tautQuotient_toBase_range_le C ij.1 ij.2) (tautQuotient_t C ij.1 ij.2) (tautQuotient_literal_t C ij.1 ij.2) V s


-- @@ L469-516 verbatim
/-- The common-basic-open piece of the overlap is exactly the preimage of the common base
open. -/
theorem tautQuotient_p_opensRange (i j : C.I) (c : C.CommonBasicOpen i j) :
    (tensorOverlap_p C i j c).opensRange = C.toBase ⁻¹ᵁ c.affineOpen.1 := by
  have hbase : (C.basicOpenOverlapCover i j).f c ≫ C.overlapToChart i j ≫ C.chartι i ≫
      C.toBase = pullback.snd _ _ ≫ c.inIntersection.ι ≫ (C.U i ⊓ C.U j).ι := by
    rw [C.chartι_toBase, ← C.chartToBase_comp_openImmersion]
    change pullback.fst _ _ ≫ pullback.fst _ _ ≫ C.chartToBase i ≫ (C.U i).ι = _
    rw [pullback.condition_assoc, pullback.condition_assoc, Scheme.homOfLE_ι]
    rfl
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := w.2
    change C.toBase (C.chartι i (C.overlapToChart i j w.1)) ∈ c.affineOpen.1
    rw [← hz]
    have h := congrArg (fun φ ↦ φ z) hbase
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact ((pullback.snd (C.overlapToIntersection i j) c.inIntersection.ι) z).2
  · intro x hx
    have hxi : x ∈ (C.chartι i).opensRange := by
      rw [tautQuotient_chartι_opensRange]
      exact c.affineOpen_le_left hx
    obtain ⟨y, rfl⟩ := hxi
    have hyU : C.toBase (C.chartι i y) ∈ C.U i ⊓ C.U j :=
      ⟨c.affineOpen_le_left hx, c.affineOpen_le_right hx⟩
    let q0 : (C.U i ⊓ C.U j : X.Opens) := ⟨C.toBase (C.chartι i y), hyU⟩
    have h0 : C.chartToBase i y = X.homOfLE (inf_le_left : C.U i ⊓ C.U j ≤ C.U i) q0 := by
      apply (C.U i).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι,
        C.chartToBase_comp_openImmersion, ← C.chartι_toBase, Scheme.Hom.comp_apply]
      rfl
    obtain ⟨z0, hz0f, hz0s⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := C.chartToBase i) (g := X.homOfLE (inf_le_left : C.U i ⊓ C.U j ≤ C.U i)) y q0 h0
    let q1 : c.inIntersection := ⟨q0, hx⟩
    obtain ⟨z1, hz1f, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := C.overlapToIntersection i j) (g := c.inIntersection.ι) z0 q1 (by
        change (pullback.snd (C.chartToBase i)
          (X.homOfLE (inf_le_left : C.U i ⊓ C.U j ≤ C.U i))) z0 = _
        rw [hz0s]
        rfl)
    refine ⟨⟨(C.basicOpenOverlapCover i j).f c z1, z1, rfl⟩, ?_⟩
    change C.chartι i (C.overlapToChart i j
      ((pullback.fst (C.overlapToIntersection i j) c.inIntersection.ι) z1)) = C.chartι i y
    rw [hz1f]
    change C.chartι i ((pullback.fst (C.chartToBase i)
      (X.homOfLE (inf_le_left : C.U i ⊓ C.U j ≤ C.U i))) z0) = _
    rw [hz0f]


-- @@ L518-520 verbatim
theorem tautQuotient_p_image_top (i j : C.I) (c : C.CommonBasicOpen i j) :
    C.toBase ⁻¹ᵁ c.affineOpen.1 = (tensorOverlap_p C i j c) ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, tautQuotient_p_opensRange]


-- @@ L522-528 verbatim
omit C in
theorem tautQuotient_thin3 {Y : Scheme.{u}} (F : Y.Modules) {A B D G : Y.Opens}
    (f1 : op A ⟶ op B) (f2 : op B ⟶ op D) (f3 : op D ⟶ op G) (g : op A ⟶ op G)
    (x : Γ(F, A)) :
    F.presheaf.map f3 (F.presheaf.map f2 (F.presheaf.map f1 x)) = F.presheaf.map g x := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 2


-- @@ L530-533 verbatim
theorem tautQuotient_p_le_chart (i j : C.I) (c : C.CommonBasicOpen i j) :
    (tensorOverlap_p C i j c) ''ᵁ ⊤ ≤ (C.chartι i) ''ᵁ ⊤ := by
  rw [← tautQuotient_p_image_top, tautQuotient_chartι_image_top]
  exact Scheme.Hom.preimage_mono _ c.affineOpen_le_left


-- @@ L535-540 verbatim
/-- Transport of a section of `p_* O(1)` over the common base open to the overlap piece. -/
def tautQuotient_Phi (i j : C.I) (c : C.CommonBasicOpen i j)
    (y : Γ(tautQuotient_N C, c.affineOpen.1)) :
    Γ((Scheme.Modules.restrictFunctor (tensorOverlap_p C i j c)).obj (C.canonicalTwistingSheaf 1), ⊤) :=
  (C.canonicalTwistingSheaf 1).presheaf.map (eqToHom (congrArg op (tautQuotient_p_image_top C i j c)))
    (show Γ(C.canonicalTwistingSheaf 1, C.toBase ⁻¹ᵁ c.affineOpen.1) from y)


-- @@ L542-546 verbatim
theorem tautQuotient_Phi_t (i j : C.I) (c : C.CommonBasicOpen i j) (k : C.basisIndex i) :
    tautQuotient_Phi C i j c ((tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_left).op (tautQuotient_t C i k)) =
      (C.canonicalTwistingSheaf 1).presheaf.map (homOfLE (tautQuotient_p_le_chart C i j c)).op
        ((C.canonicalTwistingSheafRestrictionIso 1 i).inv.app ⊤ (tautQuotient_chartTaut C i k)) :=
  tautQuotient_thin3 (C.canonicalTwistingSheaf 1) _ _ _ _ _


-- @@ L548-555 verbatim
theorem tautQuotient_Phi_t' (i j : C.I) (c : C.CommonBasicOpen i j) (l : C.basisIndex j) :
    tautQuotient_Phi C i j c ((tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_right).op
        (tautQuotient_t C j l)) =
      (C.canonicalTwistingSheaf 1).presheaf.map (homOfLE (by
          rw [← tautQuotient_p_image_top, tautQuotient_chartι_image_top]
          exact Scheme.Hom.preimage_mono _ c.affineOpen_le_right)).op
        ((C.canonicalTwistingSheafRestrictionIso 1 j).inv.app ⊤ (tautQuotient_chartTaut C j l)) :=
  tautQuotient_thin3 (C.canonicalTwistingSheaf 1) _ _ _ _ _


-- @@ L557-605 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Left side of KEY: through `leg_j = leg_i ≫ basisIso`, the chart-`i` section `bᵢₖ` becomes the
right-basis tautological section of `leftₖ`, given the left restriction compatibility. -/
theorem tautQuotient_key_L (i j : C.I) (c : C.CommonBasicOpen i j) (k : C.basisIndex i)
    (hAL : letI : Finite (C.basisIndex i) := C.basisIndex_finite i
      (c.leftTwistRestrictionData 1).restrictIso.hom.app
          ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
          ((C.chartTwistingSheaf 1 i).presheaf.map (homOfLE le_top).op (tautQuotient_chartTaut C i k)) =
        (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.leftSectionBasis
          (c.leftSectionBasis k)).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
          (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤))) :
    letI : Module.Free Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_free i
    letI : Module.Finite Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_finite i
    letI : Finite (C.basisIndex i) := C.basisIndex_finite i
    letI : Module.Free Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_free j
    letI : Module.Finite Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_finite j
    letI : Finite (C.basisIndex j) := C.basisIndex_finite j
    (tensorOverlap_leg (tensorOverlap_ιs C j) (tensorOverlap_p C i j c) (tensorOverlap_gR C i j c)
        (C.commonBasicOpenChartIsoOver i j c).hom (tensorOverlap_hR C i j c) (tensorOverlap_hκR C i j c)
        (C.canonicalTwistingSheafRestrictionIso 1 j) (c.rightTwistRestrictionData 1)).hom.app ⊤
      (tautQuotient_Phi C i j c ((tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_left).op
        (tautQuotient_t C i k))) =
    (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.rightSectionBasis
          (c.leftSectionBasis k)).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
          (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)) := by
  letI : Module.Free Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_free i
  letI : Module.Finite Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_finite i
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  letI : Module.Free Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_free j
  letI : Module.Finite Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_finite j
  letI : Finite (C.basisIndex j) := C.basisIndex_finite j
  rw [tautQuotient_Phi_t]
  have hdesc := congrArg (fun f ↦ Scheme.Modules.Hom.app f ⊤
    ((C.canonicalTwistingSheaf 1).presheaf.map (homOfLE (tautQuotient_p_le_chart C i j c)).op
        ((C.canonicalTwistingSheafRestrictionIso 1 i).inv.app ⊤ (tautQuotient_chartTaut C i k))))
    (tensorOverlap_descent C 1 i j c)
  refine hdesc.symm.trans ?_
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  refine (congrArg (fun w ↦ Scheme.Modules.Hom.app
    ((Scheme.Modules.restrictFunctor (C.commonBasicOpenChartIsoOver i j c).hom).map
      (c.twistingSheafBasisIso 1).hom) ⊤ w)
    (tautQuotient_leg_app _ _ _ _ _ _ _ _ _ _ (homOfLE le_top).op)).trans ?_
  refine (congrArg (fun w ↦ Scheme.Modules.Hom.app
    ((Scheme.Modules.restrictFunctor (C.commonBasicOpenChartIsoOver i j c).hom).map
      (c.twistingSheafBasisIso 1).hom) ⊤ w) hAL).trans ?_
  exact congrArg (fun f : SchemeProjectiveSpace.unitModules c.chart ⟶ c.rightTwistingSheaf 1 ↦
      Scheme.Modules.Hom.app f ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
      (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)))
    (tautChart_tautHom_basisChange _ _ c.leftSectionBasis c.rightSectionBasis (c.leftSectionBasis k))


-- @@ L607-613 verbatim
/-- The scalar of `Γ(X, V_c)` transported to the common chart through the overlap piece. -/
def tautQuotient_kscalar (i j : C.I) (c : C.CommonBasicOpen i j) (a : Γ(X, c.affineOpen.1)) :
    Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤) :=
  ((C.commonBasicOpenChartIsoOver i j c).hom.appIso ⊤).inv
    (((tensorOverlap_p C i j c).appIso ⊤).hom
      (C.scheme.presheaf.map (eqToHom (congrArg op (tautQuotient_p_image_top C i j c)))
        (C.toBase.app c.affineOpen.1 a)))


-- @@ L615-701 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Right side of KEY. -/
theorem tautQuotient_key_R (i j : C.I) (c : C.CommonBasicOpen i j) (k : C.basisIndex i)
    (hAR : letI : Finite (C.basisIndex j) := C.basisIndex_finite j
      ∀ l : C.basisIndex j, (c.rightTwistRestrictionData 1).restrictIso.hom.app
          ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
          ((C.chartTwistingSheaf 1 j).presheaf.map (homOfLE le_top).op (tautQuotient_chartTaut C j l)) =
        (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.rightSectionBasis
          (c.rightSectionBasis l)).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
          (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)))
    (hlin : letI : Finite (C.basisIndex j) := C.basisIndex_finite j
      (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.rightSectionBasis
          (c.leftSectionBasis k)).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
          (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)) =
        (c.rightSectionBasis.repr (c.leftSectionBasis k)).sum (fun l a ↦
          tautQuotient_kscalar C i j c a •
            (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1))
              c.rightSectionBasis (c.rightSectionBasis l)).app
              ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
              (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)))) :
    letI : Module.Free Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_free j
    letI : Module.Finite Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_finite j
    letI : Finite (C.basisIndex j) := C.basisIndex_finite j
    (tensorOverlap_leg (tensorOverlap_ιs C j) (tensorOverlap_p C i j c) (tensorOverlap_gR C i j c)
        (C.commonBasicOpenChartIsoOver i j c).hom (tensorOverlap_hR C i j c) (tensorOverlap_hκR C i j c)
        (C.canonicalTwistingSheafRestrictionIso 1 j) (c.rightTwistRestrictionData 1)).hom.app ⊤
      (tautQuotient_Phi C i j c ((c.rightSectionBasis.repr (c.leftSectionBasis k)).sum
          (fun l a ↦ a • (tautQuotient_N C).presheaf.map (homOfLE c.affineOpen_le_right).op
            (tautQuotient_t C j l)))) =
    (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.rightSectionBasis
          (c.leftSectionBasis k)).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
          (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)) := by
  letI : Module.Free Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_free j
  letI : Module.Finite Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_finite j
  letI : Finite (C.basisIndex j) := C.basisIndex_finite j
  set legJ := tensorOverlap_leg (tensorOverlap_ιs C j) (tensorOverlap_p C i j c) (tensorOverlap_gR C i j c)
    (C.commonBasicOpenChartIsoOver i j c).hom (tensorOverlap_hR C i j c) (tensorOverlap_hκR C i j c)
    (C.canonicalTwistingSheafRestrictionIso 1 j) (c.rightTwistRestrictionData 1) with hlegJ
  rw [hlin]
  have hPhi_sum : ∀ (f : C.basisIndex j →₀ Γ(X, c.affineOpen.1))
      (g : C.basisIndex j → Γ(X, c.affineOpen.1) → Γ(tautQuotient_N C, c.affineOpen.1)),
      tautQuotient_Phi C i j c (f.sum g) = f.sum (fun l a ↦ tautQuotient_Phi C i j c (g l a)) :=
    fun f g ↦ map_finsuppSum ((C.canonicalTwistingSheaf 1).presheaf.map
      (eqToHom (congrArg op (tautQuotient_p_image_top C i j c)))).hom f g
  rw [hPhi_sum]
  refine (map_finsuppSum (legJ.hom.app ⊤).hom _ _).trans ?_
  apply Finsupp.sum_congr
  intro l _
  have hsm : ∀ (a : Γ(X, c.affineOpen.1)) (y : Γ(tautQuotient_N C, c.affineOpen.1)),
      tautQuotient_Phi C i j c (a • y) = ((tensorOverlap_p C i j c).appIso ⊤).hom
        (C.scheme.presheaf.map (eqToHom (congrArg op (tautQuotient_p_image_top C i j c)))
          (C.toBase.app c.affineOpen.1 a)) • tautQuotient_Phi C i j c y := by
    intro a y
    unfold tautQuotient_Phi
    have ee : (eqToHom (congrArg op (tautQuotient_p_image_top C i j c)) :
        op (C.toBase ⁻¹ᵁ c.affineOpen.1) ⟶ op ((tensorOverlap_p C i j c) ''ᵁ ⊤)) =
        (homOfLE (tautQuotient_p_image_top C i j c).ge).op := Subsingleton.elim _ _
    rw [ee]
    change (C.canonicalTwistingSheaf 1).presheaf.map _
      ((C.toBase.app c.affineOpen.1 a) •
        (show Γ(C.canonicalTwistingSheaf 1, C.toBase ⁻¹ᵁ c.affineOpen.1) from y)) = _
    rw [Scheme.Modules.map_smul]
    change _ = (((tensorOverlap_p C i j c).appIso ⊤).inv (((tensorOverlap_p C i j c).appIso ⊤).hom
      (C.scheme.presheaf.map (homOfLE (tautQuotient_p_image_top C i j c).ge).op
        (C.toBase.app c.affineOpen.1 a)))) •
      (show Γ(C.canonicalTwistingSheaf 1, (tensorOverlap_p C i j c) ''ᵁ ⊤) from
        (C.canonicalTwistingSheaf 1).presheaf.map (homOfLE (tautQuotient_p_image_top C i j c).ge).op
          (show Γ(C.canonicalTwistingSheaf 1, C.toBase ⁻¹ᵁ c.affineOpen.1) from y))
    rw [Iso.hom_inv_id_apply]
  have hleg : ∀ (r : Γ((C.twistComparisonOpen i j c).toScheme, ⊤))
      (z : Γ((Scheme.Modules.restrictFunctor (tensorOverlap_p C i j c)).obj
        (C.canonicalTwistingSheaf 1), ⊤)),
      legJ.hom.app ⊤ (r • z) =
        (((C.commonBasicOpenChartIsoOver i j c).hom.appIso ⊤).inv r) •
          (show Γ(c.rightTwistingSheaf 1, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤) from
            legJ.hom.app ⊤ z) :=
    fun r z ↦ Scheme.Modules.Hom.app_smul _ _ _
  have hval : legJ.hom.app ⊤ (tautQuotient_Phi C i j c ((tautQuotient_N C).presheaf.map
      (homOfLE c.affineOpen_le_right).op (tautQuotient_t C j l))) =
      (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.rightSectionBasis
          (c.rightSectionBasis l)).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
          (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)) := by
    rw [tautQuotient_Phi_t']
    exact (tautQuotient_leg_app _ _ _ _ _ _ _ _ _ _ (homOfLE le_top).op).trans (hAR l)
  change legJ.hom.app ⊤ (tautQuotient_Phi C i j c (_ • _)) = _
  rw [hsm, hleg, hval]
  rfl


-- @@ L703-712 verbatim
/-- The restriction-data hypothesis (element form) for the left chart of a common basic open. -/
def tautQuotient_HypAL : Prop :=
  ∀ (i j : C.I) (c : C.CommonBasicOpen i j) (k : C.basisIndex i),
    letI : Finite (C.basisIndex i) := C.basisIndex_finite i
    (c.leftTwistRestrictionData 1).restrictIso.hom.app
        ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
        ((C.chartTwistingSheaf 1 i).presheaf.map (homOfLE le_top).op (tautQuotient_chartTaut C i k)) =
      (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.leftSectionBasis
        (c.leftSectionBasis k)).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
        (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤))


-- @@ L714-723 verbatim
/-- The restriction-data hypothesis (element form) for the right chart. -/
def tautQuotient_HypAR : Prop :=
  ∀ (i j : C.I) (c : C.CommonBasicOpen i j) (l : C.basisIndex j),
    letI : Finite (C.basisIndex j) := C.basisIndex_finite j
    (c.rightTwistRestrictionData 1).restrictIso.hom.app
        ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
        ((C.chartTwistingSheaf 1 j).presheaf.map (homOfLE le_top).op (tautQuotient_chartTaut C j l)) =
      (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.rightSectionBasis
        (c.rightSectionBasis l)).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
        (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤))


-- @@ L725-738 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The linearity hypothesis for the right-basis tautological sections. -/
def tautQuotient_HypLin : Prop :=
  ∀ (i j : C.I) (c : C.CommonBasicOpen i j) (k : C.basisIndex i),
    letI : Finite (C.basisIndex j) := C.basisIndex_finite j
    (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.rightSectionBasis
        (c.leftSectionBasis k)).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
        (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)) =
      (c.rightSectionBasis.repr (c.leftSectionBasis k)).sum (fun l a ↦
        tautQuotient_kscalar C i j c a •
          (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1))
            c.rightSectionBasis (c.rightSectionBasis l)).app
            ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
            (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)))


-- @@ L740-763 verbatim
theorem tautQuotient_key_of_hyps (hAL : tautQuotient_HypAL C) (hAR : tautQuotient_HypAR C)
    (hlin : tautQuotient_HypLin C) : tautQuotient_Key C := by
  intro i j c k
  letI : Module.Free Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_free j
  letI : Module.Finite Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_finite j
  letI : Finite (C.basisIndex j) := C.basisIndex_finite j
  let legJ := tensorOverlap_leg (tensorOverlap_ιs C j) (tensorOverlap_p C i j c) (tensorOverlap_gR C i j c)
    (C.commonBasicOpenChartIsoOver i j c).hom (tensorOverlap_hR C i j c) (tensorOverlap_hκR C i j c)
    (C.canonicalTwistingSheafRestrictionIso 1 j) (c.rightTwistRestrictionData 1)
  have hΦ : Function.Injective (tautQuotient_Phi C i j c) :=
    (ConcreteCategory.bijective_of_isIso ((C.canonicalTwistingSheaf 1).presheaf.map
      (eqToHom (congrArg op (tautQuotient_p_image_top C i j c))))).1
  have hJ : Function.Injective (legJ.hom.app ⊤) := by
    intro a b h
    have h' := congrArg (legJ.inv.app ⊤) h
    have e : ∀ z, legJ.inv.app ⊤ (legJ.hom.app ⊤ z) = z := fun z ↦ by
      have := congrArg (fun f ↦ Scheme.Modules.Hom.app f ⊤ z) legJ.hom_inv_id
      simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using this
    rwa [e, e] at h'
  apply hΦ
  apply hJ
  exact (tautQuotient_key_L C i j c k (hAL i j c k)).trans
    (tautQuotient_key_R C i j c k (hAR i j c) (hlin i j c k)).symm


-- @@ L765-769 verbatim
/-- **The leaf, modulo the two chart-level restriction compatibilities and linearity.** -/
theorem tautQuotient_exists_tautologicalQuotient_of_hyps (hAL : tautQuotient_HypAL C) (hAR : tautQuotient_HypAR C)
    (hlin : tautQuotient_HypLin C) :
    ∃ σ : (Scheme.Modules.pullback C.toBase).obj E ⟶ C.canonicalTwistingSheaf 1, Epi σ :=
  tautQuotient_exists_tautologicalQuotient_of_key C (tautQuotient_key_of_hyps C hAL hAR hlin)


-- @@ L771-776 verbatim
omit C in
theorem tautQuotient_restrictUnitIso_one {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (V : Y.Opens) :
    (Scheme.Modules.restrictUnitIso f).hom.app V (1 : Γ(Z, f ''ᵁ V)) = (1 : Γ(Y, V)) := by
  change (f.appIso V).hom 1 = 1
  exact map_one _


-- @@ L778-787 verbatim
/-- The chart-level restriction compatibility (a), morphism form, for the left leg. -/
def tautQuotient_HypA_left : Prop :=
  ∀ (i j : C.I) (c : C.CommonBasicOpen i j) (m : E.val.obj (op (C.U i))),
    letI : Finite (C.basisIndex i) := C.basisIndex_finite i
    (Scheme.Modules.restrictFunctor c.chartToLeft).map
        (tautChart_tautHom Γ(X, C.U i) (E.val.obj (op (C.U i))) (C.sectionBasis i) m) ≫
      (c.leftTwistRestrictionData 1).restrictIso.hom =
    (Scheme.Modules.restrictUnitIso c.chartToLeft).hom ≫
      tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.leftSectionBasis
        (c.leftRestriction m)


-- @@ L789-798 verbatim
/-- The chart-level restriction compatibility (a), morphism form, for the right leg. -/
def tautQuotient_HypA_right : Prop :=
  ∀ (i j : C.I) (c : C.CommonBasicOpen i j) (m : E.val.obj (op (C.U j))),
    letI : Finite (C.basisIndex j) := C.basisIndex_finite j
    (Scheme.Modules.restrictFunctor c.chartToRight).map
        (tautChart_tautHom Γ(X, C.U j) (E.val.obj (op (C.U j))) (C.sectionBasis j) m) ≫
      (c.rightTwistRestrictionData 1).restrictIso.hom =
    (Scheme.Modules.restrictUnitIso c.chartToRight).hom ≫
      tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.rightSectionBasis
        (c.rightRestriction m)


-- @@ L800-817 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem tautQuotient_HypAL_of (h : tautQuotient_HypA_left C) : tautQuotient_HypAL C := by
  intro i j c k
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  let V := (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤
  have hm := congrArg (fun f : (Scheme.Modules.restrictFunctor c.chartToLeft).obj
      (SchemeProjectiveSpace.unitModules (space Γ(X, C.U i) (E.val.obj (op (C.U i))))) ⟶
        twistingSheafOfBasisIndex Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1))
          c.leftSectionBasis 1 ↦ Scheme.Modules.Hom.app f V
    (1 : Γ(space Γ(X, C.U i) (E.val.obj (op (C.U i))), c.chartToLeft ''ᵁ V)))
    (h i j c (C.sectionBasis i k))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hm
  rw [tautQuotient_restrictUnitIso_one, c.leftRestriction_sectionBasis] at hm
  refine Eq.trans ?_ hm
  congr 1
  rw [tautQuotient_chartTaut]
  refine (tautChart_app_map _ _ _).symm.trans ?_
  congr 1


-- @@ L819-836 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem tautQuotient_HypAR_of (h : tautQuotient_HypA_right C) : tautQuotient_HypAR C := by
  intro i j c l
  letI : Finite (C.basisIndex j) := C.basisIndex_finite j
  let V := (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤
  have hm := congrArg (fun f : (Scheme.Modules.restrictFunctor c.chartToRight).obj
      (SchemeProjectiveSpace.unitModules (space Γ(X, C.U j) (E.val.obj (op (C.U j))))) ⟶
        twistingSheafOfBasisIndex Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1))
          c.rightSectionBasis 1 ↦ Scheme.Modules.Hom.app f V
    (1 : Γ(space Γ(X, C.U j) (E.val.obj (op (C.U j))), c.chartToRight ''ᵁ V)))
    (h i j c (C.sectionBasis j l))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hm
  rw [tautQuotient_restrictUnitIso_one, c.rightRestriction_sectionBasis] at hm
  refine Eq.trans ?_ hm
  congr 1
  rw [tautQuotient_chartTaut]
  refine (tautChart_app_map _ _ _).symm.trans ?_
  congr 1


-- @@ L838-843 verbatim
omit C in
theorem tautQuotient_appLE_congr {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (hfg : f = g) (U : Z.Opens)
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ g ⁻¹ᵁ U) (x : Γ(Z, U)) :
    f.appLE U V h x = g.appLE U V h' x := by
  subst hfg
  rfl


-- @@ L845-850 verbatim
omit C in
theorem tautQuotient_comp_appLE_apply {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W) (U : W.Opens)
    (V : Y.Opens) (e : V ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(W, U)) :
    (f ≫ g).appLE U V e x = f.appLE (g ⁻¹ᵁ U) V e (g.app U x) := by
  rw [Scheme.Hom.comp_appLE]
  rfl


-- @@ L852-858 verbatim
omit C in
theorem tautQuotient_map_appLE_apply {Y Z : Scheme.{u}} (f : Y ⟶ Z) {U U' : Z.Opens} {V : Y.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (i : op U' ⟶ op U) (x : Γ(Z, U')) :
    f.appLE U V e (Z.presheaf.map i x) =
      f.appLE U' V (e.trans ((Opens.map f.base).map i.unop).le) x := by
  have := ConcreteCategory.congr_hom (Scheme.Hom.map_appLE f e i) x
  simpa only [ConcreteCategory.comp_apply] using this


-- @@ L860-869 verbatim
theorem tautQuotient_p_toBase (i j : C.I) (c : C.CommonBasicOpen i j) :
    tensorOverlap_p C i j c ≫ C.toBase =
      (C.commonBasicOpenChartIsoOver i j c).hom ≫ c.chartToAmbient := by
  change (tensorOverlap_gL C i j c ≫ C.chartι i) ≫ C.toBase = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun f ↦ tensorOverlap_gL C i j c ≫ f) (C.chartι_toBase i)).trans ?_
  refine (congrArg (fun f ↦ f ≫ C.chartToAmbient i) (tensorOverlap_hκL C i j c).symm).trans ?_
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f ↦ (C.commonBasicOpenChartIsoOver i j c).hom ≫ f)
      c.chartToLeft_comp_chartToAmbient)


-- @@ L871-877 verbatim
theorem tautQuotient_p_toBase_le (i j : C.I) (c : C.CommonBasicOpen i j) :
    (⊤ : (C.twistComparisonOpen i j c).toScheme.Opens) ≤
      (tensorOverlap_p C i j c ≫ C.toBase) ⁻¹ᵁ c.affineOpen.1 := by
  intro x _
  have h : (tensorOverlap_p C i j c) x ∈ (tensorOverlap_p C i j c) ''ᵁ ⊤ := ⟨x, trivial, rfl⟩
  rw [← tautQuotient_p_image_top] at h
  exact h


-- @@ L879-913 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The transported scalar is the restriction of the chart structure scalar. -/
theorem tautQuotient_kscalar_eq (i j : C.I) (c : C.CommonBasicOpen i j) (a : Γ(X, c.affineOpen.1)) :
    tautQuotient_kscalar C i j c a = c.chart.presheaf.map
      (homOfLE (le_top : (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤ ≤ ⊤)).op
      (tautChart_scal Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) a) := by
  let κ := (C.commonBasicOpenChartIsoOver i j c).hom
  let p := tensorOverlap_p C i j c
  have hL : (p.appIso ⊤).hom (C.scheme.presheaf.map
      (eqToHom (congrArg op (tautQuotient_p_image_top C i j c))) (C.toBase.app c.affineOpen.1 a)) =
      (p ≫ C.toBase).appLE c.affineOpen.1 ⊤ (tautQuotient_p_toBase_le C i j c) a := by
    rw [Scheme.Hom.appIso_hom', tautQuotient_map_appLE_apply]
    exact (tautQuotient_comp_appLE_apply p C.toBase _ _ _ a).symm
  have hR : (κ.appIso ⊤).hom (c.chart.presheaf.map
      (homOfLE (le_top : κ ''ᵁ ⊤ ≤ ⊤)).op
      (tautChart_scal Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) a)) =
      (κ ≫ intrinsicToSpec (R := Γ(X, c.affineOpen.1)) (M := E.val.obj (op c.affineOpen.1))).appLE
        ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, c.affineOpen.1))).inv a) := by
    rw [Scheme.Hom.appIso_hom', tautQuotient_map_appLE_apply, tautQuotient_comp_appLE_apply]
    rfl
  have hM : (p ≫ C.toBase).appLE c.affineOpen.1 ⊤ (tautQuotient_p_toBase_le C i j c) a =
      (κ ≫ intrinsicToSpec (R := Γ(X, c.affineOpen.1)) (M := E.val.obj (op c.affineOpen.1))).appLE
        ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, c.affineOpen.1))).inv a) := by
    have e1 : p ≫ C.toBase = (κ ≫ intrinsicToSpec (R := Γ(X, c.affineOpen.1))
        (M := E.val.obj (op c.affineOpen.1))) ≫ c.affineOpen.2.fromSpec := by
      rw [tautQuotient_p_toBase, Category.assoc]
      rfl
    rw [tautQuotient_appLE_congr e1 _ _ _ (by rw [← e1]; exact tautQuotient_p_toBase_le C i j c),
      tautQuotient_comp_appLE_apply]
    refine (congrArg (fun z ↦ (κ ≫ intrinsicToSpec (R := Γ(X, c.affineOpen.1))
      (M := E.val.obj (op c.affineOpen.1))).appLE _ ⊤ (by simp) z)
      (IsAffineOpen.fromSpec_app_self_apply c.affineOpen.2 a)).trans ?_
    exact tautQuotient_map_appLE_apply _ _ _ _
  unfold tautQuotient_kscalar
  rw [hL, hM, ← hR, Iso.hom_inv_id_apply]


-- @@ L915-930 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The linearity hypothesis holds. -/
theorem tautQuotient_hypLin : tautQuotient_HypLin C := by
  intro i j c k
  letI : Finite (C.basisIndex j) := C.basisIndex_finite j
  have hk : c.leftSectionBasis k = (c.rightSectionBasis.repr (c.leftSectionBasis k)).sum
      (fun l a ↦ a • c.rightSectionBasis l) := by
    rw [← Finsupp.linearCombination_apply, c.rightSectionBasis.linearCombination_repr]
  refine (congrArg (fun m ↦ (tautChart_tautHom Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1))
      c.rightSectionBasis m).app ((C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤)
      (1 : Γ(c.chart, (C.commonBasicOpenChartIsoOver i j c).hom ''ᵁ ⊤))) hk).trans ?_
  refine (tautChart_tautHom_app_sum _ _ c.rightSectionBasis _ _ _).trans ?_
  apply Finsupp.sum_congr
  intro l _
  rw [tautQuotient_kscalar_eq]
  rfl


-- @@ L932-937 verbatim
/-- **The leaf, modulo only the chart-level restriction compatibility (a).** -/
theorem tautQuotient_exists_tautologicalQuotient_of_A (hL : tautQuotient_HypA_left C)
    (hR : tautQuotient_HypA_right C) :
    ∃ σ : (Scheme.Modules.pullback C.toBase).obj E ⟶ C.canonicalTwistingSheaf 1, Epi σ :=
  tautQuotient_exists_tautologicalQuotient_of_hyps C (tautQuotient_HypAL_of C hL) (tautQuotient_HypAR_of C hR)
    (tautQuotient_hypLin C)


-- @@ L939-942 verbatim
theorem tautQuotient_hypA_left : tautQuotient_HypA_left C := by
  intro i j c m
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  simpa only [tautChart_tautHom_eq_L1a] using tautSection_tautHom_leftRestrict c m


-- @@ L944-947 verbatim
theorem tautQuotient_hypA_right : tautQuotient_HypA_right C := by
  intro i j c m
  letI : Finite (C.basisIndex j) := C.basisIndex_finite j
  simpa only [tautChart_tautHom_eq_L1a] using tautSection_tautHom_rightRestrict c m


-- @@ L949-955 verbatim
/-- The tautological morphism `E ⟶ p_* O(1)`, sending the frame section `bᵢₖ` over the base
chart `Uᵢ` to the tautological section `bᵢₖ` of `O(1)` over the chart `i`. -/
def tautologicalPushforwardHom :
    E ⟶ (Scheme.Modules.pushforward C.toBase).obj (C.canonicalTwistingSheaf 1) :=
  tautQuotient_alphaGlued C (tautQuotient_key_of_hyps C
    (tautQuotient_HypAL_of C (tautQuotient_hypA_left C))
    (tautQuotient_HypAR_of C (tautQuotient_hypA_right C)) (tautQuotient_hypLin C))


-- @@ L957-959 verbatim
theorem tautologicalPushforwardHom_app (i : C.I) (k : C.basisIndex i) :
    C.tautologicalPushforwardHom.app (C.U i) (C.sectionBasis i k) = tautQuotient_t C i k :=
  tautQuotient_alphaGlued_app C _ i k


-- @@ L961-964 verbatim
/-- The tautological quotient `p^* E ⟶ O(1)`, adjoint to `tautologicalPushforwardHom`. -/
def tautologicalQuotient : (Scheme.Modules.pullback C.toBase).obj E ⟶ C.canonicalTwistingSheaf 1 :=
  ((Scheme.Modules.pullbackPushforwardAdjunction C.toBase).homEquiv _ _).symm
    C.tautologicalPushforwardHom


-- @@ L966-977 verbatim
instance tautologicalQuotient_epi : Epi C.tautologicalQuotient := by
  refine tautQuotient_epi_of_generating C.toBase (C.canonicalTwistingSheaf 1)
    C.tautologicalPushforwardHom
    (fun ij : Σ i : C.I, C.basisIndex i ↦ (C.literalLinearOpen ij).toScheme)
    (fun ij ↦ (C.literalLinearOpen ij).ι ≫ C.chartι ij.1)
    C.literalLinearOpenCover.iSup_opensRange (fun ij ↦ C.U ij.1)
    (fun ij ↦ tautQuotient_toBase_range_le C ij.1 ij.2) (fun ij ↦ C.sectionBasis ij.1 ij.2) ?_
  intro ij V s
  rw [tautologicalPushforwardHom_app]
  exact tautQuotient_generating_of_unitIso _ _ (C.canonicalTwistingSheafLiteralLinearOpenIso 1 ij)
    (tautQuotient_toBase_range_le C ij.1 ij.2) (tautQuotient_t C ij.1 ij.2)
    (tautQuotient_literal_t C ij.1 ij.2) V s


-- @@ L979-982 verbatim
/-- The tautological quotient `p^* E ↠ O(1)` exists. -/
theorem exists_tautologicalQuotient :
    ∃ σ : (Scheme.Modules.pullback C.toBase).obj E ⟶ C.canonicalTwistingSheaf 1, Epi σ :=
  ⟨C.tautologicalQuotient, inferInstance⟩


-- @@ L984-984 verbatim
end Global


-- @@ L986-986 verbatim
end AffineFrameCover

-- @@ L987-987 verbatim
end SchemeProjectiveBundle
