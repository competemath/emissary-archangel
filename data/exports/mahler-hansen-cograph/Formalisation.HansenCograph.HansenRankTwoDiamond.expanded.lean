/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.RankedFlagDiamondSwitch
import Formalisation.HansenCograph.HansenPortalDiamond
import Formalisation.HansenCograph.HansenFullFlagSingleton


-- @@ L10-17 verbatim
/-!
# Thin rank-two intervals in Hansen face lattices

This file develops the global thinness invariant used by the full-flag
argument.  The local portal squares in `HansenPortalDiamond` remain useful
for the layer switch; global thinness is the cleaner invariant for cotree
induction.
-/


-- @@ L19-19 verbatim
open Set SimpleGraph


-- @@ L21-21 verbatim
namespace HansenCograph


-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
namespace RankTwoDiamond


-- @@ L27-146 verbatim
/-- Products of thin posets are thin.  A two-step interval either changes
one coordinate twice, when thinness in that factor supplies the other
middle, or changes the two coordinates in opposite orders. -/
theorem prod {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (hP : RankTwoDiamond P) (hQ : RankTwoDiamond Q) :
    RankTwoDiamond (P × Q) := by
  intro a b c hab hbc
  rcases Prod.covBy_iff.mp hab with habP | habQ
  · rcases Prod.covBy_iff.mp hbc with hbcP | hbcQ
    · obtain ⟨p, hp, hp_unique⟩ := hP habP.1 hbcP.1
      refine ⟨(p, a.2), ?_, ?_⟩
      · constructor
        · exact Prod.covBy_iff.mpr (Or.inl ⟨hp.1, rfl⟩)
        constructor
        · exact Prod.covBy_iff.mpr (Or.inl ⟨hp.2.1,
            habP.2.trans hbcP.2⟩)
        · intro h
          apply hp.2.2
          exact congrArg Prod.fst h
      · intro x hx
        rcases Prod.covBy_iff.mp hx.1 with haxP | haxQ
        · rcases Prod.covBy_iff.mp hx.2.1 with hxcP | hxcQ
          · have hx_ne : x.1 ≠ b.1 := by
              intro hxb
              apply hx.2.2
              apply Prod.ext hxb
              exact haxP.2.symm.trans habP.2
            have hxp : x.1 = p := hp_unique x.1
              ⟨haxP.1, hxcP.1, hx_ne⟩
            apply Prod.ext hxp
            exact haxP.2.symm
          · have hac : a.2 = c.2 := habP.2.trans hbcP.2
            exact False.elim (hxcQ.1.ne
              (haxP.2.symm.trans hac))
        · rcases Prod.covBy_iff.mp hx.2.1 with hxcP | hxcQ
          · have hac : a.2 = c.2 := habP.2.trans hbcP.2
            exact False.elim (haxQ.1.ne (hxcP.2.trans hac.symm).symm)
          · have hac : a.1 = c.1 := haxQ.2.trans hxcQ.2
            exact False.elim ((lt_trans habP.1.lt hbcP.1.lt).ne hac)
    · refine ⟨(a.1, c.2), ?_, ?_⟩
      · constructor
        · exact Prod.covBy_iff.mpr (Or.inr ⟨habP.2.symm ▸ hbcQ.1, rfl⟩)
        constructor
        · exact Prod.covBy_iff.mpr (Or.inl ⟨hbcQ.2 ▸ habP.1, rfl⟩)
        · intro h
          have hfirst : a.1 = b.1 := by
            simpa using congrArg (fun z : P × Q ↦ z.1) h
          exact habP.1.ne hfirst
      · intro x hx
        rcases Prod.covBy_iff.mp hx.1 with haxP | haxQ
        · rcases Prod.covBy_iff.mp hx.2.1 with hxcP | hxcQ
          · have hac : a.2 = c.2 := haxP.2.trans hxcP.2
            exact False.elim (hbcQ.1.ne
              (habP.2.symm.trans hac))
          · exact False.elim (hx.2.2 (Prod.ext
              (hxcQ.2.trans hbcQ.2.symm)
              (haxP.2.symm.trans habP.2)))
        · rcases Prod.covBy_iff.mp hx.2.1 with hxcP | hxcQ
          · apply Prod.ext <;> simp only
            · exact haxQ.2.symm
            · exact hxcP.2
          · have hac : a.1 = c.1 := haxQ.2.trans hxcQ.2
            exact False.elim (habP.1.ne (hac.trans hbcQ.2.symm))
  · rcases Prod.covBy_iff.mp hbc with hbcP | hbcQ
    · refine ⟨(c.1, a.2), ?_, ?_⟩
      · constructor
        · exact Prod.covBy_iff.mpr (Or.inl ⟨habQ.2.symm ▸ hbcP.1, rfl⟩)
        constructor
        · exact Prod.covBy_iff.mpr (Or.inr ⟨hbcP.2 ▸ habQ.1, rfl⟩)
        · intro h
          have hsecond : a.2 = b.2 := by
            simpa using congrArg (fun z : P × Q ↦ z.2) h
          exact habQ.1.ne hsecond
      · intro x hx
        rcases Prod.covBy_iff.mp hx.1 with haxP | haxQ
        · rcases Prod.covBy_iff.mp hx.2.1 with hxcP | hxcQ
          · have hac : a.2 = c.2 := haxP.2.trans hxcP.2
            exact False.elim (habQ.1.ne (hac.trans hbcP.2.symm))
          · apply Prod.ext <;> simp only
            · exact hxcQ.2
            · exact haxP.2.symm
        · rcases Prod.covBy_iff.mp hx.2.1 with hxcP | hxcQ
          · exact False.elim (hx.2.2 (Prod.ext
              (haxQ.2.symm.trans habQ.2)
              (hxcP.2.trans hbcP.2.symm)))
          · have hac : a.1 = c.1 := haxQ.2.trans hxcQ.2
            exact False.elim (hbcP.1.ne
              (habQ.2.symm.trans hac))
    · obtain ⟨q, hq, hq_unique⟩ := hQ habQ.1 hbcQ.1
      refine ⟨(a.1, q), ?_, ?_⟩
      · constructor
        · exact Prod.covBy_iff.mpr (Or.inr ⟨hq.1, rfl⟩)
        constructor
        · exact Prod.covBy_iff.mpr (Or.inr ⟨hq.2.1,
            habQ.2.trans hbcQ.2⟩)
        · intro h
          apply hq.2.2
          exact congrArg Prod.snd h
      · intro x hx
        rcases Prod.covBy_iff.mp hx.1 with haxP | haxQ
        · rcases Prod.covBy_iff.mp hx.2.1 with hxcP | hxcQ
          · have hac : a.2 = c.2 := haxP.2.trans hxcP.2
            exact False.elim ((lt_trans habQ.1.lt hbcQ.1.lt).ne hac)
          · have hac : a.1 = c.1 := habQ.2.trans hbcQ.2
            exact False.elim (haxP.1.ne (hxcQ.2.trans hac.symm).symm)
        · rcases Prod.covBy_iff.mp hx.2.1 with hxcP | hxcQ
          · have hac : a.1 = c.1 := habQ.2.trans hbcQ.2
            exact False.elim (hxcP.1.ne
              (haxQ.2.symm.trans hac))
          · have hx_ne : x.2 ≠ b.2 := by
              intro hxb
              apply hx.2.2
              apply Prod.ext
              · exact haxQ.2.symm.trans habQ.2
              · exact hxb
            have hxq : x.2 = q := hq_unique x.2
              ⟨haxQ.1, hxcQ.1, hx_ne⟩
            apply Prod.ext <;> simp only
            · exact haxQ.2.symm
            · exact hxq


-- @@ L148-148 verbatim
end RankTwoDiamond


-- @@ L150-150 verbatim
namespace HansenCombinatorialFace


-- @@ L152-167 expanded
private theorem hansenJoinFaceEquiv_le_iff_local {V : Type u} {W : Type v} [Fintype V]
    [DecidableEq V] [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (C D : AbstractJoinFace A B) : hansenJoinFaceEquiv A B C ≤ hansenJoinFaceEquiv A B D ↔ C ≤ D :=
  by
  simpa only [hansenJoinFaceEquiv] using
    incidenceClosedTransportSurjEquiv_le_iff
      (signedJoinIncidence (signA := fun f : HansenFacetLabel A ↦ f.1) (signB :=
        fun f : HansenFacetLabel B ↦ f.1) (hansenLabelIncidence A) (hansenLabelIncidence B))
      (hansenLabelIncidence (graphJoin A B)) (joinVertexLabelMap A B) (joinFacetLabelEquiv A B)
      (joinVertexLabelMap_surjective A B)
      (fun vertex facet ↦ hansenLabelIncidence_join_map A B vertex facet) C D


-- @@ L169-183 verbatim
private theorem rootedNeg_left_projection_local
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedNeg A) (K : RootedNeg B) :
    joinFacetProjLeft
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct
          (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (F.1 : Set _) := by
  apply joinFacetProjLeft_sameSignFacetProduct_eq
  intro facet hfacet
  rcases K.2.carrier_nonempty with ⟨other, hother⟩
  exact ⟨other, hother, by rw [F.2.facet_sign hfacet, K.2.facet_sign hother]⟩


-- @@ L185-199 verbatim
private theorem rootedNeg_right_projection_local
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedNeg A) (K : RootedNeg B) :
    joinFacetProjRight
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct
          (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (K.1 : Set _) := by
  apply joinFacetProjRight_sameSignFacetProduct_eq
  intro facet hfacet
  rcases F.2.carrier_nonempty with ⟨other, hother⟩
  exact ⟨other, hother, by rw [F.2.facet_sign hother, K.2.facet_sign hfacet]⟩


-- @@ L201-214 verbatim
private theorem neutral_left_projection_local
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : NeutralOrEmpty A) (K : NeutralOrEmpty B) :
    joinFacetProjLeft
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (F.1 : Set _) := by
  apply joinFacetProjLeft_sameSignFacetProduct_eq
  intro facet hfacet
  rcases K.2.exists_facet_sign facet.1 with ⟨other, hother, hs⟩
  exact ⟨other, hother, hs.symm⟩


-- @@ L216-229 verbatim
private theorem neutral_right_projection_local
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : NeutralOrEmpty A) (K : NeutralOrEmpty B) :
    joinFacetProjRight
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (K.1 : Set _) := by
  apply joinFacetProjRight_sameSignFacetProduct_eq
  intro facet hfacet
  rcases F.2.exists_facet_sign facet.1 with ⟨other, hother, hs⟩
  exact ⟨other, hother, hs⟩


-- @@ L231-258 verbatim
/-- Within the negative-rooted stratum, the Hansen join face order is the
componentwise product order. -/
theorem joinRootedNeg_le_iff
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F₁ F₂ : RootedNeg A) (K₁ K₂ : RootedNeg B) :
    joinRootedNeg A B F₁ K₁ ≤ joinRootedNeg A B F₂ K₂ ↔
      F₁.1 ≤ F₂.1 ∧ K₁.1 ≤ K₂.1 := by
  change hansenJoinFaceEquiv A B _ ≤ hansenJoinFaceEquiv A B _ ↔ _
  rw [hansenJoinFaceEquiv_le_iff_local]
  change sameSignFacetProduct
      (F₂.1 : Set (HansenFacetLabel A)) (K₂.1 : Set (HansenFacetLabel B)) ⊆
      sameSignFacetProduct
        (F₁.1 : Set (HansenFacetLabel A)) (K₁.1 : Set (HansenFacetLabel B)) ↔
    (F₂.1 : Set (HansenFacetLabel A)) ⊆ (F₁.1 : Set (HansenFacetLabel A)) ∧
      (K₂.1 : Set (HansenFacetLabel B)) ⊆ (K₁.1 : Set (HansenFacetLabel B))
  constructor
  · intro h
    constructor
    · rw [← rootedNeg_left_projection_local A B F₂ K₂,
          ← rootedNeg_left_projection_local A B F₁ K₁]
      exact Set.image_mono h
    · rw [← rootedNeg_right_projection_local A B F₂ K₂,
          ← rootedNeg_right_projection_local A B F₁ K₁]
      exact Set.image_mono h
  · rintro ⟨hF, hK⟩ facet hfacet
    exact ⟨hF hfacet.1, hK hfacet.2⟩


-- @@ L260-286 verbatim
theorem joinNeutral_le_joinRootedNeg_iff
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W)
    (E : NeutralOrEmpty A) (L : NeutralOrEmpty B)
    (F : RootedNeg A) (K : RootedNeg B) :
    joinNeutral A B E L ≤ joinRootedNeg A B F K ↔
      E.1 ≤ F.1 ∧ L.1 ≤ K.1 := by
  change hansenJoinFaceEquiv A B _ ≤ hansenJoinFaceEquiv A B _ ↔ _
  rw [hansenJoinFaceEquiv_le_iff_local]
  change sameSignFacetProduct
      (F.1 : Set (HansenFacetLabel A)) (K.1 : Set (HansenFacetLabel B)) ⊆
      sameSignFacetProduct
        (E.1 : Set (HansenFacetLabel A)) (L.1 : Set (HansenFacetLabel B)) ↔
    (F.1 : Set (HansenFacetLabel A)) ⊆ (E.1 : Set (HansenFacetLabel A)) ∧
      (K.1 : Set (HansenFacetLabel B)) ⊆ (L.1 : Set (HansenFacetLabel B))
  constructor
  · intro h
    constructor
    · rw [← rootedNeg_left_projection_local A B F K,
          ← neutral_left_projection_local A B E L]
      exact Set.image_mono h
    · rw [← rootedNeg_right_projection_local A B F K,
          ← neutral_right_projection_local A B E L]
      exact Set.image_mono h
  · rintro ⟨hF, hK⟩ facet hfacet
    exact ⟨hF hfacet.1, hK hfacet.2⟩


-- @@ L288-294 verbatim
theorem IsRootedNeg.ne_top_local
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {F : HansenCombinatorialFace G} (hF : F.IsRootedNeg) : F ≠ top G := by
  intro h
  apply hF.2
  rw [h]
  exact containsVertex_top G _


-- @@ L296-301 verbatim
theorem IsRootedNeg.not_isRootedPos_local
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {F : HansenCombinatorialFace G} (hF : F.IsRootedNeg) :
    ¬F.IsRootedPos := by
  intro hpos
  exact hF.2 hpos.1


-- @@ L303-315 verbatim
theorem IsRootedNeg.lower_strata_local
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {F X : HansenCombinatorialFace G} (hF : F.IsRootedNeg) (hXF : X ≤ F) :
    X.IsRootedNeg ∨ X.IsNeutralOrEmpty := by
  rcases strata_cases G X with htop | hpos | hneg | hneutral
  · exfalso
    apply hF.ne_top_local
    rw [htop] at hXF
    exact top_unique hXF
  · exfalso
    exact hF.2 (hpos.1.mono hXF)
  · exact Or.inl hneg
  · exact Or.inr hneutral


-- @@ L317-327 verbatim
theorem IsRootedNeg.upper_of_ne_top_local
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {F X : HansenCombinatorialFace G} (hF : F.IsRootedNeg)
    (hFX : F ≤ X) (hX : X ≠ top G) : X.IsRootedNeg := by
  rcases strata_cases G X with htop | hpos | hneg | hneutral
  · exact False.elim (hX htop)
  · exfalso
    exact hpos.2 (hF.1.mono hFX)
  · exact hneg
  · exfalso
    exact hneutral.2 (hF.1.mono hFX)


-- @@ L329-335 expanded
noncomputable def joinRootedNegMap {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) :
    RootedNeg A × RootedNeg B → RootedNeg (graphJoin A B) := fun pair ↦
  ⟨joinRootedNeg A B pair.1 pair.2, joinRootedNeg_isRootedNeg A B pair.1 pair.2⟩


-- @@ L337-365 expanded
theorem joinRootedNegMap_bijective {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Bijective (joinRootedNegMap A B) :=
  by
  constructor
  · intro p q h
    apply joinRootedNeg_pair_injective A B
    exact congrArg Subtype.val h
  · intro X
    let code := (joinFaceCodeEquiv A B).symm X.1
    have hrepr : joinFaceCodeToFace A B code = X.1 := (joinFaceCodeEquiv A B).apply_symm_apply X.1
    rcases code with unit | code
    · change top (graphJoin A B) = X.1 at hrepr
      exact False.elim (X.2.ne_top_local hrepr.symm)
    · rcases code with pair | code
      · change joinRootedPos A B pair.1 pair.2 = X.1 at hrepr
        exfalso
        apply X.2.not_isRootedPos_local
        rw [← hrepr]
        exact joinRootedPos_isRootedPos A B pair.1 pair.2
      · rcases code with pair | pair
        · exact ⟨pair, Subtype.ext hrepr⟩
        · change joinNeutral A B pair.1 pair.2 = X.1 at hrepr
          exfalso
          apply X.2.not_isNeutralOrEmpty
          rw [← hrepr]
          exact joinNeutral_isNeutralOrEmpty A B pair.1 pair.2


-- @@ L367-377 expanded
/-- The negative-rooted stratum of a Hansen join is an order product. -/
noncomputable def joinRootedNegOrderIso {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) :
    RootedNeg A × RootedNeg B ≃o RootedNeg (graphJoin A B)
    where
  toEquiv := Equiv.ofBijective (joinRootedNegMap A B) (joinRootedNegMap_bijective A B)
  map_rel_iff' := by
    intro x y
    exact joinRootedNeg_le_iff A B x.1 y.1 x.2 y.2


-- @@ L379-507 expanded
/-- Exact neutral-to-negative portal cover law. -/
theorem joinNegativePortal_covBy_iff {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) (E : NeutralOrEmpty A)
    (L : NeutralOrEmpty B) (F : RootedNeg A) (K : RootedNeg B) :
    joinNeutral A B E L ⋖ joinRootedNeg A B F K ↔ E.1 ⋖ F.1 ∧ L.1 ⋖ K.1 :=
  by
  constructor
  · intro hjoin
    have hcomp := (joinNeutral_le_joinRootedNeg_iff A B E L F K).mp hjoin.le
    constructor
    · apply covBy_of_eq_or_eq
      · exact lt_of_le_of_ne hcomp.1 (fun h ↦ F.2.not_isNeutralOrEmpty (h.symm ▸ E.2))
      · intro X hEX hXF
        rcases F.2.lower_strata_local hXF with hXneg | hXneutral
        · let Xneg : RootedNeg A := ⟨X, hXneg⟩
          have hlower : joinNeutral A B E L ≤ joinRootedNeg A B Xneg K :=
            (joinNeutral_le_joinRootedNeg_iff A B E L Xneg K).mpr ⟨hEX, hcomp.2⟩
          have hupper : joinRootedNeg A B Xneg K ≤ joinRootedNeg A B F K :=
            (joinRootedNeg_le_iff A B Xneg F K K).mpr ⟨hXF, le_rfl⟩
          rcases hjoin.eq_or_eq hlower hupper with heq | heq
          ·
            exact
              False.elim
                ((joinRootedNeg_isRootedNeg A B Xneg K).not_isNeutralOrEmpty
                  (heq ▸ joinNeutral_isNeutralOrEmpty A B E L))
          · right
            have hp : (Xneg, K) = (F, K) := joinRootedNeg_pair_injective A B heq
            simpa only [Xneg] using congrArg (fun pair : RootedNeg A × RootedNeg B ↦ pair.1.1) hp
        · let Xneutral : NeutralOrEmpty A := ⟨X, hXneutral⟩
          have hlower : joinNeutral A B E L ≤ joinNeutral A B Xneutral L :=
            (joinNeutral_le_iff A B E Xneutral L L).mpr ⟨hEX, le_rfl⟩
          have hupper : joinNeutral A B Xneutral L ≤ joinRootedNeg A B F K :=
            (joinNeutral_le_joinRootedNeg_iff A B Xneutral L F K).mpr ⟨hXF, hcomp.2⟩
          rcases hjoin.eq_or_eq hlower hupper with heq | heq
          · left
            have hp : (Xneutral, L) = (E, L) := joinNeutral_pair_injective A B heq
            simpa only [Xneutral] using
              congrArg (fun pair : NeutralOrEmpty A × NeutralOrEmpty B ↦ pair.1.1) hp
          ·
            exact
              False.elim
                ((joinRootedNeg_isRootedNeg A B F K).not_isNeutralOrEmpty
                  (heq.symm ▸ joinNeutral_isNeutralOrEmpty A B Xneutral L))
    · apply covBy_of_eq_or_eq
      · exact lt_of_le_of_ne hcomp.2 (fun h ↦ K.2.not_isNeutralOrEmpty (h.symm ▸ L.2))
      · intro X hLX hXK
        rcases K.2.lower_strata_local hXK with hXneg | hXneutral
        · let Xneg : RootedNeg B := ⟨X, hXneg⟩
          have hlower : joinNeutral A B E L ≤ joinRootedNeg A B F Xneg :=
            (joinNeutral_le_joinRootedNeg_iff A B E L F Xneg).mpr ⟨hcomp.1, hLX⟩
          have hupper : joinRootedNeg A B F Xneg ≤ joinRootedNeg A B F K :=
            (joinRootedNeg_le_iff A B F F Xneg K).mpr ⟨le_rfl, hXK⟩
          rcases hjoin.eq_or_eq hlower hupper with heq | heq
          ·
            exact
              False.elim
                ((joinRootedNeg_isRootedNeg A B F Xneg).not_isNeutralOrEmpty
                  (heq ▸ joinNeutral_isNeutralOrEmpty A B E L))
          · right
            have hp : (F, Xneg) = (F, K) := joinRootedNeg_pair_injective A B heq
            simpa only [Xneg] using congrArg (fun pair : RootedNeg A × RootedNeg B ↦ pair.2.1) hp
        · let Xneutral : NeutralOrEmpty B := ⟨X, hXneutral⟩
          have hlower : joinNeutral A B E L ≤ joinNeutral A B E Xneutral :=
            (joinNeutral_le_iff A B E E L Xneutral).mpr ⟨le_rfl, hLX⟩
          have hupper : joinNeutral A B E Xneutral ≤ joinRootedNeg A B F K :=
            (joinNeutral_le_joinRootedNeg_iff A B E Xneutral F K).mpr ⟨hcomp.1, hXK⟩
          rcases hjoin.eq_or_eq hlower hupper with heq | heq
          · left
            have hp : (E, Xneutral) = (E, L) := joinNeutral_pair_injective A B heq
            simpa only [Xneutral] using
              congrArg (fun pair : NeutralOrEmpty A × NeutralOrEmpty B ↦ pair.2.1) hp
          ·
            exact
              False.elim
                ((joinRootedNeg_isRootedNeg A B F K).not_isNeutralOrEmpty
                  (heq.symm ▸ joinNeutral_isNeutralOrEmpty A B E Xneutral))
  · rintro ⟨hEF, hLK⟩
    apply covBy_of_eq_or_eq
    ·
      exact
        lt_of_le_of_ne ((joinNeutral_le_joinRootedNeg_iff A B E L F K).mpr ⟨hEF.le, hLK.le⟩)
          (fun h ↦
            (joinRootedNeg_isRootedNeg A B F K).not_isNeutralOrEmpty
              (h.symm ▸ joinNeutral_isNeutralOrEmpty A B E L))
    · intro X hlower hupper
      rcases (joinRootedNeg_isRootedNeg A B F K).lower_strata_local hupper with hXneg | hXneutral
      · let Xneg : RootedNeg (graphJoin A B) := ⟨X, hXneg⟩
        let eR := joinRootedNegOrderIso A B
        let x : RootedNeg A × RootedNeg B := eR.symm Xneg
        have hXrep : joinRootedNeg A B x.1 x.2 = X :=
          congrArg Subtype.val (eR.apply_symm_apply Xneg)
        have hl :=
          (joinNeutral_le_joinRootedNeg_iff A B E L x.1 x.2).mp (by simpa only [hXrep] using hlower)
        have hu := (joinRootedNeg_le_iff A B x.1 F x.2 K).mp (by simpa only [hXrep] using hupper)
        have hxF := hEF.eq_or_eq hl.1 hu.1
        have hxK := hLK.eq_or_eq hl.2 hu.2
        rcases hxF with hxF | hxF
        · exact False.elim (x.1.2.not_isNeutralOrEmpty (hxF.symm ▸ E.2))
        · rcases hxK with hxK | hxK
          · exact False.elim (x.2.2.not_isNeutralOrEmpty (hxK.symm ▸ L.2))
          · right
            rw [← hXrep]
            congr 2
            · exact Subtype.ext hxF
            · exact Subtype.ext hxK
      · let Xneutral : NeutralOrEmpty (graphJoin A B) := ⟨X, hXneutral⟩
        let eN := joinNeutralOrderIso A B
        let x : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm Xneutral
        have hXrep : joinNeutral A B x.1 x.2 = X :=
          congrArg Subtype.val (eN.apply_symm_apply Xneutral)
        have hl := (joinNeutral_le_iff A B E x.1 L x.2).mp (by simpa only [hXrep] using hlower)
        have hu :=
          (joinNeutral_le_joinRootedNeg_iff A B x.1 x.2 F K).mp (by simpa only [hXrep] using hupper)
        have hxE := hEF.eq_or_eq hl.1 hu.1
        have hxL := hLK.eq_or_eq hl.2 hu.2
        rcases hxE with hxE | hxE
        · rcases hxL with hxL | hxL
          · left
            rw [← hXrep]
            congr 2
            · exact Subtype.ext hxE
            · exact Subtype.ext hxL
          · exact False.elim (K.2.not_isNeutralOrEmpty (hxL.symm ▸ x.2.2))
        · exact False.elim (F.2.not_isNeutralOrEmpty (hxE.symm ▸ x.1.2))


-- @@ L509-517 verbatim
/-- Central symmetry as an order isomorphism between the two rooted
strata. -/
noncomputable def rootedPosNegOrderIso
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    RootedPos G ≃o RootedNeg G where
  toEquiv := rootedPosNegEquiv G
  map_rel_iff' := by
    intro F K
    exact map_le_map_iff (hansenCentralFaceOrderIso G)


-- @@ L519-531 verbatim
/-- Central symmetry restricts to an involution of the neutral stratum. -/
noncomputable def neutralCentralOrderIso
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    NeutralOrEmpty G ≃o NeutralOrEmpty G where
  toFun F := ⟨hansenCentralFaceEquiv G F.1,
    centralFace_neutral_to_neutral F.2⟩
  invFun F := ⟨hansenCentralFaceEquiv G F.1,
    centralFace_neutral_to_neutral F.2⟩
  left_inv F := Subtype.ext (hansenCentralFaceEquiv_involutive G F.1)
  right_inv F := Subtype.ext (hansenCentralFaceEquiv_involutive G F.1)
  map_rel_iff' := by
    intro F K
    exact map_le_map_iff (hansenCentralFaceOrderIso G)


-- @@ L533-540 verbatim
/-- The greatest lower bound of two incidence faces, constructed as the
closure of the union of their containing-facet sets. -/
noncomputable def faceInf {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (F K : HansenCombinatorialFace G) :
    HansenCombinatorialFace G where
  carrier := incidenceClosure (hansenLabelIncidence G)
    ((F : Set (HansenFacetLabel G)) ∪ K)
  isClosed := incidenceClosure_idem _ _


-- @@ L542-546 verbatim
theorem faceInf_le_left {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (F K : HansenCombinatorialFace G) :
    faceInf F K ≤ F := by
  intro facet hfacet
  exact subset_incidenceClosure _ _ (Or.inl hfacet)


-- @@ L548-552 verbatim
theorem faceInf_le_right {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (F K : HansenCombinatorialFace G) :
    faceInf F K ≤ K := by
  intro facet hfacet
  exact subset_incidenceClosure _ _ (Or.inr hfacet)


-- @@ L554-568 verbatim
theorem le_faceInf {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {E F K : HansenCombinatorialFace G}
    (hEF : E ≤ F) (hEK : E ≤ K) : E ≤ faceInf F K := by
  change incidenceClosure (hansenLabelIncidence G)
      ((F : Set (HansenFacetLabel G)) ∪ K) ⊆ (E : Set _)
  have hunion :
      ((F : Set (HansenFacetLabel G)) ∪ (K : Set (HansenFacetLabel G))) ⊆
        (E : Set (HansenFacetLabel G)) := by
    exact Set.union_subset hEF hEK
  have hmono := incidenceClosure_mono (hansenLabelIncidence G) hunion
  have hclosed : incidenceClosure (hansenLabelIncidence G)
      (E : Set (HansenFacetLabel G)) = (E : Set (HansenFacetLabel G)) :=
    E.isClosed
  rw [hclosed] at hmono
  exact hmono


-- @@ L570-582 verbatim
theorem faceInf_containsVertex {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {F K : HansenCombinatorialFace G}
    {vertex : HansenVertexLabel G} (hF : F.ContainsVertex vertex)
    (hK : K.ContainsVertex vertex) :
    (faceInf F K).ContainsVertex vertex := by
  change vertex ∈ incidenceModels (hansenLabelIncidence G)
    (incidenceClosure (hansenLabelIncidence G)
      ((F : Set (HansenFacetLabel G)) ∪ K))
  rw [incidenceModels_incidenceClosure_eq]
  intro facet hfacet
  rcases hfacet with hfacet | hfacet
  · exact hF facet hfacet
  · exact hK facet hfacet


-- @@ L584-592 verbatim
/-- A neutral face is never a coatom: its canonical positive-rooted
extension lies strictly between it and the whole Hansen polytope. -/
theorem neutral_not_covBy_top {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (E : NeutralOrEmpty G) : ¬E.1 ⋖ top G := by
  intro hEtop
  have hupper : (positiveRootExtension E).1 ≤ top G := le_top
  rcases hEtop.eq_or_eq (le_positiveRootExtension E) hupper with heq | heq
  · exact (lt_positiveRootExtension E).ne heq.symm
  · exact (positiveRootExtension E).2.ne_top heq


-- @@ L594-611 expanded
/-- Same-stratum positive covers in a join are exactly product covers. -/
theorem joinRootedPos_covBy_iff_product {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) (F₁ F₂ : RootedPos A)
    (K₁ K₂ : RootedPos B) :
    joinRootedPos A B F₁ K₁ ⋖ joinRootedPos A B F₂ K₂ ↔ (F₁, K₁) ⋖ (F₂, K₂) :=
  by
  let X : RootedPos (graphJoin A B) :=
    ⟨joinRootedPos A B F₁ K₁, joinRootedPos_isRootedPos A B F₁ K₁⟩
  let Y : RootedPos (graphJoin A B) :=
    ⟨joinRootedPos A B F₂ K₂, joinRootedPos_isRootedPos A B F₂ K₂⟩
  calc
    X.1 ⋖ Y.1 ↔ X ⋖ Y := rootedPos_covBy_val_iff X Y
    _ ↔ (F₁, K₁) ⋖ (F₂, K₂) :=
      by
      change (joinRootedPosOrderIso A B) (F₁, K₁) ⋖ (joinRootedPosOrderIso A B) (F₂, K₂) ↔ _
      exact apply_covBy_apply_iff (joinRootedPosOrderIso A B)


-- @@ L613-630 expanded
/-- Same-stratum neutral covers in a join are exactly product covers. -/
theorem joinNeutral_covBy_iff_product {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) (E₁ E₂ : NeutralOrEmpty A)
    (L₁ L₂ : NeutralOrEmpty B) :
    joinNeutral A B E₁ L₁ ⋖ joinNeutral A B E₂ L₂ ↔ (E₁, L₁) ⋖ (E₂, L₂) :=
  by
  let X : NeutralOrEmpty (graphJoin A B) :=
    ⟨joinNeutral A B E₁ L₁, joinNeutral_isNeutralOrEmpty A B E₁ L₁⟩
  let Y : NeutralOrEmpty (graphJoin A B) :=
    ⟨joinNeutral A B E₂ L₂, joinNeutral_isNeutralOrEmpty A B E₂ L₂⟩
  calc
    X.1 ⋖ Y.1 ↔ X ⋖ Y := neutral_covBy_val_iff X Y
    _ ↔ (E₁, L₁) ⋖ (E₂, L₂) :=
      by
      change (joinNeutralOrderIso A B) (E₁, L₁) ⋖ (joinNeutralOrderIso A B) (E₂, L₂) ↔ _
      exact apply_covBy_apply_iff (joinNeutralOrderIso A B)


-- @@ L632-650 verbatim
theorem rootedNeg_covBy_val_iff
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (F H : RootedNeg G) : F.1 ⋖ H.1 ↔ F ⋖ H := by
  constructor
  · intro h
    exact ⟨h.1, fun X hFX hXH ↦ h.2 hFX hXH⟩
  · intro h
    apply covBy_of_eq_or_eq
    · exact h.1
    · intro X hFX hXH
      have hXtop : X ≠ top G := by
        intro htop
        apply H.2.ne_top_local
        rw [htop] at hXH
        exact top_unique hXH
      let X' : RootedNeg G := ⟨X, F.2.upper_of_ne_top_local hFX hXtop⟩
      rcases h.eq_or_eq (show F ≤ X' from hFX) (show X' ≤ H from hXH) with hXF | hXH'
      · exact Or.inl (congrArg Subtype.val hXF)
      · exact Or.inr (congrArg Subtype.val hXH')


-- @@ L652-668 expanded
theorem joinRootedNeg_covBy_iff_product {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) (F₁ F₂ : RootedNeg A)
    (K₁ K₂ : RootedNeg B) :
    joinRootedNeg A B F₁ K₁ ⋖ joinRootedNeg A B F₂ K₂ ↔ (F₁, K₁) ⋖ (F₂, K₂) :=
  by
  let X : RootedNeg (graphJoin A B) :=
    ⟨joinRootedNeg A B F₁ K₁, joinRootedNeg_isRootedNeg A B F₁ K₁⟩
  let Y : RootedNeg (graphJoin A B) :=
    ⟨joinRootedNeg A B F₂ K₂, joinRootedNeg_isRootedNeg A B F₂ K₂⟩
  calc
    X.1 ⋖ Y.1 ↔ X ⋖ Y := rootedNeg_covBy_val_iff X Y
    _ ↔ (F₁, K₁) ⋖ (F₂, K₂) :=
      by
      change (joinRootedNegOrderIso A B) (F₁, K₁) ⋖ (joinRootedNegOrderIso A B) (F₂, K₂) ↔ _
      exact apply_covBy_apply_iff (joinRootedNegOrderIso A B)


-- @@ L670-743 expanded
/-- A positive-rooted join face is a coatom exactly when both factor faces
are coatoms. -/
theorem joinRootedPos_covBy_top_iff {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) (F : RootedPos A)
    (K : RootedPos B) : joinRootedPos A B F K ⋖ top (graphJoin A B) ↔ F.1 ⋖ top A ∧ K.1 ⋖ top B :=
  by
  constructor
  · intro hjoin
    constructor
    · apply covBy_of_eq_or_eq
      · exact lt_of_le_of_ne le_top F.2.ne_top
      · intro X hFX hXtop
        by_cases hX : X = top A
        · exact Or.inr hX
        · let Xpos : RootedPos A := ⟨X, F.2.upper_of_ne_top hFX hX⟩
          have hlower : joinRootedPos A B F K ≤ joinRootedPos A B Xpos K :=
            (joinRootedPos_le_iff A B F Xpos K K).mpr ⟨hFX, le_rfl⟩
          have hupper : joinRootedPos A B Xpos K ≤ top (graphJoin A B) := le_top
          rcases hjoin.eq_or_eq hlower hupper with heq | heq
          · left
            have hpairs : (F, K) = (Xpos, K) := joinRootedPos_pair_injective A B heq.symm
            simpa only [Xpos] using
              congrArg (fun pair : RootedPos A × RootedPos B ↦ pair.1.1) hpairs.symm
          · exact False.elim ((joinRootedPos_isRootedPos A B Xpos K).ne_top heq)
    · apply covBy_of_eq_or_eq
      · exact lt_of_le_of_ne le_top K.2.ne_top
      · intro X hKX hXtop
        by_cases hX : X = top B
        · exact Or.inr hX
        · let Xpos : RootedPos B := ⟨X, K.2.upper_of_ne_top hKX hX⟩
          have hlower : joinRootedPos A B F K ≤ joinRootedPos A B F Xpos :=
            (joinRootedPos_le_iff A B F F K Xpos).mpr ⟨le_rfl, hKX⟩
          have hupper : joinRootedPos A B F Xpos ≤ top (graphJoin A B) := le_top
          rcases hjoin.eq_or_eq hlower hupper with heq | heq
          · left
            have hpairs : (F, K) = (F, Xpos) := joinRootedPos_pair_injective A B heq.symm
            simpa only [Xpos] using
              congrArg (fun pair : RootedPos A × RootedPos B ↦ pair.2.1) hpairs.symm
          · exact False.elim ((joinRootedPos_isRootedPos A B F Xpos).ne_top heq)
  · rintro ⟨hF, hK⟩
    apply covBy_of_eq_or_eq
    · exact lt_of_le_of_ne le_top (joinRootedPos_isRootedPos A B F K).ne_top
    · intro X hlower hupper
      by_cases hX : X = top (graphJoin A B)
      · exact Or.inr hX
      · let Xpos : RootedPos (graphJoin A B) :=
          ⟨X, (joinRootedPos_isRootedPos A B F K).upper_of_ne_top hlower hX⟩
        let eP := joinRootedPosOrderIso A B
        let x : RootedPos A × RootedPos B := eP.symm Xpos
        have hXrep : joinRootedPos A B x.1 x.2 = X := by
          exact congrArg Subtype.val (eP.apply_symm_apply Xpos)
        have hcomp : F.1 ≤ x.1.1 ∧ K.1 ≤ x.2.1 :=
          by
          apply (joinRootedPos_le_iff A B F x.1 K x.2).mp
          simpa only [hXrep] using hlower
        have hxF : x.1 = F :=
          by
          rcases hF.eq_or_eq hcomp.1 le_top with heq | heq
          · exact Subtype.ext heq
          · exact False.elim (x.1.2.ne_top heq)
        have hxK : x.2 = K :=
          by
          rcases hK.eq_or_eq hcomp.2 le_top with heq | heq
          · exact Subtype.ext heq
          · exact False.elim (x.2.2.ne_top heq)
        left
        rw [← hXrep, hxF, hxK]


-- @@ L745-816 expanded
/-- A negative-rooted join face is a coatom exactly when both factor faces
are coatoms. -/
theorem joinRootedNeg_covBy_top_iff {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) (F : RootedNeg A)
    (K : RootedNeg B) : joinRootedNeg A B F K ⋖ top (graphJoin A B) ↔ F.1 ⋖ top A ∧ K.1 ⋖ top B :=
  by
  constructor
  · intro hjoin
    constructor
    · apply covBy_of_eq_or_eq
      · exact lt_of_le_of_ne le_top F.2.ne_top_local
      · intro X hFX hXtop
        by_cases hX : X = top A
        · exact Or.inr hX
        · let Xneg : RootedNeg A := ⟨X, F.2.upper_of_ne_top_local hFX hX⟩
          have hlower : joinRootedNeg A B F K ≤ joinRootedNeg A B Xneg K :=
            (joinRootedNeg_le_iff A B F Xneg K K).mpr ⟨hFX, le_rfl⟩
          rcases hjoin.eq_or_eq hlower le_top with heq | heq
          · left
            have hpairs : (F, K) = (Xneg, K) := joinRootedNeg_pair_injective A B heq.symm
            simpa only [Xneg] using
              congrArg (fun pair : RootedNeg A × RootedNeg B ↦ pair.1.1) hpairs.symm
          · exact False.elim ((joinRootedNeg_isRootedNeg A B Xneg K).ne_top_local heq)
    · apply covBy_of_eq_or_eq
      · exact lt_of_le_of_ne le_top K.2.ne_top_local
      · intro X hKX hXtop
        by_cases hX : X = top B
        · exact Or.inr hX
        · let Xneg : RootedNeg B := ⟨X, K.2.upper_of_ne_top_local hKX hX⟩
          have hlower : joinRootedNeg A B F K ≤ joinRootedNeg A B F Xneg :=
            (joinRootedNeg_le_iff A B F F K Xneg).mpr ⟨le_rfl, hKX⟩
          rcases hjoin.eq_or_eq hlower le_top with heq | heq
          · left
            have hpairs : (F, K) = (F, Xneg) := joinRootedNeg_pair_injective A B heq.symm
            simpa only [Xneg] using
              congrArg (fun pair : RootedNeg A × RootedNeg B ↦ pair.2.1) hpairs.symm
          · exact False.elim ((joinRootedNeg_isRootedNeg A B F Xneg).ne_top_local heq)
  · rintro ⟨hF, hK⟩
    apply covBy_of_eq_or_eq
    · exact lt_of_le_of_ne le_top (joinRootedNeg_isRootedNeg A B F K).ne_top_local
    · intro X hlower hupper
      by_cases hX : X = top (graphJoin A B)
      · exact Or.inr hX
      · let Xneg : RootedNeg (graphJoin A B) :=
          ⟨X, (joinRootedNeg_isRootedNeg A B F K).upper_of_ne_top_local hlower hX⟩
        let eN := joinRootedNegOrderIso A B
        let x : RootedNeg A × RootedNeg B := eN.symm Xneg
        have hXrep : joinRootedNeg A B x.1 x.2 = X := by
          exact congrArg Subtype.val (eN.apply_symm_apply Xneg)
        have hcomp : F.1 ≤ x.1.1 ∧ K.1 ≤ x.2.1 :=
          by
          apply (joinRootedNeg_le_iff A B F x.1 K x.2).mp
          simpa only [hXrep] using hlower
        have hxF : x.1 = F :=
          by
          rcases hF.eq_or_eq hcomp.1 le_top with heq | heq
          · exact Subtype.ext heq
          · exact False.elim (x.1.2.ne_top_local heq)
        have hxK : x.2 = K :=
          by
          rcases hK.eq_or_eq hcomp.2 le_top with heq | heq
          · exact Subtype.ext heq
          · exact False.elim (x.2.2.ne_top_local heq)
        left
        rw [← hXrep, hxF, hxK]


-- @@ L818-840 verbatim
/-- If two distinct middle faces span the same rank-two interval and both
contain a vertex, then the lower endpoint already contains that vertex. -/
theorem lower_containsVertex_of_distinct_middles
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {E F K H : HansenCombinatorialFace G} {vertex : HansenVertexLabel G}
    (hEF : E ⋖ F) (hFH : F ⋖ H)
    (hEK : E ⋖ K) (hKH : K ⋖ H) (hne : K ≠ F)
    (hFvertex : F.ContainsVertex vertex)
    (hKvertex : K.ContainsVertex vertex) : E.ContainsVertex vertex := by
  have hEinf : E ≤ faceInf F K := le_faceInf hEF.le hEK.le
  have hinfF : faceInf F K ≤ F := faceInf_le_left F K
  have hinf_eq : faceInf F K = E := by
    rcases hEF.eq_or_eq hEinf hinfF with hinfE | hinfF'
    · exact hinfE
    · exfalso
      have hFK : F ≤ K := by
        rw [← hinfF']
        exact faceInf_le_right F K
      rcases hEK.eq_or_eq hEF.le hFK with hFE | hFK'
      · exact hEF.lt.ne hFE.symm
      · exact hne hFK'.symm
  rw [← hinf_eq]
  exact faceInf_containsVertex hFvertex hKvertex


-- @@ L842-879 verbatim
/-- Global thinness forces the positive portal square, in both directions:
the alternative to a positive-rooted middle is neutral, because two
distinct rooted middles would force their neutral lower endpoint to contain
the positive apex. -/
theorem pairedPositivePortalSquare_of_rankTwoDiamond
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : RankTwoDiamond (HansenCombinatorialFace G)) :
    PairedPositivePortalSquare G := by
  constructor
  · intro E F H hEF hFH
    obtain ⟨K, hK, hK_unique⟩ := hG hEF hFH
    have hKneutral : K.IsNeutralOrEmpty := by
      rcases H.2.lower_strata hK.2.1.le with hKpos | hKneutral
      · exfalso
        exact E.2.1 (lower_containsVertex_of_distinct_middles
          hEF hFH hK.1 hK.2.1 hK.2.2 F.2.1 hKpos.1)
      · exact hKneutral
    let Kneutral : NeutralOrEmpty G := ⟨K, hKneutral⟩
    refine ⟨Kneutral, ⟨hK.1, hK.2.1⟩, ?_⟩
    intro L hL
    apply Subtype.ext
    apply hK_unique L.1
    exact ⟨hL.1, hL.2, fun h ↦ F.2.not_isNeutralOrEmpty (h ▸ L.2)⟩
  · intro E F H hEF hFH
    obtain ⟨K, hK, hK_unique⟩ := hG hEF hFH
    have hKneutral : K.IsNeutralOrEmpty := by
      rcases H.2.lower_strata hK.2.1.le with hKpos | hKneutral
      · exfalso
        exact E.2.1 (lower_containsVertex_of_distinct_middles
          hEF hFH hK.1 hK.2.1 hK.2.2 F.2.1 hKpos.1)
      · exact hKneutral
    intro F' hF'
    by_cases heq : F'.1 = F.1
    · exact Subtype.ext heq
    · have hFK : F'.1 = K := hK_unique F'.1
        ⟨hF'.1, hF'.2, heq⟩
      exfalso
      exact F'.2.not_isNeutralOrEmpty (hFK ▸ hKneutral)


-- @@ L881-900 verbatim
/-- Global thinness restricts to the neutral lower ideal. -/
theorem rankTwoDiamond_neutral
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : RankTwoDiamond (HansenCombinatorialFace G)) :
    RankTwoDiamond (NeutralOrEmpty G) := by
  intro E F H hEF hFH
  obtain ⟨K, hK, hK_unique⟩ := hG
    ((neutral_covBy_val_iff E F).mpr hEF)
    ((neutral_covBy_val_iff F H).mpr hFH)
  let Kneutral : NeutralOrEmpty G := ⟨K, H.2.lower hK.2.1.le⟩
  refine ⟨Kneutral, ?_, ?_⟩
  · exact ⟨(neutral_covBy_val_iff E Kneutral).mp hK.1,
      (neutral_covBy_val_iff Kneutral H).mp hK.2.1,
      fun h ↦ hK.2.2 (congrArg Subtype.val h)⟩
  · intro L hL
    apply Subtype.ext
    apply hK_unique L.1
    exact ⟨(neutral_covBy_val_iff E L).mpr hL.1,
      (neutral_covBy_val_iff L H).mpr hL.2.1,
      fun h ↦ hL.2.2 (Subtype.ext h)⟩


-- @@ L902-923 verbatim
/-- Global thinness restricts to either rooted stratum. -/
theorem rankTwoDiamond_rootedPos
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : RankTwoDiamond (HansenCombinatorialFace G)) :
    RankTwoDiamond (RootedPos G) := by
  intro E F H hEF hFH
  obtain ⟨K, hK, hK_unique⟩ := hG
    ((rootedPos_covBy_val_iff E F).mpr hEF)
    ((rootedPos_covBy_val_iff F H).mpr hFH)
  have hKtop : K ≠ top G := fun h ↦
    (not_lt_of_ge le_top) (h ▸ hK.2.1.lt)
  let Kpos : RootedPos G := ⟨K, E.2.upper_of_ne_top hK.1.le hKtop⟩
  refine ⟨Kpos, ?_, ?_⟩
  · exact ⟨(rootedPos_covBy_val_iff E Kpos).mp hK.1,
      (rootedPos_covBy_val_iff Kpos H).mp hK.2.1,
      fun h ↦ hK.2.2 (congrArg Subtype.val h)⟩
  · intro L hL
    apply Subtype.ext
    apply hK_unique L.1
    exact ⟨(rootedPos_covBy_val_iff E L).mpr hL.1,
      (rootedPos_covBy_val_iff L H).mpr hL.2.1,
      fun h ↦ hL.2.2 (Subtype.ext h)⟩


-- @@ L925-945 verbatim
theorem rankTwoDiamond_rootedNeg
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : RankTwoDiamond (HansenCombinatorialFace G)) :
    RankTwoDiamond (RootedNeg G) := by
  intro E F H hEF hFH
  obtain ⟨K, hK, hK_unique⟩ := hG
    ((rootedNeg_covBy_val_iff E F).mpr hEF)
    ((rootedNeg_covBy_val_iff F H).mpr hFH)
  have hKtop : K ≠ top G := fun h ↦
    (not_lt_of_ge le_top) (h ▸ hK.2.1.lt)
  let Kneg : RootedNeg G := ⟨K, E.2.upper_of_ne_top_local hK.1.le hKtop⟩
  refine ⟨Kneg, ?_, ?_⟩
  · exact ⟨(rootedNeg_covBy_val_iff E Kneg).mp hK.1,
      (rootedNeg_covBy_val_iff Kneg H).mp hK.2.1,
      fun h ↦ hK.2.2 (congrArg Subtype.val h)⟩
  · intro L hL
    apply Subtype.ext
    apply hK_unique L.1
    exact ⟨(rootedNeg_covBy_val_iff E L).mpr hL.1,
      (rootedNeg_covBy_val_iff L H).mpr hL.2.1,
      fun h ↦ hL.2.2 (Subtype.ext h)⟩


-- @@ L947-956 expanded
theorem rankTwoDiamond_joinNeutral {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) :
    RankTwoDiamond (NeutralOrEmpty (graphJoin A B)) :=
  RankTwoDiamond.orderIso (joinNeutralOrderIso A B)
    (RankTwoDiamond.prod (rankTwoDiamond_neutral A hA) (rankTwoDiamond_neutral B hB))


-- @@ L958-967 expanded
theorem rankTwoDiamond_joinRootedPos {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) :
    RankTwoDiamond (RootedPos (graphJoin A B)) :=
  RankTwoDiamond.orderIso (joinRootedPosOrderIso A B)
    (RankTwoDiamond.prod (rankTwoDiamond_rootedPos A hA) (rankTwoDiamond_rootedPos B hB))


-- @@ L969-978 expanded
theorem rankTwoDiamond_joinRootedNeg {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) :
    RankTwoDiamond (RootedNeg (graphJoin A B)) :=
  RankTwoDiamond.orderIso (joinRootedNegOrderIso A B)
    (RankTwoDiamond.prod (rankTwoDiamond_rootedNeg A hA) (rankTwoDiamond_rootedNeg B hB))


-- @@ L980-1001 expanded
theorem join_neutral_sameStratum_diamond {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) (E F H : NeutralOrEmpty (graphJoin A B))
    (hEF : E.1 ⋖ F.1) (hFH : F.1 ⋖ H.1) :
    ∃! K : HansenCombinatorialFace (graphJoin A B), E.1 ⋖ K ∧ K ⋖ H.1 ∧ K ≠ F.1 :=
  by
  obtain ⟨K, hK, hKuniq⟩ :=
    rankTwoDiamond_joinNeutral A B hA hB ((neutral_covBy_val_iff E F).mp hEF)
      ((neutral_covBy_val_iff F H).mp hFH)
  refine
    ⟨K.1,
      ⟨(neutral_covBy_val_iff E K).mpr hK.1, (neutral_covBy_val_iff K H).mpr hK.2.1, fun h ↦
        hK.2.2 (Subtype.ext h)⟩,
      ?_⟩
  intro X hX
  let Xn : NeutralOrEmpty (graphJoin A B) := ⟨X, H.2.lower hX.2.1.le⟩
  exact
    congrArg Subtype.val
      (hKuniq Xn
        ⟨(neutral_covBy_val_iff E Xn).mp hX.1, (neutral_covBy_val_iff Xn H).mp hX.2.1, fun h ↦
          hX.2.2 (congrArg Subtype.val h)⟩)


-- @@ L1003-1027 expanded
theorem join_rootedPos_sameStratum_diamond {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) (E F H : RootedPos (graphJoin A B))
    (hEF : E.1 ⋖ F.1) (hFH : F.1 ⋖ H.1) :
    ∃! K : HansenCombinatorialFace (graphJoin A B), E.1 ⋖ K ∧ K ⋖ H.1 ∧ K ≠ F.1 :=
  by
  obtain ⟨K, hK, hKuniq⟩ :=
    rankTwoDiamond_joinRootedPos A B hA hB ((rootedPos_covBy_val_iff E F).mp hEF)
      ((rootedPos_covBy_val_iff F H).mp hFH)
  refine
    ⟨K.1,
      ⟨(rootedPos_covBy_val_iff E K).mpr hK.1, (rootedPos_covBy_val_iff K H).mpr hK.2.1, fun h ↦
        hK.2.2 (Subtype.ext h)⟩,
      ?_⟩
  intro X hX
  have hXtop : X ≠ top (graphJoin A B) := fun h ↦ (not_lt_of_ge le_top) (h ▸ hX.2.1.lt)
  let Xp : RootedPos (graphJoin A B) := ⟨X, E.2.upper_of_ne_top hX.1.le hXtop⟩
  exact
    congrArg Subtype.val
      (hKuniq Xp
        ⟨(rootedPos_covBy_val_iff E Xp).mp hX.1, (rootedPos_covBy_val_iff Xp H).mp hX.2.1, fun h ↦
          hX.2.2 (congrArg Subtype.val h)⟩)


-- @@ L1029-1053 expanded
theorem join_rootedNeg_sameStratum_diamond {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) (E F H : RootedNeg (graphJoin A B))
    (hEF : E.1 ⋖ F.1) (hFH : F.1 ⋖ H.1) :
    ∃! K : HansenCombinatorialFace (graphJoin A B), E.1 ⋖ K ∧ K ⋖ H.1 ∧ K ≠ F.1 :=
  by
  obtain ⟨K, hK, hKuniq⟩ :=
    rankTwoDiamond_joinRootedNeg A B hA hB ((rootedNeg_covBy_val_iff E F).mp hEF)
      ((rootedNeg_covBy_val_iff F H).mp hFH)
  refine
    ⟨K.1,
      ⟨(rootedNeg_covBy_val_iff E K).mpr hK.1, (rootedNeg_covBy_val_iff K H).mpr hK.2.1, fun h ↦
        hK.2.2 (Subtype.ext h)⟩,
      ?_⟩
  intro X hX
  have hXtop : X ≠ top (graphJoin A B) := fun h ↦ (not_lt_of_ge le_top) (h ▸ hX.2.1.lt)
  let Xn : RootedNeg (graphJoin A B) := ⟨X, E.2.upper_of_ne_top_local hX.1.le hXtop⟩
  exact
    congrArg Subtype.val
      (hKuniq Xn
        ⟨(rootedNeg_covBy_val_iff E Xn).mp hX.1, (rootedNeg_covBy_val_iff Xn H).mp hX.2.1, fun h ↦
          hX.2.2 (congrArg Subtype.val h)⟩)


-- @@ L1055-1075 verbatim
private theorem rootedNeg_otherMiddle_to_top_aux
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : RankTwoDiamond (HansenCombinatorialFace G))
    (E : NeutralOrEmpty G) (F : RootedPos G)
    (hEF : E.1 ⋖ F.1) (hFtop : F.1 ⋖ top G) :
    ∃! K : RootedNeg G, E.1 ⋖ K.1 ∧ K.1 ⋖ top G := by
  obtain ⟨K, hK, hK_unique⟩ := hG hEF hFtop
  have hKneg : K.IsRootedNeg := by
    rcases strata_cases G K with htop | hpos | hneg | hneutral
    · exact False.elim (hK.2.1.ne htop)
    · exfalso
      exact E.2.1 (lower_containsVertex_of_distinct_middles
        hEF hFtop hK.1 hK.2.1 hK.2.2 F.2.1 hpos.1)
    · exact hneg
    · exact False.elim (neutral_not_covBy_top ⟨K, hneutral⟩ hK.2.1)
  let Kneg : RootedNeg G := ⟨K, hKneg⟩
  refine ⟨Kneg, ⟨hK.1, hK.2.1⟩, ?_⟩
  intro L hL
  apply Subtype.ext
  apply hK_unique L.1
  exact ⟨hL.1, hL.2, fun h ↦ F.2.not_isRootedNeg (h ▸ L.2)⟩


-- @@ L1077-1177 expanded
/-- The central portal-to-top rank-two interval in a join has the negative
rooted product as its unique alternative middle. -/
theorem join_neutral_rootedPos_top_diamond {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) (E : NeutralOrEmpty (graphJoin A B))
    (F : RootedPos (graphJoin A B)) (hEF : E.1 ⋖ F.1) (hFtop : F.1 ⋖ top (graphJoin A B)) :
    ∃! K : HansenCombinatorialFace (graphJoin A B), E.1 ⋖ K ∧ K ⋖ top (graphJoin A B) ∧ K ≠ F.1 :=
  by
  let eN := joinNeutralOrderIso A B
  let eP := joinRootedPosOrderIso A B
  let e : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm E
  let f : RootedPos A × RootedPos B := eP.symm F
  have hErep : joinNeutral A B e.1 e.2 = E.1 := congrArg Subtype.val (eN.apply_symm_apply E)
  have hFrep : joinRootedPos A B f.1 f.2 = F.1 := congrArg Subtype.val (eP.apply_symm_apply F)
  have hportal : e.1.1 ⋖ f.1.1 ∧ e.2.1 ⋖ f.2.1 :=
    by
    apply (joinPortal_covBy_iff A B e.1 e.2 f.1 f.2).mp
    simpa only [hErep, hFrep] using hEF
  have hcoatom : f.1.1 ⋖ top A ∧ f.2.1 ⋖ top B :=
    by
    apply (joinRootedPos_covBy_top_iff A B f.1 f.2).mp
    simpa only [hFrep] using hFtop
  obtain ⟨nA, hnA, _⟩ := rootedNeg_otherMiddle_to_top_aux A hA e.1 f.1 hportal.1 hcoatom.1
  obtain ⟨nB, hnB, _⟩ := rootedNeg_otherMiddle_to_top_aux B hB e.2 f.2 hportal.2 hcoatom.2
  let N := joinRootedNeg A B nA nB
  refine ⟨N, ?_, ?_⟩
  · constructor
    · rw [← hErep]
      exact (joinNegativePortal_covBy_iff A B e.1 e.2 nA nB).mpr ⟨hnA.1, hnB.1⟩
    constructor
    · exact (joinRootedNeg_covBy_top_iff A B nA nB).mpr ⟨hnA.2, hnB.2⟩
    · intro h
      change joinRootedNeg A B nA nB = F.1 at h
      apply (joinRootedNeg_isRootedNeg A B nA nB).not_isRootedPos_local
      rw [h]
      exact F.2
  · intro X hX
    rcases strata_cases (graphJoin A B) X with htop | hpos | hneg | hneutral
    · exact False.elim (hX.2.1.ne htop)
    · exfalso
      exact
        hX.2.2
          (by
            let xP : RootedPos (graphJoin A B) := ⟨X, hpos⟩
            let x : RootedPos A × RootedPos B := eP.symm xP
            have hXrep : joinRootedPos A B x.1 x.2 = X :=
              congrArg Subtype.val (eP.apply_symm_apply xP)
            have hxportal :=
              (joinPortal_covBy_iff A B e.1 e.2 x.1 x.2).mp
                (by simpa only [hErep, hXrep] using hX.1)
            have hxcoatom :=
              (joinRootedPos_covBy_top_iff A B x.1 x.2).mp (by simpa only [hXrep] using hX.2.1)
            have hxA : x.1 = f.1 := by
              by_contra hne
              obtain ⟨O, hO, hOuniq⟩ := hA hportal.1 hcoatom.1
              have hxO := hOuniq x.1.1 ⟨hxportal.1, hxcoatom.1, fun h ↦ hne (Subtype.ext h)⟩
              have hnO := hOuniq nA.1 ⟨hnA.1, hnA.2, fun h ↦ f.1.2.not_isRootedNeg (h.symm ▸ nA.2)⟩
              apply x.1.2.not_isRootedNeg
              rw [hxO.trans hnO.symm]
              exact nA.2
            have hxB : x.2 = f.2 := by
              by_contra hne
              obtain ⟨O, hO, hOuniq⟩ := hB hportal.2 hcoatom.2
              have hxO := hOuniq x.2.1 ⟨hxportal.2, hxcoatom.2, fun h ↦ hne (Subtype.ext h)⟩
              have hnO := hOuniq nB.1 ⟨hnB.1, hnB.2, fun h ↦ f.2.2.not_isRootedNeg (h.symm ▸ nB.2)⟩
              apply x.2.2.not_isRootedNeg
              rw [hxO.trans hnO.symm]
              exact nB.2
            rw [← hXrep, ← hFrep, hxA, hxB])
    · let xN : RootedNeg (graphJoin A B) := ⟨X, hneg⟩
      let eR := joinRootedNegOrderIso A B
      let x : RootedNeg A × RootedNeg B := eR.symm xN
      have hXrep : joinRootedNeg A B x.1 x.2 = X := congrArg Subtype.val (eR.apply_symm_apply xN)
      have hxportal :=
        (joinNegativePortal_covBy_iff A B e.1 e.2 x.1 x.2).mp
          (by simpa only [hErep, hXrep] using hX.1)
      have hxcoatom :=
        (joinRootedNeg_covBy_top_iff A B x.1 x.2).mp (by simpa only [hXrep] using hX.2.1)
      have hxA : x.1 = nA :=
        by
        obtain ⟨O, hO, hOuniq⟩ := hA hportal.1 hcoatom.1
        have hxO :=
          hOuniq x.1.1 ⟨hxportal.1, hxcoatom.1, fun h ↦ f.1.2.not_isRootedNeg (h.symm ▸ x.1.2)⟩
        have hnO := hOuniq nA.1 ⟨hnA.1, hnA.2, fun h ↦ f.1.2.not_isRootedNeg (h.symm ▸ nA.2)⟩
        exact Subtype.ext (hxO.trans hnO.symm)
      have hxB : x.2 = nB :=
        by
        obtain ⟨O, hO, hOuniq⟩ := hB hportal.2 hcoatom.2
        have hxO :=
          hOuniq x.2.1 ⟨hxportal.2, hxcoatom.2, fun h ↦ f.2.2.not_isRootedNeg (h.symm ▸ x.2.2)⟩
        have hnO := hOuniq nB.1 ⟨hnB.1, hnB.2, fun h ↦ f.2.2.not_isRootedNeg (h.symm ▸ nB.2)⟩
        exact Subtype.ext (hxO.trans hnO.symm)
      rw [← hXrep, hxA, hxB]
    · exact False.elim (neutral_not_covBy_top ⟨X, hneutral⟩ hX.2.1)


-- @@ L1179-1201 expanded
/-- Portal followed by a positive-rooted cover is the paired local square. -/
theorem join_neutral_rootedPos_rootedPos_diamond {V : Type u} {W : Type v} [Fintype V]
    [DecidableEq V] [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) (E : NeutralOrEmpty (graphJoin A B))
    (F H : RootedPos (graphJoin A B)) (hEF : E.1 ⋖ F.1) (hFH : F.1 ⋖ H.1) :
    ∃! K : HansenCombinatorialFace (graphJoin A B), E.1 ⋖ K ∧ K ⋖ H.1 ∧ K ≠ F.1 :=
  by
  have hpair : PairedPositivePortalSquare (graphJoin A B) :=
    (pairedPositivePortalSquare_of_rankTwoDiamond A hA).join A B
      (pairedPositivePortalSquare_of_rankTwoDiamond B hB)
  obtain ⟨K, hK, hKuniq⟩ := hpair.1 E F H hEF hFH
  refine ⟨K.1, ⟨hK.1, hK.2, fun h ↦ F.2.not_isNeutralOrEmpty (h.symm ▸ K.2)⟩, ?_⟩
  intro X hX
  rcases H.2.lower_strata hX.2.1.le with hXpos | hXneutral
  · exfalso
    exact hX.2.2 (congrArg Subtype.val (hpair.2 E F H hEF hFH ⟨X, hXpos⟩ ⟨hX.1, hX.2.1⟩))
  · exact congrArg Subtype.val (hKuniq ⟨X, hXneutral⟩ ⟨hX.1, hX.2.1⟩)


-- @@ L1203-1321 expanded
/-- A positive-rooted product cover followed by the common top is thin. -/
theorem join_rootedPos_rootedPos_top_diamond {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) (E F : RootedPos (graphJoin A B))
    (hEF : E.1 ⋖ F.1) (hFtop : F.1 ⋖ top (graphJoin A B)) :
    ∃! K : HansenCombinatorialFace (graphJoin A B), E.1 ⋖ K ∧ K ⋖ top (graphJoin A B) ∧ K ≠ F.1 :=
  by
  let eP := joinRootedPosOrderIso A B
  let e : RootedPos A × RootedPos B := eP.symm E
  let f : RootedPos A × RootedPos B := eP.symm F
  have hErep : joinRootedPos A B e.1 e.2 = E.1 := congrArg Subtype.val (eP.apply_symm_apply E)
  have hFrep : joinRootedPos A B f.1 f.2 = F.1 := congrArg Subtype.val (eP.apply_symm_apply F)
  have hef : e ⋖ f := (apply_covBy_apply_iff eP.symm).mpr ((rootedPos_covBy_val_iff E F).mp hEF)
  have hcoatom := (joinRootedPos_covBy_top_iff A B f.1 f.2).mp (by simpa only [hFrep] using hFtop)
  rcases Prod.covBy_iff.mp hef with hefA | hefB
  · obtain ⟨O, hO, hOuniq⟩ := hA ((rootedPos_covBy_val_iff e.1 f.1).mpr hefA.1) hcoatom.1
    have hOtop : O ≠ top A := fun h ↦ (not_lt_of_ge le_top) (h ▸ hO.2.1.lt)
    let o : RootedPos A := ⟨O, e.1.2.upper_of_ne_top hO.1.le hOtop⟩
    let K := joinRootedPos A B o f.2
    refine ⟨K, ?_, ?_⟩
    · constructor
      · rw [← hErep]
        apply (joinRootedPos_covBy_iff_product A B e.1 o e.2 f.2).mpr
        exact Prod.covBy_iff.mpr (Or.inl ⟨(rootedPos_covBy_val_iff e.1 o).mp hO.1, hefA.2⟩)
      constructor
      · exact (joinRootedPos_covBy_top_iff A B o f.2).mpr ⟨hO.2.1, hcoatom.2⟩
      · intro h
        change joinRootedPos A B o f.2 = F.1 at h
        rw [← hFrep] at h
        have hp : (o, f.2) = f := joinRootedPos_pair_injective A B h
        exact hO.2.2 (congrArg (fun p : RootedPos A × RootedPos B ↦ p.1.1) hp)
    · intro X hX
      have hXtop : X ≠ top (graphJoin A B) := hX.2.1.ne
      let xP : RootedPos (graphJoin A B) := ⟨X, E.2.upper_of_ne_top hX.1.le hXtop⟩
      let x : RootedPos A × RootedPos B := eP.symm xP
      have hXrep : joinRootedPos A B x.1 x.2 = X := congrArg Subtype.val (eP.apply_symm_apply xP)
      have hex : e ⋖ x :=
        (joinRootedPos_covBy_iff_product A B e.1 x.1 e.2 x.2).mp
          (by simpa only [hErep, hXrep] using hX.1)
      have hxcoat :=
        (joinRootedPos_covBy_top_iff A B x.1 x.2).mp (by simpa only [hXrep] using hX.2.1)
      rcases Prod.covBy_iff.mp hex with hexA | hexB
      · have hxB : x.2 = f.2 := hexA.2.symm.trans hefA.2
        have hxne : x.1.1 ≠ f.1.1 := by
          intro h
          apply hX.2.2
          rw [← hXrep, ← hFrep]
          exact
            congrArg (fun p : RootedPos A × RootedPos B ↦ joinRootedPos A B p.1 p.2)
              (Prod.ext (Subtype.ext h) hxB)
        have hxO := hOuniq x.1.1 ⟨(rootedPos_covBy_val_iff e.1 x.1).mpr hexA.1, hxcoat.1, hxne⟩
        rw [← hXrep]
        exact
          congrArg (fun p : RootedPos A × RootedPos B ↦ joinRootedPos A B p.1 p.2)
            (show x = (o, f.2) from Prod.ext (Subtype.ext hxO) hxB)
      · have hbad : e.1.1 ⋖ top A := hexB.2 ▸ hxcoat.1
        exfalso
        rcases hbad.eq_or_eq hefA.1.le hcoatom.1.le with h | h
        · exact hefA.1.ne (Subtype.ext h.symm)
        · exact hcoatom.1.ne h
  · obtain ⟨O, hO, hOuniq⟩ := hB ((rootedPos_covBy_val_iff e.2 f.2).mpr hefB.1) hcoatom.2
    have hOtop : O ≠ top B := fun h ↦ (not_lt_of_ge le_top) (h ▸ hO.2.1.lt)
    let o : RootedPos B := ⟨O, e.2.2.upper_of_ne_top hO.1.le hOtop⟩
    let K := joinRootedPos A B f.1 o
    refine ⟨K, ?_, ?_⟩
    · constructor
      · rw [← hErep]
        apply (joinRootedPos_covBy_iff_product A B e.1 f.1 e.2 o).mpr
        exact Prod.covBy_iff.mpr (Or.inr ⟨(rootedPos_covBy_val_iff e.2 o).mp hO.1, hefB.2⟩)
      constructor
      · exact (joinRootedPos_covBy_top_iff A B f.1 o).mpr ⟨hcoatom.1, hO.2.1⟩
      · intro h
        change joinRootedPos A B f.1 o = F.1 at h
        rw [← hFrep] at h
        have hp : (f.1, o) = f := joinRootedPos_pair_injective A B h
        exact hO.2.2 (congrArg (fun p : RootedPos A × RootedPos B ↦ p.2.1) hp)
    · intro X hX
      have hXtop : X ≠ top (graphJoin A B) := hX.2.1.ne
      let xP : RootedPos (graphJoin A B) := ⟨X, E.2.upper_of_ne_top hX.1.le hXtop⟩
      let x : RootedPos A × RootedPos B := eP.symm xP
      have hXrep : joinRootedPos A B x.1 x.2 = X := congrArg Subtype.val (eP.apply_symm_apply xP)
      have hex : e ⋖ x :=
        (joinRootedPos_covBy_iff_product A B e.1 x.1 e.2 x.2).mp
          (by simpa only [hErep, hXrep] using hX.1)
      have hxcoat :=
        (joinRootedPos_covBy_top_iff A B x.1 x.2).mp (by simpa only [hXrep] using hX.2.1)
      rcases Prod.covBy_iff.mp hex with hexA | hexB
      · have hbad : e.2.1 ⋖ top B := hexA.2 ▸ hxcoat.2
        exfalso
        rcases hbad.eq_or_eq hefB.1.le hcoatom.2.le with h | h
        · exact hefB.1.ne (Subtype.ext h.symm)
        · exact hcoatom.2.ne h
      · have hxA : x.1 = f.1 := hexB.2.symm.trans hefB.2
        have hxne : x.2.1 ≠ f.2.1 := by
          intro h
          apply hX.2.2
          rw [← hXrep, ← hFrep]
          exact
            congrArg (fun p : RootedPos A × RootedPos B ↦ joinRootedPos A B p.1 p.2)
              (Prod.ext hxA (Subtype.ext h))
        have hxO := hOuniq x.2.1 ⟨(rootedPos_covBy_val_iff e.2 x.2).mpr hexB.1, hxcoat.2, hxne⟩
        rw [← hXrep]
        exact
          congrArg (fun p : RootedPos A × RootedPos B ↦ joinRootedPos A B p.1 p.2)
            (show x = (f.1, o) from Prod.ext hxA (Subtype.ext hxO))


-- @@ L1323-1628 expanded
/-- A neutral product cover followed by a positive portal cover is thin. -/
theorem join_neutral_neutral_rootedPos_diamond {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) (E F : NeutralOrEmpty (graphJoin A B))
    (H : RootedPos (graphJoin A B)) (hEF : E.1 ⋖ F.1) (hFH : F.1 ⋖ H.1) :
    ∃! K : HansenCombinatorialFace (graphJoin A B), E.1 ⋖ K ∧ K ⋖ H.1 ∧ K ≠ F.1 :=
  by
  let eN := joinNeutralOrderIso A B
  let eP := joinRootedPosOrderIso A B
  let e : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm E
  let f : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm F
  let h : RootedPos A × RootedPos B := eP.symm H
  have hErep : joinNeutral A B e.1 e.2 = E.1 := congrArg Subtype.val (eN.apply_symm_apply E)
  have hFrep : joinNeutral A B f.1 f.2 = F.1 := congrArg Subtype.val (eN.apply_symm_apply F)
  have hHrep : joinRootedPos A B h.1 h.2 = H.1 := congrArg Subtype.val (eP.apply_symm_apply H)
  have hef : e ⋖ f := (apply_covBy_apply_iff eN.symm).mpr ((neutral_covBy_val_iff E F).mp hEF)
  have hportal : f.1.1 ⋖ h.1.1 ∧ f.2.1 ⋖ h.2.1 :=
    (joinPortal_covBy_iff A B f.1 f.2 h.1 h.2).mp (by simpa only [hFrep, hHrep] using hFH)
  rcases Prod.covBy_iff.mp hef with hefA | hefB
  · have hefAval : e.1.1 ⋖ f.1.1 := (neutral_covBy_val_iff e.1 f.1).mpr hefA.1
    have hnoA : ¬e.1.1 ⋖ h.1.1 := by
      intro hdirect
      rcases hdirect.eq_or_eq hefAval.le hportal.1.le with q | q
      · exact hefAval.ne q.symm
      · exact hportal.1.ne q
    obtain ⟨O, hO, hOuniq⟩ := hA hefAval hportal.1
    rcases h.1.2.lower_strata hO.2.1.le with hOpos | hOneutral
    · let o : RootedPos A := ⟨O, hOpos⟩
      let K := joinRootedPos A B o h.2
      refine ⟨K, ?_, ?_⟩
      · constructor
        · rw [← hErep]
          apply joinPortal_covBy_of_factors
          · exact hO.1
          · simpa only [← hefA.2] using hportal.2
        constructor
        · change joinRootedPos A B o h.2 ⋖ H.1
          rw [← hHrep]
          apply (joinRootedPos_covBy_iff_product A B o h.1 h.2 h.2).mpr
          exact Prod.covBy_iff.mpr (Or.inl ⟨(rootedPos_covBy_val_iff o h.1).mp hO.2.1, rfl⟩)
        · change joinRootedPos A B o h.2 ≠ F.1
          intro q
          exact (joinRootedPos_isRootedPos A B o h.2).not_isNeutralOrEmpty (q.symm ▸ F.2)
      · intro X hX
        rcases H.2.lower_strata hX.2.1.le with hXpos | hXneutral
        · let xP : RootedPos (graphJoin A B) := ⟨X, hXpos⟩
          let x : RootedPos A × RootedPos B := eP.symm xP
          have hXrep : joinRootedPos A B x.1 x.2 = X :=
            congrArg Subtype.val (eP.apply_symm_apply xP)
          have hxportal : e.1.1 ⋖ x.1.1 ∧ e.2.1 ⋖ x.2.1 :=
            (joinPortal_covBy_iff A B e.1 e.2 x.1 x.2).mp (by simpa only [hErep, hXrep] using hX.1)
          have hxh : x ⋖ h :=
            (joinRootedPos_covBy_iff_product A B x.1 h.1 x.2 h.2).mp
              (by simpa only [hXrep, hHrep] using hX.2.1)
          rcases Prod.covBy_iff.mp hxh with hxhA | hxhB
          · have hxne : x.1.1 ≠ f.1.1 := by
              intro q
              exact f.1.2.1 (q ▸ x.1.2.1)
            have hxO :=
              hOuniq x.1.1 ⟨hxportal.1, (rootedPos_covBy_val_iff x.1 h.1).mpr hxhA.1, hxne⟩
            rw [← hXrep]
            exact
              congrArg (fun p : RootedPos A × RootedPos B ↦ joinRootedPos A B p.1 p.2)
                (show x = (o, h.2) from Prod.ext (Subtype.ext hxO) hxhA.2)
          · exact False.elim (hnoA (hxhB.2 ▸ hxportal.1))
        · let xN : NeutralOrEmpty (graphJoin A B) := ⟨X, hXneutral⟩
          let x : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm xN
          have hXrep : joinNeutral A B x.1 x.2 = X := congrArg Subtype.val (eN.apply_symm_apply xN)
          have hex : e ⋖ x :=
            (joinNeutral_covBy_iff_product A B e.1 x.1 e.2 x.2).mp
              (by simpa only [hErep, hXrep] using hX.1)
          have hxportal : x.1.1 ⋖ h.1.1 ∧ x.2.1 ⋖ h.2.1 :=
            (joinPortal_covBy_iff A B x.1 x.2 h.1 h.2).mp
              (by simpa only [hXrep, hHrep] using hX.2.1)
          rcases Prod.covBy_iff.mp hex with hexA | hexB
          · by_cases q : x.1.1 = f.1.1
            · exfalso
              apply hX.2.2
              rw [← hXrep, ← hFrep]
              exact
                congrArg (fun p : NeutralOrEmpty A × NeutralOrEmpty B ↦ joinNeutral A B p.1 p.2)
                  (show x = f from Prod.ext (Subtype.ext q) (hexA.2.symm.trans hefA.2))
            · have hxO := hOuniq x.1.1 ⟨(neutral_covBy_val_iff e.1 x.1).mpr hexA.1, hxportal.1, q⟩
              exact False.elim (hOpos.not_isNeutralOrEmpty (hxO ▸ x.1.2))
          · exact False.elim (hnoA (by simpa only [← hexB.2] using hxportal.1))
    · let o : NeutralOrEmpty A := ⟨O, hOneutral⟩
      let K := joinNeutral A B o e.2
      refine ⟨K, ?_, ?_⟩
      · constructor
        · rw [← hErep]
          apply (joinNeutral_covBy_iff_product A B e.1 o e.2 e.2).mpr
          exact Prod.covBy_iff.mpr (Or.inl ⟨(neutral_covBy_val_iff e.1 o).mp hO.1, rfl⟩)
        constructor
        · change joinNeutral A B o e.2 ⋖ H.1
          rw [← hHrep]
          apply joinPortal_covBy_of_factors
          · exact hO.2.1
          · simpa only [← hefA.2] using hportal.2
        · intro q
          change joinNeutral A B o e.2 = F.1 at q
          rw [← hFrep] at q
          have qp : (o, e.2) = f := joinNeutral_pair_injective A B q
          exact hO.2.2 (congrArg (fun p : NeutralOrEmpty A × NeutralOrEmpty B ↦ p.1.1) qp)
      · intro X hX
        rcases H.2.lower_strata hX.2.1.le with hXpos | hXneutral
        · let xP : RootedPos (graphJoin A B) := ⟨X, hXpos⟩
          let x : RootedPos A × RootedPos B := eP.symm xP
          have hXrep : joinRootedPos A B x.1 x.2 = X :=
            congrArg Subtype.val (eP.apply_symm_apply xP)
          have hxportal : e.1.1 ⋖ x.1.1 ∧ e.2.1 ⋖ x.2.1 :=
            (joinPortal_covBy_iff A B e.1 e.2 x.1 x.2).mp (by simpa only [hErep, hXrep] using hX.1)
          have hxh : x ⋖ h :=
            (joinRootedPos_covBy_iff_product A B x.1 h.1 x.2 h.2).mp
              (by simpa only [hXrep, hHrep] using hX.2.1)
          rcases Prod.covBy_iff.mp hxh with hxhA | hxhB
          · have hxne : x.1.1 ≠ f.1.1 := by
              intro q
              exact f.1.2.1 (q ▸ x.1.2.1)
            have hxO :=
              hOuniq x.1.1 ⟨hxportal.1, (rootedPos_covBy_val_iff x.1 h.1).mpr hxhA.1, hxne⟩
            exact False.elim (x.1.2.not_isNeutralOrEmpty (hxO.symm ▸ hOneutral))
          · exact False.elim (hnoA (hxhB.2 ▸ hxportal.1))
        · let xN : NeutralOrEmpty (graphJoin A B) := ⟨X, hXneutral⟩
          let x : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm xN
          have hXrep : joinNeutral A B x.1 x.2 = X := congrArg Subtype.val (eN.apply_symm_apply xN)
          have hex : e ⋖ x :=
            (joinNeutral_covBy_iff_product A B e.1 x.1 e.2 x.2).mp
              (by simpa only [hErep, hXrep] using hX.1)
          have hxportal : x.1.1 ⋖ h.1.1 ∧ x.2.1 ⋖ h.2.1 :=
            (joinPortal_covBy_iff A B x.1 x.2 h.1 h.2).mp
              (by simpa only [hXrep, hHrep] using hX.2.1)
          rcases Prod.covBy_iff.mp hex with hexA | hexB
          · have hxne : x.1.1 ≠ f.1.1 := by
              intro q
              apply hX.2.2
              rw [← hXrep, ← hFrep]
              exact
                congrArg (fun p : NeutralOrEmpty A × NeutralOrEmpty B ↦ joinNeutral A B p.1 p.2)
                  (show x = f from Prod.ext (Subtype.ext q) (hexA.2.symm.trans hefA.2))
            have hxO := hOuniq x.1.1 ⟨(neutral_covBy_val_iff e.1 x.1).mpr hexA.1, hxportal.1, hxne⟩
            rw [← hXrep]
            exact
              congrArg (fun p : NeutralOrEmpty A × NeutralOrEmpty B ↦ joinNeutral A B p.1 p.2)
                (show x = (o, e.2) from Prod.ext (Subtype.ext hxO) hexA.2.symm)
          · exact False.elim (hnoA (by simpa only [← hexB.2] using hxportal.1))
  · have hefBval : e.2.1 ⋖ f.2.1 := (neutral_covBy_val_iff e.2 f.2).mpr hefB.1
    have hnoB : ¬e.2.1 ⋖ h.2.1 := by
      intro hdirect
      rcases hdirect.eq_or_eq hefBval.le hportal.2.le with q | q
      · exact hefBval.ne q.symm
      · exact hportal.2.ne q
    obtain ⟨O, hO, hOuniq⟩ := hB hefBval hportal.2
    rcases h.2.2.lower_strata hO.2.1.le with hOpos | hOneutral
    · let o : RootedPos B := ⟨O, hOpos⟩
      let K := joinRootedPos A B h.1 o
      refine ⟨K, ?_, ?_⟩
      · constructor
        · rw [← hErep]
          apply joinPortal_covBy_of_factors
          · simpa only [← hefB.2] using hportal.1
          · exact hO.1
        constructor
        · change joinRootedPos A B h.1 o ⋖ H.1
          rw [← hHrep]
          apply (joinRootedPos_covBy_iff_product A B h.1 h.1 o h.2).mpr
          exact Prod.covBy_iff.mpr (Or.inr ⟨(rootedPos_covBy_val_iff o h.2).mp hO.2.1, rfl⟩)
        · change joinRootedPos A B h.1 o ≠ F.1
          intro q
          exact (joinRootedPos_isRootedPos A B h.1 o).not_isNeutralOrEmpty (q.symm ▸ F.2)
      · intro X hX
        rcases H.2.lower_strata hX.2.1.le with hXpos | hXneutral
        · let xP : RootedPos (graphJoin A B) := ⟨X, hXpos⟩
          let x : RootedPos A × RootedPos B := eP.symm xP
          have hXrep : joinRootedPos A B x.1 x.2 = X :=
            congrArg Subtype.val (eP.apply_symm_apply xP)
          have hxportal : e.1.1 ⋖ x.1.1 ∧ e.2.1 ⋖ x.2.1 :=
            (joinPortal_covBy_iff A B e.1 e.2 x.1 x.2).mp (by simpa only [hErep, hXrep] using hX.1)
          have hxh : x ⋖ h :=
            (joinRootedPos_covBy_iff_product A B x.1 h.1 x.2 h.2).mp
              (by simpa only [hXrep, hHrep] using hX.2.1)
          rcases Prod.covBy_iff.mp hxh with hxhA | hxhB
          · exact False.elim (hnoB (hxhA.2 ▸ hxportal.2))
          · have hxne : x.2.1 ≠ f.2.1 := by
              intro q
              exact f.2.2.1 (q ▸ x.2.2.1)
            have hxO :=
              hOuniq x.2.1 ⟨hxportal.2, (rootedPos_covBy_val_iff x.2 h.2).mpr hxhB.1, hxne⟩
            rw [← hXrep]
            exact
              congrArg (fun p : RootedPos A × RootedPos B ↦ joinRootedPos A B p.1 p.2)
                (show x = (h.1, o) from Prod.ext hxhB.2 (Subtype.ext hxO))
        · let xN : NeutralOrEmpty (graphJoin A B) := ⟨X, hXneutral⟩
          let x : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm xN
          have hXrep : joinNeutral A B x.1 x.2 = X := congrArg Subtype.val (eN.apply_symm_apply xN)
          have hex : e ⋖ x :=
            (joinNeutral_covBy_iff_product A B e.1 x.1 e.2 x.2).mp
              (by simpa only [hErep, hXrep] using hX.1)
          have hxportal : x.1.1 ⋖ h.1.1 ∧ x.2.1 ⋖ h.2.1 :=
            (joinPortal_covBy_iff A B x.1 x.2 h.1 h.2).mp
              (by simpa only [hXrep, hHrep] using hX.2.1)
          rcases Prod.covBy_iff.mp hex with hexA | hexB
          · exact False.elim (hnoB (by simpa only [← hexA.2] using hxportal.2))
          · by_cases q : x.2.1 = f.2.1
            · exfalso
              apply hX.2.2
              rw [← hXrep, ← hFrep]
              exact
                congrArg (fun p : NeutralOrEmpty A × NeutralOrEmpty B ↦ joinNeutral A B p.1 p.2)
                  (show x = f from Prod.ext (hexB.2.symm.trans hefB.2) (Subtype.ext q))
            · have hxO := hOuniq x.2.1 ⟨(neutral_covBy_val_iff e.2 x.2).mpr hexB.1, hxportal.2, q⟩
              exact False.elim (hOpos.not_isNeutralOrEmpty (hxO ▸ x.2.2))
    · let o : NeutralOrEmpty B := ⟨O, hOneutral⟩
      let K := joinNeutral A B e.1 o
      refine ⟨K, ?_, ?_⟩
      · constructor
        · rw [← hErep]
          apply (joinNeutral_covBy_iff_product A B e.1 e.1 e.2 o).mpr
          exact Prod.covBy_iff.mpr (Or.inr ⟨(neutral_covBy_val_iff e.2 o).mp hO.1, rfl⟩)
        constructor
        · change joinNeutral A B e.1 o ⋖ H.1
          rw [← hHrep]
          apply joinPortal_covBy_of_factors
          · simpa only [← hefB.2] using hportal.1
          · exact hO.2.1
        · intro q
          change joinNeutral A B e.1 o = F.1 at q
          rw [← hFrep] at q
          have qp : (e.1, o) = f := joinNeutral_pair_injective A B q
          exact hO.2.2 (congrArg (fun p : NeutralOrEmpty A × NeutralOrEmpty B ↦ p.2.1) qp)
      · intro X hX
        rcases H.2.lower_strata hX.2.1.le with hXpos | hXneutral
        · let xP : RootedPos (graphJoin A B) := ⟨X, hXpos⟩
          let x : RootedPos A × RootedPos B := eP.symm xP
          have hXrep : joinRootedPos A B x.1 x.2 = X :=
            congrArg Subtype.val (eP.apply_symm_apply xP)
          have hxportal : e.1.1 ⋖ x.1.1 ∧ e.2.1 ⋖ x.2.1 :=
            (joinPortal_covBy_iff A B e.1 e.2 x.1 x.2).mp (by simpa only [hErep, hXrep] using hX.1)
          have hxh : x ⋖ h :=
            (joinRootedPos_covBy_iff_product A B x.1 h.1 x.2 h.2).mp
              (by simpa only [hXrep, hHrep] using hX.2.1)
          rcases Prod.covBy_iff.mp hxh with hxhA | hxhB
          · exact False.elim (hnoB (hxhA.2 ▸ hxportal.2))
          · have hxne : x.2.1 ≠ f.2.1 := by
              intro q
              exact f.2.2.1 (q ▸ x.2.2.1)
            have hxO :=
              hOuniq x.2.1 ⟨hxportal.2, (rootedPos_covBy_val_iff x.2 h.2).mpr hxhB.1, hxne⟩
            exact False.elim (x.2.2.not_isNeutralOrEmpty (hxO.symm ▸ hOneutral))
        · let xN : NeutralOrEmpty (graphJoin A B) := ⟨X, hXneutral⟩
          let x : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm xN
          have hXrep : joinNeutral A B x.1 x.2 = X := congrArg Subtype.val (eN.apply_symm_apply xN)
          have hex : e ⋖ x :=
            (joinNeutral_covBy_iff_product A B e.1 x.1 e.2 x.2).mp
              (by simpa only [hErep, hXrep] using hX.1)
          have hxportal : x.1.1 ⋖ h.1.1 ∧ x.2.1 ⋖ h.2.1 :=
            (joinPortal_covBy_iff A B x.1 x.2 h.1 h.2).mp
              (by simpa only [hXrep, hHrep] using hX.2.1)
          rcases Prod.covBy_iff.mp hex with hexA | hexB
          · exact False.elim (hnoB (by simpa only [← hexA.2] using hxportal.2))
          · have hxne : x.2.1 ≠ f.2.1 := by
              intro q
              apply hX.2.2
              rw [← hXrep, ← hFrep]
              exact
                congrArg (fun p : NeutralOrEmpty A × NeutralOrEmpty B ↦ joinNeutral A B p.1 p.2)
                  (show x = f from Prod.ext (hexB.2.symm.trans hefB.2) (Subtype.ext q))
            have hxO := hOuniq x.2.1 ⟨(neutral_covBy_val_iff e.2 x.2).mpr hexB.1, hxportal.2, hxne⟩
            rw [← hXrep]
            exact
              congrArg (fun p : NeutralOrEmpty A × NeutralOrEmpty B ↦ joinNeutral A B p.1 p.2)
                (show x = (e.1, o) from Prod.ext hexB.2.symm (Subtype.ext hxO))


-- @@ L1630-1652 verbatim
/-- In a thin Hansen face lattice, the other middle of a
neutral--positive-rooted--top interval is necessarily negative-rooted. -/
theorem rootedNeg_otherMiddle_to_top
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : RankTwoDiamond (HansenCombinatorialFace G))
    (E : NeutralOrEmpty G) (F : RootedPos G)
    (hEF : E.1 ⋖ F.1) (hFtop : F.1 ⋖ top G) :
    ∃! K : RootedNeg G, E.1 ⋖ K.1 ∧ K.1 ⋖ top G := by
  obtain ⟨K, hK, hK_unique⟩ := hG hEF hFtop
  have hKneg : K.IsRootedNeg := by
    rcases strata_cases G K with htop | hpos | hneg | hneutral
    · exact False.elim (hK.2.1.ne htop)
    · exfalso
      exact E.2.1 (lower_containsVertex_of_distinct_middles
        hEF hFtop hK.1 hK.2.1 hK.2.2 F.2.1 hpos.1)
    · exact hneg
    · exact False.elim (neutral_not_covBy_top ⟨K, hneutral⟩ hK.2.1)
  let Kneg : RootedNeg G := ⟨K, hKneg⟩
  refine ⟨Kneg, ⟨hK.1, hK.2.1⟩, ?_⟩
  intro L hL
  apply Subtype.ext
  apply hK_unique L.1
  exact ⟨hL.1, hL.2, fun h ↦ F.2.not_isRootedNeg (h ▸ L.2)⟩


-- @@ L1654-1675 verbatim
private theorem diamond_step_orderIso
    {P : Type*} {Q : Type*} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) {a b c : P}
    (h : ∃! x : Q, e a ⋖ x ∧ x ⋖ e c ∧ x ≠ e b) :
    ∃! x : P, a ⋖ x ∧ x ⋖ c ∧ x ≠ b := by
  obtain ⟨x, hx, huniq⟩ := h
  refine ⟨e.symm x, ?_, ?_⟩
  · constructor
    · apply (apply_covBy_apply_iff e).mp
      simpa using hx.1
    constructor
    · apply (apply_covBy_apply_iff e).mp
      simpa using hx.2.1
    · intro q
      apply hx.2.2
      simpa using congrArg e q
  · intro y hy
    apply e.injective
    simpa using huniq (e y) ⟨
      (apply_covBy_apply_iff e).mpr hy.1,
      (apply_covBy_apply_iff e).mpr hy.2.1,
      fun q ↦ hy.2.2 (e.injective q)⟩


-- @@ L1677-1705 expanded
private theorem rankTwoDiamond_join_middle_rootedPos {V : Type u} {W : Type v} [Fintype V]
    [DecidableEq V] [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) (E : HansenCombinatorialFace (graphJoin A B))
    (F : RootedPos (graphJoin A B)) (H : HansenCombinatorialFace (graphJoin A B)) (hEF : E ⋖ F.1)
    (hFH : F.1 ⋖ H) : ∃! K : HansenCombinatorialFace (graphJoin A B), E ⋖ K ∧ K ⋖ H ∧ K ≠ F.1 :=
  by
  rcases F.2.lower_strata hEF.le with hEpos | hEneutral
  · let Ep : RootedPos (graphJoin A B) := ⟨E, hEpos⟩
    rcases strata_cases (graphJoin A B) H with htop | hHpos | hHneg | hHneutral
    · subst H
      exact join_rootedPos_rootedPos_top_diamond A B hA hB Ep F hEF hFH
    · exact join_rootedPos_sameStratum_diamond A B hA hB Ep F ⟨H, hHpos⟩ hEF hFH
    · exact False.elim (hHneg.2 (F.2.1.mono hFH.le))
    · exact False.elim (hHneutral.1 (F.2.1.mono hFH.le))
  · let En : NeutralOrEmpty (graphJoin A B) := ⟨E, hEneutral⟩
    rcases strata_cases (graphJoin A B) H with htop | hHpos | hHneg | hHneutral
    · subst H
      exact join_neutral_rootedPos_top_diamond A B hA hB En F hEF hFH
    · exact join_neutral_rootedPos_rootedPos_diamond A B hA hB En F ⟨H, hHpos⟩ hEF hFH
    · exact False.elim (hHneg.2 (F.2.1.mono hFH.le))
    · exact False.elim (hHneutral.1 (F.2.1.mono hFH.le))


-- @@ L1707-1748 expanded
/-- Rank-two thinness is closed under graph join. -/
theorem rankTwoDiamond_join {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RankTwoDiamond (HansenCombinatorialFace A))
    (hB : RankTwoDiamond (HansenCombinatorialFace B)) :
    RankTwoDiamond (HansenCombinatorialFace (graphJoin A B)) :=
  by
  intro E F H hEF hFH
  rcases strata_cases (graphJoin A B) F with htop | hFpos | hFneg | hFneutral
  · exfalso
    exact (not_lt_of_ge le_top) (htop ▸ hFH.lt)
  · exact rankTwoDiamond_join_middle_rootedPos A B hA hB E ⟨F, hFpos⟩ H hEF hFH
  · let c := hansenCentralFaceOrderIso (graphJoin A B)
    let Fc : RootedPos (graphJoin A B) := ⟨c F, centralFace_rootedNeg_to_rootedPos hFneg⟩
    apply diamond_step_orderIso c
    exact
      rankTwoDiamond_join_middle_rootedPos A B hA hB (c E) Fc (c H)
        ((apply_covBy_apply_iff c).mpr hEF) ((apply_covBy_apply_iff c).mpr hFH)
  · let En : NeutralOrEmpty (graphJoin A B) := ⟨E, hFneutral.lower hEF.le⟩
    let Fn : NeutralOrEmpty (graphJoin A B) := ⟨F, hFneutral⟩
    rcases strata_cases (graphJoin A B) H with hHtop | hHpos | hHneg | hHneutral
    · subst H
      exact False.elim (neutral_not_covBy_top Fn hFH)
    · exact join_neutral_neutral_rootedPos_diamond A B hA hB En Fn ⟨H, hHpos⟩ hEF hFH
    · let c := hansenCentralFaceOrderIso (graphJoin A B)
      let Ec : NeutralOrEmpty (graphJoin A B) := ⟨c E, centralFace_neutral_to_neutral En.2⟩
      let Fc : NeutralOrEmpty (graphJoin A B) := ⟨c F, centralFace_neutral_to_neutral Fn.2⟩
      let Hc : RootedPos (graphJoin A B) := ⟨c H, centralFace_rootedNeg_to_rootedPos hHneg⟩
      apply diamond_step_orderIso c
      exact
        join_neutral_neutral_rootedPos_diamond A B hA hB Ec Fc Hc
          ((apply_covBy_apply_iff c).mpr hEF) ((apply_covBy_apply_iff c).mpr hFH)
    · exact join_neutral_sameStratum_diamond A B hA hB En Fn ⟨H, hHneutral⟩ hEF hFH


-- @@ L1750-1789 verbatim
set_option maxRecDepth 100000 in
/-- Thinness of the explicitly enumerated one-vertex Hansen square. -/
theorem rankTwoDiamond_singleton :
    RankTwoDiamond.{0}
      (HansenCombinatorialFace (⊥ : SimpleGraph PUnit)) := by
  letI : DecidableEq (OrderDual SingletonFace.Closed) := inferInstance
  letI : DecidableLE (OrderDual SingletonFace.Closed) := by
    intro F K
    change Decidable
      ((show SingletonFace.Closed from K).1 ⊆
        (show SingletonFace.Closed from F).1)
    infer_instance
  letI : DecidableLT (OrderDual SingletonFace.Closed) := by
    intro F K
    change Decidable (F ≤ K ∧ ¬K ≤ F)
    infer_instance
  letI : DecidableRel
      (fun F K : OrderDual SingletonFace.Closed ↦ F ⋖ K) := by
    intro F K
    unfold CovBy
    letI : Decidable (∀ ⦃C : OrderDual SingletonFace.Closed⦄,
        F < C → ¬C < K) := Fintype.decidableForallFintype
    infer_instance
  apply RankTwoDiamond.orderIso singletonFaceOrderIso.symm
  unfold RankTwoDiamond
  let p := fun a b c : OrderDual SingletonFace.Closed ↦
    a ⋖ b → b ⋖ c → ∃! b', a ⋖ b' ∧ b' ⋖ c ∧ b' ≠ b
  letI decP (a b c : OrderDual SingletonFace.Closed) : Decidable (p a b c) := by
    dsimp only [p]
    unfold ExistsUnique
    letI decUnique (x : OrderDual SingletonFace.Closed) : Decidable
        (∀ y, (a ⋖ y ∧ y ⋖ c ∧ y ≠ b) → y = x) :=
      Fintype.decidableForallFintype
    infer_instance
  letI decC (a b : OrderDual SingletonFace.Closed) :
      Decidable (∀ c, p a b c) := Fintype.decidableForallFintype
  letI decB (a : OrderDual SingletonFace.Closed) :
      Decidable (∀ b c, p a b c) := Fintype.decidableForallFintype
  have h : ∀ a b c, p a b c := by decide
  exact h


-- @@ L1791-1796 verbatim
/-- Hansen polarity transports thinness across graph complementation. -/
theorem rankTwoDiamond_compl {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : RankTwoDiamond (HansenCombinatorialFace G)) :
    RankTwoDiamond (HansenCombinatorialFace Gᶜ) :=
  RankTwoDiamond.orderIso (hansenFaceComplOrderIso G)
    (RankTwoDiamond.orderDual hG)


-- @@ L1798-1805 verbatim
/-- Thinness of the complement also transports back to the original graph,
without rewriting through a double graph complement. -/
theorem rankTwoDiamond_of_compl {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hGc : RankTwoDiamond (HansenCombinatorialFace Gᶜ)) :
    RankTwoDiamond (HansenCombinatorialFace G) :=
  RankTwoDiamond.orderDual
    (RankTwoDiamond.orderIso (hansenFaceComplOrderIso G).symm hGc)


-- @@ L1807-1817 verbatim
/-- Relabelling vertices transports thinness. -/
theorem rankTwoDiamond_iso {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (hG : RankTwoDiamond (HansenCombinatorialFace G)) :
    RankTwoDiamond (HansenCombinatorialFace H) := by
  intro a b c hab hbc
  apply diamond_step_orderIso (hansenFaceOrderIso e).symm
  exact hG
    ((apply_covBy_apply_iff (hansenFaceOrderIso e).symm).mpr hab)
    ((apply_covBy_apply_iff (hansenFaceOrderIso e).symm).mpr hbc)


-- @@ L1819-1819 verbatim
end HansenCombinatorialFace


-- @@ L1821-1821 verbatim
namespace Cotree


-- @@ L1823-1853 expanded
/-- The Hansen face lattice of every cotree evaluation is rank-two thin. -/
theorem rankTwoDiamond_eval : ∀ T : Cotree, RankTwoDiamond (HansenCombinatorialFace T.eval) :=
  by
  intro T
  induction T with
  | leaf => exact HansenCombinatorialFace.rankTwoDiamond_singleton
  | compl A ih => exact HansenCombinatorialFace.rankTwoDiamond_compl A.eval ih
  | sum A B ihA ihB =>
    letI : Fintype A.Vert := instFintypeVert A
    letI : DecidableEq A.Vert := instDecidableEqVert A
    letI : Fintype B.Vert := instFintypeVert B
    letI : DecidableEq B.Vert := instDecidableEqVert B
    letI : Fintype (A.Vert ⊕ B.Vert) := instFintypeVert (.sum A B)
    letI : DecidableEq (A.Vert ⊕ B.Vert) := instDecidableEqVert (.sum A B)
    have hAc : RankTwoDiamond (HansenCombinatorialFace A.evalᶜ) :=
      HansenCombinatorialFace.rankTwoDiamond_compl A.eval ihA
    have hBc : RankTwoDiamond (HansenCombinatorialFace B.evalᶜ) :=
      HansenCombinatorialFace.rankTwoDiamond_compl B.eval ihB
    have hjoin : RankTwoDiamond (HansenCombinatorialFace (graphJoin A.evalᶜ B.evalᶜ)) :=
      HansenCombinatorialFace.rankTwoDiamond_join A.evalᶜ B.evalᶜ hAc hBc
    rw [← HansenCombinatorialFace.compl_sum_eq_join_compl] at hjoin
    rw [eval_sum]
    intro a b c hab hbc
    exact (HansenCombinatorialFace.rankTwoDiamond_of_compl (A.eval ⊕g B.eval) hjoin) hab hbc


-- @@ L1855-1855 verbatim
end Cotree


-- @@ L1857-1857 verbatim
namespace HansenCombinatorialFace


-- @@ L1859-1865 verbatim
/-- Every cograph has a rank-two thin Hansen face lattice. -/
theorem rankTwoDiamond_of_isCograph
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsCograph G) :
    RankTwoDiamond (HansenCombinatorialFace G) := by
  obtain ⟨T, ⟨e⟩⟩ := hG
  exact rankTwoDiamond_iso e.symm (Cotree.rankTwoDiamond_eval T)


-- @@ L1867-1867 verbatim
end HansenCombinatorialFace


-- @@ L1869-1869 verbatim
end HansenCograph
