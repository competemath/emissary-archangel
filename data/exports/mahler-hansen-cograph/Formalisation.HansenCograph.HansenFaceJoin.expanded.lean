/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenFaceStrata
import Mathlib.Order.Cover


-- @@ L9-15 verbatim
/-!
# Restricted-product faces for a Hansen graph join

This file constructs the forward direction of the exact restricted-product
classification.  Same-apex rooted face pairs and neutral-or-empty face pairs
give closed faces of the Hansen join.
-/


-- @@ L17-17 verbatim
open Set SimpleGraph


-- @@ L19-19 verbatim
universe u v


-- @@ L21-21 verbatim
namespace HansenCograph


-- @@ L23-23 verbatim
variable {V : Type u} {W : Type v}

-- @@ L24-24 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L26-43 expanded
/-- Closed sets for the abstract same-sign join incidence are exactly closed
sets for the concretely labelled Hansen join incidence. -/
noncomputable def hansenJoinFaceEquiv (A : SimpleGraph V) (B : SimpleGraph W) :
    IncidenceClosedSet
        (signedJoinIncidence (signA := fun f : HansenFacetLabel A ↦ f.1) (signB :=
          fun f : HansenFacetLabel B ↦ f.1) (hansenLabelIncidence A) (hansenLabelIncidence B)) ≃
      HansenCombinatorialFace (graphJoin A B) :=
  incidenceClosedTransportSurjEquiv
    (signedJoinIncidence (signA := fun f : HansenFacetLabel A ↦ f.1) (signB :=
      fun f : HansenFacetLabel B ↦ f.1) (hansenLabelIncidence A) (hansenLabelIncidence B))
    (hansenLabelIncidence (graphJoin A B)) (joinVertexLabelMap A B) (joinFacetLabelEquiv A B)
    (joinVertexLabelMap_surjective A B)
    (fun vertex facet ↦ hansenLabelIncidence_join_map A B vertex facet)


-- @@ L45-54 expanded
@[simp]
theorem hansenJoinFaceEquiv_apply_carrier (A : SimpleGraph V) (B : SimpleGraph W)
    (C :
      IncidenceClosedSet
        (signedJoinIncidence (signA := fun f : HansenFacetLabel A ↦ f.1) (signB :=
          fun f : HansenFacetLabel B ↦ f.1) (hansenLabelIncidence A) (hansenLabelIncidence B))) :
    ((hansenJoinFaceEquiv A B C : HansenCombinatorialFace (graphJoin A B)) :
        Set (HansenFacetLabel (graphJoin A B))) =
      joinFacetLabelEquiv A B '' (C : Set _) :=
  rfl


-- @@ L56-64 expanded
@[simp]
theorem hansenJoinFaceEquiv_symm_carrier (A : SimpleGraph V) (B : SimpleGraph W)
    (F : HansenCombinatorialFace (graphJoin A B)) :
    (((hansenJoinFaceEquiv A B).symm F :
          IncidenceClosedSet
            (signedJoinIncidence (signA := fun f : HansenFacetLabel A ↦ f.1) (signB :=
              fun f : HansenFacetLabel B ↦ f.1) (hansenLabelIncidence A)
              (hansenLabelIncidence B))) :
        Set _) =
      (joinFacetLabelEquiv A B).symm '' (F : Set _) :=
  rfl


-- @@ L66-66 verbatim
namespace HansenCombinatorialFace


-- @@ L68-73 verbatim
abbrev AbstractJoinFace (A : SimpleGraph V) (B : SimpleGraph W) :=
  IncidenceClosedSet
    (signedJoinIncidence
      (signA := fun f : HansenFacetLabel A ↦ f.1)
      (signB := fun f : HansenFacetLabel B ↦ f.1)
      (hansenLabelIncidence A) (hansenLabelIncidence B))


-- @@ L75-93 expanded
theorem hansenJoinFaceEquiv_contains_map (A : SimpleGraph V) (B : SimpleGraph W)
    (C : AbstractJoinFace A B) (vertex : HansenVertexLabel A ⊕ HansenVertexLabel B) :
    (hansenJoinFaceEquiv A B C).ContainsVertex (joinVertexLabelMap A B vertex) ↔
      vertex ∈
        incidenceModels
          (signedJoinIncidence (signA := fun f : HansenFacetLabel A ↦ f.1) (signB :=
            fun f : HansenFacetLabel B ↦ f.1) (hansenLabelIncidence A) (hansenLabelIncidence B))
          C :=
  by
  exact
    incidenceClosedTransportSurjEquiv_models
      (signedJoinIncidence (signA := fun f : HansenFacetLabel A ↦ f.1) (signB :=
        fun f : HansenFacetLabel B ↦ f.1) (hansenLabelIncidence A) (hansenLabelIncidence B))
      (hansenLabelIncidence (graphJoin A B)) (joinVertexLabelMap A B) (joinFacetLabelEquiv A B)
      (joinVertexLabelMap_surjective A B) (fun v f ↦ hansenLabelIncidence_join_map A B v f) C vertex


-- @@ L95-132 verbatim
theorem hansenJoinFaceEquiv_rootedPos_of_sign_neg
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (hne : (C : Set (SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1))).Nonempty)
    (hsign : ∀ facet : SignedJoinFacet
        (fun f : HansenFacetLabel A ↦ f.1)
        (fun f : HansenFacetLabel B ↦ f.1),
      facet ∈ (C : Set _) → facet.1.1.1 = HansenSign.neg) :
    (hansenJoinFaceEquiv A B C).IsRootedPos := by
  constructor
  · have hmodel : Sum.inl (emptyHansenVertex A HansenSign.pos) ∈
        incidenceModels
          (signedJoinIncidence
            (signA := fun f : HansenFacetLabel A ↦ f.1)
            (signB := fun f : HansenFacetLabel B ↦ f.1)
            (hansenLabelIncidence A) (hansenLabelIncidence B)) C := by
      intro facet hfacet
      change hansenLabelIncidence A
        (emptyHansenVertex A HansenSign.pos) facet.1.1
      rw [emptyHansenVertex_incident_iff_ne]
      rw [hsign facet hfacet]
      decide
    have h := (hansenJoinFaceEquiv_contains_map A B C
      (Sum.inl (emptyHansenVertex A HansenSign.pos))).mpr hmodel
    simpa [joinVertexLabelMap, joinVertexLabelLeft, emptyHansenVertex,
      sumFinset] using h
  · intro hcontains
    have h := (hansenJoinFaceEquiv_contains_map A B C
      (Sum.inl (emptyHansenVertex A HansenSign.neg))).mp
      (by simpa [joinVertexLabelMap, joinVertexLabelLeft, emptyHansenVertex,
          sumFinset] using hcontains)
    rcases hne with ⟨facet, hfacet⟩
    have hinc := h facet hfacet
    change hansenLabelIncidence A
      (emptyHansenVertex A HansenSign.neg) facet.1.1 at hinc
    rw [emptyHansenVertex_incident_iff_ne] at hinc
    exact hinc (hsign facet hfacet)


-- @@ L134-171 verbatim
theorem hansenJoinFaceEquiv_rootedNeg_of_sign_pos
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (hne : (C : Set (SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1))).Nonempty)
    (hsign : ∀ facet : SignedJoinFacet
        (fun f : HansenFacetLabel A ↦ f.1)
        (fun f : HansenFacetLabel B ↦ f.1),
      facet ∈ (C : Set _) → facet.1.1.1 = HansenSign.pos) :
    (hansenJoinFaceEquiv A B C).IsRootedNeg := by
  constructor
  · have hmodel : Sum.inl (emptyHansenVertex A HansenSign.neg) ∈
        incidenceModels
          (signedJoinIncidence
            (signA := fun f : HansenFacetLabel A ↦ f.1)
            (signB := fun f : HansenFacetLabel B ↦ f.1)
            (hansenLabelIncidence A) (hansenLabelIncidence B)) C := by
      intro facet hfacet
      change hansenLabelIncidence A
        (emptyHansenVertex A HansenSign.neg) facet.1.1
      rw [emptyHansenVertex_incident_iff_ne]
      rw [hsign facet hfacet]
      decide
    have h := (hansenJoinFaceEquiv_contains_map A B C
      (Sum.inl (emptyHansenVertex A HansenSign.neg))).mpr hmodel
    simpa [joinVertexLabelMap, joinVertexLabelLeft, emptyHansenVertex,
      sumFinset] using h
  · intro hcontains
    have h := (hansenJoinFaceEquiv_contains_map A B C
      (Sum.inl (emptyHansenVertex A HansenSign.pos))).mp
      (by simpa [joinVertexLabelMap, joinVertexLabelLeft, emptyHansenVertex,
          sumFinset] using hcontains)
    rcases hne with ⟨facet, hfacet⟩
    have hinc := h facet hfacet
    change hansenLabelIncidence A
      (emptyHansenVertex A HansenSign.pos) facet.1.1 at hinc
    rw [emptyHansenVertex_incident_iff_ne] at hinc
    exact hinc (hsign facet hfacet)


-- @@ L173-203 verbatim
theorem hansenJoinFaceEquiv_neutral_of_both_signs
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (negFacet posFacet : SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1))
    (hnegMem : negFacet ∈ (C : Set _))
    (hneg : negFacet.1.1.1 = HansenSign.neg)
    (hposMem : posFacet ∈ (C : Set _))
    (hpos : posFacet.1.1.1 = HansenSign.pos) :
    (hansenJoinFaceEquiv A B C).IsNeutralOrEmpty := by
  constructor
  · intro hcontains
    have h := (hansenJoinFaceEquiv_contains_map A B C
      (Sum.inl (emptyHansenVertex A HansenSign.pos))).mp
      (by simpa [joinVertexLabelMap, joinVertexLabelLeft, emptyHansenVertex,
          sumFinset] using hcontains)
    have hinc := h posFacet hposMem
    change hansenLabelIncidence A
      (emptyHansenVertex A HansenSign.pos) posFacet.1.1 at hinc
    rw [emptyHansenVertex_incident_iff_ne] at hinc
    exact hinc hpos
  · intro hcontains
    have h := (hansenJoinFaceEquiv_contains_map A B C
      (Sum.inl (emptyHansenVertex A HansenSign.neg))).mp
      (by simpa [joinVertexLabelMap, joinVertexLabelLeft, emptyHansenVertex,
          sumFinset] using hcontains)
    have hinc := h negFacet hnegMem
    change hansenLabelIncidence A
      (emptyHansenVertex A HansenSign.neg) negFacet.1.1 at hinc
    rw [emptyHansenVertex_incident_iff_ne] at hinc
    exact hinc hneg


-- @@ L205-208 verbatim
/-- Closed left factor extracted from an abstract join face. -/
def joinLeftFactor (A : SimpleGraph V) (B : SimpleGraph W)
    (C : AbstractJoinFace A B) : HansenCombinatorialFace A :=
  signedJoinLeftFactor (hansenLabelIncidence A) (hansenLabelIncidence B) C


-- @@ L210-213 verbatim
/-- Closed right factor extracted from an abstract join face. -/
def joinRightFactor (A : SimpleGraph V) (B : SimpleGraph W)
    (C : AbstractJoinFace A B) : HansenCombinatorialFace B :=
  signedJoinRightFactor (hansenLabelIncidence A) (hansenLabelIncidence B) C


-- @@ L215-231 verbatim
theorem joinLeftFactor_contains_iff
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (vertex : HansenVertexLabel A) :
    (joinLeftFactor A B C).ContainsVertex vertex ↔
      Sum.inl vertex ∈ incidenceModels
        (signedJoinIncidence
          (signA := fun f : HansenFacetLabel A ↦ f.1)
          (signB := fun f : HansenFacetLabel B ↦ f.1)
          (hansenLabelIncidence A) (hansenLabelIncidence B)) C := by
  rw [mem_join_models_inl_iff
    (signA := fun f : HansenFacetLabel A ↦ f.1)
    (signB := fun f : HansenFacetLabel B ↦ f.1)]
  exact Set.ext_iff.mp
    (incidenceModels_incidenceClosure_eq (hansenLabelIncidence A)
      (joinFacetProjLeft
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1) C)) vertex


-- @@ L233-249 verbatim
theorem joinRightFactor_contains_iff
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (vertex : HansenVertexLabel B) :
    (joinRightFactor A B C).ContainsVertex vertex ↔
      Sum.inr vertex ∈ incidenceModels
        (signedJoinIncidence
          (signA := fun f : HansenFacetLabel A ↦ f.1)
          (signB := fun f : HansenFacetLabel B ↦ f.1)
          (hansenLabelIncidence A) (hansenLabelIncidence B)) C := by
  rw [mem_join_models_inr_iff
    (signA := fun f : HansenFacetLabel A ↦ f.1)
    (signB := fun f : HansenFacetLabel B ↦ f.1)]
  exact Set.ext_iff.mp
    (incidenceModels_incidenceClosure_eq (hansenLabelIncidence B)
      (joinFacetProjRight
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1) C)) vertex


-- @@ L251-294 verbatim
/-- A nonempty abstract join face supported on negative facets has positive-
rooted projected factors. -/
theorem joinFactors_rootedPos_of_sign_neg
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (hne : (C : Set (SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1))).Nonempty)
    (hsign : ∀ facet : SignedJoinFacet
        (fun f : HansenFacetLabel A ↦ f.1)
        (fun f : HansenFacetLabel B ↦ f.1),
      facet ∈ (C : Set _) → facet.1.1.1 = HansenSign.neg) :
    (joinLeftFactor A B C).IsRootedPos ∧
      (joinRightFactor A B C).IsRootedPos := by
  rcases hne with ⟨witness, hwitness⟩
  constructor
  · constructor
    · rw [joinLeftFactor_contains_iff]
      intro facet hfacet
      change hansenLabelIncidence A (emptyHansenVertex A HansenSign.pos) facet.1.1
      rw [emptyHansenVertex_incident_iff_ne]
      have hs := hsign facet hfacet
      simpa [hs]
    · intro hcontains
      rw [joinLeftFactor_contains_iff] at hcontains
      have hinc := hcontains witness hwitness
      change hansenLabelIncidence A (emptyHansenVertex A HansenSign.neg) witness.1.1 at hinc
      rw [emptyHansenVertex_incident_iff_ne] at hinc
      exact hinc (hsign witness hwitness)
  · constructor
    · rw [joinRightFactor_contains_iff]
      intro facet hfacet
      change hansenLabelIncidence B (emptyHansenVertex B HansenSign.pos) facet.1.2
      rw [emptyHansenVertex_incident_iff_ne]
      have hs : facet.1.2.1 = HansenSign.neg := by
        exact facet.2.symm.trans (hsign facet hfacet)
      simpa [hs]
    · intro hcontains
      rw [joinRightFactor_contains_iff] at hcontains
      have hinc := hcontains witness hwitness
      change hansenLabelIncidence B (emptyHansenVertex B HansenSign.neg) witness.1.2 at hinc
      rw [emptyHansenVertex_incident_iff_ne] at hinc
      have hs : witness.1.2.1 = HansenSign.neg := by
        exact witness.2.symm.trans (hsign witness hwitness)
      exact hinc hs


-- @@ L296-339 verbatim
/-- A nonempty abstract join face supported on positive facets has negative-
rooted projected factors. -/
theorem joinFactors_rootedNeg_of_sign_pos
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (hne : (C : Set (SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1))).Nonempty)
    (hsign : ∀ facet : SignedJoinFacet
        (fun f : HansenFacetLabel A ↦ f.1)
        (fun f : HansenFacetLabel B ↦ f.1),
      facet ∈ (C : Set _) → facet.1.1.1 = HansenSign.pos) :
    (joinLeftFactor A B C).IsRootedNeg ∧
      (joinRightFactor A B C).IsRootedNeg := by
  rcases hne with ⟨witness, hwitness⟩
  constructor
  · constructor
    · rw [joinLeftFactor_contains_iff]
      intro facet hfacet
      change hansenLabelIncidence A (emptyHansenVertex A HansenSign.neg) facet.1.1
      rw [emptyHansenVertex_incident_iff_ne]
      have hs := hsign facet hfacet
      simpa [hs]
    · intro hcontains
      rw [joinLeftFactor_contains_iff] at hcontains
      have hinc := hcontains witness hwitness
      change hansenLabelIncidence A (emptyHansenVertex A HansenSign.pos) witness.1.1 at hinc
      rw [emptyHansenVertex_incident_iff_ne] at hinc
      exact hinc (hsign witness hwitness)
  · constructor
    · rw [joinRightFactor_contains_iff]
      intro facet hfacet
      change hansenLabelIncidence B (emptyHansenVertex B HansenSign.neg) facet.1.2
      rw [emptyHansenVertex_incident_iff_ne]
      have hs : facet.1.2.1 = HansenSign.pos := by
        exact facet.2.symm.trans (hsign facet hfacet)
      simpa [hs]
    · intro hcontains
      rw [joinRightFactor_contains_iff] at hcontains
      have hinc := hcontains witness hwitness
      change hansenLabelIncidence B (emptyHansenVertex B HansenSign.pos) witness.1.2 at hinc
      rw [emptyHansenVertex_incident_iff_ne] at hinc
      have hs : witness.1.2.1 = HansenSign.pos := by
        exact witness.2.symm.trans (hsign witness hwitness)
      exact hinc hs


-- @@ L341-388 verbatim
/-- If both signs occur in an abstract join face, both projected factors are
neutral-or-empty. -/
theorem joinFactors_neutral_of_both_signs
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (negFacet posFacet : SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1))
    (hnegMem : negFacet ∈ (C : Set _))
    (hneg : negFacet.1.1.1 = HansenSign.neg)
    (hposMem : posFacet ∈ (C : Set _))
    (hpos : posFacet.1.1.1 = HansenSign.pos) :
    (joinLeftFactor A B C).IsNeutralOrEmpty ∧
      (joinRightFactor A B C).IsNeutralOrEmpty := by
  constructor
  · constructor
    · intro hcontains
      rw [joinLeftFactor_contains_iff] at hcontains
      have hinc := hcontains posFacet hposMem
      change hansenLabelIncidence A (emptyHansenVertex A HansenSign.pos)
        posFacet.1.1 at hinc
      rw [emptyHansenVertex_incident_iff_ne] at hinc
      exact hinc hpos
    · intro hcontains
      rw [joinLeftFactor_contains_iff] at hcontains
      have hinc := hcontains negFacet hnegMem
      change hansenLabelIncidence A (emptyHansenVertex A HansenSign.neg)
        negFacet.1.1 at hinc
      rw [emptyHansenVertex_incident_iff_ne] at hinc
      exact hinc hneg
  · constructor
    · intro hcontains
      rw [joinRightFactor_contains_iff] at hcontains
      have hinc := hcontains posFacet hposMem
      change hansenLabelIncidence B (emptyHansenVertex B HansenSign.pos)
        posFacet.1.2 at hinc
      rw [emptyHansenVertex_incident_iff_ne] at hinc
      have hs : posFacet.1.2.1 = HansenSign.pos :=
        posFacet.2.symm.trans hpos
      exact hinc hs
    · intro hcontains
      rw [joinRightFactor_contains_iff] at hcontains
      have hinc := hcontains negFacet hnegMem
      change hansenLabelIncidence B (emptyHansenVertex B HansenSign.neg)
        negFacet.1.2 at hinc
      rw [emptyHansenVertex_incident_iff_ne] at hinc
      have hs : negFacet.1.2.1 = HansenSign.neg :=
        negFacet.2.symm.trans hneg
      exact hinc hs


-- @@ L390-404 verbatim
private theorem rootedPos_left_projection
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedPos A) (K : RootedPos B) :
    joinFacetProjLeft
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct
          (signA := fun f : HansenFacetLabel A ↦ f.1)
          (signB := fun f : HansenFacetLabel B ↦ f.1)
          (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (F.1 : Set _) := by
  apply joinFacetProjLeft_sameSignFacetProduct_eq
  intro facet hfacet
  rcases K.2.carrier_nonempty with ⟨other, hother⟩
  exact ⟨other, hother, by rw [F.2.facet_sign hfacet, K.2.facet_sign hother]⟩


-- @@ L406-420 verbatim
private theorem rootedPos_right_projection
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedPos A) (K : RootedPos B) :
    joinFacetProjRight
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct
          (signA := fun f : HansenFacetLabel A ↦ f.1)
          (signB := fun f : HansenFacetLabel B ↦ f.1)
          (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (K.1 : Set _) := by
  apply joinFacetProjRight_sameSignFacetProduct_eq
  intro facet hfacet
  rcases F.2.carrier_nonempty with ⟨other, hother⟩
  exact ⟨other, hother, by rw [F.2.facet_sign hother, K.2.facet_sign hfacet]⟩


-- @@ L422-436 verbatim
private theorem rootedNeg_left_projection
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedNeg A) (K : RootedNeg B) :
    joinFacetProjLeft
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct
          (signA := fun f : HansenFacetLabel A ↦ f.1)
          (signB := fun f : HansenFacetLabel B ↦ f.1)
          (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (F.1 : Set _) := by
  apply joinFacetProjLeft_sameSignFacetProduct_eq
  intro facet hfacet
  rcases K.2.carrier_nonempty with ⟨other, hother⟩
  exact ⟨other, hother, by rw [F.2.facet_sign hfacet, K.2.facet_sign hother]⟩


-- @@ L438-452 verbatim
private theorem rootedNeg_right_projection
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedNeg A) (K : RootedNeg B) :
    joinFacetProjRight
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct
          (signA := fun f : HansenFacetLabel A ↦ f.1)
          (signB := fun f : HansenFacetLabel B ↦ f.1)
          (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (K.1 : Set _) := by
  apply joinFacetProjRight_sameSignFacetProduct_eq
  intro facet hfacet
  rcases F.2.carrier_nonempty with ⟨other, hother⟩
  exact ⟨other, hother, by rw [F.2.facet_sign hother, K.2.facet_sign hfacet]⟩


-- @@ L454-468 verbatim
private theorem neutral_left_projection
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : NeutralOrEmpty A) (K : NeutralOrEmpty B) :
    joinFacetProjLeft
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct
          (signA := fun f : HansenFacetLabel A ↦ f.1)
          (signB := fun f : HansenFacetLabel B ↦ f.1)
          (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (F.1 : Set _) := by
  apply joinFacetProjLeft_sameSignFacetProduct_eq
  intro facet hfacet
  rcases K.2.exists_facet_sign facet.1 with ⟨other, hother, hs⟩
  exact ⟨other, hother, hs.symm⟩


-- @@ L470-484 verbatim
private theorem neutral_right_projection
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : NeutralOrEmpty A) (K : NeutralOrEmpty B) :
    joinFacetProjRight
        (signA := fun f : HansenFacetLabel A ↦ f.1)
        (signB := fun f : HansenFacetLabel B ↦ f.1)
        (sameSignFacetProduct
          (signA := fun f : HansenFacetLabel A ↦ f.1)
          (signB := fun f : HansenFacetLabel B ↦ f.1)
          (F.1 : Set (HansenFacetLabel A))
          (K.1 : Set (HansenFacetLabel B))) = (K.1 : Set _) := by
  apply joinFacetProjRight_sameSignFacetProduct_eq
  intro facet hfacet
  rcases F.2.exists_facet_sign facet.1 with ⟨other, hother, hs⟩
  exact ⟨other, hother, hs⟩


-- @@ L486-495 expanded
/-- A pair of positive-rooted factor faces produces a join face. -/
noncomputable def joinRootedPos (A : SimpleGraph V) (B : SimpleGraph W) (F : RootedPos A)
    (K : RootedPos B) : HansenCombinatorialFace (graphJoin A B) :=
  hansenJoinFaceEquiv A B
    (signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B) F.1 K.1
      (rootedPos_left_projection A B F K) (rootedPos_right_projection A B F K))


-- @@ L497-506 expanded
/-- A pair of negative-rooted factor faces produces a join face. -/
noncomputable def joinRootedNeg (A : SimpleGraph V) (B : SimpleGraph W) (F : RootedNeg A)
    (K : RootedNeg B) : HansenCombinatorialFace (graphJoin A B) :=
  hansenJoinFaceEquiv A B
    (signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B) F.1 K.1
      (rootedNeg_left_projection A B F K) (rootedNeg_right_projection A B F K))


-- @@ L508-517 expanded
/-- A pair of neutral-or-empty factor faces produces a join face. -/
noncomputable def joinNeutral (A : SimpleGraph V) (B : SimpleGraph W) (F : NeutralOrEmpty A)
    (K : NeutralOrEmpty B) : HansenCombinatorialFace (graphJoin A B) :=
  hansenJoinFaceEquiv A B
    (signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B) F.1 K.1
      (neutral_left_projection A B F K) (neutral_right_projection A B F K))


-- @@ L519-530 verbatim
theorem joinRootedPos_isRootedPos
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedPos A) (K : RootedPos B) :
    (joinRootedPos A B F K).IsRootedPos := by
  apply hansenJoinFaceEquiv_rootedPos_of_sign_neg
  · rcases F.2.carrier_nonempty with ⟨left, hleft⟩
    rcases K.2.carrier_nonempty with ⟨right, hright⟩
    have hsign : left.1 = right.1 := by
      rw [F.2.facet_sign hleft, K.2.facet_sign hright]
    exact ⟨⟨(left, right), hsign⟩, hleft, hright⟩
  · intro facet hfacet
    exact F.2.facet_sign hfacet.1


-- @@ L532-543 verbatim
theorem joinRootedNeg_isRootedNeg
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedNeg A) (K : RootedNeg B) :
    (joinRootedNeg A B F K).IsRootedNeg := by
  apply hansenJoinFaceEquiv_rootedNeg_of_sign_pos
  · rcases F.2.carrier_nonempty with ⟨left, hleft⟩
    rcases K.2.carrier_nonempty with ⟨right, hright⟩
    have hsign : left.1 = right.1 := by
      rw [F.2.facet_sign hleft, K.2.facet_sign hright]
    exact ⟨⟨(left, right), hsign⟩, hleft, hright⟩
  · intro facet hfacet
    exact F.2.facet_sign hfacet.1


-- @@ L545-565 verbatim
theorem joinNeutral_isNeutralOrEmpty
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : NeutralOrEmpty A) (K : NeutralOrEmpty B) :
    (joinNeutral A B F K).IsNeutralOrEmpty := by
  rcases F.2.exists_neg_facet with ⟨leftNeg, hleftNeg, hsleftNeg⟩
  rcases K.2.exists_neg_facet with ⟨rightNeg, hrightNeg, hsrightNeg⟩
  rcases F.2.exists_pos_facet with ⟨leftPos, hleftPos, hsleftPos⟩
  rcases K.2.exists_pos_facet with ⟨rightPos, hrightPos, hsrightPos⟩
  let negFacet : SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1) :=
    ⟨(leftNeg, rightNeg), hsleftNeg.trans hsrightNeg.symm⟩
  let posFacet : SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1) :=
    ⟨(leftPos, rightPos), hsleftPos.trans hsrightPos.symm⟩
  apply hansenJoinFaceEquiv_neutral_of_both_signs A B _ negFacet posFacet
  · exact ⟨hleftNeg, hrightNeg⟩
  · exact hsleftNeg
  · exact ⟨hleftPos, hrightPos⟩
  · exact hsleftPos


-- @@ L567-571 verbatim
/-- The four restricted-product codes for join faces. -/
abbrev JoinFaceCode (A : SimpleGraph V) (B : SimpleGraph W) :=
  PUnit.{1} ⊕ ((RootedPos A × RootedPos B) ⊕
    ((RootedNeg A × RootedNeg B) ⊕
      (NeutralOrEmpty A × NeutralOrEmpty B)))


-- @@ L573-580 expanded
/-- Interpret a restricted-product code as a concrete join face. -/
noncomputable def joinFaceCodeToFace (A : SimpleGraph V) (B : SimpleGraph W) :
    JoinFaceCode A B → HansenCombinatorialFace (graphJoin A B)
  | .inl _ => top (graphJoin A B)
  | .inr (.inl pair) => joinRootedPos A B pair.1 pair.2
  | .inr (.inr (.inl pair)) => joinRootedNeg A B pair.1 pair.2
  | .inr (.inr (.inr pair)) => joinNeutral A B pair.1 pair.2


-- @@ L582-592 verbatim
private theorem joinRootedPos_eq_of_factors
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (hleft : (joinLeftFactor A B C).IsRootedPos)
    (hright : (joinRightFactor A B C).IsRootedPos) :
    joinRootedPos A B ⟨joinLeftFactor A B C, hleft⟩
        ⟨joinRightFactor A B C, hright⟩ = hansenJoinFaceEquiv A B C := by
  change (hansenJoinFaceEquiv A B) _ = (hansenJoinFaceEquiv A B) C
  apply congrArg (hansenJoinFaceEquiv A B)
  apply IncidenceClosedSet.ext
  exact (signedJoinClosed_eq_product_factors
    (hansenLabelIncidence A) (hansenLabelIncidence B) C).symm


-- @@ L594-604 verbatim
private theorem joinRootedNeg_eq_of_factors
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (hleft : (joinLeftFactor A B C).IsRootedNeg)
    (hright : (joinRightFactor A B C).IsRootedNeg) :
    joinRootedNeg A B ⟨joinLeftFactor A B C, hleft⟩
        ⟨joinRightFactor A B C, hright⟩ = hansenJoinFaceEquiv A B C := by
  change (hansenJoinFaceEquiv A B) _ = (hansenJoinFaceEquiv A B) C
  apply congrArg (hansenJoinFaceEquiv A B)
  apply IncidenceClosedSet.ext
  exact (signedJoinClosed_eq_product_factors
    (hansenLabelIncidence A) (hansenLabelIncidence B) C).symm


-- @@ L606-616 verbatim
private theorem joinNeutral_eq_of_factors
    (A : SimpleGraph V) (B : SimpleGraph W) (C : AbstractJoinFace A B)
    (hleft : (joinLeftFactor A B C).IsNeutralOrEmpty)
    (hright : (joinRightFactor A B C).IsNeutralOrEmpty) :
    joinNeutral A B ⟨joinLeftFactor A B C, hleft⟩
        ⟨joinRightFactor A B C, hright⟩ = hansenJoinFaceEquiv A B C := by
  change (hansenJoinFaceEquiv A B) _ = (hansenJoinFaceEquiv A B) C
  apply congrArg (hansenJoinFaceEquiv A B)
  apply IncidenceClosedSet.ext
  exact (signedJoinClosed_eq_product_factors
    (hansenLabelIncidence A) (hansenLabelIncidence B) C).symm


-- @@ L618-702 expanded
/-- Every Hansen join face is represented by one of the four restricted-
product codes. -/
theorem joinFaceCodeToFace_surjective (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Surjective (joinFaceCodeToFace A B) := by
  classical
  intro F
  let C : AbstractJoinFace A B := (hansenJoinFaceEquiv A B).symm F
  have hFC : hansenJoinFaceEquiv A B C = F := by exact (hansenJoinFaceEquiv A B).apply_symm_apply F
  by_cases hempty :
    (C :
        Set
          (SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1))) =
      ∅
  · have htop : F = top (graphJoin A B) := by
      rw [← hFC]
      rw [← (hansenJoinFaceEquiv A B).apply_symm_apply (top (graphJoin A B))]
      apply congrArg (hansenJoinFaceEquiv A B)
      apply IncidenceClosedSet.ext
      change
        C.carrier =
          (joinFacetLabelEquiv A B).symm ''
            (top (graphJoin A B) : Set (HansenFacetLabel (graphJoin A B)))
      have hempty' : C.carrier = ∅ := hempty
      rw [hempty']
      have htopcarrier : (top (graphJoin A B) : Set (HansenFacetLabel (graphJoin A B))) = ∅ := rfl
      rw [htopcarrier, Set.image_empty]
    exact ⟨Sum.inl PUnit.unit, by simp [joinFaceCodeToFace, htop]⟩
  · have hne :
      (C :
          Set
            (SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1)
              (fun f : HansenFacetLabel B ↦ f.1))).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hempty
    by_cases hneg :
      ∀ facet :
        SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1),
        facet ∈ (C : Set _) → facet.1.1.1 = HansenSign.neg
    · have hroot := joinFactors_rootedPos_of_sign_neg A B C hne hneg
      refine
        ⟨Sum.inr (Sum.inl (⟨joinLeftFactor A B C, hroot.1⟩, ⟨joinRightFactor A B C, hroot.2⟩)), ?_⟩
      change joinRootedPos A B ⟨joinLeftFactor A B C, hroot.1⟩ ⟨joinRightFactor A B C, hroot.2⟩ = F
      rw [joinRootedPos_eq_of_factors A B C hroot.1 hroot.2, hFC]
    · by_cases hpos :
        ∀ facet :
          SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1),
          facet ∈ (C : Set _) → facet.1.1.1 = HansenSign.pos
      · have hroot := joinFactors_rootedNeg_of_sign_pos A B C hne hpos
        refine
          ⟨Sum.inr
              (Sum.inr
                (Sum.inl (⟨joinLeftFactor A B C, hroot.1⟩, ⟨joinRightFactor A B C, hroot.2⟩))),
            ?_⟩
        change
          joinRootedNeg A B ⟨joinLeftFactor A B C, hroot.1⟩ ⟨joinRightFactor A B C, hroot.2⟩ = F
        rw [joinRootedNeg_eq_of_factors A B C hroot.1 hroot.2, hFC]
      · have hexPos :
          ∃ facet :
            SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1),
            facet ∈ (C : Set _) ∧ facet.1.1.1 = HansenSign.pos :=
          by
          push Not at hneg
          rcases hneg with ⟨facet, hfacet, hsign⟩
          refine ⟨facet, hfacet, ?_⟩
          cases hs : facet.1.1.1 with
          | neg => exact False.elim (hsign hs)
          | pos => rfl
        have hexNeg :
          ∃ facet :
            SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1),
            facet ∈ (C : Set _) ∧ facet.1.1.1 = HansenSign.neg :=
          by
          push Not at hpos
          rcases hpos with ⟨facet, hfacet, hsign⟩
          refine ⟨facet, hfacet, ?_⟩
          cases hs : facet.1.1.1 with
          | neg => rfl
          | pos => exact False.elim (hsign hs)
        rcases hexNeg with ⟨negFacet, hnegMem, hnegSign⟩
        rcases hexPos with ⟨posFacet, hposMem, hposSign⟩
        have hneutral :=
          joinFactors_neutral_of_both_signs A B C negFacet posFacet hnegMem hnegSign hposMem
            hposSign
        refine
          ⟨Sum.inr
              (Sum.inr
                (Sum.inr
                  (⟨joinLeftFactor A B C, hneutral.1⟩, ⟨joinRightFactor A B C, hneutral.2⟩))),
            ?_⟩
        change
          joinNeutral A B ⟨joinLeftFactor A B C, hneutral.1⟩ ⟨joinRightFactor A B C, hneutral.2⟩ = F
        rw [joinNeutral_eq_of_factors A B C hneutral.1 hneutral.2, hFC]


-- @@ L704-730 verbatim
theorem joinRootedPos_pair_injective
    (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Injective (fun pair : RootedPos A × RootedPos B ↦
      joinRootedPos A B pair.1 pair.2) := by
  intro pair₁ pair₂ h
  have habstract :
      signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B)
          pair₁.1.1 pair₁.2.1
          (rootedPos_left_projection A B pair₁.1 pair₁.2)
          (rootedPos_right_projection A B pair₁.1 pair₁.2) =
        signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B)
          pair₂.1.1 pair₂.2.1
          (rootedPos_left_projection A B pair₂.1 pair₂.2)
          (rootedPos_right_projection A B pair₂.1 pair₂.2) := by
    apply (hansenJoinFaceEquiv A B).injective
    exact h
  have hcarrier := congrArg IncidenceClosedSet.carrier habstract
  dsimp only [signedJoinClosedProduct] at hcarrier
  apply Prod.ext
  · apply Subtype.ext
    apply IncidenceClosedSet.ext
    rw [← rootedPos_left_projection A B pair₁.1 pair₁.2,
      ← rootedPos_left_projection A B pair₂.1 pair₂.2, hcarrier]
  · apply Subtype.ext
    apply IncidenceClosedSet.ext
    rw [← rootedPos_right_projection A B pair₁.1 pair₁.2,
      ← rootedPos_right_projection A B pair₂.1 pair₂.2, hcarrier]


-- @@ L732-758 verbatim
theorem joinRootedNeg_pair_injective
    (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Injective (fun pair : RootedNeg A × RootedNeg B ↦
      joinRootedNeg A B pair.1 pair.2) := by
  intro pair₁ pair₂ h
  have habstract :
      signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B)
          pair₁.1.1 pair₁.2.1
          (rootedNeg_left_projection A B pair₁.1 pair₁.2)
          (rootedNeg_right_projection A B pair₁.1 pair₁.2) =
        signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B)
          pair₂.1.1 pair₂.2.1
          (rootedNeg_left_projection A B pair₂.1 pair₂.2)
          (rootedNeg_right_projection A B pair₂.1 pair₂.2) := by
    apply (hansenJoinFaceEquiv A B).injective
    exact h
  have hcarrier := congrArg IncidenceClosedSet.carrier habstract
  dsimp only [signedJoinClosedProduct] at hcarrier
  apply Prod.ext
  · apply Subtype.ext
    apply IncidenceClosedSet.ext
    rw [← rootedNeg_left_projection A B pair₁.1 pair₁.2,
      ← rootedNeg_left_projection A B pair₂.1 pair₂.2, hcarrier]
  · apply Subtype.ext
    apply IncidenceClosedSet.ext
    rw [← rootedNeg_right_projection A B pair₁.1 pair₁.2,
      ← rootedNeg_right_projection A B pair₂.1 pair₂.2, hcarrier]


-- @@ L760-786 verbatim
theorem joinNeutral_pair_injective
    (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Injective (fun pair : NeutralOrEmpty A × NeutralOrEmpty B ↦
      joinNeutral A B pair.1 pair.2) := by
  intro pair₁ pair₂ h
  have habstract :
      signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B)
          pair₁.1.1 pair₁.2.1
          (neutral_left_projection A B pair₁.1 pair₁.2)
          (neutral_right_projection A B pair₁.1 pair₁.2) =
        signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B)
          pair₂.1.1 pair₂.2.1
          (neutral_left_projection A B pair₂.1 pair₂.2)
          (neutral_right_projection A B pair₂.1 pair₂.2) := by
    apply (hansenJoinFaceEquiv A B).injective
    exact h
  have hcarrier := congrArg IncidenceClosedSet.carrier habstract
  dsimp only [signedJoinClosedProduct] at hcarrier
  apply Prod.ext
  · apply Subtype.ext
    apply IncidenceClosedSet.ext
    rw [← neutral_left_projection A B pair₁.1 pair₁.2,
      ← neutral_left_projection A B pair₂.1 pair₂.2, hcarrier]
  · apply Subtype.ext
    apply IncidenceClosedSet.ext
    rw [← neutral_right_projection A B pair₁.1 pair₁.2,
      ← neutral_right_projection A B pair₂.1 pair₂.2, hcarrier]


-- @@ L788-823 expanded
private theorem joinRootedPos_ne_top (A : SimpleGraph V) (B : SimpleGraph W)
    (pair : RootedPos A × RootedPos B) : joinRootedPos A B pair.1 pair.2 ≠ top (graphJoin A B) :=
  by
  intro h
  rcases pair.1.2.carrier_nonempty with ⟨left, hleft⟩
  rcases pair.2.2.carrier_nonempty with ⟨right, hright⟩
  have hsign : left.1 = right.1 := by rw [pair.1.2.facet_sign hleft, pair.2.2.facet_sign hright]
  let facet :
    SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1) :=
    ⟨(left, right), hsign⟩
  have hmem :
    facet ∈
      (signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B) pair.1.1 pair.2.1
          (rootedPos_left_projection A B pair.1 pair.2)
          (rootedPos_right_projection A B pair.1 pair.2) :
        Set _) :=
    ⟨hleft, hright⟩
  have habstract := congrArg (hansenJoinFaceEquiv A B).symm h
  dsimp [joinRootedPos] at habstract
  rw [Equiv.symm_apply_apply] at habstract
  have hcarrier := congrArg IncidenceClosedSet.carrier habstract
  dsimp [signedJoinClosedProduct] at hcarrier
  have htopcarrier :
    ((hansenJoinFaceEquiv A B).symm (top (graphJoin A B)) : AbstractJoinFace A B).carrier =
      (∅ :
        Set
          (SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1)
            (fun f : HansenFacetLabel B ↦ f.1))) :=
    by
    change
      (joinFacetLabelEquiv A B).symm ''
          (top (graphJoin A B) : Set (HansenFacetLabel (graphJoin A B))) =
        ∅
    have ht : (top (graphJoin A B) : Set (HansenFacetLabel (graphJoin A B))) = ∅ := rfl
    rw [ht, Set.image_empty]
  have : facet ∈ (∅ : Set _) := by
    rw [← htopcarrier, ← hcarrier]
    exact hmem
  exact this.elim


-- @@ L825-860 expanded
private theorem joinRootedNeg_ne_top (A : SimpleGraph V) (B : SimpleGraph W)
    (pair : RootedNeg A × RootedNeg B) : joinRootedNeg A B pair.1 pair.2 ≠ top (graphJoin A B) :=
  by
  intro h
  rcases pair.1.2.carrier_nonempty with ⟨left, hleft⟩
  rcases pair.2.2.carrier_nonempty with ⟨right, hright⟩
  have hsign : left.1 = right.1 := by rw [pair.1.2.facet_sign hleft, pair.2.2.facet_sign hright]
  let facet :
    SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1) :=
    ⟨(left, right), hsign⟩
  have hmem :
    facet ∈
      (signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B) pair.1.1 pair.2.1
          (rootedNeg_left_projection A B pair.1 pair.2)
          (rootedNeg_right_projection A B pair.1 pair.2) :
        Set _) :=
    ⟨hleft, hright⟩
  have habstract := congrArg (hansenJoinFaceEquiv A B).symm h
  dsimp [joinRootedNeg] at habstract
  rw [Equiv.symm_apply_apply] at habstract
  have hcarrier := congrArg IncidenceClosedSet.carrier habstract
  dsimp [signedJoinClosedProduct] at hcarrier
  have htopcarrier :
    ((hansenJoinFaceEquiv A B).symm (top (graphJoin A B)) : AbstractJoinFace A B).carrier =
      (∅ :
        Set
          (SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1)
            (fun f : HansenFacetLabel B ↦ f.1))) :=
    by
    change
      (joinFacetLabelEquiv A B).symm ''
          (top (graphJoin A B) : Set (HansenFacetLabel (graphJoin A B))) =
        ∅
    have ht : (top (graphJoin A B) : Set (HansenFacetLabel (graphJoin A B))) = ∅ := rfl
    rw [ht, Set.image_empty]
  have : facet ∈ (∅ : Set _) := by
    rw [← htopcarrier, ← hcarrier]
    exact hmem
  exact this.elim


-- @@ L862-895 expanded
private theorem joinNeutral_ne_top (A : SimpleGraph V) (B : SimpleGraph W)
    (pair : NeutralOrEmpty A × NeutralOrEmpty B) :
    joinNeutral A B pair.1 pair.2 ≠ top (graphJoin A B) :=
  by
  intro h
  rcases pair.1.2.exists_neg_facet with ⟨left, hleft, hsleft⟩
  rcases pair.2.2.exists_neg_facet with ⟨right, hright, hsright⟩
  let facet :
    SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1) :=
    ⟨(left, right), hsleft.trans hsright.symm⟩
  have hmem :
    facet ∈
      (signedJoinClosedProduct (hansenLabelIncidence A) (hansenLabelIncidence B) pair.1.1 pair.2.1
          (neutral_left_projection A B pair.1 pair.2) (neutral_right_projection A B pair.1 pair.2) :
        Set _) :=
    ⟨hleft, hright⟩
  have habstract := congrArg (hansenJoinFaceEquiv A B).symm h
  dsimp [joinNeutral] at habstract
  rw [Equiv.symm_apply_apply] at habstract
  have hcarrier := congrArg IncidenceClosedSet.carrier habstract
  dsimp [signedJoinClosedProduct] at hcarrier
  have htopcarrier :
    ((hansenJoinFaceEquiv A B).symm (top (graphJoin A B)) : AbstractJoinFace A B).carrier =
      (∅ :
        Set
          (SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1)
            (fun f : HansenFacetLabel B ↦ f.1))) :=
    by
    change
      (joinFacetLabelEquiv A B).symm ''
          (top (graphJoin A B) : Set (HansenFacetLabel (graphJoin A B))) =
        ∅
    have ht : (top (graphJoin A B) : Set (HansenFacetLabel (graphJoin A B))) = ∅ := rfl
    rw [ht, Set.image_empty]
  have : facet ∈ (∅ : Set _) := by
    rw [← htopcarrier, ← hcarrier]
    exact hmem
  exact this.elim


-- @@ L897-921 verbatim
private theorem joinRootedPos_ne_joinRootedNeg
    (A : SimpleGraph V) (B : SimpleGraph W)
    (posPair : RootedPos A × RootedPos B)
    (negPair : RootedNeg A × RootedNeg B) :
    joinRootedPos A B posPair.1 posPair.2 ≠
      joinRootedNeg A B negPair.1 negPair.2 := by
  intro h
  have habstract := (hansenJoinFaceEquiv A B).injective h
  have hcarrier := congrArg IncidenceClosedSet.carrier habstract
  dsimp [signedJoinClosedProduct] at hcarrier
  rcases posPair.1.2.carrier_nonempty with ⟨left, hleft⟩
  rcases posPair.2.2.carrier_nonempty with ⟨right, hright⟩
  have hsign : left.1 = right.1 := by
    rw [posPair.1.2.facet_sign hleft, posPair.2.2.facet_sign hright]
  let facet : SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1) := ⟨(left, right), hsign⟩
  have hmemPos : facet ∈ sameSignFacetProduct
      (posPair.1.1 : Set _) (posPair.2.1 : Set _) := ⟨hleft, hright⟩
  have hmemNeg : facet ∈ sameSignFacetProduct
      (negPair.1.1 : Set _) (negPair.2.1 : Set _) := hcarrier ▸ hmemPos
  have hnegSign := negPair.1.2.facet_sign hmemNeg.1
  have hposSign := posPair.1.2.facet_sign hleft
  rw [hposSign] at hnegSign
  exact HansenSign.noConfusion hnegSign


-- @@ L923-944 verbatim
private theorem joinRootedPos_ne_joinNeutral
    (A : SimpleGraph V) (B : SimpleGraph W)
    (rootPair : RootedPos A × RootedPos B)
    (neutralPair : NeutralOrEmpty A × NeutralOrEmpty B) :
    joinRootedPos A B rootPair.1 rootPair.2 ≠
      joinNeutral A B neutralPair.1 neutralPair.2 := by
  intro h
  have habstract := (hansenJoinFaceEquiv A B).injective h
  have hcarrier := congrArg IncidenceClosedSet.carrier habstract
  dsimp [signedJoinClosedProduct] at hcarrier
  rcases neutralPair.1.2.exists_pos_facet with ⟨left, hleft, hsleft⟩
  rcases neutralPair.2.2.exists_pos_facet with ⟨right, hright, hsright⟩
  let facet : SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1) := ⟨(left, right), hsleft.trans hsright.symm⟩
  have hmemNeutral : facet ∈ sameSignFacetProduct
      (neutralPair.1.1 : Set _) (neutralPair.2.1 : Set _) := ⟨hleft, hright⟩
  have hmemRoot : facet ∈ sameSignFacetProduct
      (rootPair.1.1 : Set _) (rootPair.2.1 : Set _) := hcarrier.symm ▸ hmemNeutral
  have hrootSign := rootPair.1.2.facet_sign hmemRoot.1
  rw [hsleft] at hrootSign
  exact HansenSign.noConfusion hrootSign


-- @@ L946-967 verbatim
private theorem joinRootedNeg_ne_joinNeutral
    (A : SimpleGraph V) (B : SimpleGraph W)
    (rootPair : RootedNeg A × RootedNeg B)
    (neutralPair : NeutralOrEmpty A × NeutralOrEmpty B) :
    joinRootedNeg A B rootPair.1 rootPair.2 ≠
      joinNeutral A B neutralPair.1 neutralPair.2 := by
  intro h
  have habstract := (hansenJoinFaceEquiv A B).injective h
  have hcarrier := congrArg IncidenceClosedSet.carrier habstract
  dsimp [signedJoinClosedProduct] at hcarrier
  rcases neutralPair.1.2.exists_neg_facet with ⟨left, hleft, hsleft⟩
  rcases neutralPair.2.2.exists_neg_facet with ⟨right, hright, hsright⟩
  let facet : SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1) := ⟨(left, right), hsleft.trans hsright.symm⟩
  have hmemNeutral : facet ∈ sameSignFacetProduct
      (neutralPair.1.1 : Set _) (neutralPair.2.1 : Set _) := ⟨hleft, hright⟩
  have hmemRoot : facet ∈ sameSignFacetProduct
      (rootPair.1.1 : Set _) (rootPair.2.1 : Set _) := hcarrier.symm ▸ hmemNeutral
  have hrootSign := rootPair.1.2.facet_sign hmemRoot.1
  rw [hsleft] at hrootSign
  exact HansenSign.noConfusion hrootSign


-- @@ L969-1006 verbatim
theorem joinFaceCodeToFace_injective
    (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Injective (joinFaceCodeToFace A B) := by
  intro x y h
  rcases x with x | x
  · rcases y with y | y
    · rfl
    · rcases y with y | y
      · exact False.elim (joinRootedPos_ne_top A B y h.symm)
      · rcases y with y | y
        · exact False.elim (joinRootedNeg_ne_top A B y h.symm)
        · exact False.elim (joinNeutral_ne_top A B y h.symm)
  · rcases x with x | x
    · rcases y with y | y
      · exact False.elim (joinRootedPos_ne_top A B x h)
      · rcases y with y | y
        · exact congrArg Sum.inr (congrArg Sum.inl
            (joinRootedPos_pair_injective A B h))
        · rcases y with y | y
          · exact False.elim (joinRootedPos_ne_joinRootedNeg A B x y h)
          · exact False.elim (joinRootedPos_ne_joinNeutral A B x y h)
    · rcases x with x | x
      · rcases y with y | y
        · exact False.elim (joinRootedNeg_ne_top A B x h)
        · rcases y with y | y
          · exact False.elim (joinRootedPos_ne_joinRootedNeg A B y x h.symm)
          · rcases y with y | y
            · exact congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inl
                (joinRootedNeg_pair_injective A B h)))
            · exact False.elim (joinRootedNeg_ne_joinNeutral A B x y h)
      · rcases y with y | y
        · exact False.elim (joinNeutral_ne_top A B x h)
        · rcases y with y | y
          · exact False.elim (joinRootedPos_ne_joinNeutral A B y x h.symm)
          · rcases y with y | y
            · exact False.elim (joinRootedNeg_ne_joinNeutral A B y x h.symm)
            · exact congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inr
                (joinNeutral_pair_injective A B h)))


-- @@ L1008-1013 expanded
/-- Exact restricted-product classification of all finite Hansen join faces. -/
noncomputable def joinFaceCodeEquiv (A : SimpleGraph V) (B : SimpleGraph W) :
    JoinFaceCode A B ≃ HansenCombinatorialFace (graphJoin A B) :=
  Equiv.ofBijective (joinFaceCodeToFace A B)
    ⟨joinFaceCodeToFace_injective A B, joinFaceCodeToFace_surjective A B⟩


-- @@ L1015-1021 expanded
/-- The positive-rooted stratum of a Hansen graph join is the product of the
two positive-rooted factor strata. -/
noncomputable def joinRootedPosMap (A : SimpleGraph V) (B : SimpleGraph W) :
    RootedPos A × RootedPos B → RootedPos (graphJoin A B) := fun pair ↦
  ⟨joinRootedPos A B pair.1 pair.2, joinRootedPos_isRootedPos A B pair.1 pair.2⟩


-- @@ L1023-1049 expanded
theorem joinRootedPosMap_bijective (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Bijective (joinRootedPosMap A B) :=
  by
  constructor
  · intro p q h
    apply joinRootedPos_pair_injective A B
    exact congrArg Subtype.val h
  · intro X
    let code := (joinFaceCodeEquiv A B).symm X.1
    have hrepr : joinFaceCodeToFace A B code = X.1 := (joinFaceCodeEquiv A B).apply_symm_apply X.1
    rcases code with unit | code
    · change top (graphJoin A B) = X.1 at hrepr
      exact False.elim (X.2.ne_top hrepr.symm)
    · rcases code with pair | code
      · exact ⟨pair, Subtype.ext hrepr⟩
      · rcases code with pair | pair
        · change joinRootedNeg A B pair.1 pair.2 = X.1 at hrepr
          exfalso
          apply X.2.not_isRootedNeg
          rw [← hrepr]
          exact joinRootedNeg_isRootedNeg A B pair.1 pair.2
        · change joinNeutral A B pair.1 pair.2 = X.1 at hrepr
          exfalso
          apply X.2.not_isNeutralOrEmpty
          rw [← hrepr]
          exact joinNeutral_isNeutralOrEmpty A B pair.1 pair.2


-- @@ L1051-1054 expanded
noncomputable def joinRootedPosEquiv (A : SimpleGraph V) (B : SimpleGraph W) :
    RootedPos A × RootedPos B ≃ RootedPos (graphJoin A B) :=
  Equiv.ofBijective (joinRootedPosMap A B) (joinRootedPosMap_bijective A B)


-- @@ L1056-1062 expanded
/-- The neutral-or-empty stratum of a Hansen graph join is the product of
the two neutral-or-empty factor strata. -/
noncomputable def joinNeutralMap (A : SimpleGraph V) (B : SimpleGraph W) :
    NeutralOrEmpty A × NeutralOrEmpty B → NeutralOrEmpty (graphJoin A B) := fun pair ↦
  ⟨joinNeutral A B pair.1 pair.2, joinNeutral_isNeutralOrEmpty A B pair.1 pair.2⟩


-- @@ L1064-1090 expanded
theorem joinNeutralMap_bijective (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Bijective (joinNeutralMap A B) :=
  by
  constructor
  · intro p q h
    apply joinNeutral_pair_injective A B
    exact congrArg Subtype.val h
  · intro X
    let code := (joinFaceCodeEquiv A B).symm X.1
    have hrepr : joinFaceCodeToFace A B code = X.1 := (joinFaceCodeEquiv A B).apply_symm_apply X.1
    rcases code with unit | code
    · change top (graphJoin A B) = X.1 at hrepr
      exact False.elim (X.2.ne_top hrepr.symm)
    · rcases code with pair | code
      · change joinRootedPos A B pair.1 pair.2 = X.1 at hrepr
        exfalso
        apply (joinRootedPos_isRootedPos A B pair.1 pair.2).not_isNeutralOrEmpty
        rw [hrepr]
        exact X.2
      · rcases code with pair | pair
        · change joinRootedNeg A B pair.1 pair.2 = X.1 at hrepr
          exfalso
          apply (joinRootedNeg_isRootedNeg A B pair.1 pair.2).not_isNeutralOrEmpty
          rw [hrepr]
          exact X.2
        · exact ⟨pair, Subtype.ext hrepr⟩


-- @@ L1092-1095 expanded
noncomputable def joinNeutralEquiv (A : SimpleGraph V) (B : SimpleGraph W) :
    NeutralOrEmpty A × NeutralOrEmpty B ≃ NeutralOrEmpty (graphJoin A B) :=
  Equiv.ofBijective (joinNeutralMap A B) (joinNeutralMap_bijective A B)


-- @@ L1097-1110 expanded
private theorem hansenJoinFaceEquiv_le_iff (A : SimpleGraph V) (B : SimpleGraph W)
    (C D : AbstractJoinFace A B) : hansenJoinFaceEquiv A B C ≤ hansenJoinFaceEquiv A B D ↔ C ≤ D :=
  by
  simpa only [hansenJoinFaceEquiv] using
    incidenceClosedTransportSurjEquiv_le_iff
      (signedJoinIncidence (signA := fun f : HansenFacetLabel A ↦ f.1) (signB :=
        fun f : HansenFacetLabel B ↦ f.1) (hansenLabelIncidence A) (hansenLabelIncidence B))
      (hansenLabelIncidence (graphJoin A B)) (joinVertexLabelMap A B) (joinFacetLabelEquiv A B)
      (joinVertexLabelMap_surjective A B)
      (fun vertex facet ↦ hansenLabelIncidence_join_map A B vertex facet) C D


-- @@ L1112-1137 verbatim
/-- Within the positive-rooted stratum, the Hansen join face order is the
componentwise product order. -/
theorem joinRootedPos_le_iff
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F₁ F₂ : RootedPos A) (K₁ K₂ : RootedPos B) :
    joinRootedPos A B F₁ K₁ ≤ joinRootedPos A B F₂ K₂ ↔
      F₁.1 ≤ F₂.1 ∧ K₁.1 ≤ K₂.1 := by
  change hansenJoinFaceEquiv A B _ ≤ hansenJoinFaceEquiv A B _ ↔ _
  rw [hansenJoinFaceEquiv_le_iff]
  change sameSignFacetProduct
      (F₂.1 : Set (HansenFacetLabel A)) (K₂.1 : Set (HansenFacetLabel B)) ⊆
      sameSignFacetProduct
        (F₁.1 : Set (HansenFacetLabel A)) (K₁.1 : Set (HansenFacetLabel B)) ↔
    (F₂.1 : Set (HansenFacetLabel A)) ⊆ (F₁.1 : Set (HansenFacetLabel A)) ∧
      (K₂.1 : Set (HansenFacetLabel B)) ⊆ (K₁.1 : Set (HansenFacetLabel B))
  constructor
  · intro h
    constructor
    · rw [← rootedPos_left_projection A B F₂ K₂,
          ← rootedPos_left_projection A B F₁ K₁]
      exact Set.image_mono h
    · rw [← rootedPos_right_projection A B F₂ K₂,
          ← rootedPos_right_projection A B F₁ K₁]
      exact Set.image_mono h
  · rintro ⟨hF, hK⟩ facet hfacet
    exact ⟨hF hfacet.1, hK hfacet.2⟩


-- @@ L1139-1164 verbatim
/-- Within the neutral-or-empty stratum, the Hansen join face order is the
componentwise product order. -/
theorem joinNeutral_le_iff
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F₁ F₂ : NeutralOrEmpty A) (K₁ K₂ : NeutralOrEmpty B) :
    joinNeutral A B F₁ K₁ ≤ joinNeutral A B F₂ K₂ ↔
      F₁.1 ≤ F₂.1 ∧ K₁.1 ≤ K₂.1 := by
  change hansenJoinFaceEquiv A B _ ≤ hansenJoinFaceEquiv A B _ ↔ _
  rw [hansenJoinFaceEquiv_le_iff]
  change sameSignFacetProduct
      (F₂.1 : Set (HansenFacetLabel A)) (K₂.1 : Set (HansenFacetLabel B)) ⊆
      sameSignFacetProduct
        (F₁.1 : Set (HansenFacetLabel A)) (K₁.1 : Set (HansenFacetLabel B)) ↔
    (F₂.1 : Set (HansenFacetLabel A)) ⊆ (F₁.1 : Set (HansenFacetLabel A)) ∧
      (K₂.1 : Set (HansenFacetLabel B)) ⊆ (K₁.1 : Set (HansenFacetLabel B))
  constructor
  · intro h
    constructor
    · rw [← neutral_left_projection A B F₂ K₂,
          ← neutral_left_projection A B F₁ K₁]
      exact Set.image_mono h
    · rw [← neutral_right_projection A B F₂ K₂,
          ← neutral_right_projection A B F₁ K₁]
      exact Set.image_mono h
  · rintro ⟨hF, hK⟩ facet hfacet
    exact ⟨hF hfacet.1, hK hfacet.2⟩


-- @@ L1166-1193 verbatim
/-- Crossing from a neutral-or-empty join face to a positive-rooted join
face is likewise componentwise.  This is the order-theoretic portal bridge
used by the full-flag recurrence. -/
theorem joinNeutral_le_joinRootedPos_iff
    (A : SimpleGraph V) (B : SimpleGraph W)
    (E : NeutralOrEmpty A) (L : NeutralOrEmpty B)
    (F : RootedPos A) (K : RootedPos B) :
    joinNeutral A B E L ≤ joinRootedPos A B F K ↔
      E.1 ≤ F.1 ∧ L.1 ≤ K.1 := by
  change hansenJoinFaceEquiv A B _ ≤ hansenJoinFaceEquiv A B _ ↔ _
  rw [hansenJoinFaceEquiv_le_iff]
  change sameSignFacetProduct
      (F.1 : Set (HansenFacetLabel A)) (K.1 : Set (HansenFacetLabel B)) ⊆
      sameSignFacetProduct
        (E.1 : Set (HansenFacetLabel A)) (L.1 : Set (HansenFacetLabel B)) ↔
    (F.1 : Set (HansenFacetLabel A)) ⊆ (E.1 : Set (HansenFacetLabel A)) ∧
      (K.1 : Set (HansenFacetLabel B)) ⊆ (L.1 : Set (HansenFacetLabel B))
  constructor
  · intro h
    constructor
    · rw [← rootedPos_left_projection A B F K,
          ← neutral_left_projection A B E L]
      exact Set.image_mono h
    · rw [← rootedPos_right_projection A B F K,
          ← neutral_right_projection A B E L]
      exact Set.image_mono h
  · rintro ⟨hF, hK⟩ facet hfacet
    exact ⟨hF hfacet.1, hK hfacet.2⟩


-- @@ L1195-1272 verbatim
/-- A neutral-to-positive cover in a Hansen graph join projects to covers in
both factors.  This is the forward half of the portal-cover product law. -/
theorem joinPortal_covBy_factors
    (A : SimpleGraph V) (B : SimpleGraph W)
    (E : NeutralOrEmpty A) (L : NeutralOrEmpty B)
    (F : RootedPos A) (K : RootedPos B)
    (hportal : joinNeutral A B E L ⋖ joinRootedPos A B F K) :
    E.1 ⋖ F.1 ∧ L.1 ⋖ K.1 := by
  have hcomp := (joinNeutral_le_joinRootedPos_iff A B E L F K).mp hportal.le
  constructor
  · apply covBy_of_eq_or_eq
    · exact lt_of_le_of_ne hcomp.1 (by
        intro hEF
        exact F.2.not_isNeutralOrEmpty (hEF ▸ E.2))
    · intro X hEX hXF
      rcases F.2.lower_strata hXF with hXpos | hXneutral
      · let Xpos : RootedPos A := ⟨X, hXpos⟩
        have hlower : joinNeutral A B E L ≤ joinRootedPos A B Xpos K :=
          (joinNeutral_le_joinRootedPos_iff A B E L Xpos K).mpr
            ⟨hEX, hcomp.2⟩
        have hupper : joinRootedPos A B Xpos K ≤ joinRootedPos A B F K :=
          (joinRootedPos_le_iff A B Xpos F K K).mpr ⟨hXF, le_rfl⟩
        rcases hportal.eq_or_eq hlower hupper with heq | heq
        · exact False.elim
            (joinRootedPos_ne_joinNeutral A B (Xpos, K) (E, L) heq)
        · have hpairs : (Xpos, K) = (F, K) :=
            joinRootedPos_pair_injective A B heq
          exact Or.inr (by
            simpa only [Xpos] using congrArg
              (fun pair : RootedPos A × RootedPos B ↦ pair.1.1) hpairs)
      · let Xneutral : NeutralOrEmpty A := ⟨X, hXneutral⟩
        have hlower : joinNeutral A B E L ≤ joinNeutral A B Xneutral L :=
          (joinNeutral_le_iff A B E Xneutral L L).mpr ⟨hEX, le_rfl⟩
        have hupper : joinNeutral A B Xneutral L ≤ joinRootedPos A B F K :=
          (joinNeutral_le_joinRootedPos_iff A B Xneutral L F K).mpr
            ⟨hXF, hcomp.2⟩
        rcases hportal.eq_or_eq hlower hupper with heq | heq
        · have hpairs : (Xneutral, L) = (E, L) :=
            joinNeutral_pair_injective A B heq
          exact Or.inl (by
            simpa only [Xneutral] using congrArg
              (fun pair : NeutralOrEmpty A × NeutralOrEmpty B ↦ pair.1.1) hpairs)
        · exact False.elim
            (joinRootedPos_ne_joinNeutral A B (F, K) (Xneutral, L) heq.symm)
  · apply covBy_of_eq_or_eq
    · exact lt_of_le_of_ne hcomp.2 (by
        intro hLK
        exact K.2.not_isNeutralOrEmpty (hLK ▸ L.2))
    · intro X hLX hXK
      rcases K.2.lower_strata hXK with hXpos | hXneutral
      · let Xpos : RootedPos B := ⟨X, hXpos⟩
        have hlower : joinNeutral A B E L ≤ joinRootedPos A B F Xpos :=
          (joinNeutral_le_joinRootedPos_iff A B E L F Xpos).mpr
            ⟨hcomp.1, hLX⟩
        have hupper : joinRootedPos A B F Xpos ≤ joinRootedPos A B F K :=
          (joinRootedPos_le_iff A B F F Xpos K).mpr ⟨le_rfl, hXK⟩
        rcases hportal.eq_or_eq hlower hupper with heq | heq
        · exact False.elim
            (joinRootedPos_ne_joinNeutral A B (F, Xpos) (E, L) heq)
        · have hpairs : (F, Xpos) = (F, K) :=
            joinRootedPos_pair_injective A B heq
          exact Or.inr (by
            simpa only [Xpos] using congrArg
              (fun pair : RootedPos A × RootedPos B ↦ pair.2.1) hpairs)
      · let Xneutral : NeutralOrEmpty B := ⟨X, hXneutral⟩
        have hlower : joinNeutral A B E L ≤ joinNeutral A B E Xneutral :=
          (joinNeutral_le_iff A B E E L Xneutral).mpr ⟨le_rfl, hLX⟩
        have hupper : joinNeutral A B E Xneutral ≤ joinRootedPos A B F K :=
          (joinNeutral_le_joinRootedPos_iff A B E Xneutral F K).mpr
            ⟨hcomp.1, hXK⟩
        rcases hportal.eq_or_eq hlower hupper with heq | heq
        · have hpairs : (E, Xneutral) = (E, L) :=
            joinNeutral_pair_injective A B heq
          exact Or.inl (by
            simpa only [Xneutral] using congrArg
              (fun pair : NeutralOrEmpty A × NeutralOrEmpty B ↦ pair.2.1) hpairs)
        · exact False.elim
            (joinRootedPos_ne_joinNeutral A B (F, K) (E, Xneutral) heq.symm)


-- @@ L1274-1300 verbatim
private theorem joinRootedNeg_not_le_joinRootedPos
    (A : SimpleGraph V) (B : SimpleGraph W)
    (N : RootedNeg A) (M : RootedNeg B)
    (F : RootedPos A) (K : RootedPos B) :
    ¬joinRootedNeg A B N M ≤ joinRootedPos A B F K := by
  intro h
  change hansenJoinFaceEquiv A B _ ≤ hansenJoinFaceEquiv A B _ at h
  rw [hansenJoinFaceEquiv_le_iff] at h
  change sameSignFacetProduct
      (F.1 : Set (HansenFacetLabel A)) (K.1 : Set (HansenFacetLabel B)) ⊆
    sameSignFacetProduct
      (N.1 : Set (HansenFacetLabel A)) (M.1 : Set (HansenFacetLabel B)) at h
  rcases F.2.carrier_nonempty with ⟨left, hleft⟩
  rcases K.2.carrier_nonempty with ⟨right, hright⟩
  have hsign : left.1 = right.1 := by
    rw [F.2.facet_sign hleft, K.2.facet_sign hright]
  let facet : SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1) := ⟨(left, right), hsign⟩
  have hmemPos : facet ∈ sameSignFacetProduct
      (F.1 : Set (HansenFacetLabel A)) (K.1 : Set (HansenFacetLabel B)) :=
    ⟨hleft, hright⟩
  have hmemNeg := h hmemPos
  have hnegSign := N.2.facet_sign hmemNeg.1
  have hposSign := F.2.facet_sign hleft
  rw [hposSign] at hnegSign
  exact HansenSign.noConfusion hnegSign


-- @@ L1302-1372 expanded
/-- Two factor portals produce a neutral-to-positive cover in the Hansen
graph join. -/
theorem joinPortal_covBy_of_factors (A : SimpleGraph V) (B : SimpleGraph W) (E : NeutralOrEmpty A)
    (L : NeutralOrEmpty B) (F : RootedPos A) (K : RootedPos B) (hEF : E.1 ⋖ F.1) (hLK : L.1 ⋖ K.1) :
    joinNeutral A B E L ⋖ joinRootedPos A B F K :=
  by
  apply covBy_of_eq_or_eq
  · apply lt_of_le_of_ne
    · exact (joinNeutral_le_joinRootedPos_iff A B E L F K).mpr ⟨hEF.le, hLK.le⟩
    · exact (joinRootedPos_ne_joinNeutral A B (F, K) (E, L)).symm
  · intro X hlower hupper
    let code := (joinFaceCodeEquiv A B).symm X
    have hrepr : joinFaceCodeToFace A B code = X := (joinFaceCodeEquiv A B).apply_symm_apply X
    rcases code with unit | code
    · exfalso
      apply joinRootedPos_ne_top A B (F, K)
      apply le_antisymm
      · intro facet hfacet
        exact hfacet.elim
      · have htop_eq : top (graphJoin A B) = X := by simpa only [joinFaceCodeToFace] using hrepr
        rw [htop_eq]
        exact hupper
    · rcases code with pair | code
      · rw [← hrepr] at hlower hupper
        have hlower' := (joinNeutral_le_joinRootedPos_iff A B E L pair.1 pair.2).mp hlower
        have hupper' := (joinRootedPos_le_iff A B pair.1 F pair.2 K).mp hupper
        have hleft := hEF.eq_or_eq hlower'.1 hupper'.1
        have hright := hLK.eq_or_eq hlower'.2 hupper'.2
        rcases hleft with hleft | hleft
        · exact False.elim (pair.1.2.not_isNeutralOrEmpty (hleft ▸ E.2))
        · rcases hright with hright | hright
          · exact False.elim (pair.2.2.not_isNeutralOrEmpty (hright ▸ L.2))
          · right
            have hpairs : pair = (F, K) := by
              apply Prod.ext
              · exact Subtype.ext hleft
              · exact Subtype.ext hright
            rw [hpairs] at hrepr
            exact hrepr.symm
      · rcases code with pair | pair
        · rw [← hrepr] at hupper
          exact False.elim (joinRootedNeg_not_le_joinRootedPos A B pair.1 pair.2 F K hupper)
        · rw [← hrepr] at hlower hupper
          have hlower' := (joinNeutral_le_iff A B E pair.1 L pair.2).mp hlower
          have hupper' := (joinNeutral_le_joinRootedPos_iff A B pair.1 pair.2 F K).mp hupper
          have hleft := hEF.eq_or_eq hlower'.1 hupper'.1
          have hright := hLK.eq_or_eq hlower'.2 hupper'.2
          rcases hleft with hleft | hleft
          · rcases hright with hright | hright
            · left
              have hpairs : pair = (E, L) := by
                apply Prod.ext
                · exact Subtype.ext hleft
                · exact Subtype.ext hright
              rw [hpairs] at hrepr
              exact hrepr.symm
            · exact False.elim (K.2.not_isNeutralOrEmpty (hright.symm ▸ pair.2.2))
          · exact False.elim (F.2.not_isNeutralOrEmpty (hleft.symm ▸ pair.1.2))


-- @@ L1374-1384 verbatim
/-- Exact portal-cover product law for the Hansen graph join. -/
theorem joinPortal_covBy_iff
    (A : SimpleGraph V) (B : SimpleGraph W)
    (E : NeutralOrEmpty A) (L : NeutralOrEmpty B)
    (F : RootedPos A) (K : RootedPos B) :
    joinNeutral A B E L ⋖ joinRootedPos A B F K ↔
      E.1 ⋖ F.1 ∧ L.1 ⋖ K.1 := by
  constructor
  · exact joinPortal_covBy_factors A B E L F K
  · rintro ⟨hEF, hLK⟩
    exact joinPortal_covBy_of_factors A B E L F K hEF hLK


-- @@ L1386-1389 verbatim
/-- A Hansen portal is a cover from the neutral-or-empty stratum to the
positive-rooted stratum. -/
abbrev HansenPortal (G : SimpleGraph V) :=
  {pair : NeutralOrEmpty G × RootedPos G // pair.1.1 ⋖ pair.2.1}


-- @@ L1391-1400 expanded
/-- Pair two factor portals to obtain the corresponding portal in a Hansen
graph join. -/
noncomputable def joinPortalMap (A : SimpleGraph V) (B : SimpleGraph W) :
    HansenPortal A × HansenPortal B → HansenPortal (graphJoin A B) := fun pair ↦
  ⟨(joinNeutralMap A B (pair.1.1.1, pair.2.1.1), joinRootedPosMap A B (pair.1.1.2, pair.2.1.2)),
    joinPortal_covBy_of_factors A B pair.1.1.1 pair.2.1.1 pair.1.1.2 pair.2.1.2 pair.1.2 pair.2.2⟩


-- @@ L1402-1460 verbatim
theorem joinPortalMap_bijective
    (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Bijective (joinPortalMap A B) := by
  constructor
  · intro p q h
    have hvalues := congrArg Subtype.val h
    have hneutral :
        joinNeutralMap A B (p.1.1.1, p.2.1.1) =
          joinNeutralMap A B (q.1.1.1, q.2.1.1) :=
      congrArg Prod.fst hvalues
    have hpositive :
        joinRootedPosMap A B (p.1.1.2, p.2.1.2) =
          joinRootedPosMap A B (q.1.1.2, q.2.1.2) :=
      congrArg Prod.snd hvalues
    have hneutralFactors := (joinNeutralMap_bijective A B).1 hneutral
    have hpositiveFactors := (joinRootedPosMap_bijective A B).1 hpositive
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact congrArg
          (fun pair : NeutralOrEmpty A × NeutralOrEmpty B ↦ pair.1)
          hneutralFactors
      · exact congrArg
          (fun pair : RootedPos A × RootedPos B ↦ pair.1)
          hpositiveFactors
    · apply Subtype.ext
      apply Prod.ext
      · exact congrArg
          (fun pair : NeutralOrEmpty A × NeutralOrEmpty B ↦ pair.2)
          hneutralFactors
      · exact congrArg
          (fun pair : RootedPos A × RootedPos B ↦ pair.2)
          hpositiveFactors
  · intro X
    let neutralFactors := (joinNeutralEquiv A B).symm X.1.1
    let positiveFactors := (joinRootedPosEquiv A B).symm X.1.2
    have hneutral : joinNeutralMap A B neutralFactors = X.1.1 :=
      (joinNeutralEquiv A B).apply_symm_apply X.1.1
    have hpositive : joinRootedPosMap A B positiveFactors = X.1.2 :=
      (joinRootedPosEquiv A B).apply_symm_apply X.1.2
    have hcover :
        joinNeutral A B neutralFactors.1 neutralFactors.2 ⋖
          joinRootedPos A B positiveFactors.1 positiveFactors.2 := by
      rw [show joinNeutral A B neutralFactors.1 neutralFactors.2 = X.1.1.1 from
            congrArg Subtype.val hneutral,
          show joinRootedPos A B positiveFactors.1 positiveFactors.2 = X.1.2.1 from
            congrArg Subtype.val hpositive]
      exact X.2
    have hfactors := (joinPortal_covBy_iff A B
      neutralFactors.1 neutralFactors.2 positiveFactors.1 positiveFactors.2).mp hcover
    let leftPortal : HansenPortal A :=
      ⟨(neutralFactors.1, positiveFactors.1), hfactors.1⟩
    let rightPortal : HansenPortal B :=
      ⟨(neutralFactors.2, positiveFactors.2), hfactors.2⟩
    refine ⟨(leftPortal, rightPortal), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hneutral
    · exact hpositive


-- @@ L1462-1467 expanded
/-- The neutral-to-positive portals of a Hansen graph join are exactly pairs
of portals from its two factors. -/
noncomputable def joinPortalEquiv (A : SimpleGraph V) (B : SimpleGraph W) :
    HansenPortal A × HansenPortal B ≃ HansenPortal (graphJoin A B) :=
  Equiv.ofBijective (joinPortalMap A B) (joinPortalMap_bijective A B)


-- @@ L1469-1469 verbatim
end HansenCombinatorialFace


-- @@ L1471-1471 verbatim
end HansenCograph
