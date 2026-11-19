/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenFaceJoin
import Formalisation.HansenCograph.CographThreeDState
import Lean.Elab.Tactic.Omega


-- @@ L10-17 verbatim
/-!
# Cardinal states of the finite Hansen face lattice

This file starts the geometric realization of the pointed face-count state.
It partitions every finite labelled Hansen face lattice into its top face,
the two apex-rooted strata, and the neutral-or-empty stratum, and derives the
exact total-face recurrence for a graph join from `joinFaceCodeEquiv`.
-/


-- @@ L19-19 verbatim
open SimpleGraph


-- @@ L21-21 verbatim
universe u v


-- @@ L23-23 verbatim
namespace HansenCograph

-- @@ L24-24 verbatim
namespace HansenCombinatorialFace


-- @@ L26-26 verbatim
variable {V : Type u} {W : Type v}

-- @@ L27-27 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L29-35 verbatim
/-- The pair of factor distinguished facets corresponding to the
distinguished facet of a graph join. -/
def distinguishedJoinFacetPair (A : SimpleGraph V) (B : SimpleGraph W) :
    SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1) :=
  ⟨(positiveDistinguishedFacet A, positiveDistinguishedFacet B), rfl⟩


-- @@ L37-45 expanded
@[simp]
theorem joinFacetLabel_distinguishedJoinFacetPair (A : SimpleGraph V) (B : SimpleGraph W) :
    joinFacetLabel A B (distinguishedJoinFacetPair A B) =
      positiveDistinguishedFacet (graphJoin A B) :=
  by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [distinguishedJoinFacetPair, positiveDistinguishedFacet, emptyHansenFacet, joinFacetLabel,
      sumFinset]


-- @@ L47-61 expanded
theorem hansenJoinFaceEquiv_distinguished_iff (A : SimpleGraph V) (B : SimpleGraph W)
    (C : AbstractJoinFace A B) :
    (hansenJoinFaceEquiv A B C).IsInPositiveDistinguishedFacet ↔
      distinguishedJoinFacetPair A B ∈ (C : Set _) :=
  by
  change positiveDistinguishedFacet (graphJoin A B) ∈ joinFacetLabelEquiv A B '' (C : Set _) ↔ _
  constructor
  · rintro ⟨facet, hfacet, hmap⟩
    have hpair : facet = distinguishedJoinFacetPair A B :=
      by
      apply (joinFacetLabelEquiv A B).injective
      exact hmap.trans (joinFacetLabel_distinguishedJoinFacetPair A B).symm
    simpa [hpair] using hfacet
  · intro hpair
    exact ⟨distinguishedJoinFacetPair A B, hpair, joinFacetLabel_distinguishedJoinFacetPair A B⟩


-- @@ L63-71 verbatim
theorem joinRootedPos_distinguished_iff
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedPos A) (K : RootedPos B) :
    (joinRootedPos A B F K).IsInPositiveDistinguishedFacet ↔
      F.1.IsInPositiveDistinguishedFacet ∧
        K.1.IsInPositiveDistinguishedFacet := by
  unfold joinRootedPos
  rw [hansenJoinFaceEquiv_distinguished_iff]
  rfl


-- @@ L73-81 verbatim
theorem joinNeutral_distinguished_iff
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : NeutralOrEmpty A) (K : NeutralOrEmpty B) :
    (joinNeutral A B F K).IsInPositiveDistinguishedFacet ↔
      F.1.IsInPositiveDistinguishedFacet ∧
        K.1.IsInPositiveDistinguishedFacet := by
  unfold joinNeutral
  rw [hansenJoinFaceEquiv_distinguished_iff]
  rfl


-- @@ L83-86 verbatim
/-- The disjoint four-way code for all faces of a finite Hansen incidence
lattice. -/
abbrev FaceStrataCode (G : SimpleGraph V) :=
  PUnit.{1} ⊕ (RootedPos G ⊕ (RootedNeg G ⊕ NeutralOrEmpty G))


-- @@ L88-94 verbatim
/-- Forget the stratum tag. -/
def faceStrataCodeToFace (G : SimpleGraph V) :
    FaceStrataCode G → HansenCombinatorialFace G
  | .inl _ => top G
  | .inr (.inl F) => F.1
  | .inr (.inr (.inl F)) => F.1
  | .inr (.inr (.inr F)) => F.1


-- @@ L96-103 verbatim
theorem faceStrataCodeToFace_surjective (G : SimpleGraph V) :
    Function.Surjective (faceStrataCodeToFace G) := by
  intro F
  rcases strata_cases G F with htop | hpos | hneg | hneutral
  · exact ⟨Sum.inl PUnit.unit, by simpa [faceStrataCodeToFace] using htop.symm⟩
  · exact ⟨Sum.inr (Sum.inl ⟨F, hpos⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inl ⟨F, hneg⟩)), rfl⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inr ⟨F, hneutral⟩)), rfl⟩


-- @@ L105-191 verbatim
theorem faceStrataCodeToFace_injective (G : SimpleGraph V) :
    Function.Injective (faceStrataCodeToFace G) := by
  intro x y h
  rcases x with x | x
  · rcases y with y | y
    · rfl
    · rcases y with y | y
      · exfalso
        simp only [faceStrataCodeToFace] at h
        apply y.2.2
        rw [← h]
        exact containsVertex_top G (emptyHansenVertex G HansenSign.neg)
      · rcases y with y | y
        · exfalso
          simp only [faceStrataCodeToFace] at h
          apply y.2.2
          rw [← h]
          exact containsVertex_top G (emptyHansenVertex G HansenSign.pos)
        · exfalso
          simp only [faceStrataCodeToFace] at h
          apply y.2.1
          rw [← h]
          exact containsVertex_top G (emptyHansenVertex G HansenSign.pos)
  · rcases x with x | x
    · rcases y with y | y
      · exfalso
        simp only [faceStrataCodeToFace] at h
        apply x.2.2
        rw [h]
        exact containsVertex_top G (emptyHansenVertex G HansenSign.neg)
      · rcases y with y | y
        · simp only [faceStrataCodeToFace] at h
          exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext h))
        · rcases y with y | y
          · exfalso
            simp only [faceStrataCodeToFace] at h
            apply x.2.2
            rw [h]
            exact y.2.1
          · exfalso
            simp only [faceStrataCodeToFace] at h
            apply y.2.1
            rw [← h]
            exact x.2.1
    · rcases x with x | x
      · rcases y with y | y
        · exfalso
          simp only [faceStrataCodeToFace] at h
          apply x.2.2
          rw [h]
          exact containsVertex_top G (emptyHansenVertex G HansenSign.pos)
        · rcases y with y | y
          · exfalso
            simp only [faceStrataCodeToFace] at h
            apply x.2.2
            rw [h]
            exact y.2.1
          · rcases y with y | y
            · simp only [faceStrataCodeToFace] at h
              exact congrArg Sum.inr (congrArg Sum.inr
                (congrArg Sum.inl (Subtype.ext h)))
            · exfalso
              simp only [faceStrataCodeToFace] at h
              apply y.2.2
              rw [← h]
              exact x.2.1
      · rcases y with y | y
        · exfalso
          simp only [faceStrataCodeToFace] at h
          apply x.2.1
          rw [h]
          exact containsVertex_top G (emptyHansenVertex G HansenSign.pos)
        · rcases y with y | y
          · exfalso
            simp only [faceStrataCodeToFace] at h
            apply x.2.1
            rw [h]
            exact y.2.1
          · rcases y with y | y
            · exfalso
              simp only [faceStrataCodeToFace] at h
              apply x.2.2
              rw [h]
              exact y.2.1
            · simp only [faceStrataCodeToFace] at h
              exact congrArg Sum.inr (congrArg Sum.inr
                (congrArg Sum.inr (Subtype.ext h)))


-- @@ L193-197 verbatim
/-- Exact disjoint partition of the finite face lattice. -/
noncomputable def faceStrataEquiv (G : SimpleGraph V) :
    FaceStrataCode G ≃ HansenCombinatorialFace G :=
  Equiv.ofBijective (faceStrataCodeToFace G)
    ⟨faceStrataCodeToFace_injective G, faceStrataCodeToFace_surjective G⟩


-- @@ L199-200 verbatim
noncomputable instance instFintypeRootedPos (G : SimpleGraph V) :
    Fintype (RootedPos G) := Fintype.ofFinite _


-- @@ L202-203 verbatim
noncomputable instance instFintypeRootedNeg (G : SimpleGraph V) :
    Fintype (RootedNeg G) := Fintype.ofFinite _


-- @@ L205-206 verbatim
noncomputable instance instFintypeNeutralOrEmpty (G : SimpleGraph V) :
    Fintype (NeutralOrEmpty G) := Fintype.ofFinite _


-- @@ L208-210 verbatim
/-- Faces in the positive apex--distinguished-facet corner interval. -/
abbrev CornerFace (G : SimpleGraph V) :=
  {F : RootedPos G // F.1.IsInPositiveDistinguishedFacet}


-- @@ L212-215 verbatim
/-- Neutral-or-empty faces inside the positive distinguished facet.  The
empty face is included, making this stratum multiplicative under joins. -/
abbrev NeutralDistinguishedOrEmpty (G : SimpleGraph V) :=
  {F : NeutralOrEmpty G // F.1.IsInPositiveDistinguishedFacet}


-- @@ L217-220 verbatim
/-- All faces contained in the positive distinguished facet, including the
empty face. -/
abbrev DistinguishedFace (G : SimpleGraph V) :=
  {F : HansenCombinatorialFace G // F.IsInPositiveDistinguishedFacet}


-- @@ L222-224 verbatim
/-- Nonempty faces contained in the positive distinguished facet. -/
abbrev DistinguishedNonemptyFace (G : SimpleGraph V) :=
  {F : DistinguishedFace G // F.1 ≠ bottom G}


-- @@ L226-227 verbatim
noncomputable instance instFintypeCornerFace (G : SimpleGraph V) :
    Fintype (CornerFace G) := Fintype.ofFinite _


-- @@ L229-231 verbatim
noncomputable instance instFintypeNeutralDistinguishedOrEmpty
    (G : SimpleGraph V) : Fintype (NeutralDistinguishedOrEmpty G) :=
  Fintype.ofFinite _


-- @@ L233-234 verbatim
noncomputable instance instFintypeDistinguishedFace (G : SimpleGraph V) :
    Fintype (DistinguishedFace G) := Fintype.ofFinite _


-- @@ L236-238 verbatim
noncomputable instance instFintypeDistinguishedNonemptyFace
    (G : SimpleGraph V) : Fintype (DistinguishedNonemptyFace G) :=
  Fintype.ofFinite _


-- @@ L240-248 verbatim
theorem bottom_isNeutralOrEmpty (G : SimpleGraph V) :
    (bottom G).IsNeutralOrEmpty := by
  constructor <;> intro hcontains
  · exact emptyHansenVertex_not_incident_same_sign G HansenSign.pos
      (hcontains (emptyHansenFacet G HansenSign.pos)
        (by change _ ∈ (Set.univ : Set (HansenFacetLabel G)); exact Set.mem_univ _))
  · exact emptyHansenVertex_not_incident_same_sign G HansenSign.neg
      (hcontains (emptyHansenFacet G HansenSign.neg)
        (by change _ ∈ (Set.univ : Set (HansenFacetLabel G)); exact Set.mem_univ _))


-- @@ L250-253 verbatim
@[simp] theorem bottom_isInPositiveDistinguishedFacet (G : SimpleGraph V) :
    (bottom G).IsInPositiveDistinguishedFacet := by
  change positiveDistinguishedFacet G ∈ (Set.univ : Set (HansenFacetLabel G))
  exact Set.mem_univ _


-- @@ L255-259 verbatim
/-- Forget the rooted/neutral tag inside the distinguished facet. -/
def distinguishedStrataToFace (G : SimpleGraph V) :
    CornerFace G ⊕ NeutralDistinguishedOrEmpty G → DistinguishedFace G
  | .inl F => ⟨F.1.1, F.2⟩
  | .inr F => ⟨F.1.1, F.2⟩


-- @@ L261-280 verbatim
theorem distinguishedStrataToFace_injective (G : SimpleGraph V) :
    Function.Injective (distinguishedStrataToFace G) := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl (Subtype.ext (Subtype.ext
      (congrArg (fun z : DistinguishedFace G ↦ z.1) h)))
  · exfalso
    have hface := congrArg (fun z : DistinguishedFace G ↦ z.1) h
    change x.1.1 = y.1.1 at hface
    apply y.1.2.1
    rw [← hface]
    exact x.1.2.1
  · exfalso
    have hface := congrArg (fun z : DistinguishedFace G ↦ z.1) h
    change x.1.1 = y.1.1 at hface
    apply x.1.2.1
    rw [hface]
    exact y.1.2.1
  · exact congrArg Sum.inr (Subtype.ext (Subtype.ext
      (congrArg (fun z : DistinguishedFace G ↦ z.1) h)))


-- @@ L282-292 verbatim
theorem distinguishedStrataToFace_surjective (G : SimpleGraph V) :
    Function.Surjective (distinguishedStrataToFace G) := by
  rintro ⟨F, hdist⟩
  rcases strata_cases G F with htop | hpos | hneg | hneutral
  · subst F
    change positiveDistinguishedFacet G ∈ (∅ : Set (HansenFacetLabel G)) at hdist
    exact hdist.elim
  · exact ⟨Sum.inl ⟨⟨F, hpos⟩, hdist⟩, rfl⟩
  · have hsign := hneg.facet_sign hdist
    simp [positiveDistinguishedFacet, emptyHansenFacet] at hsign
  · exact ⟨Sum.inr ⟨⟨F, hneutral⟩, hdist⟩, rfl⟩


-- @@ L294-298 verbatim
noncomputable def distinguishedStrataEquiv (G : SimpleGraph V) :
    CornerFace G ⊕ NeutralDistinguishedOrEmpty G ≃ DistinguishedFace G :=
  Equiv.ofBijective (distinguishedStrataToFace G)
    ⟨distinguishedStrataToFace_injective G,
      distinguishedStrataToFace_surjective G⟩


-- @@ L300-304 verbatim
/-- Split off the unique empty face from the distinguished-face interval. -/
def distinguishedEmptyOrNonemptyToFace (G : SimpleGraph V) :
    PUnit.{1} ⊕ DistinguishedNonemptyFace G → DistinguishedFace G
  | .inl _ => ⟨bottom G, bottom_isInPositiveDistinguishedFacet G⟩
  | .inr F => F.1


-- @@ L306-322 verbatim
theorem distinguishedEmptyOrNonemptyToFace_bijective (G : SimpleGraph V) :
    Function.Bijective (distinguishedEmptyOrNonemptyToFace G) := by
  constructor
  · intro x y h
    rcases x with x | x <;> rcases y with y | y
    · rfl
    · exfalso
      apply y.2
      exact congrArg (fun z : DistinguishedFace G ↦ z.1) h |>.symm
    · exfalso
      apply x.2
      exact congrArg (fun z : DistinguishedFace G ↦ z.1) h
    · exact congrArg Sum.inr (Subtype.ext h)
  · intro F
    by_cases hbottom : F.1 = bottom G
    · exact ⟨Sum.inl PUnit.unit, Subtype.ext hbottom.symm⟩
    · exact ⟨Sum.inr ⟨F, hbottom⟩, rfl⟩


-- @@ L324-327 verbatim
noncomputable def distinguishedEmptyOrNonemptyEquiv (G : SimpleGraph V) :
    PUnit.{1} ⊕ DistinguishedNonemptyFace G ≃ DistinguishedFace G :=
  Equiv.ofBijective (distinguishedEmptyOrNonemptyToFace G)
    (distinguishedEmptyOrNonemptyToFace_bijective G)


-- @@ L329-341 verbatim
/-- A vertex of `G` becomes the corresponding containing facet of the dual
face for `Gᶜ`. -/
theorem hansenFaceDualEquiv_facet_mem
    (G : SimpleGraph V) (F : HansenCombinatorialFace G)
    (vertex : HansenVertexLabel G) :
    vertexComplFacetEquiv G vertex ∈
        ((hansenFaceDualEquiv G F : HansenCombinatorialFace Gᶜ) :
          Set (HansenFacetLabel Gᶜ)) ↔
      F.ContainsVertex vertex := by
  change vertexComplFacetEquiv G vertex ∈
      vertexComplFacetEquiv G ''
        incidenceModels (hansenLabelIncidence G) F ↔ _
  simp [ContainsVertex]


-- @@ L343-363 verbatim
/-- A containing facet of `G` becomes the corresponding vertex contained in
the dual face for `Gᶜ`. -/
theorem hansenFaceDualEquiv_contains_facet
    (G : SimpleGraph V) (F : HansenCombinatorialFace G)
    (facet : HansenFacetLabel G) :
    (hansenFaceDualEquiv G F).ContainsVertex
        (facetComplVertexEquiv G facet) ↔ facet ∈ (F : Set _) := by
  have h := incidenceClosedTransportSurjEquiv_models
    (dualIncidence (hansenLabelIncidence G))
    (hansenLabelIncidence Gᶜ)
    (facetComplVertexEquiv G) (vertexComplFacetEquiv G)
    (facetComplVertexEquiv G).surjective
    (fun f v ↦ hansenLabelIncidence_compl_transpose G v f)
    (incidenceClosedDual (hansenLabelIncidence G) F) facet
  change (hansenFaceDualEquiv G F).ContainsVertex
      (facetComplVertexEquiv G facet) ↔
    facet ∈ incidenceClosure (hansenLabelIncidence G) F at h
  have hclosed : incidenceClosure (hansenLabelIncidence G) (F : Set _) =
      (F : Set _) := F.isClosed
  rw [hclosed] at h
  exact h


-- @@ L365-372 verbatim
theorem hansenFaceDualEquiv_symm_contains
    (G : SimpleGraph V) (F : HansenCombinatorialFace Gᶜ)
    (vertex : HansenVertexLabel G) :
    ((hansenFaceDualEquiv G).symm F).ContainsVertex vertex ↔
      vertexComplFacetEquiv G vertex ∈ (F : Set _) := by
  rw [← hansenFaceDualEquiv_facet_mem G
    ((hansenFaceDualEquiv G).symm F) vertex]
  simp


-- @@ L374-381 verbatim
theorem hansenCentralFaceEquiv_facet_mem
    (G : SimpleGraph V) (F : HansenCombinatorialFace G)
    (facet : HansenFacetLabel G) :
    facetSignFlipEquiv G facet ∈
        ((hansenCentralFaceEquiv G F : HansenCombinatorialFace G) : Set _) ↔
      facet ∈ (F : Set _) := by
  change facetSignFlipEquiv G facet ∈ facetSignFlipEquiv G '' (F : Set _) ↔ _
  simp


-- @@ L383-397 verbatim
theorem hansenFaceDualEquiv_top (G : SimpleGraph V) :
    hansenFaceDualEquiv G (top G) = bottom Gᶜ := by
  have hinv : (hansenFaceDualEquiv G).symm (bottom Gᶜ) = top G := by
    apply (eq_top_iff_contains_both G _).mpr
    constructor
    · rw [hansenFaceDualEquiv_symm_contains]
      change vertexComplFacetEquiv G (emptyHansenVertex G HansenSign.pos) ∈
        (Set.univ : Set (HansenFacetLabel Gᶜ))
      exact Set.mem_univ _
    · rw [hansenFaceDualEquiv_symm_contains]
      change vertexComplFacetEquiv G (emptyHansenVertex G HansenSign.neg) ∈
        (Set.univ : Set (HansenFacetLabel Gᶜ))
      exact Set.mem_univ _
  apply (hansenFaceDualEquiv G).symm.injective
  simpa [hinv]


-- @@ L399-455 verbatim
/-- Central symmetry followed by Hansen polarity sends positive-rooted faces
of `G` bijectively to the nonempty faces of the positive distinguished facet
of `Gᶜ`. -/
noncomputable def rootedDistinguishedEquiv (G : SimpleGraph V) :
    RootedPos G ≃ DistinguishedNonemptyFace Gᶜ where
  toFun F := by
    let C := hansenCentralFaceEquiv G F.1
    let D := hansenFaceDualEquiv G C
    have hC : C.IsRootedNeg := centralFace_rootedPos_to_rootedNeg F.2
    refine ⟨⟨D, ?_⟩, ?_⟩
    · have h := (hansenFaceDualEquiv_facet_mem G C
        (emptyHansenVertex G HansenSign.neg)).mpr hC.1
      simpa [D, IsInPositiveDistinguishedFacet, positiveDistinguishedFacet,
        vertexComplFacetEquiv,
        emptyHansenVertex, emptyHansenFacet] using h
    · intro hbottom
      change D = bottom Gᶜ at hbottom
      have hmem : vertexComplFacetEquiv G
          (emptyHansenVertex G HansenSign.pos) ∈ (D : Set _) := by
        rw [hbottom]
        change _ ∈ (Set.univ : Set (HansenFacetLabel Gᶜ))
        exact Set.mem_univ _
      exact hC.2 ((hansenFaceDualEquiv_facet_mem G C
        (emptyHansenVertex G HansenSign.pos)).mp hmem)
  invFun F := by
    let K := (hansenFaceDualEquiv G).symm F.1.1
    have hneg : K.ContainsVertex (emptyHansenVertex G HansenSign.neg) := by
      rw [hansenFaceDualEquiv_symm_contains]
      simpa [IsInPositiveDistinguishedFacet, positiveDistinguishedFacet,
        vertexComplFacetEquiv,
        emptyHansenVertex, emptyHansenFacet] using F.1.2
    have hposNot : ¬K.ContainsVertex (emptyHansenVertex G HansenSign.pos) := by
      intro hpos
      have htop : K = top G := (eq_top_iff_contains_both G K).mpr ⟨hpos, hneg⟩
      apply F.2
      calc
        F.1.1 = hansenFaceDualEquiv G K :=
          (hansenFaceDualEquiv G).apply_symm_apply F.1.1 |>.symm
        _ = hansenFaceDualEquiv G (top G) := congrArg _ htop
        _ = bottom Gᶜ := hansenFaceDualEquiv_top G
    exact ⟨hansenCentralFaceEquiv G K,
      centralFace_rootedNeg_to_rootedPos ⟨hneg, hposNot⟩⟩
  left_inv F := by
    apply Subtype.ext
    change hansenCentralFaceEquiv G
      ((hansenFaceDualEquiv G).symm
        (hansenFaceDualEquiv G (hansenCentralFaceEquiv G F.1))) = F.1
    rw [(hansenFaceDualEquiv G).symm_apply_apply]
    exact hansenCentralFaceEquiv_involutive G F.1
  right_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    change hansenFaceDualEquiv G
      (hansenCentralFaceEquiv G
        (hansenCentralFaceEquiv G ((hansenFaceDualEquiv G).symm F.1.1))) = F.1.1
    rw [hansenCentralFaceEquiv_involutive]
    exact (hansenFaceDualEquiv G).apply_symm_apply F.1.1


-- @@ L457-542 verbatim
/-- The apex--distinguished-facet corner interval is invariant under graph
complementation. -/
noncomputable def cornerComplEquiv (G : SimpleGraph V) :
    CornerFace G ≃ CornerFace Gᶜ where
  toFun F := by
    let C := hansenCentralFaceEquiv G F.1.1
    let D := hansenFaceDualEquiv G C
    have hCroot : C.IsRootedNeg := centralFace_rootedPos_to_rootedNeg F.1.2
    have hDdist : D.IsInPositiveDistinguishedFacet := by
      have h := (hansenFaceDualEquiv_facet_mem G C
        (emptyHansenVertex G HansenSign.neg)).mpr hCroot.1
      simpa [D, IsInPositiveDistinguishedFacet, positiveDistinguishedFacet,
        vertexComplFacetEquiv, emptyHansenVertex, emptyHansenFacet] using h
    have hCfacetPos : emptyHansenFacet G HansenSign.pos ∈ (C : Set _) := by
      have h := (hansenCentralFaceEquiv_facet_mem G F.1.1
        (emptyHansenFacet G HansenSign.neg)).mpr F.2
      simpa [C, facetSignFlipEquiv, HansenSign.flipEquiv, HansenSign.flip,
        emptyHansenFacet] using h
    have hDpos : D.ContainsVertex (emptyHansenVertex Gᶜ HansenSign.pos) := by
      have h := (hansenFaceDualEquiv_contains_facet G C
        (emptyHansenFacet G HansenSign.pos)).mpr hCfacetPos
      simpa [D, facetComplVertexEquiv, emptyHansenVertex,
        emptyHansenFacet] using h
    have hDneg : ¬D.ContainsVertex (emptyHansenVertex Gᶜ HansenSign.neg) := by
      intro hcontains
      have h := (hansenFaceDualEquiv_contains_facet G C
        (emptyHansenFacet G HansenSign.neg)).mp
        (by simpa [D, facetComplVertexEquiv, emptyHansenVertex,
            emptyHansenFacet] using hcontains)
      have hsign := hCroot.facet_sign h
      simp [emptyHansenFacet] at hsign
    exact ⟨⟨D, ⟨hDpos, hDneg⟩⟩, hDdist⟩
  invFun F := by
    let K := (hansenFaceDualEquiv G).symm F.1.1
    let E := hansenCentralFaceEquiv G K
    have hKneg : K.ContainsVertex (emptyHansenVertex G HansenSign.neg) := by
      rw [hansenFaceDualEquiv_symm_contains]
      simpa [IsInPositiveDistinguishedFacet, positiveDistinguishedFacet,
        vertexComplFacetEquiv, emptyHansenVertex, emptyHansenFacet] using F.2
    have hKposNot : ¬K.ContainsVertex (emptyHansenVertex G HansenSign.pos) := by
      intro hpos
      have htop : K = top G := (eq_top_iff_contains_both G K).mpr ⟨hpos, hKneg⟩
      have hbottom : F.1.1 = bottom Gᶜ := by
        calc
          F.1.1 = hansenFaceDualEquiv G K :=
            (hansenFaceDualEquiv G).apply_symm_apply F.1.1 |>.symm
          _ = hansenFaceDualEquiv G (top G) := congrArg _ htop
          _ = bottom Gᶜ := hansenFaceDualEquiv_top G
      have hroot := F.1.2
      rw [hbottom] at hroot
      exact (bottom_isNeutralOrEmpty Gᶜ).1 hroot.1
    have hEroot : E.IsRootedPos :=
      centralFace_rootedNeg_to_rootedPos ⟨hKneg, hKposNot⟩
    have hKfacetPos : emptyHansenFacet G HansenSign.pos ∈ (K : Set _) := by
      have h := (hansenFaceDualEquiv_contains_facet G K
        (emptyHansenFacet G HansenSign.pos)).mp
        (by
          have hdual : hansenFaceDualEquiv G K = F.1.1 :=
            (hansenFaceDualEquiv G).apply_symm_apply F.1.1
          rw [hdual]
          simpa [facetComplVertexEquiv, emptyHansenVertex,
            emptyHansenFacet] using F.1.2.1)
      exact h
    have hEdist : E.IsInPositiveDistinguishedFacet := by
      have h := (hansenCentralFaceEquiv_facet_mem G K
        (emptyHansenFacet G HansenSign.pos)).mpr hKfacetPos
      simpa [E, IsInPositiveDistinguishedFacet, positiveDistinguishedFacet,
        facetSignFlipEquiv, HansenSign.flipEquiv, HansenSign.flip,
        emptyHansenFacet] using h
    exact ⟨⟨E, hEroot⟩, hEdist⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    change hansenCentralFaceEquiv G
      ((hansenFaceDualEquiv G).symm
        (hansenFaceDualEquiv G (hansenCentralFaceEquiv G F.1.1))) = F.1.1
    rw [(hansenFaceDualEquiv G).symm_apply_apply]
    exact hansenCentralFaceEquiv_involutive G F.1.1
  right_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    change hansenFaceDualEquiv G
      (hansenCentralFaceEquiv G
        (hansenCentralFaceEquiv G ((hansenFaceDualEquiv G).symm F.1.1))) = F.1.1
    rw [hansenCentralFaceEquiv_involutive]
    exact (hansenFaceDualEquiv G).apply_symm_apply F.1.1


-- @@ L544-580 expanded
/-- The corner interval of a join is the product of the two factor corner
intervals. -/
noncomputable def joinCornerEquiv (A : SimpleGraph V) (B : SimpleGraph W) :
    CornerFace A × CornerFace B ≃ CornerFace (graphJoin A B) :=
  by
  let forward : CornerFace A × CornerFace B → CornerFace (graphJoin A B) := fun pair ↦
    ⟨⟨joinRootedPos A B pair.1.1 pair.2.1, joinRootedPos_isRootedPos A B pair.1.1 pair.2.1⟩,
      (joinRootedPos_distinguished_iff A B pair.1.1 pair.2.1).mpr ⟨pair.1.2, pair.2.2⟩⟩
  apply Equiv.ofBijective forward
  constructor
  · intro x y h
    have hfaces := congrArg (fun z : CornerFace (graphJoin A B) ↦ z.1.1) h
    change joinRootedPos A B x.1.1 x.2.1 = joinRootedPos A B y.1.1 y.2.1 at hfaces
    have hpairs : (x.1.1, x.2.1) = (y.1.1, y.2.1) :=
      by
      apply joinRootedPos_pair_injective A B
      exact hfaces
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst hpairs
    · exact congrArg Prod.snd hpairs
  · rintro ⟨F, hdist⟩
    rcases (joinRootedPosEquiv A B).surjective F with ⟨pair, hpair⟩
    have hface : joinRootedPos A B pair.1 pair.2 = F.1 := congrArg Subtype.val hpair
    have hjoinDist : (joinRootedPos A B pair.1 pair.2).IsInPositiveDistinguishedFacet :=
      by
      rw [hface]
      exact hdist
    have hfactorDist := (joinRootedPos_distinguished_iff A B pair.1 pair.2).mp hjoinDist
    refine ⟨(⟨pair.1, hfactorDist.1⟩, ⟨pair.2, hfactorDist.2⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hface


-- @@ L582-622 expanded
/-- The neutral distinguished stratum of a join is the product of the two
factor strata. -/
noncomputable def joinNeutralDistinguishedEquiv (A : SimpleGraph V) (B : SimpleGraph W) :
    NeutralDistinguishedOrEmpty A × NeutralDistinguishedOrEmpty B ≃
      NeutralDistinguishedOrEmpty (graphJoin A B) :=
  by
  let forward :
    NeutralDistinguishedOrEmpty A × NeutralDistinguishedOrEmpty B →
      NeutralDistinguishedOrEmpty (graphJoin A B) :=
    fun pair ↦
    ⟨⟨joinNeutral A B pair.1.1 pair.2.1, joinNeutral_isNeutralOrEmpty A B pair.1.1 pair.2.1⟩,
      (joinNeutral_distinguished_iff A B pair.1.1 pair.2.1).mpr ⟨pair.1.2, pair.2.2⟩⟩
  apply Equiv.ofBijective forward
  constructor
  · intro x y h
    have hfaces := congrArg (fun z : NeutralDistinguishedOrEmpty (graphJoin A B) ↦ z.1.1) h
    change joinNeutral A B x.1.1 x.2.1 = joinNeutral A B y.1.1 y.2.1 at hfaces
    have hpairs : (x.1.1, x.2.1) = (y.1.1, y.2.1) :=
      by
      apply joinNeutral_pair_injective A B
      exact hfaces
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst hpairs
    · exact congrArg Prod.snd hpairs
  · rintro ⟨F, hdist⟩
    rcases (joinNeutralEquiv A B).surjective F with ⟨pair, hpair⟩
    have hface : joinNeutral A B pair.1 pair.2 = F.1 := congrArg Subtype.val hpair
    have hjoinDist : (joinNeutral A B pair.1 pair.2).IsInPositiveDistinguishedFacet :=
      by
      rw [hface]
      exact hdist
    have hfactorDist := (joinNeutral_distinguished_iff A B pair.1 pair.2).mp hjoinDist
    refine ⟨(⟨pair.1, hfactorDist.1⟩, ⟨pair.2, hfactorDist.2⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hface


-- @@ L624-626 verbatim
/-- Number of proper faces rooted at the positive apex. -/
noncomputable def rootedFaceCount (G : SimpleGraph V) : Nat :=
  Fintype.card (RootedPos G)


-- @@ L628-630 verbatim
/-- Number of faces containing neither apex, including the empty face. -/
noncomputable def neutralOrEmptyFaceCount (G : SimpleGraph V) : Nat :=
  Fintype.card (NeutralOrEmpty G)


-- @@ L632-634 verbatim
/-- Cardinality of the positive apex--distinguished-facet corner interval. -/
noncomputable def cornerFaceCount (G : SimpleGraph V) : Nat :=
  Fintype.card (CornerFace G)


-- @@ L636-639 verbatim
/-- Cardinality of the neutral distinguished stratum with the empty face
included. -/
noncomputable def neutralDistinguishedOrEmptyCount (G : SimpleGraph V) : Nat :=
  Fintype.card (NeutralDistinguishedOrEmpty G)


-- @@ L641-652 verbatim
theorem distinguishedNonemptyFaceCount_eq (G : SimpleGraph V) :
    Fintype.card (DistinguishedNonemptyFace G) =
      cornerFaceCount G + neutralDistinguishedOrEmptyCount G - 1 := by
  have hstrata := Fintype.card_congr (distinguishedStrataEquiv G)
  have hempty := Fintype.card_congr (distinguishedEmptyOrNonemptyEquiv G)
  have hstrata' : cornerFaceCount G + neutralDistinguishedOrEmptyCount G =
      Fintype.card (DistinguishedFace G) := by
    simpa [cornerFaceCount, neutralDistinguishedOrEmptyCount] using hstrata
  have hempty' : 1 + Fintype.card (DistinguishedNonemptyFace G) =
      Fintype.card (DistinguishedFace G) := by
    simpa using hempty
  omega


-- @@ L654-671 verbatim
/-- Rooted faces after graph complementation are the nonempty distinguished-
facet faces before complementation. -/
theorem rootedFaceCount_compl_add_one (G : SimpleGraph V) :
    1 + rootedFaceCount Gᶜ =
      cornerFaceCount G + neutralDistinguishedOrEmptyCount G := by
  have hroot := Fintype.card_congr (rootedDistinguishedEquiv Gᶜ)
  have hstrata := Fintype.card_congr (distinguishedStrataEquiv G)
  have hempty := Fintype.card_congr (distinguishedEmptyOrNonemptyEquiv G)
  have hroot' : rootedFaceCount Gᶜ =
      Fintype.card (DistinguishedNonemptyFace G) := by
    simpa [rootedFaceCount] using hroot
  have hstrata' : cornerFaceCount G + neutralDistinguishedOrEmptyCount G =
      Fintype.card (DistinguishedFace G) := by
    simpa [cornerFaceCount, neutralDistinguishedOrEmptyCount] using hstrata
  have hempty' : 1 + Fintype.card (DistinguishedNonemptyFace G) =
      Fintype.card (DistinguishedFace G) := by
    simpa using hempty
  omega


-- @@ L673-679 verbatim
theorem rootedFaceCount_compl_int (G : SimpleGraph V) :
    (rootedFaceCount Gᶜ : ℤ) =
      (cornerFaceCount G : ℤ) +
        (neutralDistinguishedOrEmptyCount G : ℤ) - 1 := by
  have h := congrArg Int.ofNat (rootedFaceCount_compl_add_one G)
  norm_num at h ⊢
  omega


-- @@ L681-685 verbatim
/-- The apex--facet corner cardinality is self-dual. -/
theorem cornerFaceCount_compl (G : SimpleGraph V) :
    cornerFaceCount Gᶜ = cornerFaceCount G := by
  simpa [cornerFaceCount] using
    (Fintype.card_congr (cornerComplEquiv G)).symm


-- @@ L687-689 expanded
theorem rootedFaceCount_join (A : SimpleGraph V) (B : SimpleGraph W) :
    rootedFaceCount (graphJoin A B) = rootedFaceCount A * rootedFaceCount B := by
  simpa [rootedFaceCount] using Fintype.card_congr (joinRootedPosEquiv A B).symm


-- @@ L691-696 expanded
theorem neutralOrEmptyFaceCount_join (A : SimpleGraph V) (B : SimpleGraph W) :
    neutralOrEmptyFaceCount (graphJoin A B) =
      neutralOrEmptyFaceCount A * neutralOrEmptyFaceCount B :=
  by simpa [neutralOrEmptyFaceCount] using Fintype.card_congr (joinNeutralEquiv A B).symm


-- @@ L698-700 expanded
theorem cornerFaceCount_join (A : SimpleGraph V) (B : SimpleGraph W) :
    cornerFaceCount (graphJoin A B) = cornerFaceCount A * cornerFaceCount B := by
  simpa [cornerFaceCount] using Fintype.card_congr (joinCornerEquiv A B).symm


-- @@ L702-708 expanded
theorem neutralDistinguishedOrEmptyCount_join (A : SimpleGraph V) (B : SimpleGraph W) :
    neutralDistinguishedOrEmptyCount (graphJoin A B) =
      neutralDistinguishedOrEmptyCount A * neutralDistinguishedOrEmptyCount B :=
  by
  simpa [neutralDistinguishedOrEmptyCount] using
    Fintype.card_congr (joinNeutralDistinguishedEquiv A B).symm


-- @@ L710-713 verbatim
theorem rootedNegFaceCount_eq (G : SimpleGraph V) :
    Fintype.card (RootedNeg G) = rootedFaceCount G := by
  simpa [rootedFaceCount] using
    Fintype.card_congr (rootedPosNegEquiv G).symm


-- @@ L715-723 verbatim
/-- Every face is the top face, one of two equinumerous rooted faces, or a
neutral-or-empty face. -/
theorem hansenFaceCount_eq_strata (G : SimpleGraph V) :
    Fintype.card (HansenCombinatorialFace G) =
      1 + 2 * rootedFaceCount G + neutralOrEmptyFaceCount G := by
  rw [← Fintype.card_congr (faceStrataEquiv G)]
  simp [FaceStrataCode, rootedFaceCount, neutralOrEmptyFaceCount,
    rootedNegFaceCount_eq]
  omega


-- @@ L725-730 verbatim
/-- The actual nonempty face count is the rooted/neutral state total. -/
theorem hansenNonemptyFaceCount_eq_strata (G : SimpleGraph V) :
    hansenNonemptyFaceCount G =
      2 * rootedFaceCount G + neutralOrEmptyFaceCount G := by
  rw [hansenNonemptyFaceCount, hansenFaceCount_eq_strata]
  omega


-- @@ L732-741 expanded
/-- Exact total-cardinality recurrence supplied by the restricted-product
classification of join faces. -/
theorem hansenFaceCount_join (A : SimpleGraph V) (B : SimpleGraph W) :
    Fintype.card (HansenCombinatorialFace (graphJoin A B)) =
      1 + 2 * (rootedFaceCount A * rootedFaceCount B) +
        neutralOrEmptyFaceCount A * neutralOrEmptyFaceCount B :=
  by
  rw [← Fintype.card_congr (joinFaceCodeEquiv A B)]
  simp [JoinFaceCode, rootedFaceCount, neutralOrEmptyFaceCount, rootedNegFaceCount_eq]
  omega


-- @@ L743-755 verbatim
/-- The six-coordinate pointed state realized by intrinsic finite Hansen face
strata.  The `q` coordinate counts neutral distinguished faces with the empty
face included; consequently `t = a + q - 1` is the nonempty distinguished-
facet count. -/
noncomputable def hansenPointedFaceState (G : SimpleGraph V) :
    PointedFaceState where
  s := 2 * (rootedFaceCount G : ℤ) + (neutralOrEmptyFaceCount G : ℤ)
  r := rootedFaceCount G
  t := (cornerFaceCount G : ℤ) +
    (neutralDistinguishedOrEmptyCount G : ℤ) - 1
  a := cornerFaceCount G
  p := (rootedFaceCount G : ℤ) - (cornerFaceCount G : ℤ) + 1
  q := neutralDistinguishedOrEmptyCount G


-- @@ L757-762 verbatim
theorem hansenPointedFaceState_wellFormed (G : SimpleGraph V) :
    (hansenPointedFaceState G).WellFormed := by
  constructor
  · rfl
  · dsimp [hansenPointedFaceState]
    ring


-- @@ L764-768 verbatim
/-- The realized state's total coordinate is exactly the actual nonempty
finite Hansen face count. -/
theorem hansenPointedFaceState_s (G : SimpleGraph V) :
    (hansenPointedFaceState G).s = (hansenNonemptyFaceCount G : ℤ) := by
  simp [hansenPointedFaceState, hansenNonemptyFaceCount_eq_strata]


-- @@ L770-780 expanded
/-- All six realized coordinates obey the exact abstract join recurrence. -/
theorem hansenPointedFaceState_join (A : SimpleGraph V) (B : SimpleGraph W) :
    hansenPointedFaceState (graphJoin A B) =
      (hansenPointedFaceState A).join (hansenPointedFaceState B) :=
  by
  unfold hansenPointedFaceState PointedFaceState.join
  congr 1 <;>
      simp [rootedFaceCount_join, neutralOrEmptyFaceCount_join, cornerFaceCount_join,
        neutralDistinguishedOrEmptyCount_join] <;>
    ring


-- @@ L782-807 verbatim
/-- Hansen polarity realizes the abstract dual operation on all six concrete
face-count coordinates. -/
theorem hansenPointedFaceState_compl (G : SimpleGraph V) :
    hansenPointedFaceState Gᶜ = (hansenPointedFaceState G).dual := by
  unfold hansenPointedFaceState PointedFaceState.dual
  congr 1
  · calc
      2 * (rootedFaceCount Gᶜ : ℤ) + (neutralOrEmptyFaceCount Gᶜ : ℤ) =
          (hansenNonemptyFaceCount Gᶜ : ℤ) := by
            exact hansenPointedFaceState_s Gᶜ
      _ = (hansenNonemptyFaceCount G : ℤ) := by
            rw [hansenNonemptyFaceCount_compl]
      _ = 2 * (rootedFaceCount G : ℤ) +
          (neutralOrEmptyFaceCount G : ℤ) := (hansenPointedFaceState_s G).symm
  · exact rootedFaceCount_compl_int G
  · simpa using (rootedFaceCount_compl_int Gᶜ).symm
  · change (cornerFaceCount Gᶜ : ℤ) = (cornerFaceCount G : ℤ)
    exact_mod_cast cornerFaceCount_compl G
  · rw [rootedFaceCount_compl_int, cornerFaceCount_compl]
    ring
  · have h := rootedFaceCount_compl_int Gᶜ
    simp only [compl_compl] at h
    rw [cornerFaceCount_compl] at h
    change (neutralDistinguishedOrEmptyCount Gᶜ : ℤ) =
      (rootedFaceCount G : ℤ) - (cornerFaceCount G : ℤ) + 1
    linarith


-- @@ L809-812 expanded
theorem compl_sum_eq_join_compl (A : SimpleGraph V) (B : SimpleGraph W) :
    (A ⊕g B)ᶜ = graphJoin Aᶜ Bᶜ := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> simp


-- @@ L814-823 verbatim
/-- Disjoint graph union realizes the abstract union recurrence. -/
theorem hansenPointedFaceState_sum
    (A : SimpleGraph V) (B : SimpleGraph W) :
    hansenPointedFaceState (A ⊕g B) =
      (hansenPointedFaceState A).union (hansenPointedFaceState B) := by
  have h := hansenPointedFaceState_compl (A ⊕g B)
  rw [compl_sum_eq_join_compl, hansenPointedFaceState_join,
    hansenPointedFaceState_compl A, hansenPointedFaceState_compl B] at h
  have hd := congrArg PointedFaceState.dual h
  simpa [PointedFaceState.union] using hd.symm


-- @@ L825-825 verbatim
end HansenCombinatorialFace

-- @@ L826-826 verbatim
end HansenCograph
