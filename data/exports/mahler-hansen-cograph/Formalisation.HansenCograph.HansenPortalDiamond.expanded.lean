/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenJoinPortalUpperIntervals
import Formalisation.HansenCograph.HansenFaceState


-- @@ L9-16 verbatim
/-!
# Local diamond switches at Hansen portals

For portal-vector monotonicity one does not need thinness of every rank-two
interval.  The required local statement says that a neutral-to-positive
portal followed by a positive cover has a unique alternative neutral middle
face.  This file proves that this local property is preserved by graph join.
-/


-- @@ L18-18 verbatim
open Set SimpleGraph


-- @@ L20-20 verbatim
namespace HansenCograph

-- @@ L21-21 verbatim
namespace HansenCombinatorialFace


-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
variable {V : Type u} {W : Type v}

-- @@ L26-26 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L28-33 verbatim
/-- The local rank-two square needed to move a positive portal one rank
upwards. -/
def PositivePortalSquare (G : SimpleGraph V) : Prop :=
  ∀ (E : NeutralOrEmpty G) (F H : RootedPos G),
    E.1 ⋖ F.1 → F.1 ⋖ H.1 →
      ∃! E' : NeutralOrEmpty G, E.1 ⋖ E'.1 ∧ E'.1 ⋖ H.1


-- @@ L35-41 verbatim
/-- In the same local interval, the original positive-rooted middle is the
unique positive-rooted middle.  This is the reverse uniqueness needed to
recover a source after switching to the neutral middle. -/
def RootedPortalMiddleUnique (G : SimpleGraph V) : Prop :=
  ∀ (E : NeutralOrEmpty G) (F H : RootedPos G),
    E.1 ⋖ F.1 → F.1 ⋖ H.1 →
      ∀ F' : RootedPos G, E.1 ⋖ F'.1 ∧ F'.1 ⋖ H.1 → F' = F


-- @@ L43-46 verbatim
/-- A portal square with uniqueness on both sides: exactly one neutral and
exactly one positive-rooted middle face. -/
def PairedPositivePortalSquare (G : SimpleGraph V) : Prop :=
  PositivePortalSquare G ∧ RootedPortalMiddleUnique G


-- @@ L48-54 verbatim
/-- The polarity-dual local square.  Under `hansenFaceComplOrderIso`, rooted
faces of the complementary graph are nonempty faces in a distinguished
facet of the original graph, and the order is reversed.  Keeping this as the
complementary portal statement makes that transport exact without duplicating
four facet-membership subtypes. -/
def PositiveDistinguishedFacetSquare (G : SimpleGraph V) : Prop :=
  PositivePortalSquare Gᶜ


-- @@ L56-59 verbatim
/-- The two-sided polarity-dual square required to transport an injective
switch through graph complementation. -/
def PairedPositiveDistinguishedFacetSquare (G : SimpleGraph V) : Prop :=
  PairedPositivePortalSquare Gᶜ


-- @@ L61-66 verbatim
/-- The coupled local-square invariant stable under both cotree operations.
The first component controls crossings of the apex; the second controls the
polarity-dual crossing of a distinguished facet. -/
def HansenPairedSquareState (G : SimpleGraph V) : Prop :=
  PairedPositivePortalSquare G ∧
    PairedPositiveDistinguishedFacetSquare G


-- @@ L68-74 verbatim
omit [Fintype V] in
theorem hansenPairedSquareState_compl_iff (G : SimpleGraph V) :
    HansenPairedSquareState Gᶜ ↔ HansenPairedSquareState G := by
  change (PairedPositivePortalSquare Gᶜ ∧
      PairedPositivePortalSquare Gᶜᶜ) ↔
    (PairedPositivePortalSquare G ∧ PairedPositivePortalSquare Gᶜ)
  simpa only [compl_compl, and_comm]


-- @@ L76-110 verbatim
/-- Central symmetry followed by Hansen polarity, packaged as the
order-reversing equivalence which sends positive-rooted faces to faces in the
positive distinguished facet. -/
noncomputable def centralDualFaceOrderIso (G : SimpleGraph V) :
    OrderDual (HansenCombinatorialFace G) ≃o
      HansenCombinatorialFace Gᶜ where
  toFun F := hansenFaceDualEquiv G (hansenCentralFaceEquiv G F)
  invFun F := hansenCentralFaceEquiv G ((hansenFaceDualEquiv G).symm F)
  left_inv F := by
    change hansenCentralFaceEquiv G
      ((hansenFaceDualEquiv G).symm
        (hansenFaceDualEquiv G (hansenCentralFaceEquiv G F))) = F
    rw [(hansenFaceDualEquiv G).symm_apply_apply]
    exact hansenCentralFaceEquiv_involutive G F
  right_inv F := by
    change hansenFaceDualEquiv G
      (hansenCentralFaceEquiv G
        (hansenCentralFaceEquiv G ((hansenFaceDualEquiv G).symm F))) = F
    rw [hansenCentralFaceEquiv_involutive]
    exact (hansenFaceDualEquiv G).apply_symm_apply F
  map_rel_iff' := by
    intro F H
    change (hansenFaceComplOrderIso G)
          (show OrderDual (HansenCombinatorialFace G) from
            hansenCentralFaceEquiv G (show HansenCombinatorialFace G from F)) ≤
        (hansenFaceComplOrderIso G)
          (show OrderDual (HansenCombinatorialFace G) from
            hansenCentralFaceEquiv G (show HansenCombinatorialFace G from H)) ↔
      @LE.le (OrderDual (HansenCombinatorialFace G)) _ F H
    rw [map_le_map_iff (hansenFaceComplOrderIso G)]
    change hansenCentralFaceEquiv G (show HansenCombinatorialFace G from H) ≤
        hansenCentralFaceEquiv G (show HansenCombinatorialFace G from F) ↔
      (show HansenCombinatorialFace G from H) ≤
        (show HansenCombinatorialFace G from F)
    exact map_le_map_iff (hansenCentralFaceOrderIso G)


-- @@ L112-114 verbatim
/-- The empty-clique facet opposite the negative apex. -/
def negativeDistinguishedFacet (G : SimpleGraph V) : HansenFacetLabel G :=
  emptyHansenFacet G HansenSign.pos


-- @@ L116-120 verbatim
/-- Faces lying in neither of the two distinguished facets. -/
def IsOutsideDistinguishedFacets {G : SimpleGraph V}
    (F : HansenCombinatorialFace G) : Prop :=
  positiveDistinguishedFacet G ∉ (F : Set (HansenFacetLabel G)) ∧
    negativeDistinguishedFacet G ∉ (F : Set (HansenFacetLabel G))


-- @@ L122-125 verbatim
/-- The facet-side neutral stratum exchanged with `NeutralOrEmpty` by
central symmetry followed by Hansen polarity. -/
abbrev OutsideDistinguishedFacets (G : SimpleGraph V) :=
  {F : HansenCombinatorialFace G // F.IsOutsideDistinguishedFacets}


-- @@ L127-145 verbatim
/-- A face contained in both opposite distinguished facets is empty. -/
theorem eq_bottom_of_mem_both_distinguished {G : SimpleGraph V}
    (F : HansenCombinatorialFace G)
    (hpos : positiveDistinguishedFacet G ∈ (F : Set _))
    (hneg : negativeDistinguishedFacet G ∈ (F : Set _)) :
    F = bottom G := by
  apply IncidenceClosedSet.ext
  change F.carrier = Set.univ
  apply Set.eq_univ_iff_forall.mpr
  intro facet
  change facet ∈ F.carrier
  rw [← F.isClosed]
  intro vertex hvertex
  have hp := hvertex (positiveDistinguishedFacet G) hpos
  have hn := hvertex (negativeDistinguishedFacet G) hneg
  rcases vertex with ⟨sign, stable⟩
  cases sign <;>
    simp [positiveDistinguishedFacet, negativeDistinguishedFacet,
      emptyHansenFacet, hansenLabelIncidence] at hp hn


-- @@ L147-153 verbatim
/-- A nonempty face in the positive distinguished facet is not in the
opposite distinguished facet. -/
theorem DistinguishedNonemptyFace.not_mem_negativeDistinguishedFacet
    {G : SimpleGraph V} (F : DistinguishedNonemptyFace G) :
    negativeDistinguishedFacet G ∉ (F.1.1 : Set _) := by
  intro hneg
  exact F.2 (eq_bottom_of_mem_both_distinguished F.1.1 F.1.2 hneg)


-- @@ L155-159 verbatim
omit [Fintype V] in
@[simp] theorem positiveDistinguishedFacetSquare_compl_iff
    (G : SimpleGraph V) :
    PositiveDistinguishedFacetSquare Gᶜ ↔ PositivePortalSquare G := by
  simp [PositiveDistinguishedFacetSquare]


-- @@ L161-165 verbatim
omit [Fintype V] in
@[simp] theorem positivePortalSquare_compl_iff
    (G : SimpleGraph V) :
    PositivePortalSquare Gᶜ ↔ PositiveDistinguishedFacetSquare G := by
  rfl


-- @@ L167-172 verbatim
omit [Fintype V] in
@[simp] theorem pairedPositiveDistinguishedFacetSquare_compl_iff
    (G : SimpleGraph V) :
    PairedPositiveDistinguishedFacetSquare Gᶜ ↔
      PairedPositivePortalSquare G := by
  simp [PairedPositiveDistinguishedFacetSquare]


-- @@ L174-179 verbatim
omit [Fintype V] in
@[simp] theorem pairedPositivePortalSquare_compl_iff
    (G : SimpleGraph V) :
    PairedPositivePortalSquare Gᶜ ↔
      PairedPositiveDistinguishedFacetSquare G := by
  rfl


-- @@ L181-202 verbatim
/-- Covers between positive-rooted faces can be checked either in the full
face poset or in the positive-rooted subtype. -/
theorem rootedPos_covBy_val_iff {G : SimpleGraph V} (F H : RootedPos G) :
    F.1 ⋖ H.1 ↔ F ⋖ H := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro X hFX hXH
    exact h.2 hFX hXH
  · intro h
    apply covBy_of_eq_or_eq
    · exact h.1
    · intro X hFX hXH
      have hXtop : X ≠ top G := by
        intro htop
        apply H.2.ne_top
        rw [htop] at hXH
        exact top_unique hXH
      let X' : RootedPos G := ⟨X, F.2.upper_of_ne_top hFX hXtop⟩
      rcases h.eq_or_eq (show F ≤ X' from hFX) (show X' ≤ H from hXH) with hXF | hXH'
      · exact Or.inl (congrArg Subtype.val hXF)
      · exact Or.inr (congrArg Subtype.val hXH')


-- @@ L204-220 verbatim
/-- Covers between neutral-or-empty faces can be checked either in the full
face poset or in the neutral subtype. -/
theorem neutral_covBy_val_iff {G : SimpleGraph V}
    (E L : NeutralOrEmpty G) : E.1 ⋖ L.1 ↔ E ⋖ L := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro X hEX hXL
    exact h.2 hEX hXL
  · intro h
    apply covBy_of_eq_or_eq
    · exact h.1
    · intro X hEX hXL
      let X' : NeutralOrEmpty G := ⟨X, L.2.lower hXL⟩
      rcases h.eq_or_eq (show E ≤ X' from hEX) (show X' ≤ L from hXL) with hXE | hXL'
      · exact Or.inl (congrArg Subtype.val hXE)
      · exact Or.inr (congrArg Subtype.val hXL')


-- @@ L222-227 verbatim
private theorem not_covBy_of_two_covers {P : Type*} [PartialOrder P]
    {a b c : P} (hab : a ⋖ b) (hbc : b ⋖ c) : ¬a ⋖ c := by
  intro hac
  rcases hac.eq_or_eq hab.le hbc.le with hab' | hbc'
  · exact hab.ne hab'.symm
  · exact hbc.ne hbc'


-- @@ L229-331 expanded
/-- Positive portal squares in both factors assemble to a positive portal
square in their graph join. -/
theorem PositivePortalSquare.join (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : PositivePortalSquare A) (hB : PositivePortalSquare B) :
    PositivePortalSquare (graphJoin A B) :=
  by
  intro E F H hEF hFH
  let eN := joinNeutralOrderIso A B
  let eP := joinRootedPosOrderIso A B
  let e : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm E
  let f : RootedPos A × RootedPos B := eP.symm F
  let h : RootedPos A × RootedPos B := eP.symm H
  have hErep : joinNeutral A B e.1 e.2 = E.1 := by
    exact congrArg Subtype.val (eN.apply_symm_apply E)
  have hFrep : joinRootedPos A B f.1 f.2 = F.1 := by
    exact congrArg Subtype.val (eP.apply_symm_apply F)
  have hHrep : joinRootedPos A B h.1 h.2 = H.1 := by
    exact congrArg Subtype.val (eP.apply_symm_apply H)
  have hportal : e.1.1 ⋖ f.1.1 ∧ e.2.1 ⋖ f.2.1 :=
    by
    apply (joinPortal_covBy_iff A B e.1 e.2 f.1 f.2).mp
    simpa only [hErep, hFrep] using hEF
  have hFHsub : F ⋖ H := (rootedPos_covBy_val_iff F H).mp hFH
  have hfh : f ⋖ h := by exact (apply_covBy_apply_iff eP.symm).mpr hFHsub
  rcases Prod.covBy_iff.mp hfh with hleft | hright
  · obtain ⟨E'A, hE'A, huniqA⟩ :=
      hA e.1 f.1 h.1 hportal.1 ((rootedPos_covBy_val_iff f.1 h.1).mpr hleft.1)
    let E' : NeutralOrEmpty (graphJoin A B) := eN (E'A, e.2)
    refine ⟨E', ?_, ?_⟩
    · constructor
      · apply (neutral_covBy_val_iff E E').mpr
        have hp : e ⋖ (E'A, e.2) :=
          Prod.covBy_iff.mpr (Or.inl ⟨(neutral_covBy_val_iff e.1 E'A).mp hE'A.1, rfl⟩)
        have heN : eN e = E := eN.apply_symm_apply E
        rw [← heN]
        exact (apply_covBy_apply_iff eN).mpr hp
      · have heq : f.2 = h.2 := hleft.2
        rw [← hHrep]
        change E'.1 ⋖ joinRootedPos A B h.1 h.2
        change joinNeutral A B E'A e.2 ⋖ joinRootedPos A B h.1 h.2
        apply joinPortal_covBy_of_factors
        · exact hE'A.2
        · simpa only [← heq] using hportal.2
    · intro X hX
      let x : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm X
      have hXrep : joinNeutral A B x.1 x.2 = X.1 := by
        exact congrArg Subtype.val (eN.apply_symm_apply X)
      have hEXsub : E ⋖ X := (neutral_covBy_val_iff E X).mp hX.1
      have hex : e ⋖ x := (apply_covBy_apply_iff eN.symm).mpr hEXsub
      have hxportal : x.1.1 ⋖ h.1.1 ∧ x.2.1 ⋖ h.2.1 :=
        by
        apply (joinPortal_covBy_iff A B x.1 x.2 h.1 h.2).mp
        simpa only [hXrep, hHrep] using hX.2
      rcases Prod.covBy_iff.mp hex with hxleft | hxright
      · have hxA : x.1 = E'A :=
          huniqA x.1 ⟨(neutral_covBy_val_iff e.1 x.1).mpr hxleft.1, hxportal.1⟩
        calc
          X = eN x := (eN.apply_symm_apply X).symm
          _ = eN (E'A, e.2) := (congrArg eN (Prod.ext hxA hxleft.2.symm))
          _ = E' := rfl
      · exfalso
        apply not_covBy_of_two_covers hportal.1 ((rootedPos_covBy_val_iff f.1 h.1).mpr hleft.1)
        simpa only [← hxright.2] using hxportal.1
  · obtain ⟨E'B, hE'B, huniqB⟩ :=
      hB e.2 f.2 h.2 hportal.2 ((rootedPos_covBy_val_iff f.2 h.2).mpr hright.1)
    let E' : NeutralOrEmpty (graphJoin A B) := eN (e.1, E'B)
    refine ⟨E', ?_, ?_⟩
    · constructor
      · apply (neutral_covBy_val_iff E E').mpr
        have hp : e ⋖ (e.1, E'B) :=
          Prod.covBy_iff.mpr (Or.inr ⟨(neutral_covBy_val_iff e.2 E'B).mp hE'B.1, rfl⟩)
        have heN : eN e = E := eN.apply_symm_apply E
        rw [← heN]
        exact (apply_covBy_apply_iff eN).mpr hp
      · have heq : f.1 = h.1 := hright.2
        rw [← hHrep]
        change E'.1 ⋖ joinRootedPos A B h.1 h.2
        change joinNeutral A B e.1 E'B ⋖ joinRootedPos A B h.1 h.2
        apply joinPortal_covBy_of_factors
        · simpa only [← heq] using hportal.1
        · exact hE'B.2
    · intro X hX
      let x : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm X
      have hXrep : joinNeutral A B x.1 x.2 = X.1 := by
        exact congrArg Subtype.val (eN.apply_symm_apply X)
      have hEXsub : E ⋖ X := (neutral_covBy_val_iff E X).mp hX.1
      have hex : e ⋖ x := (apply_covBy_apply_iff eN.symm).mpr hEXsub
      have hxportal : x.1.1 ⋖ h.1.1 ∧ x.2.1 ⋖ h.2.1 :=
        by
        apply (joinPortal_covBy_iff A B x.1 x.2 h.1 h.2).mp
        simpa only [hXrep, hHrep] using hX.2
      rcases Prod.covBy_iff.mp hex with hxleft | hxright
      · exfalso
        apply not_covBy_of_two_covers hportal.2 ((rootedPos_covBy_val_iff f.2 h.2).mpr hright.1)
        simpa only [← hxleft.2] using hxportal.2
      · have hxB : x.2 = E'B :=
          huniqB x.2 ⟨(neutral_covBy_val_iff e.2 x.2).mpr hxright.1, hxportal.2⟩
        calc
          X = eN x := (eN.apply_symm_apply X).symm
          _ = eN (e.1, E'B) := (congrArg eN (Prod.ext hxright.2.symm hxB))
          _ = E' := rfl


-- @@ L333-391 expanded
/-- Reverse uniqueness of the positive middle is also preserved by graph
join. -/
theorem RootedPortalMiddleUnique.join (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : RootedPortalMiddleUnique A) (hB : RootedPortalMiddleUnique B) :
    RootedPortalMiddleUnique (graphJoin A B) :=
  by
  intro E F H hEF hFH X hX
  let eN := joinNeutralOrderIso A B
  let eP := joinRootedPosOrderIso A B
  let e : NeutralOrEmpty A × NeutralOrEmpty B := eN.symm E
  let f : RootedPos A × RootedPos B := eP.symm F
  let h : RootedPos A × RootedPos B := eP.symm H
  let x : RootedPos A × RootedPos B := eP.symm X
  have hErep : joinNeutral A B e.1 e.2 = E.1 := by
    exact congrArg Subtype.val (eN.apply_symm_apply E)
  have hFrep : joinRootedPos A B f.1 f.2 = F.1 := by
    exact congrArg Subtype.val (eP.apply_symm_apply F)
  have hHrep : joinRootedPos A B h.1 h.2 = H.1 := by
    exact congrArg Subtype.val (eP.apply_symm_apply H)
  have hXrep : joinRootedPos A B x.1 x.2 = X.1 := by
    exact congrArg Subtype.val (eP.apply_symm_apply X)
  have hef : e.1.1 ⋖ f.1.1 ∧ e.2.1 ⋖ f.2.1 :=
    by
    apply (joinPortal_covBy_iff A B e.1 e.2 f.1 f.2).mp
    simpa only [hErep, hFrep] using hEF
  have hex : e.1.1 ⋖ x.1.1 ∧ e.2.1 ⋖ x.2.1 :=
    by
    apply (joinPortal_covBy_iff A B e.1 e.2 x.1 x.2).mp
    simpa only [hErep, hXrep] using hX.1
  have hfh : f ⋖ h := by
    apply (apply_covBy_apply_iff eP.symm).mpr
    exact (rootedPos_covBy_val_iff F H).mp hFH
  have hxh : x ⋖ h := by
    apply (apply_covBy_apply_iff eP.symm).mpr
    exact (rootedPos_covBy_val_iff X H).mp hX.2
  rcases Prod.covBy_iff.mp hfh with hfleft | hfright
  · rcases Prod.covBy_iff.mp hxh with hxleft | hxright
    · have hxA : x.1 = f.1 :=
        hA e.1 f.1 h.1 hef.1 ((rootedPos_covBy_val_iff f.1 h.1).mpr hfleft.1) x.1
          ⟨hex.1, (rootedPos_covBy_val_iff x.1 h.1).mpr hxleft.1⟩
      calc
        X = eP x := (eP.apply_symm_apply X).symm
        _ = eP f := (congrArg eP (Prod.ext hxA (hxleft.2.trans hfleft.2.symm)))
        _ = F := eP.apply_symm_apply F
    · exfalso
      apply not_covBy_of_two_covers hef.1 ((rootedPos_covBy_val_iff f.1 h.1).mpr hfleft.1)
      simpa only [← hxright.2] using hex.1
  · rcases Prod.covBy_iff.mp hxh with hxleft | hxright
    · exfalso
      apply not_covBy_of_two_covers hef.2 ((rootedPos_covBy_val_iff f.2 h.2).mpr hfright.1)
      simpa only [← hxleft.2] using hex.2
    · have hxB : x.2 = f.2 :=
        hB e.2 f.2 h.2 hef.2 ((rootedPos_covBy_val_iff f.2 h.2).mpr hfright.1) x.2
          ⟨hex.2, (rootedPos_covBy_val_iff x.2 h.2).mpr hxright.1⟩
      calc
        X = eP x := (eP.apply_symm_apply X).symm
        _ = eP f := (congrArg eP (Prod.ext (hxright.2.trans hfright.2.symm) hxB))
        _ = F := eP.apply_symm_apply F


-- @@ L393-399 expanded
/-- The two-sided local portal-square invariant is closed under graph join. -/
theorem PairedPositivePortalSquare.join (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : PairedPositivePortalSquare A) (hB : PairedPositivePortalSquare B) :
    PairedPositivePortalSquare (graphJoin A B) :=
  ⟨hA.1.join A B hB.1, hA.2.join A B hB.2⟩


-- @@ L401-401 verbatim
end HansenCombinatorialFace

-- @@ L402-402 verbatim
end HansenCograph
