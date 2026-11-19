/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.FaceFlagIncidenceClosure
import Formalisation.HansenCograph.FaceFlagCliqueIncidence
import Formalisation.HansenCograph.FaceFlagSignedLayerEvaluation
import Formalisation.HansenCograph.Invariant
import Formalisation.HansenCograph.Hansen


-- @@ L12-23 verbatim
/-!
# Labelled signed incidence for Hansen generators and clique faces

This module packages the exact signed stable-set/clique incidence relation and
connects it to the affine clique functional.  It also constructs the labelled
facets of a graph join from pairs of factor clique labels and verifies their
incidence on each embedded factor vertex.

The word `Facet` in a label name records the intended Hansen interpretation.
The theorem that these labels are the complete irredundant geometric facets
under a perfectness hypothesis remains a separate bridge.
-/


-- @@ L25-25 verbatim
open Set SimpleGraph


-- @@ L27-27 verbatim
universe u v


-- @@ L29-29 verbatim
namespace HansenCograph


-- @@ L31-35 verbatim
/-- The two signs used for Hansen vertices and clique labels. -/
inductive HansenSign : Type
  | neg
  | pos
deriving DecidableEq


-- @@ L37-39 verbatim
instance : Fintype HansenSign where
  elems := {HansenSign.neg, HansenSign.pos}
  complete sign := by cases sign <;> simp


-- @@ L41-41 verbatim
namespace HansenSign


-- @@ L43-46 verbatim
/-- Real value of a Hansen sign. -/
def real : HansenSign → ℝ
  | .neg => -1
  | .pos => 1


-- @@ L48-48 verbatim
@[simp] theorem real_neg : real .neg = (-1 : ℝ) := rfl

-- @@ L49-49 verbatim
@[simp] theorem real_pos : real .pos = (1 : ℝ) := rfl


-- @@ L51-51 verbatim
end HansenSign


-- @@ L53-53 verbatim
section Labels


-- @@ L55-55 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]


-- @@ L57-59 verbatim
/-- A finite stable set used as a Hansen vertex label. -/
abbrev StableSetLabel (G : SimpleGraph V) :=
  {s : Finset V // G.IsIndepSet (↑s : Set V)}


-- @@ L61-63 verbatim
/-- A finite clique used as a Hansen signed-facet label. -/
abbrev CliqueLabel (G : SimpleGraph V) :=
  {c : Finset V // G.IsClique (↑c : Set V)}


-- @@ L65-66 verbatim
/-- A signed stable-set generator label. -/
abbrev HansenVertexLabel (G : SimpleGraph V) := HansenSign × StableSetLabel G


-- @@ L68-69 verbatim
/-- A signed clique equality label. -/
abbrev HansenFacetLabel (G : SimpleGraph V) := HansenSign × CliqueLabel G


-- @@ L71-76 verbatim
/-- The exact finite incidence relation between signed stable-set and clique
labels. -/
def hansenLabelIncidence (G : SimpleGraph V) :
    HansenVertexLabel G → HansenFacetLabel G → Prop :=
  fun vertex facet ↦
    (facet.1 = vertex.1) ↔ (facet.2.1 ∩ vertex.2.1).Nonempty


-- @@ L78-81 verbatim
/-- The point represented by a signed stable-set label. -/
def HansenVertexLabel.point {G : SimpleGraph V} (vertex : HansenVertexLabel G) :
    ℝ × (V → ℝ) :=
  signedStableLayerPoint vertex.1.real vertex.2.1


-- @@ L83-85 verbatim
/-- The signed clique equality represented by a facet label. -/
def HansenFacetLabel.value {G : SimpleGraph V} (facet : HansenFacetLabel G) : ℝ :=
  facet.1.real


-- @@ L87-103 verbatim
/-- The labelled incidence relation agrees with equality in the signed clique
functional. -/
theorem cliqueFacetFunctional_eq_label_iff
    (G : SimpleGraph V) (vertex : HansenVertexLabel G)
    (facet : HansenFacetLabel G) :
    cliqueFacetFunctional facet.2.1 vertex.point = facet.value ↔
      hansenLabelIncidence G vertex facet := by
  rcases vertex with ⟨vertexSign, ⟨stable, hstable⟩⟩
  rcases facet with ⟨facetSign, ⟨clique, hclique⟩⟩
  have h := cliqueFacetFunctional_eq_iff G vertexSign.real facetSign.real
    clique stable hclique hstable
  cases vertexSign <;> cases facetSign <;>
    simp [HansenVertexLabel.point, HansenFacetLabel.value,
      hansenLabelIncidence, HansenSign.real,
      Finset.disjoint_iff_inter_eq_empty] at h ⊢ <;>
    norm_num at h ⊢ <;>
    exact h


-- @@ L105-110 verbatim
/-- A clique functional is nonnegative on the stable-set polytope. -/
theorem cliqueFunctional_nonneg_of_mem_stab
    (G : SimpleGraph V) (c : Finset V) {x : V → ℝ} (hx : x ∈ stab G) :
    0 ≤ cliqueFunctional c x := by
  unfold cliqueFunctional
  exact Finset.sum_nonneg (fun v _ ↦ stab_coordinate_nonneg G hx v)


-- @@ L112-132 verbatim
/-- A clique functional is at most one on the stable-set polytope. -/
theorem cliqueFunctional_le_one_of_mem_stab
    (G : SimpleGraph V) (c : Finset V)
    (hc : G.IsClique (↑c : Set V)) {x : V → ℝ} (hx : x ∈ stab G) :
    cliqueFunctional c x ≤ 1 := by
  change x ∈ {y : V → ℝ | cliqueFunctional c y ≤ 1}
  apply (convexHull_min ?_ ?_) hx
  · rintro y ⟨s, hs, rfl⟩
    change cliqueFunctional c (indicator s) ≤ 1
    rw [cliqueFunctional_indicator]
    exact_mod_cast clique_inter_indep_card_le_one G c s hc hs
  · intro y hy z hz a b ha hb hab
    change cliqueFunctional c y ≤ 1 at hy
    change cliqueFunctional c z ≤ 1 at hz
    change cliqueFunctional c (a • y + b • z) ≤ 1
    have hlinear :
        cliqueFunctional c (a • y + b • z) =
          a * cliqueFunctional c y + b * cliqueFunctional c z := by
      simp [cliqueFunctional, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hlinear]
    nlinarith


-- @@ L134-188 verbatim
/-- Every signed clique expression lies between `-1` and `1` on the Hansen
polytope.  Thus each signed clique label defines a supporting equality; facet
completeness and codimension are not asserted here. -/
theorem cliqueFacetFunctional_bounds_on_hansen
    (G : SimpleGraph V) (c : Finset V)
    (hc : G.IsClique (↑c : Set V)) {x : ℝ × (V → ℝ)}
    (hx : x ∈ hansen G) :
    -1 ≤ cliqueFacetFunctional c x ∧ cliqueFacetFunctional c x ≤ 1 := by
  constructor
  · change x ∈ {y : ℝ × (V → ℝ) | -1 ≤ cliqueFacetFunctional c y}
    apply (convexHull_min ?_ ?_) hx
    · rintro y (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · have hnonneg := cliqueFunctional_nonneg_of_mem_stab G c hp
        dsimp [cliqueFacetFunctional]
        nlinarith
      · have hle := cliqueFunctional_le_one_of_mem_stab G c hc hp
        dsimp [cliqueFacetFunctional]
        rw [show cliqueFunctional c (-p) = -cliqueFunctional c p by
          simp [cliqueFunctional]]
        nlinarith
    · intro y hy z hz a b ha hb hab
      change -1 ≤ cliqueFacetFunctional c y at hy
      change -1 ≤ cliqueFacetFunctional c z at hz
      change -1 ≤ cliqueFacetFunctional c (a • y + b • z)
      have hlinear :
          cliqueFacetFunctional c (a • y + b • z) =
            a * cliqueFacetFunctional c y + b * cliqueFacetFunctional c z := by
        simp [cliqueFacetFunctional, cliqueFunctional, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        ring
      rw [hlinear]
      nlinarith
  · change x ∈ {y : ℝ × (V → ℝ) | cliqueFacetFunctional c y ≤ 1}
    apply (convexHull_min ?_ ?_) hx
    · rintro y (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · have hle := cliqueFunctional_le_one_of_mem_stab G c hc hp
        dsimp [cliqueFacetFunctional]
        nlinarith
      · have hnonneg := cliqueFunctional_nonneg_of_mem_stab G c hp
        dsimp [cliqueFacetFunctional]
        rw [show cliqueFunctional c (-p) = -cliqueFunctional c p by
          simp [cliqueFunctional]]
        nlinarith
    · intro y hy z hz a b ha hb hab
      change cliqueFacetFunctional c y ≤ 1 at hy
      change cliqueFacetFunctional c z ≤ 1 at hz
      change cliqueFacetFunctional c (a • y + b • z) ≤ 1
      have hlinear :
          cliqueFacetFunctional c (a • y + b • z) =
            a * cliqueFacetFunctional c y + b * cliqueFacetFunctional c z := by
        simp [cliqueFacetFunctional, cliqueFunctional, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        ring
      rw [hlinear]
      nlinarith


-- @@ L190-190 verbatim
end Labels


-- @@ L192-192 verbatim
section JoinLabels


-- @@ L194-194 verbatim
variable {V : Type u} {W : Type v}

-- @@ L195-195 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L197-217 expanded
/-- The union of factor cliques is a clique in the graph join. -/
theorem join_sumFinset_clique (A : SimpleGraph V) (B : SimpleGraph W) {c : Finset V} {d : Finset W}
    (hc : A.IsClique (↑c : Set V)) (hd : B.IsClique (↑d : Set W)) :
    (graphJoin A B).IsClique (↑(sumFinset c d) : Set (V ⊕ W)) :=
  by
  intro x hx y hy hxy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact
        (graphJoin_adj_inl_inl A B x y).2
          (hc (by simpa using hx) (by simpa using hy) (fun h ↦ hxy (congrArg Sum.inl h)))
    | inr y => exact graphJoin_adj_inl_inr A B x y
  | inr x =>
    cases y with
    | inl y => exact graphJoin_adj_inr_inl A B x y
    | inr y =>
      exact
        (graphJoin_adj_inr_inr A B x y).2
          (hd (by simpa using hx) (by simpa using hy) (fun h ↦ hxy (congrArg Sum.inr h)))


-- @@ L219-235 verbatim
theorem sumFinset_inter_left_nonempty_iff
    (c s : Finset V) (d : Finset W) :
    ((sumFinset c d) ∩ sumFinset s ∅).Nonempty ↔ (c ∩ s).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    have hx' := Finset.mem_inter.mp hx
    cases x with
    | inl x =>
        exact ⟨x, Finset.mem_inter.mpr
          ⟨(inl_mem_sumFinset c d x).mp hx'.1,
            (inl_mem_sumFinset s ∅ x).mp hx'.2⟩⟩
    | inr x => simp at hx'
  · rintro ⟨x, hx⟩
    have hx' := Finset.mem_inter.mp hx
    exact ⟨Sum.inl x, Finset.mem_inter.mpr
      ⟨(inl_mem_sumFinset c d x).mpr hx'.1,
        (inl_mem_sumFinset s ∅ x).mpr hx'.2⟩⟩


-- @@ L237-253 verbatim
theorem sumFinset_inter_right_nonempty_iff
    (c : Finset V) (d s : Finset W) :
    ((sumFinset c d) ∩ sumFinset ∅ s).Nonempty ↔ (d ∩ s).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    have hx' := Finset.mem_inter.mp hx
    cases x with
    | inl x => simp at hx'
    | inr x =>
        exact ⟨x, Finset.mem_inter.mpr
          ⟨(inr_mem_sumFinset c d x).mp hx'.1,
            (inr_mem_sumFinset ∅ s x).mp hx'.2⟩⟩
  · rintro ⟨x, hx⟩
    have hx' := Finset.mem_inter.mp hx
    exact ⟨Sum.inr x, Finset.mem_inter.mpr
      ⟨(inr_mem_sumFinset c d x).mpr hx'.1,
        (inr_mem_sumFinset ∅ s x).mpr hx'.2⟩⟩


-- @@ L255-259 verbatim
@[simp]
theorem sumLeftPart_sumFinset_faceflag (c : Finset V) (d : Finset W) :
    sumLeftPart (sumFinset c d) = c := by
  ext x
  simp [sumLeftPart, sumFinset]


-- @@ L261-265 verbatim
@[simp]
theorem sumRightPart_sumFinset_faceflag (c : Finset V) (d : Finset W) :
    sumRightPart (sumFinset c d) = d := by
  ext x
  simp [sumRightPart, sumFinset]


-- @@ L267-271 verbatim
@[simp]
theorem sumFinset_sumParts_faceflag (c : Finset (V ⊕ W)) :
    sumFinset (sumLeftPart c) (sumRightPart c) = c := by
  ext x
  cases x <;> simp [sumLeftPart, sumRightPart, sumFinset]


-- @@ L273-281 expanded
/-- Restrict a graph-join clique to its left vertex type. -/
theorem join_left_clique (A : SimpleGraph V) (B : SimpleGraph W) {c : Finset (V ⊕ W)}
    (hc : (graphJoin A B).IsClique (↑c : Set (V ⊕ W))) : A.IsClique (↑(sumLeftPart c) : Set V) :=
  by
  intro x hx y hy hxy
  exact
    (graphJoin_adj_inl_inl A B x y).mp
      (hc (by simpa using hx) (by simpa using hy) (fun h ↦ hxy (Sum.inl_injective h)))


-- @@ L283-291 expanded
/-- Restrict a graph-join clique to its right vertex type. -/
theorem join_right_clique (A : SimpleGraph V) (B : SimpleGraph W) {c : Finset (V ⊕ W)}
    (hc : (graphJoin A B).IsClique (↑c : Set (V ⊕ W))) : B.IsClique (↑(sumRightPart c) : Set W) :=
  by
  intro x hx y hy hxy
  exact
    (graphJoin_adj_inr_inr A B x y).mp
      (hc (by simpa using hx) (by simpa using hy) (fun h ↦ hxy (Sum.inr_injective h)))


-- @@ L293-297 expanded
/-- Embed a left factor stable label into a graph-join stable label. -/
def joinVertexLabelLeft (A : SimpleGraph V) (B : SimpleGraph W) (vertex : HansenVertexLabel A) :
    HansenVertexLabel (graphJoin A B) :=
  ⟨vertex.1, ⟨sumFinset vertex.2.1 ∅, join_sumFinset_left_indep A B vertex.2.2⟩⟩


-- @@ L299-303 expanded
/-- Embed a right factor stable label into a graph-join stable label. -/
def joinVertexLabelRight (A : SimpleGraph V) (B : SimpleGraph W) (vertex : HansenVertexLabel B) :
    HansenVertexLabel (graphJoin A B) :=
  ⟨vertex.1, ⟨sumFinset ∅ vertex.2.1, join_sumFinset_right_indep A B vertex.2.2⟩⟩


-- @@ L305-343 expanded
/-- Every signed stable-set label of a graph join comes from at least one
factor.  The empty stable set has one preimage in each factor; this harmless
duplication is why the abstract join incidence uses a sum rather than an
equivalence of vertex labels. -/
theorem joinVertexLabel_left_or_right (A : SimpleGraph V) (B : SimpleGraph W)
    (vertex : HansenVertexLabel (graphJoin A B)) :
    (∃ left : HansenVertexLabel A, joinVertexLabelLeft A B left = vertex) ∨
      (∃ right : HansenVertexLabel B, joinVertexLabelRight A B right = vertex) :=
  by
  by_cases hleft : sumLeftPart vertex.2.1 = ∅
  · right
    let right : HansenVertexLabel B :=
      ⟨vertex.1, ⟨sumRightPart vertex.2.1, join_right_indep A B vertex.2.2⟩⟩
    refine ⟨right, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change sumFinset ∅ (sumRightPart vertex.2.1) = vertex.2.1
      calc
        sumFinset ∅ (sumRightPart vertex.2.1) =
            sumFinset (sumLeftPart vertex.2.1) (sumRightPart vertex.2.1) :=
          (congrArg (fun left ↦ sumFinset left (sumRightPart vertex.2.1)) hleft).symm
        _ = vertex.2.1 := sumFinset_sumParts_faceflag vertex.2.1
  · left
    have hright : sumRightPart vertex.2.1 = ∅ := join_indep_right_empty A B vertex.2.2 hleft
    let left : HansenVertexLabel A :=
      ⟨vertex.1, ⟨sumLeftPart vertex.2.1, join_left_indep A B vertex.2.2⟩⟩
    refine ⟨left, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change sumFinset (sumLeftPart vertex.2.1) ∅ = vertex.2.1
      calc
        sumFinset (sumLeftPart vertex.2.1) ∅ =
            sumFinset (sumLeftPart vertex.2.1) (sumRightPart vertex.2.1) :=
          (congrArg (sumFinset (sumLeftPart vertex.2.1)) hright).symm
        _ = vertex.2.1 := sumFinset_sumParts_faceflag vertex.2.1


-- @@ L345-349 expanded
/-- Map the duplicated factor-vertex sum to the graph-join vertex labels. -/
def joinVertexLabelMap (A : SimpleGraph V) (B : SimpleGraph W) :
    HansenVertexLabel A ⊕ HansenVertexLabel B → HansenVertexLabel (graphJoin A B)
  | Sum.inl vertex => joinVertexLabelLeft A B vertex
  | Sum.inr vertex => joinVertexLabelRight A B vertex


-- @@ L351-356 verbatim
theorem joinVertexLabelMap_surjective (A : SimpleGraph V) (B : SimpleGraph W) :
    Function.Surjective (joinVertexLabelMap A B) := by
  intro vertex
  rcases joinVertexLabel_left_or_right A B vertex with ⟨left, hleft⟩ | ⟨right, hright⟩
  · exact ⟨Sum.inl left, hleft⟩
  · exact ⟨Sum.inr right, hright⟩


-- @@ L358-365 expanded
/-- Combine two same-sign factor clique labels into a graph-join clique label. -/
def joinFacetLabel (A : SimpleGraph V) (B : SimpleGraph W)
    (facet :
      SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1)) :
    HansenFacetLabel (graphJoin A B) :=
  ⟨facet.1.1.1,
    ⟨sumFinset facet.1.1.2.1 facet.1.2.2.1, join_sumFinset_clique A B facet.1.1.2.2 facet.1.2.2.2⟩⟩


-- @@ L367-376 expanded
/-- Split a graph-join clique label into its two same-sign factor labels. -/
noncomputable def splitJoinFacetLabel (A : SimpleGraph V) (B : SimpleGraph W)
    (facet : HansenFacetLabel (graphJoin A B)) :
    SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1) :=
  ⟨(⟨facet.1, ⟨sumLeftPart facet.2.1, join_left_clique A B facet.2.2⟩⟩,
      ⟨facet.1, ⟨sumRightPart facet.2.1, join_right_clique A B facet.2.2⟩⟩),
    rfl⟩


-- @@ L378-393 verbatim
theorem splitJoinFacetLabel_joinFacetLabel
    (A : SimpleGraph V) (B : SimpleGraph W)
    (facet : SignedJoinFacet
      (fun f : HansenFacetLabel A ↦ f.1)
      (fun f : HansenFacetLabel B ↦ f.1)) :
    splitJoinFacetLabel A B (joinFacetLabel A B facet) = facet := by
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact sumLeftPart_sumFinset_faceflag _ _
  · apply Prod.ext
    · exact facet.2
    · apply Subtype.ext
      exact sumRightPart_sumFinset_faceflag _ _


-- @@ L395-402 expanded
theorem joinFacetLabel_splitJoinFacetLabel (A : SimpleGraph V) (B : SimpleGraph W)
    (facet : HansenFacetLabel (graphJoin A B)) :
    joinFacetLabel A B (splitJoinFacetLabel A B facet) = facet :=
  by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact sumFinset_sumParts_faceflag _


-- @@ L404-414 expanded
/-- Signed clique labels of a graph join are exactly same-sign pairs of
factor clique labels. -/
noncomputable def joinFacetLabelEquiv (A : SimpleGraph V) (B : SimpleGraph W) :
    SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1) ≃
      HansenFacetLabel (graphJoin A B)
    where
  toFun := joinFacetLabel A B
  invFun := splitJoinFacetLabel A B
  left_inv := splitJoinFacetLabel_joinFacetLabel A B
  right_inv := joinFacetLabel_splitJoinFacetLabel A B


-- @@ L416-427 expanded
/-- Incidence on an embedded left vertex ignores the right facet component. -/
theorem hansenLabelIncidence_join_left (A : SimpleGraph V) (B : SimpleGraph W)
    (vertex : HansenVertexLabel A)
    (facet :
      SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1)) :
    hansenLabelIncidence (graphJoin A B) (joinVertexLabelLeft A B vertex)
        (joinFacetLabel A B facet) ↔
      hansenLabelIncidence A vertex facet.1.1 :=
  by
  simp [hansenLabelIncidence, joinVertexLabelLeft, joinFacetLabel,
    sumFinset_inter_left_nonempty_iff]


-- @@ L429-441 expanded
/-- Incidence on an embedded right vertex ignores the left facet component. -/
theorem hansenLabelIncidence_join_right (A : SimpleGraph V) (B : SimpleGraph W)
    (vertex : HansenVertexLabel B)
    (facet :
      SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1)) :
    hansenLabelIncidence (graphJoin A B) (joinVertexLabelRight A B vertex)
        (joinFacetLabel A B facet) ↔
      hansenLabelIncidence B vertex facet.1.2 :=
  by
  have hsign : facet.1.1.1 = facet.1.2.1 := facet.2
  simp [hansenLabelIncidence, joinVertexLabelRight, joinFacetLabel,
    sumFinset_inter_right_nonempty_iff, hsign]


-- @@ L443-457 expanded
/-- The concrete labelled join incidence is the abstract same-sign fibre
product incidence after applying the vertex map and facet equivalence. -/
theorem hansenLabelIncidence_join_map (A : SimpleGraph V) (B : SimpleGraph W)
    (vertex : HansenVertexLabel A ⊕ HansenVertexLabel B)
    (facet :
      SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1)) :
    hansenLabelIncidence (graphJoin A B) (joinVertexLabelMap A B vertex)
        (joinFacetLabel A B facet) ↔
      signedJoinIncidence (hansenLabelIncidence A) (hansenLabelIncidence B) vertex facet :=
  by
  cases vertex with
  | inl vertex => exact hansenLabelIncidence_join_left A B vertex facet
  | inr vertex => exact hansenLabelIncidence_join_right A B vertex facet


-- @@ L459-488 expanded
/-- Exact common-facet closure transfer for the labelled Hansen incidence of
a graph join.  This is the finite Galois-closure theorem before identifying
closed label sets with geometric faces. -/
theorem hansenJoinFacetClosure_preimage (A : SimpleGraph V) (B : SimpleGraph W)
    (T :
      Set (SignedJoinFacet (fun f : HansenFacetLabel A ↦ f.1) (fun f : HansenFacetLabel B ↦ f.1))) :
    (joinFacetLabelEquiv A B) ⁻¹'
        incidenceClosure (hansenLabelIncidence (graphJoin A B)) ((joinFacetLabelEquiv A B) '' T) =
      sameSignFacetProduct (incidenceClosure (hansenLabelIncidence A) (joinFacetProjLeft T))
        (incidenceClosure (hansenLabelIncidence B) (joinFacetProjRight T)) :=
  by
  calc
    (joinFacetLabelEquiv A B) ⁻¹'
          incidenceClosure (hansenLabelIncidence (graphJoin A B)) ((joinFacetLabelEquiv A B) '' T) =
        incidenceClosure (signedJoinIncidence (hansenLabelIncidence A) (hansenLabelIncidence B))
          T :=
      incidenceClosure_preimage_equiv
        (signedJoinIncidence (hansenLabelIncidence A) (hansenLabelIncidence B))
        (hansenLabelIncidence (graphJoin A B)) (joinVertexLabelMap A B) (joinFacetLabelEquiv A B)
        (joinVertexLabelMap_surjective A B)
        (fun vertex facet ↦ hansenLabelIncidence_join_map A B vertex facet) T
    _ =
        sameSignFacetProduct (incidenceClosure (hansenLabelIncidence A) (joinFacetProjLeft T))
          (incidenceClosure (hansenLabelIncidence B) (joinFacetProjRight T)) :=
      joinFacetClosure_eq (hansenLabelIncidence A) (hansenLabelIncidence B) T


-- @@ L490-490 verbatim
end JoinLabels


-- @@ L492-492 verbatim
end HansenCograph
