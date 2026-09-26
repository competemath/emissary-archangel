/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil


-- @@ L19-33 verbatim
/-!
# Testing Graph Invariants

This file contains tests for graph invariants on 5 specific concrete graphs:
1. `HouseGraph`: A graph on 5 vertices.
2. `K4`: The complete graph on 4 vertices.
3. `PetersenGraph`: The Petersen graph on 10 vertices.
4. `C6`: The cycle graph on 6 vertices.
5. `Star5`: The star graph with 5 leaves (6 vertices total).

Tests cover:
independence_number, dominationNumber, average_distance, diameter, radius,
girth, order, size, szeged_index, wiener_index, min_degree, max_degree,
average_degree, matching_number, residue, annihilation_number, cvetkovic.
-/


-- @@ L35-35 verbatim
open SimpleGraph


-- @@ L37-44 verbatim
namespace WrittenOnTheWallII.Test


-- Bridge theorems for Sym2/edist-based invariants:
-- All 6 (indep_num, dom_num, dist, wiener, avg_dist, szeged) are proved in
-- FormalConjecturesForMathlib/.../Invariants.lean and exported via that module.

/-  ### Graph Definitions -/


-- @@ L46-51 verbatim
/-- House Graph: Square 0-1-2-3-0 with roof 4 connected to 2,3. -/
abbrev HouseGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 3), s(3, 0),
    s(2, 4), s(3, 4)
  }


-- @@ L53-54 verbatim
/-- K4: Complete graph on 4 vertices. -/
abbrev K4 : SimpleGraph (Fin 4) := completeGraph (Fin 4)


-- @@ L56-65 verbatim
/-- Petersen Graph on 10 vertices. -/
abbrev PetersenGraph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromEdgeSet {
    -- Outer Cycle
    s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0),
    -- Spokes
    s(0, 5), s(1, 6), s(2, 7), s(3, 8), s(4, 9),
    -- Inner Star
    s(5, 7), s(7, 9), s(9, 6), s(6, 8), s(8, 5)
  }


-- @@ L67-68 verbatim
/-- C6: Cycle graph on 6 vertices. -/
abbrev C6 : SimpleGraph (Fin 6) := cycleGraph 6


-- @@ L70-71 verbatim
/-- Star5: Star graph with center 0 and 5 leaves. -/
abbrev Star5 : SimpleGraph (Fin 1 ⊕ Fin 5) := completeBipartiteGraph (Fin 1) (Fin 5)


-- @@ L73-76 verbatim
instance : DecidableRel Star5.Adj := by unfold Star5 completeBipartiteGraph; infer_instance


/-  ### House Graph Tests -/


-- @@ L78-80 expanded
@[category test, AMS 5]
theorem house_indep : indepNum HouseGraph = 2 := by rw [indep_num_eq_computable]; decide +native


-- @@ L82-84 verbatim
@[category test, AMS 5]
theorem house_dom : dominationNumber HouseGraph = 2 := by
  rw [dom_num_eq_computable]; decide +native


-- @@ L86-89 verbatim
@[category test, AMS 5]
theorem house_avg_dist : averageDistance HouseGraph = 7/5 := by
  rw [avg_dist_eq_computable, show computable_avg_dist HouseGraph = (7 / 5 : ℚ) from by decide +native]
  norm_num


-- @@ L91-94 verbatim
@[category test, AMS 5]
theorem house_diameter : ediam HouseGraph = 2 := by
  rw [ediam_eq_computable HouseGraph (by decide)]
  exact_mod_cast (by decide +native : computable_ediam HouseGraph = 2)


-- @@ L96-99 verbatim
@[category test, AMS 5]
theorem house_radius : radius HouseGraph = 2 := by
  rw [radius_eq_computable HouseGraph (by decide)]
  exact_mod_cast (by decide +native : computable_radius HouseGraph = 2)


-- @@ L101-112 verbatim
@[category test, AMS 5]
theorem house_girth : HouseGraph.girth = 3 := by
  have hcyc : (Walk.cons (show HouseGraph.Adj 2 3 by decide)
      (Walk.cons (show HouseGraph.Adj 3 4 by decide)
      (Walk.cons (show HouseGraph.Adj 4 2 by decide) Walk.nil))).IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  refine le_antisymm ?_ (three_le_girth (fun hac => hac _ hcyc))
  simpa using girth_le_length hcyc


-- @@ L114-118 verbatim
open scoped Classical in
@[category test, AMS 5]
theorem house_order : Fintype.card ↥(⊤ : Subgraph HouseGraph).verts = 5 := by
  rw [Fintype.card_congr SimpleGraph.Subgraph.topIso.toEquiv]
  rfl


-- @@ L120-122 verbatim
@[category test, AMS 5]
theorem house_size : HouseGraph.edgeFinset.card = 6 := by
  decide +native


-- @@ L124-126 verbatim
@[category test, AMS 5]
theorem house_szeged : szegedIndex HouseGraph = 24 := by
  rw [szeged_eq_computable]; decide +native


-- @@ L128-130 verbatim
@[category test, AMS 5]
theorem house_wiener : wienerIndex HouseGraph = 14 := by
  rw [wiener_eq_computable]; decide +native


-- @@ L132-134 verbatim
@[category test, AMS 5]
theorem house_min_deg : HouseGraph.minDegree = 2 := by
  decide +native


-- @@ L136-138 verbatim
@[category test, AMS 5]
theorem house_max_deg : HouseGraph.maxDegree = 3 := by
  decide +native


-- @@ L140-142 verbatim
@[category test, AMS 5]
theorem house_avg_deg : averageDegree HouseGraph = 12/5 := by
  unfold averageDegree; simp [Fintype.card_fin]; decide +native


-- @@ L144-165 verbatim
@[category test, AMS 5]
theorem house_matching : matchingNumber HouseGraph = 2 := by
  classical
  have hbdd : BddAbove (Set.image (fun M : Subgraph HouseGraph => (M.edgeSet.toFinset.card : ℝ)) {M | M.IsMatching}) := by
    refine ⟨(Fintype.card (Fin 5) : ℝ), ?_⟩
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ Fintype.card (Fin 5)
    have hb := matching_card_bound HouseGraph M hM
    exact_mod_cast (by omega : M.edgeSet.toFinset.card ≤ Fintype.card (Fin 5))
  unfold matchingNumber
  apply le_antisymm
  · apply csSup_le (Set.Nonempty.image _ ⟨⊥, by simp [Subgraph.IsMatching]⟩)
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ 2
    have hb := matching_card_bound HouseGraph M hM
    simp only [Fintype.card_fin] at hb
    exact_mod_cast (by omega : M.edgeSet.toFinset.card ≤ 2)
  · apply le_csSup hbdd
    refine ⟨HouseGraph.subgraphOfAdj (show HouseGraph.Adj 0 1 by decide) ⊔ HouseGraph.subgraphOfAdj (show HouseGraph.Adj 2 3 by decide), ?_, ?_⟩
    · exact (Subgraph.IsMatching.subgraphOfAdj _).sup (Subgraph.IsMatching.subgraphOfAdj _)
        (by rw [support_subgraphOfAdj, support_subgraphOfAdj]; simp [Set.disjoint_left])
    · simp


-- @@ L167-169 verbatim
@[category test, AMS 5]
theorem house_residue : residue HouseGraph = 2 := by
  unfold residue; decide +native


-- @@ L171-173 verbatim
@[category test, AMS 5]
theorem house_annihilation : annihilationNumber HouseGraph = 3 := by
  decide +native


-- @@ L175-180 verbatim
@[category test, AMS 5]
theorem house_cvetkovic : cvetkovic HouseGraph = 3 := by
  sorry


/-  ### K4 Tests -/


-- @@ L182-184 expanded
@[category test, AMS 5]
theorem K4_indep : indepNum K4 = 1 := by rw [indep_num_eq_computable]; decide +native


-- @@ L186-188 verbatim
@[category test, AMS 5]
theorem K4_dom : dominationNumber K4 = 1 := by
  rw [dom_num_eq_computable]; decide +native


-- @@ L190-193 verbatim
@[category test, AMS 5]
theorem K4_avg_dist : averageDistance K4 = 1 := by
  rw [avg_dist_eq_computable, show computable_avg_dist K4 = (1 : ℚ) from by decide +native]
  norm_num


-- @@ L195-198 verbatim
@[category test, AMS 5]
theorem K4_diameter : ediam K4 = 1 := by
  rw [ediam_eq_computable K4 (by decide)]
  exact_mod_cast (by decide +native : computable_ediam K4 = 1)


-- @@ L200-203 verbatim
@[category test, AMS 5]
theorem K4_radius : radius K4 = 1 := by
  rw [radius_eq_computable K4 (by decide)]
  exact_mod_cast (by decide +native : computable_radius K4 = 1)


-- @@ L205-216 verbatim
@[category test, AMS 5]
theorem K4_girth : K4.girth = 3 := by
  have hcyc : (Walk.cons (show K4.Adj 0 1 by decide)
      (Walk.cons (show K4.Adj 1 2 by decide)
      (Walk.cons (show K4.Adj 2 0 by decide) Walk.nil))).IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  refine le_antisymm ?_ (three_le_girth (fun hac => hac _ hcyc))
  simpa using girth_le_length hcyc


-- @@ L218-222 verbatim
open scoped Classical in
@[category test, AMS 5]
theorem K4_order : Fintype.card ↥(⊤ : Subgraph K4).verts = 4 := by
  rw [Fintype.card_congr SimpleGraph.Subgraph.topIso.toEquiv]
  rfl


-- @@ L224-226 verbatim
@[category test, AMS 5]
theorem K4_size : K4.edgeFinset.card = 6 := by
  decide +native


-- @@ L228-230 verbatim
@[category test, AMS 5]
theorem K4_szeged : szegedIndex K4 = 6 := by
  rw [szeged_eq_computable]; decide +native


-- @@ L232-234 verbatim
@[category test, AMS 5]
theorem K4_wiener : wienerIndex K4 = 6 := by
  rw [wiener_eq_computable]; decide +native


-- @@ L236-238 verbatim
@[category test, AMS 5]
theorem K4_min_deg : K4.minDegree = 3 := by
  decide +native


-- @@ L240-242 verbatim
@[category test, AMS 5]
theorem K4_max_deg : K4.maxDegree = 3 := by
  decide +native


-- @@ L244-246 verbatim
@[category test, AMS 5]
theorem K4_avg_deg : averageDegree K4 = 3 := by
  unfold averageDegree; simp [Fintype.card_fin]


-- @@ L248-269 verbatim
@[category test, AMS 5]
theorem K4_matching : matchingNumber K4 = 2 := by
  classical
  have hbdd : BddAbove (Set.image (fun M : Subgraph K4 => (M.edgeSet.toFinset.card : ℝ)) {M | M.IsMatching}) := by
    refine ⟨(Fintype.card (Fin 4) : ℝ), ?_⟩
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ Fintype.card (Fin 4)
    have hb := matching_card_bound K4 M hM
    exact_mod_cast (by omega : M.edgeSet.toFinset.card ≤ Fintype.card (Fin 4))
  unfold matchingNumber
  apply le_antisymm
  · apply csSup_le (Set.Nonempty.image _ ⟨⊥, by simp [Subgraph.IsMatching]⟩)
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ 2
    have hb := matching_card_bound K4 M hM
    simp only [Fintype.card_fin] at hb
    exact_mod_cast (by omega : M.edgeSet.toFinset.card ≤ 2)
  · apply le_csSup hbdd
    refine ⟨K4.subgraphOfAdj (show K4.Adj 0 1 by decide) ⊔ K4.subgraphOfAdj (show K4.Adj 2 3 by decide), ?_, ?_⟩
    · exact (Subgraph.IsMatching.subgraphOfAdj _).sup (Subgraph.IsMatching.subgraphOfAdj _)
        (by rw [support_subgraphOfAdj, support_subgraphOfAdj]; simp [Set.disjoint_left])
    · simp


-- @@ L271-273 verbatim
@[category test, AMS 5]
theorem K4_residue : residue K4 = 1 := by
  unfold residue; decide +native


-- @@ L275-277 verbatim
@[category test, AMS 5]
theorem K4_annihilation : annihilationNumber K4 = 2 := by
  decide +native


-- @@ L279-284 verbatim
@[category test, AMS 5]
theorem K4_cvetkovic : cvetkovic K4 = 1 := by
  sorry


/-  ### Petersen Graph Tests -/


-- @@ L286-288 expanded
@[category test, AMS 5]
theorem petersen_indep : indepNum PetersenGraph = 4 := by rw [indep_num_eq_computable];
  decide +native


-- @@ L290-292 verbatim
@[category test, AMS 5]
theorem petersen_dom : dominationNumber PetersenGraph = 3 := by
  rw [dom_num_eq_computable]; decide +native


-- @@ L294-297 verbatim
@[category test, AMS 5]
theorem petersen_avg_dist : averageDistance PetersenGraph = 5/3 := by
  rw [avg_dist_eq_computable, show computable_avg_dist PetersenGraph = (5 / 3 : ℚ) from by decide +native]
  norm_num


-- @@ L299-302 verbatim
@[category test, AMS 5]
theorem petersen_diameter : ediam PetersenGraph = 2 := by
  rw [ediam_eq_computable PetersenGraph (by decide)]
  exact_mod_cast (by decide +native : computable_ediam PetersenGraph = 2)


-- @@ L304-307 verbatim
@[category test, AMS 5]
theorem petersen_radius : radius PetersenGraph = 2 := by
  rw [radius_eq_computable PetersenGraph (by decide)]
  exact_mod_cast (by decide +native : computable_radius PetersenGraph = 2)


-- @@ L309-311 verbatim
@[category test, AMS 5]
theorem petersen_girth : PetersenGraph.girth = 5 := by
  sorry


-- @@ L313-317 verbatim
open scoped Classical in
@[category test, AMS 5]
theorem petersen_order : Fintype.card ↥(⊤ : Subgraph PetersenGraph).verts = 10 := by
  rw [Fintype.card_congr SimpleGraph.Subgraph.topIso.toEquiv]
  rfl


-- @@ L319-321 verbatim
@[category test, AMS 5]
theorem petersen_size : PetersenGraph.edgeFinset.card = 15 := by
  decide +native


-- @@ L323-325 verbatim
@[category test, AMS 5]
theorem petersen_szeged : szegedIndex PetersenGraph = 135 := by
  rw [szeged_eq_computable]; decide +native


-- @@ L327-329 verbatim
@[category test, AMS 5]
theorem petersen_wiener : wienerIndex PetersenGraph = 75 := by
  rw [wiener_eq_computable]; decide +native


-- @@ L331-333 verbatim
@[category test, AMS 5]
theorem petersen_min_deg : PetersenGraph.minDegree = 3 := by
  decide +native


-- @@ L335-337 verbatim
@[category test, AMS 5]
theorem petersen_max_deg : PetersenGraph.maxDegree = 3 := by
  decide +native


-- @@ L339-341 verbatim
@[category test, AMS 5]
theorem petersen_avg_deg : averageDegree PetersenGraph = 3 := by
  unfold averageDegree; simp [Fintype.card_fin]; decide +native


-- @@ L343-376 verbatim
@[category test, AMS 5]
theorem petersen_matching : matchingNumber PetersenGraph = 5 := by
  classical
  have hbdd : BddAbove (Set.image (fun M : Subgraph PetersenGraph => (M.edgeSet.toFinset.card : ℝ)) {M | M.IsMatching}) := by
    refine ⟨(Fintype.card (Fin 10) : ℝ), ?_⟩
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ Fintype.card (Fin 10)
    have hb := matching_card_bound PetersenGraph M hM
    exact_mod_cast (by omega : M.edgeSet.toFinset.card ≤ Fintype.card (Fin 10))
  unfold matchingNumber
  apply le_antisymm
  · apply csSup_le (Set.Nonempty.image _ ⟨⊥, by simp [Subgraph.IsMatching]⟩)
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ 5
    have hb := matching_card_bound PetersenGraph M hM
    simp only [Fintype.card_fin] at hb
    exact_mod_cast (by omega : M.edgeSet.toFinset.card ≤ 5)
  · apply le_csSup hbdd
    refine ⟨PetersenGraph.subgraphOfAdj (show PetersenGraph.Adj 0 5 by decide) ⊔ PetersenGraph.subgraphOfAdj (show PetersenGraph.Adj 1 6 by decide) ⊔ PetersenGraph.subgraphOfAdj (show PetersenGraph.Adj 2 7 by decide) ⊔ PetersenGraph.subgraphOfAdj (show PetersenGraph.Adj 3 8 by decide) ⊔ PetersenGraph.subgraphOfAdj (show PetersenGraph.Adj 4 9 by decide), ?_, ?_⟩
    · apply Subgraph.IsMatching.sup
      · apply Subgraph.IsMatching.sup
        · apply Subgraph.IsMatching.sup
          · exact (Subgraph.IsMatching.subgraphOfAdj _).sup (Subgraph.IsMatching.subgraphOfAdj _)
              (by rw [support_subgraphOfAdj, support_subgraphOfAdj]; simp [Set.disjoint_left])
          · exact Subgraph.IsMatching.subgraphOfAdj _
          · apply Set.disjoint_of_subset (Subgraph.support_subset_verts _) (Subgraph.support_subset_verts _)
            simp [Subgraph.verts_sup, subgraphOfAdj_verts, Set.disjoint_left]
        · exact Subgraph.IsMatching.subgraphOfAdj _
        · apply Set.disjoint_of_subset (Subgraph.support_subset_verts _) (Subgraph.support_subset_verts _)
          simp [Subgraph.verts_sup, subgraphOfAdj_verts, Set.disjoint_left]
      · exact Subgraph.IsMatching.subgraphOfAdj _
      · apply Set.disjoint_of_subset (Subgraph.support_subset_verts _) (Subgraph.support_subset_verts _)
        simp [Subgraph.verts_sup, subgraphOfAdj_verts, Set.disjoint_left]
    · simp


-- @@ L378-380 verbatim
@[category test, AMS 5]
theorem petersen_residue : residue PetersenGraph = 3 := by
  unfold residue; decide +native


-- @@ L382-384 verbatim
@[category test, AMS 5]
theorem petersen_annihilation : annihilationNumber PetersenGraph = 5 := by
  decide +native


-- @@ L386-391 verbatim
@[category test, AMS 5]
theorem petersen_cvetkovic : cvetkovic PetersenGraph = 4 := by
  sorry


/-  ### C6 Tests -/


-- @@ L393-395 expanded
@[category test, AMS 5]
theorem C6_indep : indepNum C6 = 3 := by rw [indep_num_eq_computable]; decide +native


-- @@ L397-399 verbatim
@[category test, AMS 5]
theorem C6_dom : dominationNumber C6 = 2 := by
  rw [dom_num_eq_computable]; decide +native


-- @@ L401-404 verbatim
@[category test, AMS 5]
theorem C6_avg_dist : averageDistance C6 = 9/5 := by
  rw [avg_dist_eq_computable, show computable_avg_dist C6 = (9 / 5 : ℚ) from by decide +native]
  norm_num


-- @@ L406-409 verbatim
@[category test, AMS 5]
theorem C6_diameter : ediam C6 = 3 := by
  rw [ediam_eq_computable C6 (by decide)]
  exact_mod_cast (by decide +native : computable_ediam C6 = 3)


-- @@ L411-414 verbatim
@[category test, AMS 5]
theorem C6_radius : radius C6 = 3 := by
  rw [radius_eq_computable C6 (by decide)]
  exact_mod_cast (by decide +native : computable_radius C6 = 3)


-- @@ L416-418 verbatim
@[category test, AMS 5]
theorem C6_girth : C6.girth = 6 := by
  sorry


-- @@ L420-424 verbatim
open scoped Classical in
@[category test, AMS 5]
theorem C6_order : Fintype.card ↥(⊤ : Subgraph C6).verts = 6 := by
  rw [Fintype.card_congr SimpleGraph.Subgraph.topIso.toEquiv]
  rfl


-- @@ L426-428 verbatim
@[category test, AMS 5]
theorem C6_size : C6.edgeFinset.card = 6 := by
  decide +native


-- @@ L430-432 verbatim
@[category test, AMS 5]
theorem C6_szeged : szegedIndex C6 = 54 := by
  rw [szeged_eq_computable]; decide +native


-- @@ L434-436 verbatim
@[category test, AMS 5]
theorem C6_wiener : wienerIndex C6 = 27 := by
  rw [wiener_eq_computable]; decide +native


-- @@ L438-440 verbatim
@[category test, AMS 5]
theorem C6_min_deg : C6.minDegree = 2 := by
  decide +native


-- @@ L442-444 verbatim
@[category test, AMS 5]
theorem C6_max_deg : C6.maxDegree = 2 := by
  decide +native


-- @@ L446-448 verbatim
@[category test, AMS 5]
theorem C6_avg_deg : averageDegree C6 = 2 := by
  unfold averageDegree; simp [Fintype.card_fin]; decide +native


-- @@ L450-475 verbatim
@[category test, AMS 5]
theorem C6_matching : matchingNumber C6 = 3 := by
  classical
  have hbdd : BddAbove (Set.image (fun M : Subgraph C6 => (M.edgeSet.toFinset.card : ℝ)) {M | M.IsMatching}) := by
    refine ⟨(Fintype.card (Fin 6) : ℝ), ?_⟩
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ Fintype.card (Fin 6)
    have hb := matching_card_bound C6 M hM
    exact_mod_cast (by omega : M.edgeSet.toFinset.card ≤ Fintype.card (Fin 6))
  unfold matchingNumber
  apply le_antisymm
  · apply csSup_le (Set.Nonempty.image _ ⟨⊥, by simp [Subgraph.IsMatching]⟩)
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ 3
    have hb := matching_card_bound C6 M hM
    simp only [Fintype.card_fin] at hb
    exact_mod_cast (by omega : M.edgeSet.toFinset.card ≤ 3)
  · apply le_csSup hbdd
    refine ⟨C6.subgraphOfAdj (show C6.Adj 0 1 by decide) ⊔ C6.subgraphOfAdj (show C6.Adj 2 3 by decide) ⊔ C6.subgraphOfAdj (show C6.Adj 4 5 by decide), ?_, ?_⟩
    · apply Subgraph.IsMatching.sup
      · exact (Subgraph.IsMatching.subgraphOfAdj _).sup (Subgraph.IsMatching.subgraphOfAdj _)
          (by rw [support_subgraphOfAdj, support_subgraphOfAdj]; simp [Set.disjoint_left])
      · exact Subgraph.IsMatching.subgraphOfAdj _
      · apply Set.disjoint_of_subset (Subgraph.support_subset_verts _) (Subgraph.support_subset_verts _)
        simp [Subgraph.verts_sup, subgraphOfAdj_verts, Set.disjoint_left]
    · simp


-- @@ L477-479 verbatim
@[category test, AMS 5]
theorem C6_residue : residue C6 = 2 := by
  unfold residue; decide +native


-- @@ L481-483 verbatim
@[category test, AMS 5]
theorem C6_annihilation : annihilationNumber C6 = 3 := by
  decide +native


-- @@ L485-489 verbatim
@[category test, AMS 5]
theorem C6_cvetkovic : cvetkovic C6 = 3 := by
  sorry

/-  ### Star5 Tests -/


-- @@ L491-493 expanded
@[category test, AMS 5]
theorem Star5_indep : indepNum Star5 = 5 := by rw [indep_num_eq_computable]; decide +native


-- @@ L495-497 verbatim
@[category test, AMS 5]
theorem Star5_dom : dominationNumber Star5 = 1 := by
  rw [dom_num_eq_computable]; decide +native


-- @@ L499-502 verbatim
@[category test, AMS 5]
theorem Star5_avg_dist : averageDistance Star5 = 5/3 := by
  rw [avg_dist_eq_computable, show computable_avg_dist Star5 = (5 / 3 : ℚ) from by decide +native]
  norm_num


-- @@ L504-507 verbatim
@[category test, AMS 5]
theorem Star5_diameter : ediam Star5 = 2 := by
  rw [ediam_eq_computable Star5 (by decide)]
  exact_mod_cast (by decide +native : computable_ediam Star5 = 2)


-- @@ L509-512 verbatim
@[category test, AMS 5]
theorem Star5_radius : radius Star5 = 1 := by
  rw [radius_eq_computable Star5 (by decide)]
  exact_mod_cast (by decide +native : computable_radius Star5 = 1)


-- @@ L514-541 verbatim
@[category test, AMS 5]
theorem Star5_girth : Star5.egirth = ⊤ := by
  rw [egirth_eq_top]
  have key : ∀ (b : Fin 5) (c : Star5.Walk (Sum.inr b) (Sum.inr b)), ¬ c.IsCycle := by
    intro b c hc
    have h1 := c.adj_snd hc.not_nil
    have h2 := c.adj_penultimate hc.not_nil
    have hs : c.snd.isLeft := by
      simp only [Star5, completeBipartiteGraph, Sum.isRight_inr, Sum.isLeft_inr] at h1
      tauto
    have hp : c.penultimate.isLeft := by
      simp only [Star5, completeBipartiteGraph, Sum.isRight_inr, Sum.isLeft_inr] at h2
      tauto
    apply hc.snd_ne_penultimate
    obtain ⟨x, hx⟩ := Sum.isLeft_iff.mp hs
    obtain ⟨y, hy⟩ := Sum.isLeft_iff.mp hp
    rw [hx, hy, Subsingleton.elim x y]
  intro v c hc
  cases v with
  | inr b => exact key b c hc
  | inl a =>
    have h1 := c.adj_snd hc.not_nil
    obtain ⟨b, hb⟩ : ∃ b, c.snd = Sum.inr b := by
      rcases hsnd : c.snd with x | y
      · rw [hsnd] at h1; simp [Star5, completeBipartiteGraph] at h1
      · exact ⟨y, rfl⟩
    have hmem : Sum.inr b ∈ c.support := hb ▸ List.mem_of_mem_tail (c.snd_mem_tail_support hc.not_nil)
    exact key b (c.rotate _ hmem) (hc.rotate hmem)


-- @@ L543-547 verbatim
open scoped Classical in
@[category test, AMS 5]
theorem Star5_order : Fintype.card ↥(⊤ : Subgraph Star5).verts = 6 := by
  rw [Fintype.card_congr SimpleGraph.Subgraph.topIso.toEquiv]
  rfl


-- @@ L549-551 verbatim
@[category test, AMS 5]
theorem Star5_size : Star5.edgeFinset.card = 5 := by
  decide +native


-- @@ L553-555 verbatim
@[category test, AMS 5]
theorem Star5_szeged : szegedIndex Star5 = 25 := by
  rw [szeged_eq_computable]; decide +native


-- @@ L557-559 verbatim
@[category test, AMS 5]
theorem Star5_wiener : wienerIndex Star5 = 25 := by
  rw [wiener_eq_computable]; decide +native


-- @@ L561-563 verbatim
@[category test, AMS 5]
theorem Star5_min_deg : Star5.minDegree = 1 := by
  decide +native


-- @@ L565-567 verbatim
@[category test, AMS 5]
theorem Star5_max_deg : Star5.maxDegree = 5 := by
  decide +native


-- @@ L569-571 verbatim
@[category test, AMS 5]
theorem Star5_avg_deg : averageDegree Star5 = 5/3 := by
  unfold averageDegree; simp [Fintype.card_sum, Fintype.card_fin]; decide +native


-- @@ L573-609 verbatim
@[category test, AMS 5]
theorem Star5_matching : matchingNumber Star5 = 1 := by
  classical
  have hle : ∀ M : Subgraph Star5, M.IsMatching → M.edgeSet.toFinset.card ≤ 1 := by
    intro M hM
    have hcenter : ∀ e ∈ M.edgeSet, (Sum.inl 0 : Fin 1 ⊕ Fin 5) ∈ e := by
      intro e he
      induction e using Sym2.inductionOn with | _ a b =>
      rw [Subgraph.mem_edgeSet] at he
      have hadj := he.adj_sub
      simp only [Star5, completeBipartiteGraph] at hadj
      rw [Sym2.mem_iff]
      rcases hadj with ⟨ha, _⟩ | ⟨_, hb⟩
      · left; obtain ⟨a', rfl⟩ := Sum.isLeft_iff.mp ha; exact congrArg Sum.inl (Subsingleton.elim 0 a')
      · right; obtain ⟨b', rfl⟩ := Sum.isLeft_iff.mp hb; exact congrArg Sum.inl (Subsingleton.elim 0 b')
    rw [Finset.card_le_one]
    intro e he f hf
    rw [Set.mem_toFinset] at he hf
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp (hcenter e he)
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp (hcenter f hf)
    rw [Subgraph.mem_edgeSet] at he hf
    rw [hM.eq_of_adj_left he hf]
  have hbdd : BddAbove (Set.image (fun M : Subgraph Star5 => (M.edgeSet.toFinset.card : ℝ)) {M | M.IsMatching}) := by
    refine ⟨1, ?_⟩
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ 1
    exact_mod_cast hle M hM
  unfold matchingNumber
  apply le_antisymm
  · apply csSup_le (Set.Nonempty.image _ ⟨⊥, by simp [Subgraph.IsMatching]⟩)
    rintro x ⟨M, hM, rfl⟩
    show (M.edgeSet.toFinset.card : ℝ) ≤ 1
    exact_mod_cast hle M hM
  · apply le_csSup hbdd
    refine ⟨Star5.subgraphOfAdj (show Star5.Adj (Sum.inl 0) (Sum.inr 0) by simp [Star5, completeBipartiteGraph]), ?_, ?_⟩
    · exact Subgraph.IsMatching.subgraphOfAdj _
    · simp


-- @@ L611-613 verbatim
@[category test, AMS 5]
theorem Star5_residue : residue Star5 = 5 := by
  unfold residue; decide +native


-- @@ L615-617 verbatim
@[category test, AMS 5]
theorem Star5_annihilation : annihilationNumber Star5 = 5 := by
  decide +native


-- @@ L619-621 verbatim
@[category test, AMS 5]
theorem Star5_cvetkovic : cvetkovic Star5 = 5 := by
  sorry


-- @@ L623-623 verbatim
end WrittenOnTheWallII.Test
