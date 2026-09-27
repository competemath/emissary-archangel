/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetEmbeddingCore


-- @@ L10-10 verbatim
/-! Generated edge-geometry checks, group 0. -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace HadwigerNelsonBounds


-- @@ L16-22 verbatim
lemma partsGadgetEdgeCase0 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 0) :
    PartsGadgetEdgeCase 0 neighbor := by
  change neighbor ∈ [1, 4, 5] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L24-30 verbatim
lemma partsGadgetEdgeCase1 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 1) :
    PartsGadgetEdgeCase 1 neighbor := by
  change neighbor ∈ [0, 2, 5, 6] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L32-38 verbatim
lemma partsGadgetEdgeCase2 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 2) :
    PartsGadgetEdgeCase 2 neighbor := by
  change neighbor ∈ [1, 3, 6, 7] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L40-46 verbatim
lemma partsGadgetEdgeCase3 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 3) :
    PartsGadgetEdgeCase 3 neighbor := by
  change neighbor ∈ [2, 7, 8] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L48-54 verbatim
lemma partsGadgetEdgeCase4 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 4) :
    PartsGadgetEdgeCase 4 neighbor := by
  change neighbor ∈ [0, 5, 9, 10] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L56-62 verbatim
lemma partsGadgetEdgeCase5 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 5) :
    PartsGadgetEdgeCase 5 neighbor := by
  change neighbor ∈ [0, 1, 4, 6, 10, 11, 42] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L64-70 verbatim
lemma partsGadgetEdgeCase6 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 6) :
    PartsGadgetEdgeCase 6 neighbor := by
  change neighbor ∈ [1, 2, 5, 7, 11, 12] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L72-78 verbatim
lemma partsGadgetEdgeCase7 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 7) :
    PartsGadgetEdgeCase 7 neighbor := by
  change neighbor ∈ [2, 3, 6, 8, 12, 13, 44] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L80-86 verbatim
lemma partsGadgetEdgeCase8 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 8) :
    PartsGadgetEdgeCase 8 neighbor := by
  change neighbor ∈ [3, 7, 13, 14] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L88-94 verbatim
lemma partsGadgetEdgeCase9 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 9) :
    PartsGadgetEdgeCase 9 neighbor := by
  change neighbor ∈ [4, 10, 15, 16] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L96-102 verbatim
lemma partsGadgetEdgeCase10 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 10) :
    PartsGadgetEdgeCase 10 neighbor := by
  change neighbor ∈ [4, 5, 9, 11, 16, 17] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L104-110 verbatim
lemma partsGadgetEdgeCase11 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 11) :
    PartsGadgetEdgeCase 11 neighbor := by
  change neighbor ∈ [5, 6, 10, 12, 17, 18] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L112-118 verbatim
lemma partsGadgetEdgeCase12 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 12) :
    PartsGadgetEdgeCase 12 neighbor := by
  change neighbor ∈ [6, 7, 11, 13, 18, 19] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L120-126 verbatim
lemma partsGadgetEdgeCase13 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 13) :
    PartsGadgetEdgeCase 13 neighbor := by
  change neighbor ∈ [7, 8, 12, 14, 19, 20] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L128-134 verbatim
lemma partsGadgetEdgeCase14 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 14) :
    PartsGadgetEdgeCase 14 neighbor := by
  change neighbor ∈ [8, 13, 20, 21] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L136-142 verbatim
lemma partsGadgetEdgeCase15 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 15) :
    PartsGadgetEdgeCase 15 neighbor := by
  change neighbor ∈ [9, 16, 22] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L144-150 verbatim
lemma partsGadgetEdgeCase16 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 16) :
    PartsGadgetEdgeCase 16 neighbor := by
  change neighbor ∈ [9, 10, 15, 17, 22, 23, 53] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L152-158 verbatim
lemma partsGadgetEdgeCase17 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 17) :
    PartsGadgetEdgeCase 17 neighbor := by
  change neighbor ∈ [10, 11, 16, 18, 23, 24] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L160-166 verbatim
lemma partsGadgetEdgeCase18 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 18) :
    PartsGadgetEdgeCase 18 neighbor := by
  change neighbor ∈ [11, 12, 17, 19, 24, 25, 48, 49, 54, 55, 60, 61] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L168-168 verbatim
end HadwigerNelsonBounds
