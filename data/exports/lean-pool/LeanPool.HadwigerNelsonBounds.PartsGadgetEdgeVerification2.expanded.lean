/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetEmbeddingCore


-- @@ L10-10 verbatim
/-! Generated edge-geometry checks, group 2. -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace HadwigerNelsonBounds


-- @@ L16-22 verbatim
lemma partsGadgetEdgeCase38 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 38) :
    PartsGadgetEdgeCase 38 neighbor := by
  change neighbor ∈ [37, 39, 42, 43] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L24-30 verbatim
lemma partsGadgetEdgeCase39 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 39) :
    PartsGadgetEdgeCase 39 neighbor := by
  change neighbor ∈ [38, 40, 43, 44] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L32-38 verbatim
lemma partsGadgetEdgeCase40 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 40) :
    PartsGadgetEdgeCase 40 neighbor := by
  change neighbor ∈ [39, 44, 45] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L40-46 verbatim
lemma partsGadgetEdgeCase41 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 41) :
    PartsGadgetEdgeCase 41 neighbor := by
  change neighbor ∈ [37, 42, 46, 47] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L48-54 verbatim
lemma partsGadgetEdgeCase42 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 42) :
    PartsGadgetEdgeCase 42 neighbor := by
  change neighbor ∈ [5, 37, 38, 41, 43, 47, 48] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L56-62 verbatim
lemma partsGadgetEdgeCase43 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 43) :
    PartsGadgetEdgeCase 43 neighbor := by
  change neighbor ∈ [38, 39, 42, 44, 48, 49] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L64-70 verbatim
lemma partsGadgetEdgeCase44 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 44) :
    PartsGadgetEdgeCase 44 neighbor := by
  change neighbor ∈ [7, 39, 40, 43, 45, 49, 50] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L72-78 verbatim
lemma partsGadgetEdgeCase45 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 45) :
    PartsGadgetEdgeCase 45 neighbor := by
  change neighbor ∈ [40, 44, 50, 51] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L80-86 verbatim
lemma partsGadgetEdgeCase46 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 46) :
    PartsGadgetEdgeCase 46 neighbor := by
  change neighbor ∈ [41, 47, 52, 53] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L88-94 verbatim
lemma partsGadgetEdgeCase47 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 47) :
    PartsGadgetEdgeCase 47 neighbor := by
  change neighbor ∈ [41, 42, 46, 48, 53, 54] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L96-102 verbatim
lemma partsGadgetEdgeCase48 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 48) :
    PartsGadgetEdgeCase 48 neighbor := by
  change neighbor ∈ [18, 42, 43, 47, 49, 54] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L104-110 verbatim
lemma partsGadgetEdgeCase49 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 49) :
    PartsGadgetEdgeCase 49 neighbor := by
  change neighbor ∈ [18, 43, 44, 48, 50, 55] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L112-118 verbatim
lemma partsGadgetEdgeCase50 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 50) :
    PartsGadgetEdgeCase 50 neighbor := by
  change neighbor ∈ [44, 45, 49, 51, 55, 56] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L120-126 verbatim
lemma partsGadgetEdgeCase51 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 51) :
    PartsGadgetEdgeCase 51 neighbor := by
  change neighbor ∈ [45, 50, 56, 57] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L128-134 verbatim
lemma partsGadgetEdgeCase52 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 52) :
    PartsGadgetEdgeCase 52 neighbor := by
  change neighbor ∈ [46, 53, 58] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L136-142 verbatim
lemma partsGadgetEdgeCase53 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 53) :
    PartsGadgetEdgeCase 53 neighbor := by
  change neighbor ∈ [16, 46, 47, 52, 54, 58, 59] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L144-150 verbatim
lemma partsGadgetEdgeCase54 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 54) :
    PartsGadgetEdgeCase 54 neighbor := by
  change neighbor ∈ [18, 47, 48, 53, 59, 60] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L152-158 verbatim
lemma partsGadgetEdgeCase55 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 55) :
    PartsGadgetEdgeCase 55 neighbor := by
  change neighbor ∈ [18, 49, 50, 56, 61, 62] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L160-166 verbatim
lemma partsGadgetEdgeCase56 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 56) :
    PartsGadgetEdgeCase 56 neighbor := by
  change neighbor ∈ [20, 50, 51, 55, 57, 62, 63] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L168-168 verbatim
end HadwigerNelsonBounds
