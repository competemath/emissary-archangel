/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetEmbeddingCore


-- @@ L10-10 verbatim
/-! Generated edge-geometry checks, group 1. -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace HadwigerNelsonBounds


-- @@ L16-22 verbatim
lemma partsGadgetEdgeCase19 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 19) :
    PartsGadgetEdgeCase 19 neighbor := by
  change neighbor ∈ [12, 13, 18, 20, 25, 26] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L24-30 verbatim
lemma partsGadgetEdgeCase20 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 20) :
    PartsGadgetEdgeCase 20 neighbor := by
  change neighbor ∈ [13, 14, 19, 21, 26, 27, 56] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L32-38 verbatim
lemma partsGadgetEdgeCase21 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 21) :
    PartsGadgetEdgeCase 21 neighbor := by
  change neighbor ∈ [14, 20, 27] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L40-46 verbatim
lemma partsGadgetEdgeCase22 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 22) :
    PartsGadgetEdgeCase 22 neighbor := by
  change neighbor ∈ [15, 16, 23, 28] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L48-54 verbatim
lemma partsGadgetEdgeCase23 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 23) :
    PartsGadgetEdgeCase 23 neighbor := by
  change neighbor ∈ [16, 17, 22, 24, 28, 29] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L56-62 verbatim
lemma partsGadgetEdgeCase24 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 24) :
    PartsGadgetEdgeCase 24 neighbor := by
  change neighbor ∈ [17, 18, 23, 25, 29, 30] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L64-70 verbatim
lemma partsGadgetEdgeCase25 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 25) :
    PartsGadgetEdgeCase 25 neighbor := by
  change neighbor ∈ [18, 19, 24, 26, 30, 31] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L72-78 verbatim
lemma partsGadgetEdgeCase26 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 26) :
    PartsGadgetEdgeCase 26 neighbor := by
  change neighbor ∈ [19, 20, 25, 27, 31, 32] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L80-86 verbatim
lemma partsGadgetEdgeCase27 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 27) :
    PartsGadgetEdgeCase 27 neighbor := by
  change neighbor ∈ [20, 21, 26, 32] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L88-94 verbatim
lemma partsGadgetEdgeCase28 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 28) :
    PartsGadgetEdgeCase 28 neighbor := by
  change neighbor ∈ [22, 23, 29, 33] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L96-102 verbatim
lemma partsGadgetEdgeCase29 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 29) :
    PartsGadgetEdgeCase 29 neighbor := by
  change neighbor ∈ [23, 24, 28, 30, 33, 34, 65] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L104-110 verbatim
lemma partsGadgetEdgeCase30 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 30) :
    PartsGadgetEdgeCase 30 neighbor := by
  change neighbor ∈ [24, 25, 29, 31, 34, 35] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L112-118 verbatim
lemma partsGadgetEdgeCase31 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 31) :
    PartsGadgetEdgeCase 31 neighbor := by
  change neighbor ∈ [25, 26, 30, 32, 35, 36, 67] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L120-126 verbatim
lemma partsGadgetEdgeCase32 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 32) :
    PartsGadgetEdgeCase 32 neighbor := by
  change neighbor ∈ [26, 27, 31, 36] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L128-134 verbatim
lemma partsGadgetEdgeCase33 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 33) :
    PartsGadgetEdgeCase 33 neighbor := by
  change neighbor ∈ [28, 29, 34] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L136-142 verbatim
lemma partsGadgetEdgeCase34 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 34) :
    PartsGadgetEdgeCase 34 neighbor := by
  change neighbor ∈ [29, 30, 33, 35] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L144-150 verbatim
lemma partsGadgetEdgeCase35 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 35) :
    PartsGadgetEdgeCase 35 neighbor := by
  change neighbor ∈ [30, 31, 34, 36] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L152-158 verbatim
lemma partsGadgetEdgeCase36 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 36) :
    PartsGadgetEdgeCase 36 neighbor := by
  change neighbor ∈ [31, 32, 35] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L160-166 verbatim
lemma partsGadgetEdgeCase37 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 37) :
    PartsGadgetEdgeCase 37 neighbor := by
  change neighbor ∈ [38, 41, 42] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L168-168 verbatim
end HadwigerNelsonBounds
