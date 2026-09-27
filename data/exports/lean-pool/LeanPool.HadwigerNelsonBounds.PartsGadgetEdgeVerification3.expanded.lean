/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetEmbeddingCore


-- @@ L10-10 verbatim
/-! Generated edge-geometry checks, group 3. -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace HadwigerNelsonBounds


-- @@ L16-22 verbatim
lemma partsGadgetEdgeCase57 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 57) :
    PartsGadgetEdgeCase 57 neighbor := by
  change neighbor ∈ [51, 56, 63] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L24-30 verbatim
lemma partsGadgetEdgeCase58 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 58) :
    PartsGadgetEdgeCase 58 neighbor := by
  change neighbor ∈ [52, 53, 59, 64] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L32-38 verbatim
lemma partsGadgetEdgeCase59 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 59) :
    PartsGadgetEdgeCase 59 neighbor := by
  change neighbor ∈ [53, 54, 58, 60, 64, 65] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L40-46 verbatim
lemma partsGadgetEdgeCase60 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 60) :
    PartsGadgetEdgeCase 60 neighbor := by
  change neighbor ∈ [18, 54, 59, 61, 65, 66] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L48-54 verbatim
lemma partsGadgetEdgeCase61 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 61) :
    PartsGadgetEdgeCase 61 neighbor := by
  change neighbor ∈ [18, 55, 60, 62, 66, 67] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L56-62 verbatim
lemma partsGadgetEdgeCase62 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 62) :
    PartsGadgetEdgeCase 62 neighbor := by
  change neighbor ∈ [55, 56, 61, 63, 67, 68] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L64-70 verbatim
lemma partsGadgetEdgeCase63 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 63) :
    PartsGadgetEdgeCase 63 neighbor := by
  change neighbor ∈ [56, 57, 62, 68] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L72-78 verbatim
lemma partsGadgetEdgeCase64 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 64) :
    PartsGadgetEdgeCase 64 neighbor := by
  change neighbor ∈ [58, 59, 65, 69] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L80-86 verbatim
lemma partsGadgetEdgeCase65 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 65) :
    PartsGadgetEdgeCase 65 neighbor := by
  change neighbor ∈ [29, 59, 60, 64, 66, 69, 70] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L88-94 verbatim
lemma partsGadgetEdgeCase66 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 66) :
    PartsGadgetEdgeCase 66 neighbor := by
  change neighbor ∈ [60, 61, 65, 67, 70, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L96-102 verbatim
lemma partsGadgetEdgeCase67 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 67) :
    PartsGadgetEdgeCase 67 neighbor := by
  change neighbor ∈ [31, 61, 62, 66, 68, 71, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L104-110 verbatim
lemma partsGadgetEdgeCase68 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 68) :
    PartsGadgetEdgeCase 68 neighbor := by
  change neighbor ∈ [62, 63, 67, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L112-118 verbatim
lemma partsGadgetEdgeCase69 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 69) :
    PartsGadgetEdgeCase 69 neighbor := by
  change neighbor ∈ [64, 65, 70] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L120-126 verbatim
lemma partsGadgetEdgeCase70 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 70) :
    PartsGadgetEdgeCase 70 neighbor := by
  change neighbor ∈ [65, 66, 69, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L128-134 verbatim
lemma partsGadgetEdgeCase71 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 71) :
    PartsGadgetEdgeCase 71 neighbor := by
  change neighbor ∈ [66, 67, 70, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide


-- @@ L136-142 verbatim
lemma partsGadgetEdgeCase72 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 72) :
    PartsGadgetEdgeCase 72 neighbor := by
  change neighbor ∈ [67, 68, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide


-- @@ L144-144 verbatim
end HadwigerNelsonBounds
