import OAI.Analysis.SegmentLenses.Completed


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SegmentLenses


-- @@ L7-16 verbatim
theorem midpoint_lens_main :
    (∀ (H : Finset ForestVertex) (_ : Ancestral ForestAncestor H)
      (x y : X) (_ : x = head H x) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) ∧
    (∀ (H : Finset InfiniteVertex) (_ : Ancestral List.IsPrefix H)
      (x y : BInfinite) (_ : x.val = head H x.val) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y.val‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) :=
  ⟨forest_main_tail, infinite_main_tail⟩


-- @@ L18-18 verbatim
end SegmentLenses


-- @@ L20-20 verbatim
end OAI
