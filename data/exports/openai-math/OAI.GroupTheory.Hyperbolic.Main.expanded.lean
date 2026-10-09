import OAI.GroupTheory.Hyperbolic.Hyperbolicity


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Release075


-- @@ L7-16 verbatim
theorem main : ∃ (G : Type) (_ : Group G),
    TorsionFree G ∧ WordHyperbolic G ∧ ¬ Group.ResiduallyFinite G := by
  obtain ⟨q,r,hq,hr,hrq,hrb,⟨d⟩⟩ := exists_markedLineData
  let : Fact q.Prime := ⟨hq⟩
  have hq200 : 200 ≤ q := by
    have hb : 200 ≤ 100*100^20 := by norm_num
    omega
  exact ⟨(d.presentation hr).GroupType, inferInstance,
    d.presentation_torsionFree hr, d.presentation_wordHyperbolic hr,
    d.actual_presentation_not_residuallyFinite hr hrq hq200⟩


-- @@ L18-18 verbatim
end Release075


-- @@ L20-20 verbatim
end OAI
