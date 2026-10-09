import OAI.Analysis.IntegralMeans.DomainArea


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set MeasureTheory Filter Function

-- @@ L7-7 verbatim
open scoped Topology ENNReal

-- @@ L8-8 verbatim
namespace Brennan


-- @@ L10-18 verbatim
theorem main_theorem : MainStatement := by
  refine ⟨?_,inverse_spectrum_eq_one,?_,?_⟩
  · intro ε hε
    obtain ⟨C,_hC,hbound⟩ := uniform_inverse_square_bound ε hε
    exact ⟨C,hbound⟩
  · intro W hW _hconnected _hsimply _hboundary φ hφ hb s hs hs4
    exact conformal_domain_area hW hφ hb hs hs4
  · intro f hf t ht ht2
    exact univalent_disk_area hf ht ht2


-- @@ L20-20 verbatim
end Brennan


-- @@ L22-22 verbatim
end


-- @@ L24-24 verbatim
end OAI
