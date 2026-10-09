import OAI.Analysis.StructuralCrouzeix.Main
import OAI.Analysis.StructuralCrouzeix.UnitDisk


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace StructuralCrouzeixReference

-- @@ L7-9 verbatim
theorem challenge : StructuralCrouzeix.FullEndpoint ∧
    StructuralCrouzeix.IsAdmissible (Metric.ball (0 : ℂ) 1) :=
  ⟨StructuralCrouzeix.fullEndpoint, StructuralCrouzeix.isAdmissible_unitDisk⟩

-- @@ L10-10 verbatim
end StructuralCrouzeixReference


-- @@ L12-12 verbatim
end OAI
