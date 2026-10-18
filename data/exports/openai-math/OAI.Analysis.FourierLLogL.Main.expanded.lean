import OAI.Analysis.FourierLLogL.Weak.Endpoint
import OAI.Analysis.FourierLLogL.Assembly.Endpoint
import OAI.Analysis.FourierLLogL.Dyadic.Lift
import OAI.Analysis.FourierLLogL.Fourier.Good


-- @@ L6-8 verbatim
/-!
# Almost everywhere Fourier convergence in L log L
-/


-- @@ L10-10 verbatim
open MeasureTheory Filter Set

-- @@ L11-11 verbatim
open scoped Topology


-- @@ L13-13 verbatim
namespace OAI


-- @@ L15-15 verbatim
namespace FourierLLogL


-- @@ L17-20 verbatim
theorem main_of_grid (h : Dyadic.GridBound) {f : Torus → ℂ} (hf : MemLLogL f) :
    ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧ ∀ x ∉ E,
      Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x)) :=
  h.unitTreeBound.affine.realGoodBound.goodBound.main_bound_consequence hf

-- @@ L21-21 verbatim
end FourierLLogL


-- @@ L23-23 verbatim
namespace FourierLLogL

-- @@ L24-28 verbatim
/-- Almost everywhere convergence in L log L, all symmetric cutoffs. -/
theorem almost_everywhere_fourier_convergence (f : Torus → ℂ) (hf : MemLLogL f) :
    ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧ ∀ x ∉ E,
      Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x)) :=
    main_of_grid Dyadic.gridProof hf


-- @@ L30-31 verbatim
theorem maximal_good_sets : GoodBound :=
    Dyadic.gridProof.unitTreeBound.affine.realGoodBound.goodBound

-- @@ L32-32 verbatim
end FourierLLogL


-- @@ L34-34 verbatim
namespace FourierLLogL

-- @@ L35-40 verbatim
/-- Cor. "Weak-L^1 maximal bound", in the equivalent all-levels form. -/
theorem weak_L1_maximal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Torus → ℂ), MemLLogL f →
      ∀ w : ℝ, 0 < w →
        w*circleMeasure.real (cloudSet f w) ≤ C*luxNorm f :=
    Weak.consequence_maximal maximal_good_sets

-- @@ L41-41 verbatim
end FourierLLogL


-- @@ L43-43 verbatim
end OAI
