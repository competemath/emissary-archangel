import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued


-- @@ L5-5 verbatim
set_option autoImplicit false


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open CategoryTheory AlgebraicGeometry IntermediateField


-- @@ L11-11 verbatim
universe u


-- @@ L13-13 verbatim
namespace AlgebraicCurve.CurveModel


-- @@ L15-25 verbatim
theorem isProper_smooth_places_affineCover_glued (K : Type u) [Field K] [Infinite K]
    [PerfectField K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    (ht : Transcendental K t) [FiniteDimensional ↥K⟮t⟯ L] [Algebra.IsSeparable ↥K⟮t⟯ L] :
    IsProper (gluedToBase K t) ∧
    SmoothOfRelativeDimension 1 (gluedToBase K t) ∧
    (∃ P : closedPoints (glued K t) → Place K L, Function.Bijective P ∧
      ∀ x : closedPoints (glued K t),
        (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
            (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
          (P x).toValuationSubring.toSubring) ∧
    (∀ F : Finset (glued K t), ∃ U : (glued K t).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.solution
