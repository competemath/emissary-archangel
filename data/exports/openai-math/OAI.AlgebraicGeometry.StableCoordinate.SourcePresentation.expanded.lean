import OAI.AlgebraicGeometry.StableCoordinate.Presentation
import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
/-! # The polynomial presentation in the canonical obstruction interface -/


-- @@ L10-10 verbatim
namespace StableCoordinate.Obstruction


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-16 verbatim
/-- The exact canonical source hypersurface is the four-variable polynomial ring. -/
def sourcePresentation : A ℂ ≃ₐ[ℂ] StableCoordinate.R 4 :=
  Presentation.originalPresentation


-- @@ L18-19 verbatim
@[simp] theorem sourcePresentation_p : sourcePresentation (aX ℂ 0) = StableCoordinate.f :=
  Presentation.originalPresentation_p


-- @@ L21-22 verbatim
instance : IsDomain (A ℂ) :=
  sourcePresentation.toRingEquiv.isDomain _


-- @@ L24-25 verbatim
instance : IsNoetherianRing (A ℂ) :=
  isNoetherianRing_of_ringEquiv (StableCoordinate.R 4) sourcePresentation.symm.toRingEquiv



-- @@ L28-43 verbatim
/-- Coordinateness of the exact polynomial is equivalent to coordinateness of
the distinguished element in the source presentation, with arbitrary ambient
coordinate changes on both sides. -/
theorem f_coordinate_iff_source_coordinate :
    IsCoordinate (by decide : 0 < 4) StableCoordinate.f ↔
      ∃ e : A ℂ ≃ₐ[ℂ] StableCoordinate.R 4, e (aX ℂ 0) = MvPolynomial.X 0 := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨sourcePresentation.trans e, ?_⟩
    change e StableCoordinate.f = MvPolynomial.X 0 at he
    simpa only [AlgEquiv.trans_apply, sourcePresentation_p] using he
  · rintro ⟨e, he⟩
    refine ⟨sourcePresentation.symm.trans e, ?_⟩
    change e (sourcePresentation.symm StableCoordinate.f) = MvPolynomial.X 0
    rw [← sourcePresentation_p, AlgEquiv.symm_apply_apply]
    exact he


-- @@ L45-45 verbatim
end

-- @@ L46-46 verbatim
end StableCoordinate.Obstruction


-- @@ L48-48 verbatim
end OAI
