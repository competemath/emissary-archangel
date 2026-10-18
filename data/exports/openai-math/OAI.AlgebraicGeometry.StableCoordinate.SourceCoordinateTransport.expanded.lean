import OAI.AlgebraicGeometry.StableCoordinate.SourcePresentation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-13 verbatim
/-!
# Literal-polynomial coordinate systems in the canonical source algebra

The source presentation carries exactly `aX 0` to the prescribed polynomial
`f`.  This reverses the presentation equivalence so a hypothetical coordinate
automorphism of the literal four-variable polynomial gives precisely the
coordinate-system direction used by the leading-derivation construction.
No ambient automorphism is restricted or excluded.
-/


-- @@ L15-15 verbatim
namespace StableCoordinate.Obstruction


-- @@ L17-17 verbatim
open MvPolynomial


-- @@ L19-30 verbatim
/-- The exact coordinate predicate is equivalent to a polynomial coordinate
system on the canonical source algebra, with its first coordinate equal to `p`.
The equivalence quantifies over all ambient polynomial automorphisms. -/
theorem f_coordinate_iff_source_coordinate_system :
    IsCoordinate (by decide : 0 < 4) StableCoordinate.f ↔
      ∃ e : StableCoordinate.R 4 ≃ₐ[ℂ] A ℂ, e (X 0) = aX ℂ 0 := by
  rw [f_coordinate_iff_source_coordinate]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.symm, by rw [← he, AlgEquiv.symm_apply_apply]⟩
  · rintro ⟨e, he⟩
    exact ⟨e.symm, by rw [← he, AlgEquiv.symm_apply_apply]⟩


-- @@ L32-37 verbatim
/-- A four-variable coordinate for the literal polynomial supplies the actual
source-coordinate equivalence needed by the negative proof. -/
theorem source_coordinate_system_of_f_coordinate
    (h : IsCoordinate (by decide : 0 < 4) StableCoordinate.f) :
    ∃ e : StableCoordinate.R 4 ≃ₐ[ℂ] A ℂ, e (X 0) = aX ℂ 0 :=
  f_coordinate_iff_source_coordinate_system.mp h


-- @@ L39-39 verbatim
end StableCoordinate.Obstruction


-- @@ L41-41 verbatim
end OAI
