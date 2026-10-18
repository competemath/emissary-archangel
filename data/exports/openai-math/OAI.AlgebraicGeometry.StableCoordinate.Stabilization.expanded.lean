import OAI.AlgebraicGeometry.StableCoordinate.Definitions
import OAI.AlgebraicGeometry.StableCoordinate.ExponentialShift
import OAI.AlgebraicGeometry.StableCoordinate.Linearization
import OAI.AlgebraicGeometry.StableCoordinate.StabilizedQuotient
import OAI.AlgebraicGeometry.StableCoordinate.Presentation
import Mathlib.RingTheory.Ideal.Quotient.Operations


-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-16 verbatim
/-!
# Stabilization assembly

The exponential shift is transported through the principal hypersurface ideal.
The final assembly will combine this with the polynomial presentation and the
linear elimination isomorphisms. No statement here assumes the principal target.
-/

-- @@ L17-17 verbatim
namespace StableCoordinate

-- @@ L18-18 verbatim
namespace Stabilization


-- @@ L20-20 verbatim
open MvPolynomial


-- @@ L22-23 verbatim
noncomputable def presentationIdeal : Ideal (R 6) :=
  Ideal.span ({ExponentialShift.H ℂ} : Set (R 6))


-- @@ L25-26 verbatim
noncomputable def shiftedIdeal : Ideal (R 6) :=
  Ideal.span ({ExponentialShift.H ℂ + ExponentialShift.p ℂ * ExponentialShift.w ℂ} : Set (R 6))


-- @@ L28-28 verbatim
abbrev PresentationRing := R 6 ⧸ presentationIdeal

-- @@ L29-29 verbatim
abbrev ShiftedRing := R 6 ⧸ shiftedIdeal


-- @@ L31-41 verbatim
/-- The explicit exponential substitution identifies the two hypersurface rings. -/
noncomputable def shiftQuotientEquiv : PresentationRing ≃ₐ[ℂ] ShiftedRing :=
  Ideal.quotientEquivAlg presentationIdeal shiftedIdeal
    (ExponentialShift.shiftEquiv ℂ 1) (by
      have h : ExponentialShift.shiftEquiv ℂ 1 (ExponentialShift.H ℂ) =
          ExponentialShift.H ℂ + ExponentialShift.p ℂ * ExponentialShift.w ℂ := by
        rw [ExponentialShift.shiftEquiv_apply, ExponentialShift.shift_H]
        congr 1
        simp only [ExponentialShift.t, map_one, one_mul]
      rw [presentationIdeal, shiftedIdeal, Ideal.map_span, Set.image_singleton]
      exact congrArg (fun a : R 6 => Ideal.span ({a} : Set (R 6))) h.symm)


-- @@ L43-45 verbatim
@[simp] theorem shiftQuotientEquiv_mk (a : R 6) :
    shiftQuotientEquiv (Ideal.Quotient.mk presentationIdeal a) =
      Ideal.Quotient.mk shiftedIdeal (ExponentialShift.shiftEquiv ℂ 1 a) := rfl


-- @@ L47-53 verbatim
@[simp] theorem shiftQuotientEquiv_p :
    shiftQuotientEquiv (Ideal.Quotient.mk presentationIdeal (X 0)) =
      Ideal.Quotient.mk shiftedIdeal (X 0) := by
  change Ideal.Quotient.mk shiftedIdeal
    (ExponentialShift.shiftEquiv ℂ 1 (ExponentialShift.p ℂ)) = _
  rw [ExponentialShift.shiftEquiv_apply, ExponentialShift.shift_p]
  rfl


-- @@ L55-64 verbatim
/-- Normalize the shifted equation to the monic linear equation `F-u+p*w`. -/
noncomputable def normalizationQuotientEquiv : ShiftedRing ≃ₐ[ℂ] StabilizedQuotient.A :=
  Ideal.quotientEquivAlg shiftedIdeal StabilizedQuotient.equationIdeal
    (Linearization.normalization ℂ) (by
      have h : Linearization.normalization ℂ
          (ExponentialShift.H ℂ + ExponentialShift.p ℂ * ExponentialShift.w ℂ) =
          StabilizedQuotient.equation := by
        exact Linearization.normalization_stabilized_h ℂ
      rw [shiftedIdeal, StabilizedQuotient.equationIdeal, Ideal.map_span, Set.image_singleton]
      exact congrArg (fun a : R 6 => Ideal.span ({a} : Set (R 6))) h.symm)


-- @@ L66-68 verbatim
@[simp] theorem normalizationQuotientEquiv_mk (a : R 6) :
    normalizationQuotientEquiv (Ideal.Quotient.mk shiftedIdeal a) =
      Ideal.Quotient.mk StabilizedQuotient.equationIdeal (Linearization.normalization ℂ a) := rfl


-- @@ L70-73 verbatim
/-- The shifted hypersurface is a five-variable polynomial ring, with `p` as
its first coordinate. This is the explicit final variable elimination. -/
noncomputable def eliminateQuotientEquiv : ShiftedRing ≃ₐ[ℂ] R 5 :=
  normalizationQuotientEquiv.trans StabilizedQuotient.equiv


-- @@ L75-77 verbatim
@[simp] theorem eliminateQuotientEquiv_p :
    eliminateQuotientEquiv (Ideal.Quotient.mk shiftedIdeal (X 0)) = X 0 := by
  simp [eliminateQuotientEquiv, StabilizedQuotient.evaluate]


-- @@ L79-82 verbatim
/-- The original presented hypersurface, after adjoining `w`, is a polynomial
ring in which the distinguished `p` is the first coordinate. -/
noncomputable def stablePresentationEquiv : PresentationRing ≃ₐ[ℂ] R 5 :=
  shiftQuotientEquiv.trans eliminateQuotientEquiv


-- @@ L84-89 verbatim
private theorem trans_apply_eq {K A B C : Type*} [CommSemiring K]
    [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (e : A ≃ₐ[K] B) (d : B ≃ₐ[K] C) (a : A) (b : B) (c : C)
    (he : e a = b) (hd : d b = c) : e.trans d a = c := by
  rw [AlgEquiv.trans_apply, he, hd]


-- @@ L91-94 verbatim
@[simp] theorem stablePresentationEquiv_p :
    stablePresentationEquiv (Ideal.Quotient.mk presentationIdeal (X 0)) = X 0 :=
  trans_apply_eq shiftQuotientEquiv eliminateQuotientEquiv _ _ _
    shiftQuotientEquiv_p eliminateQuotientEquiv_p


-- @@ L96-105 verbatim
/-- Composition interface: two polynomial presentations of the same algebra,
with the specified images of one element, produce the required automorphism.
This is only a supporting theorem; its hypotheses must be discharged by the
explicit presentation and elimination constructions. -/
theorem oneStable_of_presentations {A : Type*} [CommRing A] [Algebra ℂ A]
    (p : A) (present eliminate : A ≃ₐ[ℂ] R 5)
    (hpresent : present p = stabilize f) (heliminate : eliminate p = X 0) :
    IsOneStableCoordinate f := by
  refine ⟨present.symm.trans eliminate, ?_⟩
  rw [AlgEquiv.trans_apply, ← hpresent, AlgEquiv.symm_apply_apply, heliminate]


-- @@ L107-107 verbatim
end Stabilization


-- @@ L109-118 verbatim
/-- The exact degree-five polynomial of the paper is a coordinate after
adjoining one independent variable. The witnessing automorphism is built from
explicit matrix, exponential, and linear/shear polynomial substitutions. -/
theorem f_isOneStableCoordinate : IsOneStableCoordinate f := by
  exact Stabilization.oneStable_of_presentations
    (Presentation.mk 1 (Presentation.p 1))
    Presentation.stabilizedPresentation
    Stabilization.stablePresentationEquiv
    Presentation.stabilizedPresentation_p
    Stabilization.stablePresentationEquiv_p


-- @@ L120-120 verbatim
end StableCoordinate


-- @@ L122-122 verbatim
end OAI
