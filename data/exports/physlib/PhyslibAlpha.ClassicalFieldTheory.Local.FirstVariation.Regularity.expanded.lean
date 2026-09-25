/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.Support

-- @@ L9-32 verbatim
/-!
# First variation regularity

## i. Overview

This module contains regularity consequences used in the local Euler-Lagrange criterion: continuity
of the Euler-Lagrange operator from coefficient regularity, and the bridge from coordinate
regularity of the local Lagrangian to the packaged smooth-regularity statement.

## ii. Key results

- `ClassicalFieldTheory.Local.continuous_eulerLagrangeOp_of_regular`
- `ClassicalFieldTheory.Local.hasSmoothEulerLagrangeRegularity_of_contDiffCoordDerivInCoordinates`

## iii. Table of contents

- A. Continuity of the Euler-Lagrange operator
- B. Smooth regularity in coordinates

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics, Chapter 5,
  Theorem 5.2. [ref: cortes_haupt_2016]
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open MeasureTheory

-- @@ L37-37 verbatim
open InnerProductSpace

-- @@ L38-38 verbatim
open Physlib

-- @@ L39-39 verbatim
open scoped BigOperators ContDiff


-- @@ L41-41 verbatim
namespace ClassicalFieldTheory

-- @@ L42-42 verbatim
namespace Local


-- @@ L44-47 verbatim
/-!
## A. Continuity of the Euler-Lagrange operator

-/


-- @@ L49-56 verbatim
/-- The combined regularity package currently needed to derive the local Euler-Lagrange
criterion for a field `f`: smooth coefficient functions along `f`, and continuity of the
corresponding coefficient families along every admissible varied-field family based at `f`. -/
def HasEulerLagrangeRegularityAt (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  Lagrangian.ContDiffCoordDerivAlongField L f ∧
    ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
      Lagrangian.ContinuousCoordDerivAlongFamily L (fun s : ℝ => variedField f η s)


-- @@ L58-62 verbatim
/-- A local Lagrangian has smooth Euler-Lagrange regularity if every smooth field satisfies the
regularity package currently needed by the local first-variation proof. -/
def HasSmoothEulerLagrangeRegularity (L : Lagrangian d m k) : Prop :=
  ∀ f : Space d → EuclideanSpace ℝ (Fin m),
    ContDiff ℝ ∞ f → HasEulerLagrangeRegularityAt L f


-- @@ L64-76 verbatim
lemma continuous_eulerLagrangeTerm_of_regular
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hcoeff : Lagrangian.ContDiffCoordDerivAlongField L f)
    (I : DerivativeIndex d k) (a : Fin m) :
    Continuous (eulerLagrangeTerm L I a f) := by
  have htd : ContDiff ℝ ∞
      (iteratedTotalDerivative k I.1 (L.coordDeriv I a) f) := by
    exact
      Space.iteratedDeriv_contDiff I.1 (hcoeff I a)
  have hsign : ContDiff ℝ ∞
      (fun _ : Space d => (-1 : ℝ) ^ I.1.order) := by
    fun_prop
  exact (hsign.mul htd).continuous


-- @@ L78-85 verbatim
lemma continuous_eulerLagrangeComponent_of_regular
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hcoeff : Lagrangian.ContDiffCoordDerivAlongField L f)
    (a : Fin m) :
    Continuous (eulerLagrangeComponent L a f) := by
  refine continuous_finsetSum Finset.univ ?_
  intro I _
  exact continuous_eulerLagrangeTerm_of_regular L f hcoeff I a


-- @@ L87-95 verbatim
lemma continuous_eulerLagrangeOp_of_regular
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hcoeff : Lagrangian.ContDiffCoordDerivAlongField L f) :
    Continuous (eulerLagrangeOp L f) := by
  let g : Space d → Fin m → ℝ := fun x a => eulerLagrangeComponent L a f x
  have hg : Continuous g := continuous_pi fun a =>
    continuous_eulerLagrangeComponent_of_regular L f hcoeff a
  change Continuous (fun x : Space d => (WithLp.toLp 2 (g x) : EuclideanSpace ℝ (Fin m)))
  fun_prop


-- @@ L97-100 verbatim
/-!
## B. Smooth regularity in coordinates

-/


-- @@ L102-110 verbatim
theorem hasSmoothEulerLagrangeRegularity_of_contDiffCoordDerivInCoordinates
    (L : Lagrangian d m k) (hcoord : Lagrangian.ContDiffCoordDerivInCoordinates L) :
    HasSmoothEulerLagrangeRegularity L := by
  intro f hf
  refine ⟨Lagrangian.contDiffCoordDerivAlongField_of_inCoordinates L hcoord f hf, ?_⟩
  intro η
  exact Lagrangian.continuousCoordDerivAlongFamily_of_inCoordinates L hcoord
    (fun s : ℝ => variedField f η s)
    (continuous_jetBaseCoordinates_variedField k f η hf)


-- @@ L112-112 verbatim
end Local

-- @@ L113-113 verbatim
end ClassicalFieldTheory
