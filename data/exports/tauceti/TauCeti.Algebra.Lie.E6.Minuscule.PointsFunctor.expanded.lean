/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme


-- @@ L11-24 verbatim
/-!
# Presented points of the type-E₆ minuscule carrier

`TauCeti.E6Minuscule.pointsPresentation` presents the carrier's matrix points by its defining
integral Hopf ideal. The shared `GeneralLinear.IntegralPointsPresentation` API supplies maps
of value rings, their functoriality, and the representing equivalence with quotient-algebra
points. This file proves that those maps preserve the pinned root subgroups and weight torus.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  Sections 1.15 and 1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
-/


-- @@ L26-26 verbatim
public section


-- @@ L28-28 verbatim
namespace TauCeti.E6Minuscule


-- @@ L30-30 verbatim
local notation "Λ" => TauCeti.coordinateLattice (Fin 27)

-- @@ L31-31 verbatim
local notation "𝓑" => TauCeti.coordinateLatticeBasis (Fin 27)


-- @@ L33-33 verbatim
universe v v'


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-41 verbatim
/-- The carrier's matrix points, presented by its defining integral Hopf ideal. -/
abbrev pointsPresentation (A : Type v) [CommRing A] :
    TauCeti.GeneralLinear.IntegralPointsPresentation 27 definingIdeal A where
  val := points A
  property := points_def A


-- @@ L43-43 verbatim
variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]


-- @@ L45-66 verbatim
/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem map_rootSubgroupPoints (f : A →+* B) (i : Fin 6 ⊕ Fin 6)
    (u : Multiplicative A) :
    (pointsPresentation A).map (pointsPresentation B) f (rootSubgroupPoints i A u) =
      rootSubgroupPoints i B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralRootSubgroupPoints
      (e := TauCeti.serreRootGenerator weightTable.cartanMatrix)
      (h := TauCeti.serreH ℚ weightTable.cartanMatrix) (ρ := weightTable.rep)
      (M := (Λ).toAddSubgroup)
      (hM := fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      (hnil := weightTable.isNilpotent_rep_serreRootGenerator)
      (b := 𝓑) (wt := weightTable.weight) f i u)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints] using h


-- @@ L68-88 verbatim
/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem map_weightTorusPoints (f : A →+* B) (s : Fin 6 → Aˣ) :
    (pointsPresentation A).map (pointsPresentation B) f (weightTorusPoints A s) =
      weightTorusPoints B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (UniversalEnvelopingAlgebra.map_kostantToralWeightTorusPoints
      (e := TauCeti.serreRootGenerator weightTable.cartanMatrix)
      (h := TauCeti.serreH ℚ weightTable.cartanMatrix) (ρ := weightTable.rep)
      (M := (Λ).toAddSubgroup)
      (hM := fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      (hnil := weightTable.isNilpotent_rep_serreRootGenerator)
      (b := 𝓑) (wt := weightTable.weight) f s)
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map] at h
  rw [TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map]
  simpa only [coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints] using h


-- @@ L90-90 verbatim
end


-- @@ L92-92 verbatim
end TauCeti.E6Minuscule
