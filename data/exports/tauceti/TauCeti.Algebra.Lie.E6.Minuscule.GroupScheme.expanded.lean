/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Basic
public import TauCeti.Algebra.Lie.E6.RootCharacters
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus


-- @@ L17-52 verbatim
/-!
# The full-weight type-E6 minuscule carrier

This file feeds the explicit `27`-dimensional type-`E₆` minuscule representation, its admissible
coordinate lattice, and its full set of weights into the Kostant toral-closure construction. The
result is an explicit affine group scheme over `ℤ`, cut out inside `GL₂₇` by the largest Hopf
ideal killed by the twelve numbered simple-root subgroups and the represented rank-six split
torus.

The root-subgroup characters are identified with the positive and negative simple roots of
`TauCeti.DynkinType.e6SimplyConnectedRootDatum`. Since the minuscule weights span the entire
character lattice, the represented split torus is a closed immersion. The scheme-level pinning
equation records its conjugation action on every numbered root subgroup.

No reductivity, smoothness, maximality of the torus, or identification of the carrier's root datum
is asserted here. Those are subsequent steps in the pinned Chevalley--Demazure construction.

## Main declarations

* `TauCeti.E6Minuscule.groupScheme`: the minuscule Kostant toral-closure carrier over `ℤ`.
* `TauCeti.E6Minuscule.rootSubgroup`: its twelve numbered simple-root subgroup morphisms.
* `TauCeti.E6Minuscule.weightTorus`: its closed rank-six split torus.
* `TauCeti.E6Minuscule.points`: its matrix-valued points over a commutative ring.
* `TauCeti.E6Minuscule.rootSubgroupPoints`: its numbered root subgroups on matrix-valued points.
* `TauCeti.E6Minuscule.weightTorus_conj_rootSubgroup`: the scheme-level pinning equation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
* The carrier API follows the formal templates in
  `TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic` and
  `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme`, specialized here using the
  type-`E₆` minuscule representation, lattice, weights, and root characters.
-/


-- @@ L54-54 verbatim
public section


-- @@ L56-56 verbatim
open scoped Matrix


-- @@ L58-58 verbatim
universe v


-- @@ L60-60 verbatim
namespace TauCeti.E6Minuscule


-- @@ L62-62 verbatim
open TauCeti.E6


-- @@ L64-64 verbatim
local notation "Λ" => TauCeti.coordinateLattice (Fin 27)

-- @@ L65-65 verbatim
local notation "𝓑" => TauCeti.coordinateLatticeBasis (Fin 27)


-- @@ L67-67 verbatim
open AlgebraicGeometry CategoryTheory

-- @@ L68-68 verbatim
open TauCeti.DynkinType

-- @@ L69-69 verbatim
open TauCeti.UniversalEnvelopingAlgebra

-- @@ L70-70 verbatim
open scoped CategoryTheory.MonObj TensorProduct


-- @@ L72-72 verbatim
attribute [local instance] TauCeti.moduleNNRat

-- @@ L73-73 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing

-- @@ L74-74 verbatim
attribute [local instance high] Algebra.toModule


-- @@ L76-76 verbatim
/-! ## The pinned carrier -/


-- @@ L78-87 verbatim
/-- The Hopf ideal cutting out the type-`E₆` minuscule carrier inside `GL₂₇`. -/
noncomputable def definingIdeal :
    HopfIdeal ℤ (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ 27) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
    (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
      rw [TauCeti.serreKostantForm_def]
      exact hu) hv)
    weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight


-- @@ L89-99 verbatim
/-- The defining ideal is the ideal supplied by the generic Kostant toral-closure construction. -/
theorem definingIdeal_def :
    definingIdeal =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
        (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv)
        weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight := by
  rw [definingIdeal]


-- @@ L101-110 verbatim
/-- The full-weight type-`E₆` minuscule carrier over `ℤ`, obtained as the smallest closed
subgroup scheme of `GL₂₇` containing the represented numbered root subgroups and weight torus. -/
noncomputable abbrev groupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
    (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
      rw [TauCeti.serreKostantForm_def]
      exact hu) hv)
    weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight


-- @@ L112-116 verbatim
/-- The quotient-spectrum presentation of the type-`E₆` minuscule carrier. -/
theorem groupScheme_def :
    groupScheme = CommHopfAlgCat.quotientSpec
      (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal := by
  rw [groupScheme, definingIdeal]


-- @@ L118-126 verbatim
/-- The canonical inclusion of the type-`E₆` minuscule carrier into `GL₂₇`. -/
noncomputable def carrierι : groupScheme ⟶ TauCeti.GeneralLinear.groupScheme ℤ 27 :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
    (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
      rw [TauCeti.serreKostantForm_def]
      exact hu) hv)
    weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight


-- @@ L128-137 verbatim
/-- The carrier inclusion is the generic Kostant toral-closure inclusion. -/
theorem carrierι_def :
    carrierι = TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι
      (TauCeti.serreRootGenerator weightTable.cartanMatrix)
      (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
      (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight := by
  rw [carrierι]


-- @@ L139-143 verbatim
/-- The type-`E₆` minuscule carrier is a closed subgroup scheme of `GL₂₇`. -/
instance isClosedImmersion_carrierι : IsClosedImmersion carrierι.hom.hom.left := by
  rw [carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantToralGroupSchemeι
    _ _ _ _ _ _ _ _


-- @@ L145-154 verbatim
/-- A positive or negative numbered simple-root subgroup of the type-`E₆` carrier. -/
noncomputable def rootSubgroup (k : Fin 6 ⊕ Fin 6) :
    AdditiveGroup.groupScheme ℤ ⟶ groupScheme :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
    (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
      rw [TauCeti.serreKostantForm_def]
      exact hu) hv)
    weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight k


-- @@ L156-166 verbatim
/-- The root subgroup is the one supplied by the generic Kostant toral-closure construction. -/
theorem rootSubgroup_def (k : Fin 6 ⊕ Fin 6) :
    rootSubgroup k =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
        (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv)
        weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight k := by
  rw [rootSubgroup]


-- @@ L168-182 verbatim
/-- Including a numbered root subgroup into `GL₂₇` recovers its represented divided-power
exponential subgroup. -/
@[simp]
theorem rootSubgroup_comp_carrierι (k : Fin 6 ⊕ Fin 6) :
    rootSubgroup k ≫ carrierι =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroup
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
        (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv) k
        (weightTable.isNilpotent_rep_serreRootGenerator k) 𝓑 := by
  rw [rootSubgroup, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_comp_ι
    _ _ _ _ _ _ _ _ k


-- @@ L184-192 verbatim
/-- The represented rank-six split weight torus in the type-`E₆` carrier. -/
noncomputable def weightTorus : SplitTorus.groupScheme ℤ (Fin 6) ⟶ groupScheme :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
    (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
      rw [TauCeti.serreKostantForm_def]
      exact hu) hv)
    weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight


-- @@ L194-204 verbatim
/-- The weight torus is the one supplied by the generic Kostant toral-closure construction. -/
theorem weightTorus_def :
    weightTorus =
      TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
        (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv)
        weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight := by
  rw [weightTorus]


-- @@ L206-214 verbatim
/-- Including the weight torus into `GL₂₇` recovers the diagonal torus of the minuscule
weights. -/
@[simp]
theorem weightTorus_comp_carrierι :
    weightTorus ≫ carrierι =
      TauCeti.GeneralLinear.weightTorus (R := ℤ) weightTable.weight := by
  rw [weightTorus, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_comp_ι
    _ _ _ _ _ _ _ _


-- @@ L216-222 verbatim
/-- The minuscule weights make the represented split torus a closed subgroup scheme of the
carrier. -/
instance isClosedImmersion_weightTorus : IsClosedImmersion weightTorus.hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantWeightTorusToToral
    _ _ _ _ _ _ _ _ (by
      rw [weightTable_weight]
      exact span_range_e6MinusculeWeight_eq_top)


-- @@ L224-233 verbatim
/-- Two morphisms out of the type-`E₆` carrier agree when they agree on its numbered root
subgroups and represented split torus. -/
@[ext]
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (f g : groupScheme ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ k, rootSubgroup k ≫ f = rootSubgroup k ≫ g)
    (htorus : weightTorus ≫ f = weightTorus ≫ g) : f = g := by
  exact TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme_hom_ext
    _ _ _ _ _ _ _ _ f g hroot htorus


-- @@ L235-235 verbatim
/-! ## Matrix-valued points -/


-- @@ L237-246 verbatim
/-- The matrix-valued points of the type-`E₆` minuscule carrier. -/
noncomputable def points (A : Type v) [CommRing A] :
    Subgroup (_root_.Matrix.GeneralLinearGroup (Fin 27) A) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
    (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
      rw [TauCeti.serreKostantForm_def]
      exact hu) hv)
    weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight A


-- @@ L248-253 verbatim
/-- The carrier points are exactly the invertible matrices cut out by the defining Hopf ideal. -/
theorem points_def (A : Type v) [CommRing A] :
    points A = TauCeti.GeneralLinear.hopfIdealPointsSubgroup 27 definingIdeal A := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def
    _ _ _ _ _ _ _ _ A


-- @@ L255-265 verbatim
/-- A matrix is a carrier point exactly when its associated convolution point kills the
defining Hopf ideal. -/
@[simp]
theorem mem_points_iff (A : Type v) [CommRing A]
    (g : _root_.Matrix.GeneralLinearGroup (Fin 27) A) :
    g ∈ points A ↔
      ∀ x ∈ definingIdeal,
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ℤ) 27).symm g).ofConv x = 0 := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff
    _ _ _ _ _ _ _ _ A g


-- @@ L267-275 verbatim
/-- The parametrized numbered root subgroup inside the type-`E₆` minuscule carrier points. -/
noncomputable def rootSubgroupPoints (k : Fin 6 ⊕ Fin 6) (A : Type v) [CommRing A] :
    Multiplicative A →* points A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralRootSubgroupPoints
      (TauCeti.serreRootGenerator weightTable.cartanMatrix)
      (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
      (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv) weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight k A


-- @@ L277-290 verbatim
/-- A numbered root-subgroup point is its represented divided-power exponential matrix. -/
@[simp]
theorem coe_rootSubgroupPoints (k : Fin 6 ⊕ Fin 6) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    (rootSubgroupPoints k A u : _root_.Matrix.GeneralLinearGroup (Fin 27) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
        (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv) k (weightTable.isNilpotent_rep_serreRootGenerator k) 𝓑
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
  exact TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints
    _ _ _ _ _ _ _ _ k A u


-- @@ L292-300 verbatim
/-- The split weight torus on matrix-valued points of the type-`E₆` carrier. -/
noncomputable def weightTorusPoints (A : Type v) [CommRing A] :
    (Fin 6 → Aˣ) →* points A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralWeightTorusPoints
    (TauCeti.serreRootGenerator weightTable.cartanMatrix)
    (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
    (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
      rw [TauCeti.serreKostantForm_def]
      exact hu) hv) weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight A


-- @@ L302-309 verbatim
/-- A minuscule weight-torus point is the diagonal matrix obtained by evaluating each weight. -/
@[simp]
theorem coe_weightTorusPoints (A : Type v) [CommRing A] (s : Fin 6 → Aˣ) :
    (weightTorusPoints A s : _root_.Matrix.GeneralLinearGroup (Fin 27) A) =
      TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix
        (Λ).toAddSubgroup 𝓑 weightTable.weight s := by
  exact TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints
    _ _ _ _ _ _ _ _ A s


-- @@ L311-311 verbatim
/-! ## The pinning equation -/


-- @@ L313-335 verbatim
/-- **Conjugation by the minuscule weight torus acts on each numbered root subgroup through its
positive or negative pinned simple-root character.** -/
@[simp]
theorem weightTorus_conj_rootSubgroup (k : Fin 6 ⊕ Fin 6) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 6)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup k).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (rootGeneratorWeight k) : A) * u)) ≫
        (rootSubgroup k).hom.hom :=
  kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
      _ _ _ _ _ _ _ weightTable.isCartanWeightVector_coordinateLatticeBasis
      weightTable.isNilpotent_rep_serreRootGenerator A
      (by intro j; rw [weightTable_cartanMatrix]; exact lie_serreH_rootGenerator k j)
      s u


-- @@ L337-337 verbatim
end TauCeti.E6Minuscule
