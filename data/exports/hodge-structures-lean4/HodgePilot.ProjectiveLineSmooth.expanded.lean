import HodgePilot.ProjectiveLineUnits
import HodgePilot.ChartsSmoothAffine


-- @@ L4-75 verbatim
/-! # The projective line: the structure morphism is smooth of relative
# dimension one

Golden-path smoothness module.  For the projective line
`p1 = Proj ℂ[X₀, X₁]` of `HodgePilot.ProjectiveLine` and its structure
morphism `structMor : p1 ⟶ Spec ℂ`, this module proves the instance

* `SmoothOfRelativeDimension 1 structMor` — **the structure morphism of
  the projective line is smooth of relative dimension one**, in the sense
  of Mathlib's `AlgebraicGeometry.SmoothOfRelativeDimension`: every point
  has an affine open neighbourhood on which the induced ring map is
  standard smooth of relative dimension `1`.

The ladder (all pieces exhibited, nothing hypothesized):

1. `instIsStandardSmoothOfRelativeDimensionPoly` — the polynomial ring
   `ℂ[x₁, …, xₙ]` is standard smooth of relative dimension `n` over `ℂ`:
   the repo's tautological submersive presentation
   (`HodgePilot.ChartsStandardSmooth.affinePresentation`; `n` generators,
   no relations, unit Jacobian) packaged into Mathlib's existence-form
   class `Algebra.IsStandardSmoothOfRelativeDimension` by its dimension
   arithmetic (`affinePresentation_dimension`).
2. `isStandardSmoothOfRelativeDimension_away` — the chart rings
   `(ℂ[X₀,X₁]_{Xᵢ})₀` are standard smooth of relative dimension `1` over
   `ℂ`: transport of 1. along the wave-2 chart isomorphism
   `polyChartEquiv : ℂ[t] ≃ₐ[ℂ] Away 𝒜 Xᵢ`
   (`Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv`), at the
   single `ℂ`-structure `instAlgebraAwayC` of
   `HodgePilot.ProjectiveLineUnits`.
3. `awayι_structMor` — the chart-to-base composite
   `Spec (Away 𝒜 Xᵢ) ⟶ p1 ⟶ Spec ℂ` is `Spec.map` of the constants map
   `algebraMap ℂ (Away 𝒜 Xᵢ)` (the pin's `Proj.awayι_toSpecZero`
   composed with wave 1's grade-zero identification `gradeZeroEquiv`).
4. `instSmoothOfRelativeDimensionStructMor` — the two charts cover `p1`
   (`iSup_basicOpen_X_eq_top`), the property is Zariski-local at the
   source (Mathlib's `HasRingHomProperty` for
   `SmoothOfRelativeDimension`), and on each chart it is 2., via
   `HasRingHomProperty.Spec_iff` and the repo's
   `ChartsSmoothAffine.locally_of_isStandardSmoothOfRelativeDimension`.

`instSmoothStructMor : Smooth structMor` records the pin's implication
`SmoothOfRelativeDimension.smooth` as an instance for downstream
synthesis; it adds no content beyond the headline instance.

## Claim discipline

The statement proved is exactly Mathlib's
`AlgebraicGeometry.SmoothOfRelativeDimension 1 structMor` — an
affine-locally standard-smooth statement for one exhibited structure
morphism.  "Relative dimension" is Mathlib's presentation-counting notion
(the `Algebra.Presentation.dimension` of the chart presentations,
`#variables − #relations`, the rank of the Kähler module Ω¹ for a
submersive presentation); **no Krull-dimension statement is made or
claimed anywhere**.  No consequence of smoothness is claimed in this
module: no manifold structure on any point space, no predicate evaluation
of any kind, no cohomological statement, and no comparison with any other
notion of smoothness.  No canonicity is claimed for the exhibited chart
presentations or isomorphisms.  Properness of `structMor` (wave 1)
remains the pin's EGA properness; no projectivity claim is made.  Nothing
here makes the Hodge conjecture statable.

## Credits

`Proj`, its charts and `toSpecZero` are Andrew Yang's and Jujian Zhang's
Mathlib infrastructure; the smoothness / standard-smoothness morphism
framework (`SmoothOfRelativeDimension`, `HasRingHomProperty`, submersive
presentations) is by Christian Merten, Jung Tao Cheng and Andrew Yang
(AIM workshop "Formalizing algebraic geometry", June 2024); the chart
isomorphisms consumed here are `HodgePilot.ProjectiveLineUnits` (wave 2);
the submersive-presentation anchor and the `RingHom.Locally` packaging
are `HodgePilot.ChartsStandardSmooth` / `HodgePilot.ChartsSmoothAffine`.
-/


-- @@ L77-77 verbatim
set_option maxHeartbeats 1000000

-- @@ L78-78 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L80-80 verbatim
noncomputable section


-- @@ L82-82 verbatim
open CategoryTheory TopologicalSpace Opposite

-- @@ L83-83 verbatim
open AlgebraicGeometry HomogeneousLocalization


-- @@ L85-85 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L87-87 verbatim
namespace HodgePilot


-- @@ L89-89 verbatim
namespace ProjectiveLineSmooth


-- @@ L91-91 verbatim
open HodgePilot.ProjectiveLine HodgePilot.ProjectiveLineUnits


-- @@ L93-94 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L96-102 verbatim
/-! ## Ladder step 1.  The polynomial ring is standard smooth of relative
dimension `n` over `ℂ`

The repo's tautological submersive presentation of affine `n`-space
(`ChartsStandardSmooth.affinePresentation`), packaged into Mathlib's
existence-form class.  Not a pin instance (verified by fresh grep); an
upstream-shaped chip. -/


-- @@ L104-111 verbatim
/-- **`ℂ[x₁, …, xₙ]` is standard smooth of relative dimension `n` over
`ℂ`**: the tautological submersive presentation (`n` generators, no
relations, unit Jacobian) has dimension `n`.  The relative dimension is
`Algebra.Presentation.dimension`; no Krull-dimension statement is made. -/
instance instIsStandardSmoothOfRelativeDimensionPoly (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n ℂ (MvPolynomial (Fin n) ℂ) :=
  (ChartsStandardSmooth.affinePresentation n).isStandardSmoothOfRelativeDimension
    (ChartsStandardSmooth.affinePresentation_dimension n)


-- @@ L113-114 verbatim
/-! ## Ladder step 2.  The chart rings are standard smooth of relative
dimension `1` over `ℂ` -/


-- @@ L116-124 verbatim
/-- **The chart rings are standard smooth of relative dimension `1`**:
transport of `instIsStandardSmoothOfRelativeDimensionPoly` along the
wave-2 chart isomorphism `polyChartEquiv : ℂ[t] ≃ₐ[ℂ] (ℂ[X₀,X₁]_{Xᵢ})₀`,
at the single `ℂ`-structure `instAlgebraAwayC`. -/
theorem isStandardSmoothOfRelativeDimension_away (i j : Fin 2) (hij : i ≠ j) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ
      (Away 𝒜₂ (MvPolynomial.X i)) :=
  Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (polyChartEquiv i j hij)


-- @@ L126-127 verbatim
/-- In `Fin 2`, every index differs from its complement `1 - i`. -/
theorem fin_two_ne_one_sub : ∀ i : Fin 2, i ≠ 1 - i := by decide


-- @@ L129-138 verbatim
/-- The chart-ring smoothness datum in the ring-hom-property form consumed
by Mathlib's `HasRingHomProperty` for `SmoothOfRelativeDimension`
(`RingHom.Locally`, via the repo's
`ChartsSmoothAffine.locally_of_isStandardSmoothOfRelativeDimension`). -/
theorem locally_isStandardSmooth_away (i : Fin 2) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i))) :=
  haveI := isStandardSmoothOfRelativeDimension_away i (1 - i)
    (fin_two_ne_one_sub i)
  ChartsSmoothAffine.locally_of_isStandardSmoothOfRelativeDimension


-- @@ L140-141 verbatim
/-! ## Ladder step 3.  The chart-to-base composite is `Spec.map` of the
constants map -/


-- @@ L143-155 verbatim
/-- **The chart-to-base composite**: the open immersion of the chart
`Spec (ℂ[X₀,X₁]_{Xᵢ})₀ ⟶ p1` followed by the structure morphism is
`Spec.map` of the constants map `algebraMap ℂ (Away 𝒜 Xᵢ)` (the algebra
structure of `instAlgebraAwayC`, whose constants map is literally the
grade-zero composite `ℂ → 𝒜 0 → Away 𝒜 Xᵢ`). -/
theorem awayι_structMor (i : Fin 2) :
    Proj.awayι 𝒜₂ (MvPolynomial.X i) (X_mem_grade_one i) one_pos ≫ structMor =
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)))) := by
  show Proj.awayι 𝒜₂ (MvPolynomial.X i) (X_mem_grade_one i) one_pos ≫
      (Proj.toSpecZero 𝒜₂ ≫ Spec.map gradeZeroEquiv.toCommRingCatIso.hom) = _
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1


-- @@ L157-157 verbatim
/-! ## Ladder step 4.  The two-chart cover and the instance -/


-- @@ L159-166 verbatim
/-- The basic opens of the two variables cover the projective line (the
`Fin 2`-indexed `iSup` form of wave 1's `U0_sup_U1`, consumed by the
source-locality lemma). -/
theorem iSup_basicOpen_X_eq_top :
    (⨆ i : Fin 2, Proj.basicOpen 𝒜₂ (MvPolynomial.X i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' 𝒜₂
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)
    (fun i => ⟨1, X_mem_grade_one i⟩) adjoin_range_X_eq_top


-- @@ L168-186 verbatim
/-- **The structure morphism of the projective line is smooth of relative
dimension one** (Mathlib's `AlgebraicGeometry.SmoothOfRelativeDimension`):
verified on the two-chart cover, where each chart ring is standard smooth
of relative dimension `1` over `ℂ` by the wave-2 chart isomorphism.
"Relative dimension" is the presentation-counting notion throughout; no
Krull-dimension statement is made, and no consequence of smoothness is
claimed in this module. -/
instance instSmoothOfRelativeDimensionStructMor :
    SmoothOfRelativeDimension 1 structMor := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
    (P := @SmoothOfRelativeDimension 1) _ iSup_basicOpen_X_eq_top]
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1)
      (Proj.basicOpenIsoSpec 𝒜₂ (MvPolynomial.X i)
        (X_mem_grade_one i) one_pos).inv,
    Proj.basicOpenIsoSpec_inv_ι_assoc, awayι_structMor i,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact locally_isStandardSmooth_away i


-- @@ L188-192 verbatim
/-- The structure morphism is smooth (the pin's implication
`SmoothOfRelativeDimension.smooth`, recorded as an instance for downstream
synthesis; no content beyond `instSmoothOfRelativeDimensionStructMor`). -/
instance instSmoothStructMor : AlgebraicGeometry.Smooth structMor :=
  SmoothOfRelativeDimension.smooth 1 structMor


-- @@ L194-201 verbatim
/-! ## Synthesis receipts (falsifier discipline)

The binder shape the smooth-proper machinery consumes downstream is
`[SmoothOfRelativeDimension d g] [AlgebraicGeometry.IsProper g]` (e.g.
`HodgePilot.CalibrationZero.isHodgeClassProper_zero`).  Both instances
synthesize for `g := structMor`, `d := 1` with no hypothesized binder.
These are instance-synthesis receipts only; no predicate statement on
`p1` is made or recorded in this module. -/


-- @@ L203-203 verbatim
example : SmoothOfRelativeDimension 1 structMor := inferInstance


-- @@ L205-205 verbatim
example : AlgebraicGeometry.IsProper structMor := inferInstance


-- @@ L207-207 verbatim
end ProjectiveLineSmooth


-- @@ L209-209 verbatim
end HodgePilot


-- @@ L211-211 verbatim
end
