import NLAlib.Matrix.Functions.KTransformLowerEdge
import NLAlib.Matrix.Functions.KTransformReflection
import NLAlib.Matrix.Functions.KTransformCompactStieltjesLaw


-- @@ L5-10 verbatim
/-! # Native upper-edge formula by actual sample reflection

The reflected sample law constructs an actual upper branch whose true
Stieltjes measure is the reflection of the original measure. Applying
the proved lower-edge formula then identifies the actual upper edge.
-/


-- @@ L12-12 verbatim
noncomputable section

-- @@ L13-13 verbatim
set_option autoImplicit false

-- @@ L14-14 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L15-15 verbatim
open Matrix MeasureTheory Set

-- @@ L16-16 verbatim
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology

-- @@ L17-17 verbatim
namespace NLAlib

-- @@ L18-18 verbatim
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

-- @@ L19-19 verbatim
local notation "M" => Matrix n n ℂ


-- @@ L21-61 verbatim
/-- The true upper edge is minus the native lower-edge variational
supremum for the original sample law reflected by T↦−T. The proof
constructs and identifies the reflected Stieltjes law by native
nonlinear uniqueness; no spectral reflection is assumed.
Source: Montanari--Saeed (2026), Theorem 1 and Remark 3.1.
atlas: block-wishart-variational-edges (partial) -/
theorem sSup_support_eq_neg_sSup_lambdaMin_matrixKTransform_map_neg
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ) (hmass : μ.mass=1)
    (hcompact : IsCompact (μ : Measure ℝ).support)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ)) :
    sSup (μ : Measure ℝ).support =
      -sSup ((fun S : M => lambdaMin (matrixKTransform
        (ν.map (fun T : selfAdjoint M => -T)) α S)) ''
          matrixKStableDomain (ν.map (fun T : selfAdjoint M => -T)) α) := by
  let η : Measure (selfAdjoint M) := ν.map (fun T : selfAdjoint M => -T)
  let ρ : FiniteMeasure ℝ := μ.map (fun t : ℝ => -t)
  have hηs : η.support=(fun T : selfAdjoint M => -T) '' ν.support :=
    Measure.support_map_homeomorph ν (Homeomorph.neg (selfAdjoint M))
  have hρs : (ρ : Measure ℝ).support=(fun t : ℝ => -t) '' (μ : Measure ℝ).support :=
    Measure.support_map_homeomorph (μ : Measure ℝ) (Homeomorph.neg ℝ)
  have hηc : IsCompact η.support := by rw [hηs]; exact hν.image continuous_neg
  have hρc : IsCompact (ρ : Measure ℝ).support := by rw [hρs]; exact hcompact.image continuous_neg
  have : IsProbabilityMeasure η := ν.isProbabilityMeasure_map continuous_neg.measurable.aemeasurable
  have hρmass : ρ.mass=1 := by
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass,FiniteMeasure.toMeasure_map,
      Measure.map_apply continuous_neg.measurable MeasurableSet.univ,preimage_univ,
      ← FiniteMeasure.ennreal_mass,hmass]
  obtain ⟨H,hHa,hH,_hreflect,hrep⟩ :=
    exists_analytic_matrixKTransform_reflected_stieltjes_branch ν hν α hα F hF μ hμ
  have hlower := sInf_support_eq_sSup_lambdaMin_matrixKTransform
    η hηc α hα H hHa hH ρ hρmass hρc hrep
  have hedge : sInf (ρ : Measure ℝ).support= -sSup (μ : Measure ℝ).support := by
    rw [hρs,Set.image_neg_eq_neg,Real.sInf_neg]
  rw [hedge] at hlower
  exact (neg_eq_iff_eq_neg).mp hlower


-- @@ L63-99 verbatim
/-- Every original compact Hermitian probability law constructs its
actual nonlinear K branch and characterized compact Stieltjes law,
whose two spectral support edges satisfy the source variational
formulas. Strict positivity is equivalent to the actual finite
positive derivative witnesses. Singular and indefinite block samples
are included. No branch, law, gap, variational equality or optimizer
attainment is assumed.
Source: Montanari--Saeed (2026), Theorems 1 and 3, Corollary 1,
and Remark 3.1.
atlas: block-wishart-variational-edges -/
theorem exists_matrixKTransform_law_variational_support_edges
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) :
    ∃ F : ℂ → M, AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} ∧
      (∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
        matrixKTransform ν α (F z)=z•1) ∧
      ∃ μ : FiniteMeasure ℝ, μ.mass=1 ∧ IsCompact (μ : Measure ℝ).support ∧
        (∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
          ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ)) ∧
        (sInf (μ : Measure ℝ).support =
          sSup ((fun S : M => lambdaMin (matrixKTransform ν α S)) '' matrixKStableDomain ν α)) ∧
        (0<sInf (μ : Measure ℝ).support ↔
          ∃ S B : M, S.PosDef ∧ B.PosDef ∧
            (∀ T∈ν.support,(S⁻¹+T.val).PosDef) ∧
            (matrixKTransformDeriv ν α S B).PosDef ∧ (matrixKTransform ν α S).PosDef) ∧
        sSup (μ : Measure ℝ).support =
          -sSup ((fun S : M => lambdaMin (matrixKTransform
            (ν.map (fun T : selfAdjoint M => -T)) α S)) ''
              matrixKStableDomain (ν.map (fun T : selfAdjoint M => -T)) α) := by
  obtain ⟨F,hFa,hF,μ,hμ,_huniq⟩ :=
    exists_analytic_matrixKTransform_compact_stieltjes_probability_measure ν hν α hα
  exact ⟨F,hFa,hF,μ,hμ.1,hμ.2.1,hμ.2.2,
    sInf_support_eq_sSup_lambdaMin_matrixKTransform ν hν α hα F hFa hF μ hμ.1 hμ.2.1 hμ.2.2,
    sInf_support_pos_iff_exists_matrixKTransform_posDef_witness ν hν α hα F hFa hF
      μ hμ.1 hμ.2.1 hμ.2.2,
    sSup_support_eq_neg_sSup_lambdaMin_matrixKTransform_map_neg ν hν α hα F hF
      μ hμ.1 hμ.2.1 hμ.2.2⟩


-- @@ L101-101 verbatim
end NLAlib
