import OAI.Combinatorics.SphericalRamsey.RealTranscendenceBasis
import OAI.Combinatorics.SphericalRamsey.BasisDerivation
import OAI.Combinatorics.SphericalRamsey.AlgebraicExtension


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace GrahamSpherical


-- @@ L10-30 verbatim
/-- Prescribe a derivation at any transcendental real, with an arbitrary real
value. The final scalar need not belong to the rational-function subfield. -/
theorem exists_real_derivation (a c : ℝ) (ha : Transcendental ℚ a) :
    ∃ D : Derivation ℤ ℝ ℝ, D a = c := by
  classical
  obtain ⟨B, haB, hB⟩ := exists_real_transcendenceBasis_containing a ha
  let b : B → ℝ := fun x => (x : ℝ)
  let i : B := ⟨a, haB⟩
  let F := IntermediateField.adjoin ℚ (Set.range b)
  let : Algebra.IsAlgebraic F ℝ := hB.isAlgebraic_field
  obtain ⟨δ, hδ⟩ := exists_derivation_adjoin_coordinate b hB.1 i
  obtain ⟨D, hD⟩ := AlgebraicExtension.exists_extension (K := ℝ) δ
  let x : F := ⟨b i, IntermediateField.subset_adjoin ℚ (Set.range b) ⟨i, rfl⟩⟩
  have hδx : δ x = 1 := by
    exact hδ
  have hDa : D a = 1 := by
    have h := hD x
    rw [hδx, map_one] at h
    exact h
  refine ⟨c • D, ?_⟩
  simp [Derivation.smul_apply, hDa]


-- @@ L32-32 verbatim
end GrahamSpherical


-- @@ L34-34 verbatim
end


-- @@ L36-36 verbatim
end OAI
