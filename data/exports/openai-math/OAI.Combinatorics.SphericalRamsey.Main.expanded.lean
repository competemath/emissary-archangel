import OAI.Combinatorics.SphericalRamsey.Ramsey
import OAI.Combinatorics.SphericalRamsey.CopyInvariant
import OAI.Combinatorics.SphericalRamsey.RealDerivation
import OAI.Combinatorics.SphericalRamsey.Parameter
import OAI.Combinatorics.SphericalRamsey.WitnessCoordinates


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
namespace GrahamSpherical


-- @@ L12-19 verbatim
/-- A single actual real derivation defines avoiding colorings in all dimensions. -/
theorem exists_common_derivation_colorings :
    ∃ D : Derivation ℤ ℝ ℝ,
      D parameter = (1 + parameter ^ 2) / 2 ∧
      ∀ n : ℕ, AvoidsCopy witness (energyColor (derivationEnergy (n := n) D)) := by
  obtain ⟨D, hD⟩ := exists_real_derivation parameter
    ((1 + parameter ^ 2) / 2) parameter_transcendental
  exact ⟨D, hD, fun _ => derivationColor_avoids D hD⟩


-- @@ L21-27 verbatim
/-- The literal twelve-point spherical witness defeats fifty colors in every
positive dimension, hence is not Euclidean Ramsey. No auxiliary premise remains. -/
theorem full_main : Specification.FullAuthoredResult := by
  obtain ⟨D, _hD, hcolors⟩ := exists_common_derivation_colorings
  apply assemble_full_result witness_ncard witness_subset_sphere
  intro n _hn
  exact ⟨energyColor (derivationEnergy (n := n) D), hcolors n⟩


-- @@ L29-29 verbatim
end GrahamSpherical


-- @@ L31-31 verbatim
end


-- @@ L33-33 verbatim
end OAI
