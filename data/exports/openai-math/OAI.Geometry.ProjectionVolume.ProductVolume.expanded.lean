import OAI.Geometry.ProjectionVolume.SimplexVolume


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open Set MeasureTheory

-- @@ L8-8 verbatim
open scoped ENNReal


-- @@ L10-10 verbatim
namespace Paper092


-- @@ L12-21 verbatim
theorem splitBlocks_measurePreserving : MeasurePreserving splitBlocks volume volume := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin 20)
  have h₂ := (volume_measurePreserving_piCongrLeft (fun _ : Fin 20 => ℝ)
    (finSumFinEquiv : Fin 10 ⊕ Fin 10 ≃ Fin 20)).symm
  have h₃ := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin 10 ⊕ Fin 10 => ℝ)
  have h₄ := (PiLp.volume_preserving_toLp (Fin 10)).prod
    (PiLp.volume_preserving_toLp (Fin 10))
  convert h₄.comp (h₃.comp (h₂.comp h₁)) using 1
  all_goals rfl


-- @@ L23-28 verbatim
theorem productWitness_volume_product :
    volume productWitness = volume (standardSimplex 10) * volume (standardSimplex 10) := by
  rw [productWitness_eq_preimage,
    splitBlocks_measurePreserving.measure_preimage
      (((standardSimplex_isCompact 10).prod (standardSimplex_isCompact 10)).measurableSet.nullMeasurableSet)]
  exact Measure.prod_prod _ _


-- @@ L30-35 verbatim
theorem productWitness_volume :
    volume productWitness = ENNReal.ofReal ((1 / (Nat.factorial 10 : ℝ)) ^ 2) := by
  rw [productWitness_volume_product, standardSimplex_volume,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring


-- @@ L37-39 verbatim
theorem standardSimplex_volume_real (n : ℕ) :
    (volume (standardSimplex n)).toReal = 1 / (Nat.factorial n : ℝ) := by
  rw [standardSimplex_volume, ENNReal.toReal_ofReal (by positivity)]


-- @@ L41-43 verbatim
theorem productWitness_volume_real :
    (volume productWitness).toReal = (1 / (Nat.factorial 10 : ℝ)) ^ 2 := by
  rw [productWitness_volume, ENNReal.toReal_ofReal (by positivity)]


-- @@ L45-45 verbatim
end Paper092


-- @@ L47-47 verbatim
end


-- @@ L49-49 verbatim
end OAI
