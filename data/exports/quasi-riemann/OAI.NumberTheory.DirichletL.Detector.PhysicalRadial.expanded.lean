import OAI.NumberTheory.DirichletL.Detector.RadialSpectral
import OAI.NumberTheory.DirichletL.Detector.Transformed


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators ContDiff

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L9-9 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-24 verbatim
def radialMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ) (X Y Z σ : ℝ) : ℂ :=
  (Y:ℂ)⁻¹*∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      W1 (qs/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ))*
      verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
        ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
          (elementNorm C.generator*qs*X) σ t p.1 p.2)
    else 0


-- @@ L26-61 verbatim
theorem markedPhysicalProbe_eq_radial_mellin (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Set.Icc a b)
    (X Y Z σ : ℝ) (hX : 0<X) (hZ : 0<Z) (hσ : 1<σ) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      radialMellinPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z σ := by
  have hWc : HasCompactSupport (W0 : ℝ→ℂ) := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW
  rw [markedPhysicalProbe_eq_poisson η (calibrationForSet S hS) D W0 W1 hWc (W0.smooth (⊤:ℕ∞)) X Y Z hX hZ]
  unfold poissonPhysicalProbe radialMellinPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    congr 1
    unfold verticalIntegral
    congr 1
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    congr 1
    apply tsum_congr
    intro p
    have hcs : IsCoprime (calibrationForSet S hS).generator (primaryGenerator s.val) := by
      apply calibrationForSet_coprime_of_excluded S hS
      rw [(primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1]
      simpa only [calibrationForSet_excluded] using hs
    have hK : 0<elementNorm (calibrationForSet S hS).generator*(Ideal.absNorm s.val:ℝ)*X :=
      mul_pos (mul_pos (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero)
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1))) hX
    simpa only [calibrationForSet_excluded] using transformedSpectralTerm_radial_mellin η S hS hSne D
      (primaryGenerator s.val) ((supported_span_primaryGenerator_iff s.val).mpr s.property) hcs
      W0 a b ha hW _ σ hK hσ _ p.1 p.2
  · rfl


-- @@ L63-63 verbatim
end SevenEighths.ProbePhysical

-- @@ L64-64 verbatim
end


-- @@ L66-66 verbatim
end OAI
