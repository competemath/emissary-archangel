import OAI.NumberTheory.DirichletL.Detector.MellinPoisson


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators ContDiff

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L11-23 verbatim
def poissonPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y:ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p∈C.excluded, ¬p∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s/Y) * CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q_s*X):ℂ)) *
      verticalIntegral 4 (fun t => (Real.sqrt q_s:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D a has W₀
          (elementNorm C.generator*q_s*X) t p.1 p.2)
    else 0


-- @@ L25-50 verbatim
theorem markedPhysicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀)
    (hWs : ContDiff ℝ ∞ W₀) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) :
    markedPhysicalProbe η C D W₀ W₁ X Y Z = poissonPhysicalProbe η C D W₀ W₁ X Y Z := by
  unfold markedPhysicalProbe poissonPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    have ha := supported_primaryGenerator_ne_zero s.val s.property
    have has := (supported_span_primaryGenerator_iff s.val).mpr s.property
    have hn : elementNorm (primaryGenerator s.val) = (Ideal.absNorm s.val:ℝ) := by
      unfold elementNorm
      rw [(primaryGenerator_spec s.val ha).1]
    have hb : 0<elementNorm C.generator := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
    have hs : 0<(Ideal.absNorm s.val:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
    have hK : 0<elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := mul_pos (mul_pos hb hs) hX
    simpa only [hn] using inner_mellin_poisson η C D (primaryGenerator s.val) has
      W₀ hWc hWs (elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X) Z hK hZ
  · rfl


-- @@ L52-56 verbatim
theorem physicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀) (hWs : ContDiff ℝ ∞ W₀)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) :
    physicalProbe η C W₀ W₁ X Y Z = poissonPhysicalProbe η C 1 W₀ W₁ X Y Z :=
  markedPhysicalProbe_eq_poisson η C 1 W₀ W₁ hWc hWs X Y Z hX hZ


-- @@ L58-58 verbatim
end SevenEighths.ProbePhysical

-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
end OAI
