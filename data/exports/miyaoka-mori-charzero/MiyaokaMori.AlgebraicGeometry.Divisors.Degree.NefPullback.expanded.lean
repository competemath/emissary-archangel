import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackDegreeOnCurve


-- @@ L5-8 verbatim
/-! # Pullback of nef line bundles

The pullback of a nef line bundle along a proper `k`-morphism of smooth projective varieties is nef.
-/


-- @@ L10-10 verbatim
set_option autoImplicit false

-- @@ L11-11 verbatim
set_option maxHeartbeats 400000


-- @@ L13-13 verbatim
universe u v w u' v'


-- @@ L15-15 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L16-16 verbatim
open scoped AlgebraicGeometry


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-32 expanded
/-- The pullback of a nef line bundle along a proper `k`-morphism is nef. -/
theorem IsNef.pullback {k : Type u} [Field k] [IsAlgClosed k] {S X : SmoothProjectiveVariety k}
    (Φ : S.toScheme ⟶ X.toScheme) [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper Φ] {L : LineBundle X.toVariety} (hL : IsNef L) :
    IsNef (LineBundle.pullback Φ L) := by
  intro Γ
  obtain ⟨hconst, hnonconst⟩ := degree_pullback_restrict Φ L Γ
  by_cases hΓ : IsConstantMorphism (Γ.ι ≫ Φ)
  · rw [hconst hΓ]
  · obtain ⟨R, g, _, _, hEq⟩ := hnonconst hΓ
    have hR : 0 ≤ intersectionNumber _ L R.fundamentalClass := hL R
    rw [hEq]
    exact mul_nonneg (Int.natCast_nonneg _) hR


-- @@ L34-34 verbatim
end
