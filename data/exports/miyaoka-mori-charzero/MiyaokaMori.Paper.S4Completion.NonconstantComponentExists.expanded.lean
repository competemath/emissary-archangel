import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DivisorCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.Paper.S2WeightedJets.Cone.AmpleOXOne
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.DegreeZeroIffConstant
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefLineBundle


-- @@ L19-24 verbatim
/-! # Existence of a nonconstant fibre component

In the identity `∑ᵢ mᵢ (A_S · Γᵢ) = d_F > 0` every summand is nonnegative (`A_S` is nef), so some
component `Γᵢ` has positive `A_S`-degree; equivalently `Φ|_{Γᵢ}` is nonconstant
(Lemma 5.1 of the paper, §5).
-/


-- @@ L26-26 verbatim
set_option autoImplicit false

-- @@ L27-27 verbatim
set_option maxHeartbeats 400000


-- @@ L29-29 verbatim
universe u v w u' v'


-- @@ L31-31 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L32-32 verbatim
open scoped AlgebraicGeometry


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-38 verbatim
private theorem exists_pos_of_sum_pos {ι : Type*} {s : Finset ι} {f : ι → ℤ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : 0 < ∑ i ∈ s, f i) : ∃ i ∈ s, 0 < f i := by
  exact (Finset.sum_pos_iff_of_nonneg hf).mp h


-- @@ L40-72 expanded
/--
If the nonnegative terms `mᵢ (A_S · Γᵢ)` sum to a positive number, some `Γᵢ` has positive `A_S`-degree,
i.e. `Φ` is nonconstant on `Γᵢ`. -/
theorem exists_nonconstant_component {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] {ι : Type} [Fintype ι] {m : ι → ℕ}
    {Γ : ι → IntegralCurve k S.toScheme} (hm : ∀ i, 0 < m i)
    (hnef : IsNef (LineBundle.pullback Φ (X.OX 1))) {dF : ℤ} (hdF : 0 < dF)
    (hsum :
      ∑ i,
          (m i : ℤ) *
            (intersectionNumber _ (LineBundle.pullback Φ (X.OX 1)) (Γ i).fundamentalClass) =
        dF) :
    ∃ i,
      0 < intersectionNumber _ (LineBundle.pullback Φ (X.OX 1)) (Γ i).fundamentalClass ∧
        ¬IsConstantMorphism ((Γ i).ι ≫ Φ) :=
  by
  let A : LineBundle S.toVariety := LineBundle.pullback Φ (X.OX 1)
  have hterm_nonneg : ∀ i, 0 ≤ (m i : ℤ) * (intersectionNumber _ A (Γ i).fundamentalClass) :=
    by
    intro i
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le (m i))) (hnef (Γ i))
  have hsum_pos : 0 < ∑ i, (m i : ℤ) * (intersectionNumber _ A (Γ i).fundamentalClass) :=
    by
    rw [hsum]
    exact hdF
  obtain ⟨i, hi, hprod⟩ :=
    exists_pos_of_sum_pos (s := (Finset.univ : Finset ι)) (f := fun i =>
      (m i : ℤ) * (intersectionNumber _ A (Γ i).fundamentalClass))
      (by intro j hj; simpa using hterm_nonneg j) (by simpa using hsum_pos)
  have hmi : 0 < (m i : ℤ) := by exact_mod_cast hm i
  have hdeg : 0 < intersectionNumber _ A (Γ i).fundamentalClass := by nlinarith
  have hL : AlgebraicGeometry.IsAmple (X.OX 1).toModules := ample_OX_one X
  letI : AlgebraicGeometry.IsProper Φ := isProper_of_projective Φ
  have hnotconst : ¬IsConstantMorphism ((Γ i).ι ≫ Φ) :=
    by
    intro hconst
    have hz : intersectionNumber _ A (Γ i).fundamentalClass = 0 :=
      by
      have hiff := degree_eq_zero_iff_constant Φ hL (Γ i)
      apply hiff.mpr hconst
    linarith
  exact ⟨i, by simpa [A] using hdeg, hnotconst⟩


-- @@ L74-74 verbatim
end
