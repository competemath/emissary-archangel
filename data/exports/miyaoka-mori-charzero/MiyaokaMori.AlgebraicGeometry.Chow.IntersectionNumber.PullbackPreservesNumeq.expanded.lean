import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.CartierPullbackLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.NumericalEquivalence
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.PullbackDegreeOnCurve


-- @@ L6-9 verbatim
/-! # Pullback preserves numerical equivalence of divisors

The pullbacks along a morphism of two numerically equivalent divisors are numerically equivalent
(§4 of the paper, proof of Lemma 5.1). -/


-- @@ L11-11 verbatim
set_option autoImplicit false

-- @@ L12-12 verbatim
set_option maxHeartbeats 400000


-- @@ L14-14 verbatim
universe u v w u' v'


-- @@ L16-16 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L17-17 verbatim
open scoped AlgebraicGeometry


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-67 expanded
/-- **Pullback preserves numerical equivalence of divisors** (Stacks 0BET with
`d = 1`). For every integral curve `Γ ⊂ S`: `(π^*D)·Γ = O_S(π^*D)·Γ = (π^*O_C(D))·Γ = O_C(D)·π_*[Γ]`
(`CartierDivisor.lineBundle_inter`, `CartierDivisor.lineBundle_pullback`, projection formula
`LineBundle.inter_pullback`). If `π|_Γ` is constant, `π_*[Γ] = 0` and both sides vanish; otherwise
`π_*[Γ] = [K(Γ):K(R)]·[R]` for the image curve `R ⊂ C`, and `D ≡ E` gives `D·R = E·R`. -/
theorem pullback_numEquiv {k : Type u} [Field k] [IsAlgClosed k] {S : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme)
    [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper π]
    (hπ : Function.Surjective π.base) {D E : CartierDivisor C.toVariety}
    (h : NumEquivDivisor (X := C.toSmoothProjectiveVariety) D E) :
    NumEquivDivisor (CartierDivisor.pullback (Y := C.toVariety) π hπ D)
      (CartierDivisor.pullback (Y := C.toVariety) π hπ E) :=
  by
  intro Γ
  obtain ⟨eD⟩ := CartierDivisor.lineBundle_pullback π hπ D
  obtain ⟨eE⟩ := CartierDivisor.lineBundle_pullback π hπ E
  have hD :
    intersectionNumber _ (CartierDivisor.pullback (Y := C.toVariety) π hπ D) Γ.fundamentalClass =
      intersectionNumber _
        (LineBundle.pullback (X := S.toVariety) (Y := C.toVariety) π D.lineBundle)
        Γ.fundamentalClass :=
    by
    rw [← CartierDivisor.lineBundle_inter]
    exact LineBundle.inter_congr (X := S) eD Γ.fundamentalClass
  have hE :
    intersectionNumber _ (CartierDivisor.pullback (Y := C.toVariety) π hπ E) Γ.fundamentalClass =
      intersectionNumber _
        (LineBundle.pullback (X := S.toVariety) (Y := C.toVariety) π E.lineBundle)
        Γ.fundamentalClass :=
    by
    rw [← CartierDivisor.lineBundle_inter]
    exact LineBundle.inter_congr (X := S) eE Γ.fundamentalClass
  have hover : π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := inferInstance
  have hproper : AlgebraicGeometry.IsProper π := inferInstance
  rw [hD, hE]
  have hpD :=
    @LineBundle.inter_pullback k _ _ S C.toSmoothProjectiveVariety π hover hproper D.lineBundle
      Γ.fundamentalClass
  have hpE :=
    @LineBundle.inter_pullback k _ _ S C.toSmoothProjectiveVariety π hover hproper E.lineBundle
      Γ.fundamentalClass
  refine hpD.trans (Eq.trans ?_ hpE.symm)
  by_cases hc : IsConstantMorphism (Γ.ι ≫ π)
  · rw [@cyclePushforward_fundamentalClass_eq_zero_of_isConstant k _ S C.toSmoothProjectiveVariety π
        hproper Γ hc]
    unfold LineBundle.inter
    rw [map_zero, map_zero]
  · rw [@cyclePushforward_fundamentalClass_eq_of_not_isConstant k _ S C.toSmoothProjectiveVariety π
        hover hproper Γ hc]
    set R := @IntegralCurve.imageCurve k _ S C.toSmoothProjectiveVariety π hover hproper Γ hc with
      hRdef
    have hR :
      intersectionNumber _ D.lineBundle R.fundamentalClass =
        intersectionNumber _ E.lineBundle R.fundamentalClass :=
      (CartierDivisor.lineBundle_inter (X := C.toSmoothProjectiveVariety) D _).trans
        ((h R).trans (CartierDivisor.lineBundle_inter (X := C.toSmoothProjectiveVariety) E _).symm)
    unfold LineBundle.inter at hR ⊢
    rw [map_zsmul, map_zsmul, hR]


-- @@ L69-69 verbatim
end
