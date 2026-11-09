import ModularCurves.EllipticCurve.AffineModelCoordinates
import ModularCurves.EllipticCurve.WeierstrassModelCoordinateTransition


-- @@ L4-10 verbatim
/-!
# The affine evaluation map on the projective `Z`-chart

The chart homomorphism attached to a projective triple `[x,y,1]` is the
affine Weierstrass evaluation map after identifying the `Z`-chart ring with
the affine coordinate ring.
-/


-- @@ L12-12 verbatim
open AlgebraicGeometry CategoryTheory TopologicalSpace

-- @@ L13-13 verbatim
open WeierstrassCurve.Projective


-- @@ L15-15 verbatim
universe u


-- @@ L17-17 verbatim
namespace ModularCurves


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]


-- @@ L23-66 verbatim
/-- Transporting the chart homomorphism of `[x,y,1]` through the standard
`Z`-chart equivalence gives affine evaluation at `(x,y)`. -/
lemma chartAwayHomOfTriple_z_comp_chartZRingEquiv_symm
    (W : WeierstrassCurve R) (x y : S)
    (hxy : (W.map (algebraMap R S)).toAffine.Equation x y) :
    let P : Fin 3 → S := ![x, y, 1]
    let hP : (W.map (algebraMap R S)).toProjective.Equation P := by
      rw [WeierstrassCurve.Projective.equation_some]
      exact hxy
    ((chartAwayHomOfTriple W 2 P 1 (by simp [P]) hP).toRingHom.comp
      (chartZRingEquiv W).symm.toRingHom) =
        affineModelEval W (algebraMap R S) x y hxy := by
  dsimp only
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply]
      change chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _
          ((chartZRingEquiv W).symm
            (algebraMap R W.toAffine.CoordinateRing a)) = _
      rw [← chartZRingEquiv_fromZero W a, RingEquiv.symm_apply_apply]
      change chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _
          (algebraMap R (chartAway W 2) a) = _
      rw [(chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _).commutes]
      exact (RingHom.congr_fun (affineModelEval_comp_algebraMap W
        (algebraMap R S) x y hxy) a).symm
    · simp only [RingHom.comp_apply]
      change chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _
          ((chartZRingEquiv W).symm (coordX W)) =
        affineModelEval W (algebraMap R S) x y hxy (coordX W)
      rw [affineModelEval_coordX]
      rw [← chartZRingEquiv_x W, RingEquiv.symm_apply_apply]
      rw [chartAwayHomOfTriple_isLocalizationElem
        (hkl := by decide)]
      simp
  · simp only [RingHom.comp_apply]
    change chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _
        ((chartZRingEquiv W).symm (coordY W)) =
      affineModelEval W (algebraMap R S) x y hxy (coordY W)
    rw [affineModelEval_coordY]
    rw [← chartZRingEquiv_y W, RingEquiv.symm_apply_apply]
    rw [chartAwayHomOfTriple_isLocalizationElem
      (hkl := by decide)]
    simp


-- @@ L68-98 verbatim
/-- If affine evaluation at `(x,y)` is bijective, then so is the corresponding
projective `Z`-chart homomorphism. -/
lemma chartAwayHomOfTriple_z_bijective
    (W : WeierstrassCurve R) (x y : S)
    (hxy : (W.map (algebraMap R S)).toAffine.Equation x y)
    (hbij : Function.Bijective
      (affineModelEval W (algebraMap R S) x y hxy)) :
    let P : Fin 3 → S := ![x, y, 1]
    let hP : (W.map (algebraMap R S)).toProjective.Equation P := by
      rw [WeierstrassCurve.Projective.equation_some]
      exact hxy
    Function.Bijective
      (chartAwayHomOfTriple W 2 P 1 (by simp [P]) hP).toRingHom := by
  dsimp only
  have heval :
      ((chartAwayHomOfTriple W 2 ![x, y, 1] 1 (by simp) (by
          rw [WeierstrassCurve.Projective.equation_some]
          exact hxy)).toRingHom.comp
        (chartZRingEquiv W).symm.toRingHom) =
          affineModelEval W (algebraMap R S) x y hxy := by
    simpa only using
      chartAwayHomOfTriple_z_comp_chartZRingEquiv_symm W x y hxy
  have hcomp : Function.Bijective
      ((chartAwayHomOfTriple W 2 ![x, y, 1] 1 (by simp) (by
          rw [WeierstrassCurve.Projective.equation_some]
          exact hxy)).toRingHom.comp
        (chartZRingEquiv W).symm.toRingHom) := by
    rw [heval]
    exact hbij
  exact (Function.Bijective.of_comp_iff _
    (chartZRingEquiv W).symm.bijective).mp hcomp


-- @@ L100-100 verbatim
section ExplicitBaseMap


-- @@ L102-102 verbatim
variable {R S : Type u} [CommRing R] [CommRing S]


-- @@ L104-124 verbatim
/-- The chart-bijectivity result with an explicit coefficient homomorphism,
using the algebra structure induced by that homomorphism. -/
lemma chartAwayHomOfTriple_z_bijective_of_ringHom
    (W : WeierstrassCurve R) (f : R →+* S) (x y : S)
    (hxy : (W.map f).toAffine.Equation x y)
    (hbij : Function.Bijective (affineModelEval W f x y hxy)) :
    letI : Algebra R S := f.toAlgebra
    let hxy' : (W.map (algebraMap R S)).toAffine.Equation x y := by
      rw [RingHom.algebraMap_toAlgebra]
      exact hxy
    let P : Fin 3 → S := ![x, y, 1]
    let hP : (W.map (algebraMap R S)).toProjective.Equation P := by
      rw [WeierstrassCurve.Projective.equation_some]
      exact hxy'
    Function.Bijective
      (chartAwayHomOfTriple W 2 P 1 (by simp [P]) hP).toRingHom := by
  letI : Algebra R S := f.toAlgebra
  dsimp only
  apply chartAwayHomOfTriple_z_bijective W x y
    (by simpa only [RingHom.algebraMap_toAlgebra] using hxy)
  simpa only [RingHom.algebraMap_toAlgebra] using hbij


-- @@ L126-126 verbatim
end ExplicitBaseMap


-- @@ L128-128 verbatim
end


-- @@ L130-130 verbatim
end ModularCurves
