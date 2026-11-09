import ModularCurves.EllipticCurve.PoleFiltration


-- @@ L3-9 verbatim
/-!
# Evaluation on the affine Weierstrass model

A pair satisfying the mapped affine Weierstrass equation defines a ring
homomorphism from the affine coordinate ring.  The formulas below record its
values on the base ring and the two standard coordinates.
-/


-- @@ L11-11 verbatim
universe u


-- @@ L13-13 verbatim
namespace ModularCurves


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
variable {R A : Type u} [CommRing R] [CommRing A]


-- @@ L19-28 verbatim
/-- Evaluation of the affine Weierstrass coordinate ring at a pair satisfying
the mapped affine equation. -/
noncomputable def affineModelEval
    (W : WeierstrassCurve R) (f : R →+* A) (x y : A)
    (hxy : (W.map f).toAffine.Equation x y) :
    W.toAffine.CoordinateRing →+* A :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom f x) y (by
    rw [Polynomial.eval₂_eval₂RingHom_apply,
      ← W.toAffine.map_polynomial f]
    exact hxy)


-- @@ L30-39 verbatim
@[simp]
lemma affineModelEval_coordX
    (W : WeierstrassCurve R) (f : R →+* A) (x y : A)
    (hxy : (W.map f).toAffine.Equation x y) :
    affineModelEval W f x y hxy (coordX W) = x := by
  rw [show coordX W =
    AdjoinRoot.of W.toAffine.polynomial Polynomial.X from rfl]
  unfold affineModelEval
  rw [AdjoinRoot.lift_of]
  exact Polynomial.eval₂_X _ _


-- @@ L41-49 verbatim
@[simp]
lemma affineModelEval_coordY
    (W : WeierstrassCurve R) (f : R →+* A) (x y : A)
    (hxy : (W.map f).toAffine.Equation x y) :
    affineModelEval W f x y hxy (coordY W) = y := by
  rw [show coordY W =
    AdjoinRoot.root W.toAffine.polynomial from rfl]
  unfold affineModelEval
  rw [AdjoinRoot.lift_root]


-- @@ L51-62 verbatim
lemma affineModelEval_comp_algebraMap
    (W : WeierstrassCurve R) (f : R →+* A) (x y : A)
    (hxy : (W.map f).toAffine.Equation x y) :
    (affineModelEval W f x y hxy).comp
      (algebraMap R W.toAffine.CoordinateRing) = f := by
  ext r
  rw [RingHom.comp_apply]
  change affineModelEval W f x y hxy
    (AdjoinRoot.of W.toAffine.polynomial (Polynomial.C r)) = f r
  unfold affineModelEval
  rw [AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C]


-- @@ L64-71 verbatim
/-- Mapping a solution of an affine Weierstrass equation and composing the
coefficient homomorphisms gives a solution of the composite base change. -/
lemma affineEquation_map_comp
    {B : Type u} [CommRing B]
    (W : WeierstrassCurve R) (f : R →+* A) (g : A →+* B)
    (x y : A) (hxy : (W.map f).toAffine.Equation x y) :
    (W.map (g.comp f)).toAffine.Equation (g x) (g y) := by
  simpa only [WeierstrassCurve.map_map] using hxy.map g


-- @@ L73-101 verbatim
/-- Affine-model evaluation is natural under postcomposition of the target
ring homomorphism. -/
lemma affineModelEval_comp
    {B : Type u} [CommRing B]
    (W : WeierstrassCurve R) (f : R →+* A) (g : A →+* B)
    (x y : A) (hxy : (W.map f).toAffine.Equation x y) :
    g.comp (affineModelEval W f x y hxy) =
      affineModelEval W (g.comp f) (g x) (g y)
        (affineEquation_map_comp W f g x y hxy) := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply]
      change g (((affineModelEval W f x y hxy).comp
        (algebraMap R W.toAffine.CoordinateRing)) r) =
          ((affineModelEval W (g.comp f) (g x) (g y)
            (affineEquation_map_comp W f g x y hxy)).comp
            (algebraMap R W.toAffine.CoordinateRing)) r
      rw [affineModelEval_comp_algebraMap,
        affineModelEval_comp_algebraMap]
      rfl
    · simp only [RingHom.comp_apply]
      change g (affineModelEval W f x y hxy (coordX W)) =
        affineModelEval W (g.comp f) (g x) (g y) _ (coordX W)
      rw [affineModelEval_coordX, affineModelEval_coordX]
  · simp only [RingHom.comp_apply]
    change g (affineModelEval W f x y hxy (coordY W)) =
      affineModelEval W (g.comp f) (g x) (g y) _ (coordY W)
    rw [affineModelEval_coordY, affineModelEval_coordY]


-- @@ L103-115 verbatim
/-- Bijective postcomposition preserves bijectivity of affine-model
evaluation. -/
lemma affineModelEval_map_bijective
    {B : Type u} [CommRing B]
    (W : WeierstrassCurve R) (f : R →+* A) (g : A →+* B)
    (x y : A) (hxy : (W.map f).toAffine.Equation x y)
    (hg : Function.Bijective g)
    (heval : Function.Bijective (affineModelEval W f x y hxy)) :
    Function.Bijective
      (affineModelEval W (g.comp f) (g x) (g y)
        (affineEquation_map_comp W f g x y hxy)) := by
  rw [← affineModelEval_comp W f g x y hxy]
  exact hg.comp heval


-- @@ L117-117 verbatim
end


-- @@ L119-119 verbatim
end ModularCurves
