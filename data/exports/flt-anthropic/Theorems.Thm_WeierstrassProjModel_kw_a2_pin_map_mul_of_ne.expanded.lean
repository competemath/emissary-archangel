import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_a2_pin_map_mul_of_ne


-- @@ L7-7 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

-- @@ L8-8 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization

-- @@ L9-9 verbatim
open scoped TensorProduct


-- @@ L11-11 verbatim
universe u


-- @@ L13-13 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L14-14 verbatim
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra


-- @@ L16-16 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

-- @@ L17-17 verbatim
variable (F : Type u) [Field F] [Algebra R F]


-- @@ L19-22 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

-- @@ L23-47 expanded
theorem WeierstrassProjModel.kw_a2_pin_map_mul_of_ne (hΔ : algebraMap R F W.Δ ≠ 0)
    (m :
      pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ⟶
        projModelCR W.toProjective)
    (hmpin :
      ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
        kw_lrSixU_locMap W i j l ≫
            (kwProjPullbackChartIsoCR R W.toProjective i j).inv ≫
              (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j) ≫ m =
          kw_lrSixU_toE W i j l)
    (i j : Fin 3)
    (ψᵢ :
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (X i : MvPolynomial (Fin 3) R))) →ₐ[R]
        F)
    (ψⱼ :
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (X j : MvPolynomial (Fin 3) R))) →ₐ[R]
        F)
    (k : Fin 3)
    (ψₖ :
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (X k : MvPolynomial (Fin 3) R))) →ₐ[R]
        F)
    (x y : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective))
    (hfacx :
      x.1 =
        Spec.map (CommRingCat.ofHom ψᵢ.toRingHom) ≫
          (projModelAffineOpenCoverCR R W.toProjective).openCover.f i)
    (hfacy :
      y.1 =
        Spec.map (CommRingCat.ofHom ψⱼ.toRingHom) ≫
          (projModelAffineOpenCoverCR R W.toProjective).openCover.f j)
    (hfacsum :
      pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m =
        Spec.map (CommRingCat.ofHom ψₖ.toRingHom) ≫
          (projModelAffineOpenCoverCR R W.toProjective).openCover.f k)
    (hne :
      (⟦kw_lrApt_chartEval W F i ψᵢ⟧ : WeierstrassCurve.Projective.PointClass F) ≠
        ⟦kw_lrApt_chartEval W F j ψⱼ⟧) :
    (⟦kw_lrApt_chartEval W F k ψₖ⟧ : WeierstrassCurve.Projective.PointClass F) =
      (kw_lrApt_WF W F).addMap ⟦kw_lrApt_chartEval W F i ψᵢ⟧ ⟦kw_lrApt_chartEval W F j ψⱼ⟧ :=
  by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_a2_pin_map_mul_of_ne.solution

