import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage


-- @@ L5-5 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

-- @@ L6-6 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization

-- @@ L7-7 verbatim
open scoped TensorProduct


-- @@ L9-9 verbatim
universe u


-- @@ L11-11 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L12-12 verbatim
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra


-- @@ L14-14 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L16-19 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

-- @@ L20-38 expanded
theorem WeierstrassProjModel.relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage [IsDomain R]
    [IsNoetherianRing R] [W.IsElliptic]
    (u₃ :
      ∀ (i j : Fin 3),
        Fin 3 →
          (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X i : MvPolynomial (Fin 3) R))) ⊗[R]
            (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X j : MvPolynomial (Fin 3) R))))
    (toE₃ :
      ∀ (i j k : Fin 3),
        Spec (CommRingCat.of (Localization.Away (u₃ i j k))) ⟶ projModelCR W.toProjective)
    (hcov₉ :
      ∀ i j,
        Ideal.span (Set.range (kw_lrSixU W i j) ∪ Set.range (u₃ i j)) =
          (⊤ :
            Ideal
              ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X j : MvPolynomial (Fin 3) R))))))
    (hcompat₃ :
      ∀ (i j k : Fin 3) (l : Fin 3 ⊕ Fin 3),
        pullback.fst
              (Spec.map
                (CommRingCat.ofHom
                  (algebraMap
                    ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                          (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                          (X j : MvPolynomial (Fin 3) R))))
                    (Localization.Away (u₃ i j k)))))
              (kw_lrSixU_locMap W i j l) ≫
            toE₃ i j k =
          pullback.snd
              (Spec.map
                (CommRingCat.ofHom
                  (algebraMap
                    ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                          (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                          (X j : MvPolynomial (Fin 3) R))))
                    (Localization.Away (u₃ i j k)))))
              (kw_lrSixU_locMap W i j l) ≫
            kw_lrSixU_toE W i j l) :
    Nonempty (WeierstrassProjModel.RelativeGroupLaw R (projModelStrCR W.toProjective)) := by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_relativeGroupLaw_nonempty_of_thirdLaw_nineCoverage.solution

