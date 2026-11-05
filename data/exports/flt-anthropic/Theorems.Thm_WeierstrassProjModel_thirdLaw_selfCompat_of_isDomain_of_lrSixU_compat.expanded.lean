import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat


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

-- @@ L20-49 expanded
theorem WeierstrassProjModel.thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat (i j : Fin 3)
    [IsDomain
        ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (X i : MvPolynomial (Fin 3) R))) ⊗[R]
          (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (X j : MvPolynomial (Fin 3) R))))]
    (hne : ∃ l, kw_lrSixU W i j l ≠ 0)
    (u₃ :
      Fin 3 →
        (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (X i : MvPolynomial (Fin 3) R))) ⊗[R]
          (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (X j : MvPolynomial (Fin 3) R))))
    (toE₃ :
      ∀ k : Fin 3, Spec (CommRingCat.of (Localization.Away (u₃ k))) ⟶ projModelCR W.toProjective)
    (hcompat₃ :
      ∀ (k : Fin 3) (l : Fin 3 ⊕ Fin 3),
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
                    (Localization.Away (u₃ k)))))
              (kw_lrSixU_locMap W i j l) ≫
            toE₃ k =
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
                    (Localization.Away (u₃ k)))))
              (kw_lrSixU_locMap W i j l) ≫
            kw_lrSixU_toE W i j l)
    (k k' : Fin 3) :
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
                (Localization.Away (u₃ k)))))
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap
                ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                    (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                      (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                  (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                    (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                      (X j : MvPolynomial (Fin 3) R))))
                (Localization.Away (u₃ k'))))) ≫
        toE₃ k =
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
                (Localization.Away (u₃ k)))))
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap
                ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                    (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                      (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                  (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                    (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                      (X j : MvPolynomial (Fin 3) R))))
                (Localization.Away (u₃ k'))))) ≫
        toE₃ k' :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat.solution

