import OAI.AlgebraicGeometry.StableCoordinate.Definitions
import OAI.AlgebraicGeometry.StableCoordinate.AffineGeometry
import Mathlib.Algebra.MvPolynomial.Division


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# Schemes of the complex hypersurface fibers

An algebraic isomorphism of fiber coordinate rings induces an isomorphism of
affine schemes over `Spec ℂ`. Nonrectifiability excludes every ambient scheme
automorphism over the complex base, for each complex parameter.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
namespace StableCoordinate

-- @@ L18-18 verbatim
namespace GeometricInterpretation


-- @@ L20-20 verbatim
open CategoryTheory AlgebraicGeometry MvPolynomial

-- @@ L21-21 verbatim
open scoped AlgebraicGeometry


-- @@ L23-24 verbatim
/-- The complex affine four-space in its standard spectrum presentation. -/
abbrev Ambient := Spec (CommRingCat.of (R 4))


-- @@ L26-27 verbatim
/-- The fiber as a scheme, with its full coordinate-ring structure. -/
abbrev Fiber (t : ℂ) := Spec (CommRingCat.of (FiberRing t))


-- @@ L29-31 verbatim
/-- The actual closed immersion defined by `f - t`. -/
def fiberEmbedding (t : ℂ) : Fiber t ⟶ Ambient :=
  AffineGeometry.quotientEmbedding (fiberIdeal t)


-- @@ L33-35 verbatim
instance fiberEmbedding_isClosedImmersion (t : ℂ) :
    IsClosedImmersion (fiberEmbedding t) :=
  AffineGeometry.quotientEmbedding_isClosedImmersion (fiberIdeal t)


-- @@ L37-40 verbatim
/-- Standard identification of the ambient spectrum with affine four-space. -/
def ambientAffineSpaceIso :
    Ambient ≅ AffineSpace (Fin 4) (Spec (CommRingCat.of ℂ)) :=
  AffineGeometry.affineSpaceIsoOfAlgEquiv (AlgEquiv.refl : R 4 ≃ₐ[ℂ] R 4)


-- @@ L42-43 verbatim
/-- The coordinate hyperplane's defining ideal. -/
def hyperplaneIdeal : Ideal (R 4) := Ideal.span {X 0}


-- @@ L45-47 verbatim
theorem hyperplaneIdeal_isPrime : hyperplaneIdeal.IsPrime := by
  apply (Ideal.span_singleton_prime (X_ne_zero (0 : Fin 4))).mpr
  exact X_prime


-- @@ L49-55 verbatim
/-- The fiber algebra condition proves its defining ideal is prime; this is not
an additional hypothesis about the source polynomial. -/
theorem fiberIdeal_isPrime_of_affineFiber (t : ℂ) (h : IsAffineThreeSpaceFiber t) :
    (fiberIdeal t).IsPrime := by
  obtain ⟨e⟩ := h
  let : IsDomain (FiberRing t) := Function.Injective.isDomain e e.injective
  exact (Ideal.Quotient.isDomain_iff_prime (fiberIdeal t)).mp inferInstance


-- @@ L57-64 verbatim
/-- Geometric rectifiability of the embedded image by an arbitrary ambient
scheme automorphism over the complex base scheme. -/
def IsSchemeRectifiableFiber (t : ℂ) : Prop :=
  ∃ e : Ambient ≅ Ambient,
    (e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (R 4))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (R 4)))) ∧
    e.hom '' Set.range (fiberEmbedding t) =
      PrimeSpectrum.zeroLocus (hyperplaneIdeal : Set (R 4))


-- @@ L66-75 verbatim
/-- The defining-ideal orbit formulation captures exactly the geometric orbit
condition under all ambient automorphisms. Radicality follows from the specified
fiber algebra isomorphism, and is therefore not a new principal assumption. -/
theorem rectifiableFiber_iff_schemeRectifiable (t : ℂ)
    (h : IsAffineThreeSpaceFiber t) :
    IsRectifiableFiber t ↔ IsSchemeRectifiableFiber t := by
  unfold IsRectifiableFiber IsSchemeRectifiableFiber fiberEmbedding
  rw [AffineGeometry.quotientEmbedding_range]
  exact AffineGeometry.ideal_transport_iff_scheme_transport (fiberIdeal t) hyperplaneIdeal
    (fiberIdeal_isPrime_of_affineFiber t h).isRadical hyperplaneIdeal_isPrime.isRadical


-- @@ L77-84 verbatim
/-- The fiber condition produces an isomorphism with affine three-space in the
category of schemes **over** `Spec ℂ`, not only an equivalence of sets. -/
theorem affineFiber_gives_schemeIso (t : ℂ) (h : IsAffineThreeSpaceFiber t) :
    Nonempty (AffineGeometry.algebraSpec ℂ (FiberRing t) ≅
      Over.mk (AffineSpace (Fin 3) (Spec (CommRingCat.of ℂ)) ↘
        Spec (CommRingCat.of ℂ))) := by
  obtain ⟨e⟩ := h
  exact ⟨AffineGeometry.affineSpaceOverIsoOfAlgEquiv e⟩


-- @@ L86-98 verbatim
/-- The full algebraic fiber package entails the full all-fiber geometric
conclusion, including closed immersion and nonrectifiability of its image. -/
theorem fiberPackage_gives_geometric_conclusion (h : FiberPackage) :
    ∀ t : ℂ,
      Nonempty (AffineGeometry.algebraSpec ℂ (FiberRing t) ≅
        Over.mk (AffineSpace (Fin 3) (Spec (CommRingCat.of ℂ)) ↘
          Spec (CommRingCat.of ℂ))) ∧
      IsClosedImmersion (fiberEmbedding t) ∧
      ¬ IsSchemeRectifiableFiber t := by
  intro t
  obtain ⟨haff, hnonrect⟩ := h t
  refine ⟨affineFiber_gives_schemeIso t haff, inferInstance, ?_⟩
  exact fun hrect => hnonrect ((rectifiableFiber_iff_schemeRectifiable t haff).mpr hrect)


-- @@ L100-100 verbatim
end GeometricInterpretation

-- @@ L101-101 verbatim
end StableCoordinate


-- @@ L103-103 verbatim
end


-- @@ L105-105 verbatim
end OAI
