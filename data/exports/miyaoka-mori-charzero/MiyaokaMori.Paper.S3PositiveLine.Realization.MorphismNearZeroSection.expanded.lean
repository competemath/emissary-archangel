import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroData
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroProjectivization
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroJetCompatibility


-- @@ L5-10 verbatim
/-! # The morphism near the zero section

The tuple `(ρ^*f_0,…,ρ^*f_N)` on the zero section is nowhere zero, so the projectivization of the polynomial tuple
`P` defines a morphism `Φ₀` to `X` on a Zariski open neighbourhood `U` of the zero section; on the zero section it
equals `f∘ρ`, and on the jet neighbourhood it equals the projection of `ȷ` to `X` (proof of Theorem 4.2 of the paper).
-/


-- @@ L12-12 verbatim
set_option autoImplicit false

-- @@ L13-13 verbatim
set_option maxHeartbeats 400000


-- @@ L15-15 verbatim
universe u v w u' v'


-- @@ L17-17 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L18-18 verbatim
open scoped AlgebraicGeometry


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-49 verbatim
theorem morphism_near_zero_section {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (jet : BasedJet f ρ L κ)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ
        = restrictToThickening L (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ (P ℓ))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ)
      = sectionPullbackAlong ρ.hom
              ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
                (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom (D.coord ℓ)))
    (hvanish : ∀ j, evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P = 0) :
    ∃ (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
      (Φ₀ : U.toScheme ⟶ X.toScheme),
      IsTupleProjectivization
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules) P U Φ₀ ∧
      RealizesJet jet U Φ₀ := by
  obtain ⟨U, Φ₀, hPhi, hU0⟩ :=
    morphism_near_zero_projectivization_core jet P hjet hzero hvanish
  have hRealizes :=
    morphism_near_zero_jet_compatibility_core jet P hjet hzero hvanish U Φ₀ hPhi hU0
  exact ⟨U, Φ₀, hPhi, hRealizes⟩


-- @@ L51-51 verbatim
end
