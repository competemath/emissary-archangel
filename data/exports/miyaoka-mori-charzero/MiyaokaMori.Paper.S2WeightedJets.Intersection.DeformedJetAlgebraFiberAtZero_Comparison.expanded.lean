import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_Generators
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_WeightedSymLift


-- @@ L5-19 verbatim
/-! # The comparison morphism `weightedSymAlgebra V ⟶ s₀^*R`

Write `T := S.reesDeformation.restrictToLambda 0 = s₀^*R` for the fibre at `λ = 0` of the Rees deformation of a graded
quasi-coherent algebra `S`, `L_m := coker (S.irrelevantPow 2 m).2 = S_m/I^{(2)}_m` for its linear pieces and
`γ_q := reesDeformation.linearPieceToFiber S q : L_{q+1} ⟶ T_{q+1}` for the generator maps
(`DeformedJetAlgebraFiberAtZero_Generators`). Given identifications `e q : V_q^∨ ≅ L_{q+1}`, the universal property of
the weighted symmetric algebra (`weightedSymAlgebra.liftHom`, `DeformedJetAlgebraFiberAtZero_WeightedSymLift`) produces the
**comparison morphism**
`comparisonHom S V e : weightedSymAlgebra V ⟶ T` with `genIncl V q ≫ Φ_{q+1} = (e q).hom ≫ γ_q`
(`genIncl_comp_comparisonHom`). That `Φ` is an isomorphism when `S` is locally weighted-polynomial with the jet weights is
proved in `DeformedJetAlgebraFiberAtZero_ComparisonIso` from the fibre chart of `DeformedJetAlgebraFiberAtZero_FiberChart`;
`reesDeformation_restrictToLambda_zero_iso_weightedSym` (`DeformedJetAlgebraFiberAtZero`) is assembled from it.

Source: Lemma 2.3 of the paper ("removing the nonlinear terms"); Stacks 052P.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false

-- @@ L22-22 verbatim
set_option maxHeartbeats 400000


-- @@ L24-24 verbatim
universe u


-- @@ L26-26 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L27-27 verbatim
open scoped AlgebraicGeometry


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation


-- @@ L33-33 verbatim
variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

-- @@ L34-34 verbatim
variable {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]


-- @@ L36-38 verbatim
variable {r : ℕ} (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]
  (e : ∀ q : Fin r, AlgebraicGeometry.Scheme.Modules.dual (V q) ≅
    CategoryTheory.Limits.cokernel (S.irrelevantPow 2 (q.1 + 1)).2)


-- @@ L40-43 verbatim
/-- The generator map `V_q^∨ ≅ L_{q+1} ⟶ T_{q+1}` of the comparison morphism: `(e q).hom ≫ linearPieceToFiber S q`. -/
def comparisonGen (q : Fin r) :
    AlgebraicGeometry.Scheme.Modules.dual (V q) ⟶ (S.reesDeformation.restrictToLambda (0 : k)).part (q.1 + 1) :=
  (e q).hom ≫ linearPieceToFiber S (k := k) q


-- @@ L45-47 verbatim
instance comparisonGen_mono (q : Fin r) : Mono (comparisonGen S (k := k) V e q) := by
  unfold comparisonGen
  infer_instance


-- @@ L49-53 verbatim
/-- **The comparison morphism** `Φ : weightedSymAlgebra V ⟶ s₀^*R`, induced by the generator maps `comparisonGen`
through the universal property of the weighted symmetric algebra (`weightedSymAlgebra.liftHom`). -/
def comparisonHom : AlgebraicGeometry.Scheme.weightedSymAlgebra V ⟶ S.reesDeformation.restrictToLambda (0 : k) :=
  AlgebraicGeometry.Scheme.weightedSymAlgebra.liftHom (S.reesDeformation.restrictToLambda (0 : k)) V
    (comparisonGen S (k := k) V e)


-- @@ L55-59 verbatim
/-- `Φ` sends the generator `genIncl V q : V_q^∨ ⟶ (weightedSymAlgebra V)_{q+1}` to `(e q).hom ≫ γ_q`. -/
theorem genIncl_comp_comparisonHom (q : Fin r) :
    AlgebraicGeometry.Scheme.weightedSymAlgebra.genIncl V q ≫ (comparisonHom S (k := k) V e).app (q.1 + 1) =
      comparisonGen S (k := k) V e q :=
  AlgebraicGeometry.Scheme.weightedSymAlgebra.genIncl_comp_liftHom _ V _ q


-- @@ L61-65 verbatim
/-- `genIncl_comp_comparisonHom` on sections. -/
theorem comparisonHom_app_app_genIncl_app (q : Fin r) (U : X.Opens) (v : Γ(AlgebraicGeometry.Scheme.Modules.dual (V q), U)) :
    ((comparisonHom S (k := k) V e).app (q.1 + 1)).app U ((AlgebraicGeometry.Scheme.weightedSymAlgebra.genIncl V q).app U v) =
      (linearPieceToFiber S (k := k) q).app U ((e q).hom.app U v) :=
  congrArg (fun φ => φ.app U v) (genIncl_comp_comparisonHom S (k := k) V e q)


-- @@ L67-67 verbatim
end AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation


-- @@ L69-69 verbatim
end
