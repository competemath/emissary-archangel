import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistPiApp


-- @@ L3-23 verbatim
/-! # The chart comparison map of the twisting sheaf is an isomorphism

Statement (Stacks 01LI / 01NR): the chart comparison map `twistChartHom m U : ι_U^* O(m) ⟶ O_U(m)`
(`RelativeProjTwistLimit`; the adjoint transpose of the limit projection `twistπ m U`) is an
isomorphism, for every chart `U : X.AffineZariskiSite`; `twistChartIso` is the resulting isomorphism.

Proof:
1. `twistChartHom m U = (pullback ι_U).map (twistπ m U) ≫ counit` (`Adjunction.homEquiv_counit`).
2. The counit of `pullback ι_U ⊣ pushforward ι_U` is an isomorphism because `pushforward ι_U` is fully faithful for
   the open immersion `ι_U` (Mathlib instances `Scheme.Modules.instFullPushforward…` and
   `Adjunction.counit_isIso_of_R_fully_faithful`).
3. `(pullback ι_U).map (twistπ m U)` is an isomorphism iff `(restrictFunctor ι_U).map (twistπ m U)` is
   (`NatIso.isIso_map_iff` along `restrictFunctorIsoPullback`), and the latter is
   `isIso_restrictFunctor_map_twistπ` (the actual content of Stacks 01LI).

Compile note: a version going through `restrictAdjunction` with `change`/`rfl` steps made the kernel spend 23–27 s
per declaration unfolding the adjunction data (`Adjunction.homEquiv`, `leftAdjointUniq`) down to sections. Only
`rw` with fully instantiated equations is used now; `Proj.twist` is kept irreducible as a guard.

Source: Stacks 01LI, 01NR; Lemma 2.2 of the paper.
-/


-- @@ L25-25 verbatim
set_option autoImplicit false


-- @@ L27-27 verbatim
universe u


-- @@ L29-29 verbatim
open CategoryTheory CategoryTheory.Limits Opposite

-- @@ L30-30 verbatim
open scoped AlgebraicGeometry


-- @@ L32-34 verbatim
noncomputable section

-- Guard (as in `RelativeProjTwistLimit`): `O_U(m)` is treated as an opaque module sheaf here.

-- @@ L35-35 verbatim
attribute [local irreducible] AlgebraicGeometry.Proj.twist


-- @@ L37-37 verbatim
namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra


-- @@ L39-39 verbatim
variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)


-- @@ L41-46 verbatim
/-- The pullback of the limit projection to the chart is an isomorphism (transport of
`isIso_restrictFunctor_map_twistπ` along `restrictFunctorIsoPullback`). -/
theorem isIso_pullback_map_twistπ (m : ℤ) (U : X.AffineZariskiSite) :
    IsIso ((Scheme.Modules.pullback (S.projChart U)).map (S.twistπ m U)) :=
  (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (S.projChart U)) (S.twistπ m U)).mp
    (S.isIso_restrictFunctor_map_twistπ m U)


-- @@ L48-54 verbatim
/-- `twistChartHom` is `(pullback ι_U).map (twistπ m U)` followed by the counit. -/
theorem twistChartHom_eq_comp (m : ℤ) (U : X.AffineZariskiSite) :
    S.twistChartHom m U =
      (Scheme.Modules.pullback (S.projChart U)).map (S.twistπ m U) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (S.projChart U)).counit.app
          (Proj.twist (S.grading U) m) := by
  rw [twistChartHom, Adjunction.homEquiv_counit]


-- @@ L56-60 verbatim
/-- **Stacks 01LI / 01NR**: the chart comparison `ι_U^* O(m) ⟶ O_U(m)` is an isomorphism. -/
theorem isIso_twistChartHom (m : ℤ) (U : X.AffineZariskiSite) : IsIso (S.twistChartHom m U) := by
  rw [twistChartHom_eq_comp]
  have := S.isIso_pullback_map_twistπ m U
  infer_instance


-- @@ L62-66 verbatim
/-- `ι_U^* O(m) ≅ O_U(m)` (Stacks 01NR). The data is `twistChartHom`; only `IsIso` is a proof obligation. -/
def twistChartIso (m : ℤ) (U : X.AffineZariskiSite) :
    (Scheme.Modules.pullback (S.projChart U)).obj (S.twist m) ≅ Proj.twist (S.grading U) m :=
  haveI := S.isIso_twistChartHom m U
  asIso (S.twistChartHom m U)


-- @@ L68-68 verbatim
end AlgebraicGeometry.Scheme.GradedAffineAlgebra


-- @@ L70-70 verbatim
end
