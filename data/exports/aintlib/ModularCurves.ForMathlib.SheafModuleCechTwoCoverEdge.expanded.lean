/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechTwoCoverExact
import ModularCurves.ForMathlib.TotalComplexUpNatHorizontalEdgeModule


-- @@ L9-15 verbatim
/-!
# Horizontal edge of the module-valued two-cover Cech bicomplex

The horizontal edge from the native Cech complex for the outer family is a
degree-one quasi-isomorphism when the inner family covers and its native Cech
complex on the zeroth outer Cech term is exact in degree one.
-/


-- @@ L17-17 verbatim
open CategoryTheory TopologicalSpace


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
universe u


-- @@ L23-23 verbatim
namespace TopCat.Sheaf


-- @@ L25-25 verbatim
variable {R : Type u} [CommRing R] {X : TopCat.{u}}

-- @@ L26-26 verbatim
variable (F : Sheaf (ModuleCat.{u} R) X)

-- @@ L27-27 verbatim
variable {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)


-- @@ L29-57 verbatim
/-- The horizontal edge of the module-valued two-cover Cech bicomplex is a
degree-one quasi-isomorphism under the one required native Cech exactness
condition. -/
theorem moduleCechTwoCoverHorizontalEdge_quasiIsoAt_one
    (hV : ⨆ i, V i = ⊤)
    (hrow : ((cechComplexFunctor V).obj
      (moduleCechTerm F U 0).obj).ExactAt 1) :
    QuasiIsoAt
      ((moduleCechTwoCoverBicomplex F U V).totalUpNatHorizontalEdge
        ((cechComplexFunctor U).obj F.obj)
        (moduleCechTwoCoverHorizontalAugmentation F U V)
        (moduleCechTwoCoverHorizontalAugmentation_comm F U V)
        (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V)) 1 := by
  letI : Mono (moduleCechTwoCoverHorizontalAugmentation F U V 1) :=
    moduleCechTwoCoverHorizontalAugmentation_mono F U V 1 hV
  letI : Mono (moduleCechTwoCoverHorizontalAugmentation F U V 2) :=
    moduleCechTwoCoverHorizontalAugmentation_mono F U V 2 hV
  exact
    HomologicalComplex₂.totalUpNatHorizontalEdge_quasiIsoAt_one_module
      (moduleCechTwoCoverBicomplex F U V)
      ((cechComplexFunctor U).obj F.obj)
      (moduleCechTwoCoverHorizontalAugmentation F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comm F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V)
      (moduleCechTwoCoverHorizontalAugmentedShortComplex_exact
        F U V 0 hV)
      (moduleCechTwoCoverHorizontalAugmentedShortComplex_exact
        F U V 1 hV)
      (moduleCechTwoCover_row_exactAt_one F U V 0 hrow)


-- @@ L59-103 verbatim
/-- The horizontal edge of the module-valued two-cover Cech bicomplex is a
quasi-isomorphism in every positive degree when the required native Cech rows
are exact on the two adjacent antidiagonals. -/
theorem moduleCechTwoCoverHorizontalEdge_quasiIsoAt_succ
    (hV : ⨆ i, V i = ⊤)
    (n : ℕ)
    (hrow_n : ∀ q p, q + p = n → 0 < p →
      ((cechComplexFunctor V).obj
        (moduleCechTerm F U q).obj).ExactAt p)
    (hrow_succ : ∀ q p, q + p = n + 1 → 0 < p →
      ((cechComplexFunctor V).obj
        (moduleCechTerm F U q).obj).ExactAt p) :
    QuasiIsoAt
      ((moduleCechTwoCoverBicomplex F U V).totalUpNatHorizontalEdge
        ((cechComplexFunctor U).obj F.obj)
        (moduleCechTwoCoverHorizontalAugmentation F U V)
        (moduleCechTwoCoverHorizontalAugmentation_comm F U V)
        (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V))
      (n + 1) := by
  letI : Mono
      (moduleCechTwoCoverHorizontalAugmentation F U V (n + 1)) :=
    moduleCechTwoCoverHorizontalAugmentation_mono
      F U V (n + 1) hV
  letI : Mono
      (moduleCechTwoCoverHorizontalAugmentation F U V (n + 2)) :=
    moduleCechTwoCoverHorizontalAugmentation_mono
      F U V (n + 2) hV
  apply
    HomologicalComplex₂.totalUpNatHorizontalEdge_quasiIsoAt_succ_module
      (moduleCechTwoCoverBicomplex F U V)
      ((cechComplexFunctor U).obj F.obj)
      (moduleCechTwoCoverHorizontalAugmentation F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comm F U V)
      (moduleCechTwoCoverHorizontalAugmentation_comp_d F U V)
      n
      (moduleCechTwoCoverHorizontalAugmentedShortComplex_exact
        F U V n hV)
      (moduleCechTwoCoverHorizontalAugmentedShortComplex_exact
        F U V (n + 1) hV)
  · intro q p hqp hp
    exact moduleCechTwoCover_row_exactAt F U V q p hp
      (hrow_n q p hqp hp)
  · intro q p hqp hp
    exact moduleCechTwoCover_row_exactAt F U V q p hp
      (hrow_succ q p hqp hp)


-- @@ L105-105 verbatim
end TopCat.Sheaf
