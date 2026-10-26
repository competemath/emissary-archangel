/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import RiemannRoch.Chow.NormalCone.ProjectiveCompletionDeformationInfinityComponentIntersectionNormalBundleTwistChartRecoveryIC1
import RiemannRoch.Chow.NormalCone.ProjectiveCompletionDeformationInfinityNormalBundleTwistNativeCubeIdentityC5


-- @@ L9-24 verbatim
/-!
# Restriction compatibility of the global native kernel charts (route B5)

Built from the native pullback composition law (C5/C4) and the independent global kernel's
compatible-family property:

* the ORIGINAL affine restriction mates `nativeKernelRestrictionMate` are the all-degree-one
  native pullback comparisons, so they compose along `U ≤ V ≤ W` through the actual
  `pullbackComp`/`pullbackCongr` (the mate cocycle);
* the actual global chart morphisms `nativeGlobalChartHom` are compatible with the mates
  under chart refinement (global chart cocycle), and consequently invertibility of
  `nativeGlobalChartHom` passes from a chart to every smaller affine chart.

Not proved here: invertibility of `nativeGlobalChartHom` (route B4 / overlap covering), and the
global canonical O(1), quotient and total-twist comparisons.
-/


-- @@ L26-26 verbatim
noncomputable section

-- @@ L27-27 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

-- @@ L28-28 verbatim
universe u

-- @@ L29-29 verbatim
namespace SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityComponentIntersectionNormalBundleTwistChartRecoveryB5

-- @@ L30-35 verbatim
open InfinityComponentIntersectionNormalBundleTwistDescent InfinityComponentIntersectionGlobal
  InfinityNormalConeGlobal InfinityNormalBundleTwistNativeOverlap
  InfinityNormalBundleTwistNativeComparison InfinityNormalBundleTwistLineRecovery
  InfinityNormalBundleTwistNativeRecovery InfinityNormalBundleTwistNativeIdentityC5
  InfinityComponentIntersectionNormalBundleTwistChartRecovery
  InfinityComponentIntersectionNormalBundleTwistChartRecoveryIC1


-- @@ L37-37 verbatim
section Native

-- @@ L38-45 verbatim
variable {A B C σ τ ρ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → ρ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (g : 𝒜 →+*ᵍ ℬ) (g' : ℬ →+*ᵍ 𝒞)
  (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
  (hg' : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map g')
  {ι : Type u} (f : ι → 𝒜 1)


-- @@ L47-67 verbatim
/-- The all-degree-one native pullback composition law for a third graded map equal to the
composite (the composite is only known up to a propositional equality). -/
theorem allTarget_comp_of_eq (g₃ : 𝒜 →+*ᵍ 𝒞) (e : g'.comp g = g₃)
    (hg₃ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map g₃)
    (eP : Proj.map g' hg' ≫ Proj.map g hg = Proj.map g₃ hg₃) (d : ℤ)
    (h : (Opens.grothendieckTopology (Proj 𝒜)).CoversTop
      (fun i ↦ Native.generatorOpen 𝒜 (f i)))
    (h' : (Opens.grothendieckTopology (Proj ℬ)).CoversTop
      (fun i : ℬ 1 ↦ Native.generatorOpen ℬ i)) :
    nativeAllTargetPullbackHom 𝒜 𝒞 g₃ hg₃ f d h =
      (Scheme.Modules.pullbackCongr eP.symm).hom.app (Native.degreeOneSheaf 𝒜 f d) ≫
        (Scheme.Modules.pullbackComp (Proj.map g' hg') (Proj.map g hg)).inv.app
          (Native.degreeOneSheaf 𝒜 f d) ≫
        (Scheme.Modules.pullback (Proj.map g' hg')).map
          (nativeAllTargetPullbackHom 𝒜 ℬ g hg f d h) ≫
        nativeAllTargetPullbackHom ℬ 𝒞 g' hg' (fun x : ℬ 1 ↦ x) d h' := by
  subst e
  have key := nativeAllTargetPullbackHom_comp 𝒜 ℬ 𝒞 g g' hg hg' hg₃ f d h h'
  have e2 : eP = InfinityNormalBundleTwistNativeCube.projMap_comp_eq 𝒜 ℬ 𝒞 g g' hg hg' hg₃ := rfl
  rw [e2]
  exact key

-- @@ L68-68 verbatim
end Native


-- @@ L70-70 verbatim
variable (Y : Scheme.{u}) (J : Y.IdealSheafData)

-- @@ L71-73 verbatim
noncomputable local instance b5GrCommRing (U : Y.affineOpens) :
    CommRing (AffineNormalCone.associatedGradedRing Γ(Y,U.1) (J.ideal U)) :=
  Ideal.Quotient.commRing _


-- @@ L75-81 verbatim
/-- The ORIGINAL affine restriction mate is the all-degree-one native pullback comparison. -/
theorem nativeKernelRestrictionMate_eq_allTarget {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ) :
    nativeKernelRestrictionMate Y J h d =
      nativeAllTargetPullbackHom (ReesBlowup.grGrade (J.ideal V)) (ReesBlowup.grGrade (J.ideal U))
        (nativeGradedRestriction Y J h) (nativeGradedRestriction_irrelevant Y J h)
        (fun x => x) d (affineNativeGenerator_covers Y J V) := by
  native_cache_exact (nativeKernelRestrictionMateNormalization Y J h d)


-- @@ L83-104 verbatim
/-- Genuine composition law (mate cocycle) of the ORIGINAL affine native restriction mates. -/
theorem nativeKernelRestrictionMate_comp {U V W : Y.affineOpens} (h : U ≤ V) (k : V ≤ W) (d : ℤ) :
    nativeKernelRestrictionMate Y J (h.trans k) d =
      (Scheme.Modules.pullbackCongr (nativeRestriction_scheme_comp Y J h k).symm).hom.app
          (affineNativeKernel Y J d W) ≫
        (Scheme.Modules.pullbackComp (boundaryRestriction Y J h)
          (boundaryRestriction Y J k)).inv.app (affineNativeKernel Y J d W) ≫
        (Scheme.Modules.pullback (boundaryRestriction Y J h)).map
          (nativeKernelRestrictionMate Y J k d) ≫
        nativeKernelRestrictionMate Y J h d := by
  have key := allTarget_comp_of_eq (ReesBlowup.grGrade (J.ideal W))
    (ReesBlowup.grGrade (J.ideal V)) (ReesBlowup.grGrade (J.ideal U))
    (nativeGradedRestriction Y J k) (nativeGradedRestriction Y J h)
    (nativeGradedRestriction_irrelevant Y J k) (nativeGradedRestriction_irrelevant Y J h)
    (fun x => x) (nativeGradedRestriction Y J (h.trans k)) (nativeRestriction_coeff_comp Y J h k)
    (nativeGradedRestriction_irrelevant Y J (h.trans k))
    (nativeRestriction_scheme_comp Y J h k) d (affineNativeGenerator_covers Y J W)
    (affineNativeGenerator_covers Y J V)
  rw [nativeKernelRestrictionMate_eq_allTarget Y J (h.trans k) d,
    nativeKernelRestrictionMate_eq_allTarget Y J k d,
    nativeKernelRestrictionMate_eq_allTarget Y J h d]
  exact key


-- @@ L106-110 verbatim
theorem nativeGlobalProjection_compatible' {U V W : Y.affineOpens} (hU : W ≤ U) (hV : W ≤ V) (d : ℤ) :
    nativeGlobalProjection Y J d U ≫ pushedNativeRestriction Y J hU d =
      nativeGlobalProjection Y J d V ≫ pushedNativeRestriction Y J hV d := by
  have := nativeGlobalProjection_compatible Y J d (NativeRefinement.mk U V W hU hV)
  with_reducible exact this


-- @@ L112-117 verbatim
theorem nativeGlobalProjection_restriction {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ) :
    nativeGlobalProjection Y J d V ≫ pushedNativeRestriction Y J h d =
      nativeGlobalProjection Y J d U := by
  have hc := nativeGlobalProjection_compatible' Y J h (le_refl U) d
  simp only [pushedNativeRestriction_refl, Category.comp_id] at hc
  exact hc


-- @@ L119-124 verbatim
theorem pushforwardComp_hom_eq_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    (Scheme.Modules.pushforwardComp f g).hom.app M = (Scheme.Modules.pushforwardComp f g).inv.app M := by
  apply Scheme.Modules.hom_ext
  intro T
  ext s
  rfl


-- @@ L126-128 verbatim
theorem cancel_hom_inv {C : Type*} [Category C] {K A B : C} (a : K ⟶ A) (e : A ≅ B) :
    (a ≫ e.hom) ≫ e.inv = a := by
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]


-- @@ L130-187 verbatim
theorem nativeGlobalChartHom_restriction {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ) :
    nativeGlobalChartHom Y J d U =
      (Scheme.Modules.pullbackCongr (boundaryRestriction_affineι Y J h).symm).hom.app
          (nativeGlobalKernel Y J d) ≫
        (Scheme.Modules.pullbackComp (boundaryRestriction Y J h)
          (projectiveConeAffineι Y J V)).inv.app (nativeGlobalKernel Y J d) ≫
        (Scheme.Modules.pullback (boundaryRestriction Y J h)).map (nativeGlobalChartHom Y J d V) ≫
        nativeKernelRestrictionMate Y J h d := by
  have s1 := iteratedComponentMate
    (Scheme.Modules.pullbackPushforwardAdjunction (projectiveConeAffineι Y J V))
    (Scheme.Modules.pullbackPushforwardAdjunction (boundaryRestriction Y J h))
    (nativeGlobalProjection Y J d V) (nativeKernelRestriction Y J h d)
  have s2 := compositeComponentMate (projectiveConeAffineι Y J V) (boundaryRestriction Y J h)
    (M := nativeGlobalKernel Y J d) (N := affineNativeKernel Y J d U)
    ((nativeGlobalProjection Y J d V ≫
        (Scheme.Modules.pushforward (projectiveConeAffineι Y J V)).map
          (nativeKernelRestriction Y J h d)) ≫
      (Scheme.Modules.pushforwardComp (boundaryRestriction Y J h)
        (projectiveConeAffineι Y J V)).hom.app (affineNativeKernel Y J d U))
  have s3 := equalityComponentMate (boundaryRestriction_affineι Y J h).symm
    (M := nativeGlobalKernel Y J d) (N := affineNativeKernel Y J d U)
    ((nativeGlobalProjection Y J d V ≫
        (Scheme.Modules.pushforward (projectiveConeAffineι Y J V)).map
          (nativeKernelRestriction Y J h d)) ≫
      (Scheme.Modules.pushforwardComp (boundaryRestriction Y J h)
        (projectiveConeAffineι Y J V)).hom.app (affineNativeKernel Y J d U))
  have hcan : ((nativeGlobalProjection Y J d V ≫
        (Scheme.Modules.pushforward (projectiveConeAffineι Y J V)).map
          (nativeKernelRestriction Y J h d)) ≫
      (Scheme.Modules.pushforwardComp (boundaryRestriction Y J h)
        (projectiveConeAffineι Y J V)).hom.app (affineNativeKernel Y J d U)) ≫
      (Scheme.Modules.pushforwardComp (boundaryRestriction Y J h)
        (projectiveConeAffineι Y J V)).inv.app (affineNativeKernel Y J d U) =
      nativeGlobalProjection Y J d V ≫
        (Scheme.Modules.pushforward (projectiveConeAffineι Y J V)).map
          (nativeKernelRestriction Y J h d) := by
    exact cancel_hom_inv _ ((Scheme.Modules.pushforwardComp (boundaryRestriction Y J h)
      (projectiveConeAffineι Y J V)).app (affineNativeKernel Y J d U))
  have hcc : ((nativeGlobalProjection Y J d V ≫
        (Scheme.Modules.pushforward (projectiveConeAffineι Y J V)).map
          (nativeKernelRestriction Y J h d)) ≫
      (Scheme.Modules.pushforwardComp (boundaryRestriction Y J h)
        (projectiveConeAffineι Y J V)).hom.app (affineNativeKernel Y J d U)) ≫
      (Scheme.Modules.pushforwardCongr (boundaryRestriction_affineι Y J h)).hom.app
        (affineNativeKernel Y J d U) =
      nativeGlobalProjection Y J d U := by
    rw [← nativeGlobalProjection_restriction Y J h d]
    unfold pushedNativeRestriction
    rw [pushforwardComp_hom_eq_inv]
    simp only [Category.assoc]
    rfl
  rw [hcan] at s2
  rw [hcc] at s3
  have E := s1.symm.trans s2
  unfold nativeGlobalChartHom nativeKernelRestrictionMate
  erw [E]
  rw [Iso.inv_hom_id_app_assoc]
  exact s3



-- @@ L190-202 verbatim
/-- Chart restriction closure: invertibility of the global chart morphism descends along
refinement `U ≤ V`, since the restriction mate is invertible. -/
theorem nativeGlobalChartHom_isIso_of_le {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ)
    [IsIso (nativeGlobalChartHom Y J d V)] : IsIso (nativeGlobalChartHom Y J d U) := by
  rw [nativeGlobalChartHom_restriction Y J h d]
  haveI h1 : IsIso ((Scheme.Modules.pullbackCongr (boundaryRestriction_affineι Y J h).symm).hom.app
      (nativeGlobalKernel Y J d)) := inferInstance
  haveI h2 : IsIso ((Scheme.Modules.pullbackComp (boundaryRestriction Y J h)
      (projectiveConeAffineι Y J V)).inv.app (nativeGlobalKernel Y J d)) := inferInstance
  haveI h3 : IsIso ((Scheme.Modules.pullback (boundaryRestriction Y J h)).map
      (nativeGlobalChartHom Y J d V)) := inferInstance
  haveI h4 : IsIso (nativeKernelRestrictionMate Y J h d) := inferInstance
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 (IsIso.comp_isIso' h3 h4))


-- @@ L204-204 verbatim
end SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityComponentIntersectionNormalBundleTwistChartRecoveryB5
