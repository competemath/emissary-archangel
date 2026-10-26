/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import RiemannRoch.Chow.NormalCone.ProjectiveCompletionDeformationInfinityComponentIntersectionNormalBundleTwistChartRecovery
import RiemannRoch.Chow.NormalCone.ProjectiveCompletionDeformationInfinityNormalBundleTwistNativeCubeAdjointC4
import RiemannRoch.Chow.NormalCone.ProjectiveCompletionDeformationInfinityNormalBundleTwistNativeRestriction


-- @@ L10-19 verbatim
/-!
# Native kernel restriction mates compose (route B4)

Naturality of the native kernel-to-pushforward comparison in the all-degree-one product
selection, assembled with the composition law of the native kernel pullback comparisons
(route C4) to give `mate(W ≤ V) = cast ≫ mate(U ≤ V) ≫ mate(W ≤ U)` for the ORIGINAL native
affine restriction mates. The identity law is not proved here. All integer twists and the
empty family are retained; no cover, rank or desired-comparison hypothesis other than the
derived selection isomorphism of the composite restriction.
-/


-- @@ L21-21 verbatim
noncomputable section

-- @@ L22-22 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

-- @@ L23-23 verbatim
universe u

-- @@ L24-24 verbatim
namespace KernelRestrictionCompB4

-- @@ L25-25 verbatim
open SchemeProjectiveBundle.AffineFrameCover

-- @@ L26-48 verbatim
/-- Naturality of kernel-induced maps in morphisms of squares. -/
theorem kernelMap_natural {X Y : Scheme.{u}} (q : X ⟶ Y)
    {T₀ T₁ T₀' T₁' : Y.Modules} {S₀ S₁ S₀' S₁' : X.Modules}
    (t : T₀ ⟶ T₁) (t' : T₀' ⟶ T₁') (s : S₀ ⟶ S₁) (s' : S₀' ⟶ S₁')
    (a : T₀ ⟶ (Scheme.Modules.pushforward q).obj S₀)
    (b : T₁ ⟶ (Scheme.Modules.pushforward q).obj S₁)
    (a' : T₀' ⟶ (Scheme.Modules.pushforward q).obj S₀')
    (b' : T₁' ⟶ (Scheme.Modules.pushforward q).obj S₁')
    (h : t ≫ b = a ≫ (Scheme.Modules.pushforward q).map s)
    (h' : t' ≫ b' = a' ≫ (Scheme.Modules.pushforward q).map s')
    (u₀ : T₀ ⟶ T₀') (u₁ : T₁ ⟶ T₁') (v₀ : S₀ ⟶ S₀') (v₁ : S₁ ⟶ S₁')
    (hu : t ≫ u₁ = u₀ ≫ t') (hv : s ≫ v₁ = v₀ ≫ s')
    (ha : u₀ ≫ a' = a ≫ (Scheme.Modules.pushforward q).map v₀) :
    kernel.map t t' u₀ u₁ hu ≫ SchemeProjectiveBundle.AffineFrameCover.pullbackTwistOverlap_kernelMap q t' s' a' b' h' =
      SchemeProjectiveBundle.AffineFrameCover.pullbackTwistOverlap_kernelMap q t s a b h ≫
        (Scheme.Modules.pushforward q).map (kernel.map s s' v₀ v₁ hv) := by
  have hk : kernel.map s s' v₀ v₁ hv ≫ kernel.ι s' = kernel.ι s ≫ v₀ := kernel.lift_ι _ _ _
  have hk' : kernel.map t t' u₀ u₁ hu ≫ kernel.ι t' = kernel.ι t ≫ u₀ := kernel.lift_ι _ _ _
  apply (cancel_mono ((Scheme.Modules.pushforward q).map (kernel.ι s'))).1
  try simp only [Category.assoc]
  rw [pullbackTwistOverlap_kernelMap_ι, ← Functor.map_comp, hk, Functor.map_comp,
    ← Category.assoc, hk', Category.assoc, ha]
  rw [pullbackTwistOverlap_kernelMap_ι_assoc]


-- @@ L50-50 verbatim
section Native

-- @@ L51-51 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation

-- @@ L52-53 verbatim
open InfinityNormalBundleTwistLineRecovery InfinityNormalBundleTwistNativeComparison
  InfinityNormalBundleTwistNativeOverlap

-- @@ L54-58 verbatim
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (g : 𝒜 →+*ᵍ ℬ) (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
  {ι : Type u} (f : ι → 𝒜 1)

-- @@ L59-59 verbatim
section Selection

-- @@ L60-60 verbatim
variable {κ : Type u} (r : κ → ι)


-- @@ L62-80 verbatim
theorem nativeChartSelection_natural :
    NativeFamily.chartSelection 𝒜 f r ≫ nativeChartCochainMap 𝒜 ℬ g hg (f ∘ r) =
      nativeChartCochainMap 𝒜 ℬ g hg f ≫ (Scheme.Modules.pushforward (Proj.map g hg)).map
        (NativeFamily.chartSelection ℬ (imageDegreeOneFamily 𝒜 ℬ g f) r) := by
  apply pullbackTwistOverlap_pushforwardPi_hom_ext
  intro j
  have h1 := nativeChartCochainMap_π 𝒜 ℬ g hg (f ∘ r) j
  have h2 := NativeFamily.chartSelection_π 𝒜 f r j
  have h3 := nativeChartCochainMap_π 𝒜 ℬ g hg f (r j)
  have h4 := NativeFamily.chartSelection_π ℬ (imageDegreeOneFamily 𝒜 ℬ g f) r j
  refine (congrArg (fun m => NativeFamily.chartSelection 𝒜 f r ≫ m) h1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m => m ≫ nativeChartPushedUnitMap 𝒜 ℬ g hg (f ∘ r) j) h2).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun m => nativeChartCochainMap 𝒜 ℬ g hg f ≫ m)
    (Functor.map_comp _ _ _).symm)
  refine Eq.trans ?_ (congrArg (fun m => nativeChartCochainMap 𝒜 ℬ g hg f ≫
    (Scheme.Modules.pushforward (Proj.map g hg)).map m) h4.symm)
  exact h3.symm


-- @@ L82-91 verbatim
theorem nativeKernelSelection_natural (d : ℤ) :
    NativeFamily.kernelSelection 𝒜 f r d ≫ nativeKernelToPushforward 𝒜 ℬ g hg (f ∘ r) d =
      nativeKernelToPushforward 𝒜 ℬ g hg f d ≫ (Scheme.Modules.pushforward (Proj.map g hg)).map
        (NativeFamily.kernelSelection ℬ (imageDegreeOneFamily 𝒜 ℬ g f) r d) :=
  kernelMap_natural (Proj.map g hg)
    (h := nativeChartCochainMap_differential 𝒜 ℬ g hg f d)
    (h' := nativeChartCochainMap_differential 𝒜 ℬ g hg (f ∘ r) d)
    (hu := NativeFamily.selection_difference 𝒜 f r d)
    (hv := NativeFamily.selection_difference ℬ (imageDegreeOneFamily 𝒜 ℬ g f) r d)
    (ha := nativeChartSelection_natural 𝒜 ℬ g hg f r)


-- @@ L93-110 verbatim
theorem nativeKernelPullbackHom_selection_natural (d : ℤ) :
    (Scheme.Modules.pullback (Proj.map g hg)).map (NativeFamily.kernelSelection 𝒜 f r d) ≫
      nativeKernelPullbackHom 𝒜 ℬ g hg (f ∘ r) d =
    nativeKernelPullbackHom 𝒜 ℬ g hg f d ≫
      NativeFamily.kernelSelection ℬ (imageDegreeOneFamily 𝒜 ℬ g f) r d := by
  have e1 : ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map g hg)).homEquiv _ _)
      ((Scheme.Modules.pullback (Proj.map g hg)).map (NativeFamily.kernelSelection 𝒜 f r d) ≫
        nativeKernelPullbackHom 𝒜 ℬ g hg (f ∘ r) d) =
      NativeFamily.kernelSelection 𝒜 f r d ≫ nativeKernelToPushforward 𝒜 ℬ g hg (f ∘ r) d := by
    rw [Adjunction.homEquiv_naturality_left, nativeKernelPullbackHom_adjoint]
  have e2 : ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map g hg)).homEquiv _ _)
      (nativeKernelPullbackHom 𝒜 ℬ g hg f d ≫
        NativeFamily.kernelSelection ℬ (imageDegreeOneFamily 𝒜 ℬ g f) r d) =
      nativeKernelToPushforward 𝒜 ℬ g hg f d ≫ (Scheme.Modules.pushforward (Proj.map g hg)).map
        (NativeFamily.kernelSelection ℬ (imageDegreeOneFamily 𝒜 ℬ g f) r d) := by
    rw [Adjunction.homEquiv_naturality_right, nativeKernelPullbackHom_adjoint]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map g hg)).homEquiv _ _).injective
    (e1.trans ((nativeKernelSelection_natural 𝒜 ℬ g hg f r d).trans e2.symm))

-- @@ L111-111 verbatim
end Selection


-- @@ L113-113 verbatim
section Comp

-- @@ L114-118 verbatim
variable {C ψ : Type u} [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  (𝒞 : ℕ → ψ) [GradedRing 𝒞]
  (g' : ℬ →+*ᵍ 𝒞) (hg' : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map g')
  {g₃ : 𝒜 →+*ᵍ 𝒞}
  (hk₃ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map g₃)


-- @@ L120-124 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityNormalBundleTwistNativeCube in
theorem projMap_comp_eq' (e : g'.comp g = g₃) :
    Proj.map g' hg' ≫ Proj.map g hg = Proj.map g₃ hk₃ := by
  subst e
  exact projMap_comp_eq 𝒜 ℬ 𝒞 g g' hg hg' hk₃



-- @@ L127-226 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityNormalBundleTwistNativeCube
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityNormalBundleTwistNativeRestriction in
/-- Ring-level composition law of selected native restriction mates. -/
theorem mate_comp (d : ℤ) (e : g'.comp g = g₃)
    [Mono (NativeFamily.kernelSelection 𝒞 (fun x : 𝒞 1 => x)
      (imageDegreeOneFamily 𝒜 𝒞 g₃ (fun x : 𝒜 1 => x)) d)]
    (m : (Scheme.Modules.pullback (Proj.map g hg)).obj
        (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ⟶
      Native.degreeOneSheaf ℬ (fun x : ℬ 1 => x) d)
    (hm : m ≫ NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
      (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d =
      nativeKernelPullbackHom 𝒜 ℬ g hg (fun x : 𝒜 1 => x) d)
    (m' : (Scheme.Modules.pullback (Proj.map g' hg')).obj
        (Native.degreeOneSheaf ℬ (fun x : ℬ 1 => x) d) ⟶
      Native.degreeOneSheaf 𝒞 (fun x : 𝒞 1 => x) d)
    (hm' : m' ≫ NativeFamily.kernelSelection 𝒞 (fun x : 𝒞 1 => x)
      (imageDegreeOneFamily ℬ 𝒞 g' (fun x : ℬ 1 => x)) d =
      nativeKernelPullbackHom ℬ 𝒞 g' hg' (fun x : ℬ 1 => x) d)
    (m₃ : (Scheme.Modules.pullback (Proj.map g₃ hk₃)).obj
        (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ⟶
      Native.degreeOneSheaf 𝒞 (fun x : 𝒞 1 => x) d)
    (hm₃ : m₃ ≫ NativeFamily.kernelSelection 𝒞 (fun x : 𝒞 1 => x)
      (imageDegreeOneFamily 𝒜 𝒞 g₃ (fun x : 𝒜 1 => x)) d =
      nativeKernelPullbackHom 𝒜 𝒞 g₃ hk₃ (fun x : 𝒜 1 => x) d) :
    m₃ = (Scheme.Modules.pullbackCongr (projMap_comp_eq' 𝒜 ℬ g hg 𝒞 g' hg' hk₃ e).symm).hom.app
        (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫
      (Scheme.Modules.pullbackComp (Proj.map g' hg') (Proj.map g hg)).inv.app
        (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫
      (Scheme.Modules.pullback (Proj.map g' hg')).map m ≫ m' := by
  subst e
  have hsel := nativeKernelSelection_comp 𝒞 (fun x : 𝒞 1 => x)
    (imageDegreeOneFamily ℬ 𝒞 g' (fun x : ℬ 1 => x))
    (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d
  have hnat := nativeKernelPullbackHom_selection_natural ℬ 𝒞 g' hg' (fun x : ℬ 1 => x)
    (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d
  have s1 : (Scheme.Modules.pullback (Proj.map g' hg')).map
        (nativeKernelPullbackHom 𝒜 ℬ g hg (fun x : 𝒜 1 => x) d) ≫
        nativeKernelPullbackHom ℬ 𝒞 g' hg' (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d
      = (Scheme.Modules.pullback (Proj.map g' hg')).map m ≫
        ((Scheme.Modules.pullback (Proj.map g' hg')).map
          (NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
            (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d) ≫
        nativeKernelPullbackHom ℬ 𝒞 g' hg' (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d) := by
    rw [← hm]
    exact (congrArg (fun z => z ≫ nativeKernelPullbackHom ℬ 𝒞 g' hg'
      (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d) (Functor.map_comp _ _ _)).trans
      (Category.assoc _ _ _)
  have s2 : (Scheme.Modules.pullback (Proj.map g' hg')).map m ≫
        ((Scheme.Modules.pullback (Proj.map g' hg')).map
          (NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
            (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d) ≫
        nativeKernelPullbackHom ℬ 𝒞 g' hg' (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d) =
      (Scheme.Modules.pullback (Proj.map g' hg')).map m ≫
        (nativeKernelPullbackHom ℬ 𝒞 g' hg' (fun x : ℬ 1 => x) d ≫
          NativeFamily.kernelSelection 𝒞 (imageDegreeOneFamily ℬ 𝒞 g' (fun x : ℬ 1 => x))
            (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d) :=
    congrArg (fun z => (Scheme.Modules.pullback (Proj.map g' hg')).map m ≫ z) hnat
  have s3 : (Scheme.Modules.pullback (Proj.map g' hg')).map m ≫
        (nativeKernelPullbackHom ℬ 𝒞 g' hg' (fun x : ℬ 1 => x) d ≫
          NativeFamily.kernelSelection 𝒞 (imageDegreeOneFamily ℬ 𝒞 g' (fun x : ℬ 1 => x))
            (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d) =
      (Scheme.Modules.pullback (Proj.map g' hg')).map m ≫ m' ≫
        NativeFamily.kernelSelection 𝒞 (fun x : 𝒞 1 => x)
          (imageDegreeOneFamily 𝒜 𝒞 (g'.comp g) (fun x : 𝒜 1 => x)) d := by
    rw [← hm']
    exact congrArg (fun z => (Scheme.Modules.pullback (Proj.map g' hg')).map m ≫ z)
      ((Category.assoc _ _ _).trans (congrArg (fun z => m' ≫ z) hsel))
  have key := (s1.trans s2).trans s3
  have A1 : m₃ ≫ (NativeFamily.kernelSelection 𝒞 (fun x : 𝒞 1 => x)
    (imageDegreeOneFamily 𝒜 𝒞 (g'.comp g) (fun x : 𝒜 1 => x)) d) = (Scheme.Modules.pullbackCongr (projMap_comp_eq 𝒜 ℬ 𝒞 g g' hg hg' hk₃).symm).hom.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ (Scheme.Modules.pullbackComp (Proj.map g' hg') (Proj.map g hg)).inv.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ ((Scheme.Modules.pullback (Proj.map g' hg')).map (nativeKernelPullbackHom 𝒜 ℬ g hg (fun x : 𝒜 1 => x) d) ≫
      nativeKernelPullbackHom ℬ 𝒞 g' hg' (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d) :=
    hm₃.trans (nativeKernelPullbackHom_comp 𝒜 ℬ 𝒞 g g' hg hg' hk₃ (fun x : 𝒜 1 => x) d)
  have A2 : ((Scheme.Modules.pullbackCongr (projMap_comp_eq' 𝒜 ℬ g hg 𝒞 g' hg' hk₃ (Eq.refl (g'.comp g))).symm).hom.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ (Scheme.Modules.pullbackComp (Proj.map g' hg') (Proj.map g hg)).inv.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ ((Scheme.Modules.pullback (Proj.map g' hg')).map m ≫ m')) ≫ (NativeFamily.kernelSelection 𝒞 (fun x : 𝒞 1 => x)
    (imageDegreeOneFamily 𝒜 𝒞 (g'.comp g) (fun x : 𝒜 1 => x)) d) = (Scheme.Modules.pullbackCongr (projMap_comp_eq' 𝒜 ℬ g hg 𝒞 g' hg' hk₃ (Eq.refl (g'.comp g))).symm).hom.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ (Scheme.Modules.pullbackComp (Proj.map g' hg') (Proj.map g hg)).inv.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ ((Scheme.Modules.pullback (Proj.map g' hg')).map m ≫ m' ≫
      NativeFamily.kernelSelection 𝒞 (fun x : 𝒞 1 => x)
        (imageDegreeOneFamily 𝒜 𝒞 (g'.comp g) (fun x : 𝒜 1 => x)) d) := by
    simp only [Category.assoc]
  have E : (Scheme.Modules.pullbackCongr (projMap_comp_eq' 𝒜 ℬ g hg 𝒞 g' hg' hk₃ (Eq.refl (g'.comp g))).symm).hom.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ (Scheme.Modules.pullbackComp (Proj.map g' hg') (Proj.map g hg)).inv.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ ((Scheme.Modules.pullback (Proj.map g' hg')).map (nativeKernelPullbackHom 𝒜 ℬ g hg (fun x : 𝒜 1 => x) d) ≫
      nativeKernelPullbackHom ℬ 𝒞 g' hg' (imageDegreeOneFamily 𝒜 ℬ g (fun x : 𝒜 1 => x)) d) = (Scheme.Modules.pullbackCongr (projMap_comp_eq' 𝒜 ℬ g hg 𝒞 g' hg' hk₃ (Eq.refl (g'.comp g))).symm).hom.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ (Scheme.Modules.pullbackComp (Proj.map g' hg') (Proj.map g hg)).inv.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ ((Scheme.Modules.pullback (Proj.map g' hg')).map m ≫ m' ≫
      NativeFamily.kernelSelection 𝒞 (fun x : 𝒞 1 => x)
        (imageDegreeOneFamily 𝒜 𝒞 (g'.comp g) (fun x : 𝒜 1 => x)) d) := (congrArg (fun z => (Scheme.Modules.pullbackCongr (projMap_comp_eq' 𝒜 ℬ g hg 𝒞 g' hg' hk₃ (Eq.refl (g'.comp g))).symm).hom.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ (Scheme.Modules.pullbackComp (Proj.map g' hg') (Proj.map g hg)).inv.app
      (Native.degreeOneSheaf 𝒜 (fun x : 𝒜 1 => x) d) ≫ z) key)
  have hp : projMap_comp_eq' 𝒜 ℬ g hg 𝒞 g' hg' hk₃ (Eq.refl (g'.comp g)) = projMap_comp_eq 𝒜 ℬ 𝒞 g g' hg hg' hk₃ := rfl
  rw [← hp] at A1
  have z1 := E.trans A2.symm
  have z2 := A1.trans z1
  have z3 := (cancel_mono (NativeFamily.kernelSelection 𝒞 (fun x : 𝒞 1 => x)
    (imageDegreeOneFamily 𝒜 𝒞 (g'.comp g) (fun x : 𝒜 1 => x)) d)).1 z2
  exact z3


-- @@ L228-228 verbatim
end Comp

-- @@ L229-229 verbatim
end Native



-- @@ L232-232 verbatim
section Generic

-- @@ L233-238 verbatim
/-- Proof/endpoint irrelevance for `pullbackCongr`, generic in the endpoints. -/
theorem pullbackCongr_hom_app_heq {X Y : Scheme.{u}} {f g f' g' : X ⟶ Y}
    (hf : f = f') (hg : g = g') (h : f = g) (h' : f' = g') (M : Y.Modules) :
    HEq ((Scheme.Modules.pullbackCongr h).hom.app M) ((Scheme.Modules.pullbackCongr h').hom.app M) := by
  subst hf hg
  rfl

-- @@ L239-239 verbatim
end Generic

-- @@ L240-240 verbatim
end KernelRestrictionCompB4



-- @@ L243-243 verbatim
namespace SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityComponentIntersectionNormalBundleTwistDescent

-- @@ L244-246 verbatim
open InfinityComponentIntersectionGlobal InfinityNormalConeGlobal
  InfinityNormalBundleTwistNativeComparison InfinityNormalBundleTwistNativeOverlap
  InfinityComponentIntersectionNormalBundleTwistChartRecovery

-- @@ L247-247 verbatim
variable (Y : Scheme.{u}) (J : Y.IdealSheafData)

-- @@ L248-250 verbatim
noncomputable local instance b4GrCommRing (U : Y.affineOpens) :
    CommRing (AffineNormalCone.associatedGradedRing Γ(Y,U.1) (J.ideal U)) :=
  Ideal.Quotient.commRing _


-- @@ L252-263 verbatim
theorem b4_cong_conv {W U V : Y.affineOpens} (h : W ≤ U) (k : U ≤ V) (d : ℤ) :
    (Scheme.Modules.pullbackCongr (nativeRestriction_scheme_comp Y J h k).symm).hom.app
        (affineNativeKernel Y J d V) =
    (Scheme.Modules.pullbackCongr (KernelRestrictionCompB4.projMap_comp_eq'
      (ReesBlowup.grGrade (J.ideal V)) (ReesBlowup.grGrade (J.ideal U))
      (nativeGradedRestriction Y J k) (nativeGradedRestriction_irrelevant Y J k)
      (ReesBlowup.grGrade (J.ideal W)) (nativeGradedRestriction Y J h)
      (nativeGradedRestriction_irrelevant Y J h) (nativeGradedRestriction_irrelevant Y J (h.trans k))
      (nativeRestriction_coeff_comp Y J h k)).symm).hom.app
        (InfinityNormalBundleTwistLineRecovery.Native.degreeOneSheaf (ReesBlowup.grGrade (J.ideal V)) (fun x => x) d) :=
  eq_of_heq (KernelRestrictionCompB4.pullbackCongr_hom_app_heq
    (rfl : _) (rfl : _) _ _ _)


-- @@ L265-277 verbatim
/-- Normalise the Descent-level definitions (and the several local `CommRing` instances) to their
common `Proj`-level bodies, so that terms from different files agree syntactically. -/
local macro "b4norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (
    try unfold nativeRestrictionImageFamily $[$loc]?
    try unfold affineNativeKernel $[$loc]?
    try unfold boundaryRestriction $[$loc]?
    try unfold grSchemeRestrictionOfEq $[$loc]?
    try unfold nativeGradedRestriction $[$loc]?
    try unfold grRestrictionOfEq $[$loc]?
    try unfold chartRecoveryGrCommRing $[$loc]?
    try unfold nativeGrCommRing $[$loc]?
    try unfold b4GrCommRing $[$loc]?))


-- @@ L279-311 verbatim
/-- Composition law of the ORIGINAL native affine restriction mates: for `W ≤ U ≤ V` the mate of
`W ≤ V` is the pullback-composition and Proj-equality cast of the mate of `U ≤ V` followed by the
mate of `W ≤ U`. -/
theorem nativeKernelRestrictionMate_comp {W U V : Y.affineOpens} (h : W ≤ U) (k : U ≤ V)
    (d : ℤ) :
    nativeKernelRestrictionMate Y J (h.trans k) d =
      (Scheme.Modules.pullbackCongr (nativeRestriction_scheme_comp Y J h k).symm).hom.app
        (affineNativeKernel Y J d V) ≫
      (Scheme.Modules.pullbackComp (boundaryRestriction Y J h) (boundaryRestriction Y J k)).inv.app
        (affineNativeKernel Y J d V) ≫
      (Scheme.Modules.pullback (boundaryRestriction Y J h)).map
        (nativeKernelRestrictionMate Y J k d) ≫
      nativeKernelRestrictionMate Y J h d := by
  haveI : Mono (NativeFamily.kernelSelection (ReesBlowup.grGrade (J.ideal W)) (fun x => x)
      (imageDegreeOneFamily (ReesBlowup.grGrade (J.ideal V)) (ReesBlowup.grGrade (J.ideal W))
        (nativeGradedRestriction Y J (h.trans k)) (fun x => x)) d) :=
    (inferInstance : Mono (NativeFamily.kernelSelection (ReesBlowup.grGrade (J.ideal W)) (fun x => x)
      (nativeRestrictionImageFamily Y J (h.trans k)) d))
  have hk := nativeKernelRestrictionMate_selection Y J k d
  have hh := nativeKernelRestrictionMate_selection Y J h d
  have hhk := nativeKernelRestrictionMate_selection Y J (h.trans k) d
  have z := KernelRestrictionCompB4.mate_comp (ReesBlowup.grGrade (J.ideal V))
    (ReesBlowup.grGrade (J.ideal U))
    (nativeGradedRestriction Y J k) (nativeGradedRestriction_irrelevant Y J k)
    (ReesBlowup.grGrade (J.ideal W)) (nativeGradedRestriction Y J h)
    (nativeGradedRestriction_irrelevant Y J h) (nativeGradedRestriction_irrelevant Y J (h.trans k))
    d (nativeRestriction_coeff_comp Y J h k)
    (nativeKernelRestrictionMate Y J k d) (by b4norm at hk ⊢; exact hk)
    (nativeKernelRestrictionMate Y J h d) (by b4norm at hh ⊢; exact hh)
    (nativeKernelRestrictionMate Y J (h.trans k) d) (by b4norm at hhk ⊢; exact hhk)
  rw [b4_cong_conv Y J h k d]
  b4norm at z ⊢
  exact z

-- @@ L312-312 verbatim
end SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityComponentIntersectionNormalBundleTwistDescent
