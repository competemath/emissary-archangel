/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import RiemannRoch.Chow.NormalCone.ProjectiveCompletionDeformationInfinityComponentIntersectionNormalBundleTwistDescent


-- @@ L8-30 verbatim
/-!
# Original no-line native twist restriction recovery

The genuine degree-one source cover proves invertibility of the ORIGINAL affine
restriction adjunction mate. Its unchanged hom, original pushed restriction, native
image selection, and prescribed chart/unit routes are recovered explicitly. Actual
coefficient, scheme and image-family identity/composition laws are also proved.
All integer twists and rank zero are retained.

The small `native_cache_exact` elaboration helper avoids expected-type unification
through large imported module-sheaf carriers. It uses ordinary closed-term
elaboration and `closeMainGoalUsing`, retaining normal metavariable/occurs checks
and final declaration kernel validation. The original mate's mathematical proof
body is precisely the checked affine mate theorem applied to the literal indices.
No trust primitive, reducibility attribute or proof-budget change is introduced.
The proof-valued affine cache retains its inferred native boundary; its linter
warning is left visible.

These affine recovery laws do not assert identity/composition of the full native
kernel pullback maps. The independent global kernel's `nativeGlobalChartHom`
local recovery/IsIso, kernel cocycle, global canonical O(1), quotient and actual
total-twist recovery remain open.
-/


-- @@ L32-32 verbatim
noncomputable section

-- @@ L33-33 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

-- @@ L34-34 verbatim
universe u

-- @@ L35-35 verbatim
namespace SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityComponentIntersectionNormalBundleTwistChartRecovery

-- @@ L36-38 verbatim
open InfinityComponentIntersectionNormalBundleTwistDescent InfinityComponentIntersectionGlobal
  InfinityNormalConeGlobal InfinityNormalBundleTwistNativeOverlap
  InfinityNormalBundleTwistNativeComparison

-- @@ L39-39 verbatim
variable (Y : Scheme.{u}) (J : Y.IdealSheafData)

-- @@ L40-42 verbatim
noncomputable local instance chartRecoveryGrCommRing (U : Y.affineOpens) :
    CommRing (AffineNormalCone.associatedGradedRing Γ(Y,U.1) (J.ideal U)) :=
  Ideal.Quotient.commRing _


-- @@ L44-47 verbatim
/-- The actual original scheme restriction is the native Proj coefficient map. -/
theorem nativeRestriction_schemeMap {U V : Y.affineOpens} (h : U ≤ V) :
    boundaryRestriction Y J h = Proj.map (nativeGradedRestriction Y J h)
      (nativeGradedRestriction_irrelevant Y J h) := rfl


-- @@ L49-56 verbatim
/-- Genuine adjunction-mate invertibility under actual invertible factors. -/
theorem nativeMate_postcomp_isIso {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    {L : 𝒞 ⥤ 𝒟} {F : 𝒟 ⥤ 𝒞} (a : L ⊣ F)
    {X : 𝒞} {P Q : 𝒟} (k : X ⟶ F.obj P) (v : P ⟶ Q)
    (hk : IsIso ((a.homEquiv X P).symm k)) (hv : IsIso v) :
    IsIso ((a.homEquiv X Q).symm (k ≫ F.map v)) := by
  rw [nativeMate_postcomp]
  exact IsIso.comp_isIso' hk hv


-- @@ L58-58 verbatim
section Native

-- @@ L59-65 verbatim
variable {R S σ τ ι : Type u} [CommRing R] [CommRing S]
  [SetLike σ R] [AddSubgroupClass σ R] [SetLike τ S] [AddSubgroupClass τ S]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (g : 𝒜 →+*ᵍ ℬ) (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
  (f : ι → 𝒜 1) (d : ℤ)
  (hcover : (Opens.grothendieckTopology (Proj 𝒜)).CoversTop
    (fun i => InfinityNormalBundleTwistLineRecovery.Native.generatorOpen 𝒜 (f i)))


-- @@ L67-78 verbatim
/-- Invertibility of the actual adjunction mate of native restriction followed by
original all-degree-one selection; cover is genuine, not an IsIso premise. -/
theorem nativeAllTargetRestrictionMate_isIso :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map g hg)).homEquiv _ _).symm
      (nativeKernelToPushforward 𝒜 ℬ g hg f d ≫
        (Scheme.Modules.pushforward (Proj.map g hg)).map
          (@asIso _ _ _ _ (NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
            (imageDegreeOneFamily 𝒜 ℬ g f) d)
            (allDegreeOneToImage_isIso 𝒜 ℬ g hg f d hcover)).inv)) := by
  exact nativeMate_postcomp_isIso _ _ _
    (InfinityNormalBundleTwistNativeRecovery.nativeKernelPullbackHom_isIso_of_cover
      𝒜 ℬ g hg f d hcover) (Iso.isIso_inv _)

-- @@ L79-79 verbatim
end Native


-- @@ L81-86 verbatim
/-- Actual native affine specialization, retaining the exact inferred map carrier. -/
def nativeAffineRestrictionMateInvertible {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ) :=
  nativeAllTargetRestrictionMate_isIso (ReesBlowup.grGrade (J.ideal V))
    (ReesBlowup.grGrade (J.ideal U)) (nativeGradedRestriction Y J h)
    (nativeGradedRestriction_irrelevant Y J h) (fun x => x) d
    (affineNativeGenerator_covers Y J V)


-- @@ L88-94 verbatim
/-- Elaborate a closed cached proof without expected-type guidance. The declaration
kernel still checks the resulting proof against the actual target; no trust primitive
or reducibility change is introduced. This avoids redundant elaborator conversion of
large native module-sheaf carriers. -/
elab "native_cache_exact " e:term : tactic =>
  Lean.Elab.Tactic.closeMainGoalUsing `native_cache_exact
    (fun _ _ => Lean.Elab.Tactic.elabTerm e none)


-- @@ L96-100 verbatim
/-- ORIGINAL affine native restriction mate, with literal source and target indices. -/
instance nativeKernelRestrictionMate_isIso {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ) :
    IsIso (@nativeKernelRestrictionMate Y J U V h d) :=
  by
    native_cache_exact (@nativeAffineRestrictionMateInvertible Y J U V h d)


-- @@ L102-105 verbatim
/-- The genuine ORIGINAL affine restriction isomorphism, with unchanged hom. -/
def nativeKernelRestrictionIso {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ) :
    (Scheme.Modules.pullback (boundaryRestriction Y J h)).obj (affineNativeKernel Y J d V) ≅
      affineNativeKernel Y J d U := asIso (nativeKernelRestrictionMate Y J h d)


-- @@ L107-109 verbatim
/-- Literal recovery of the ORIGINAL native adjunction mate. -/
theorem nativeKernelRestrictionIso_hom {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ) :
    (nativeKernelRestrictionIso Y J h d).hom = nativeKernelRestrictionMate Y J h d := rfl


-- @@ L111-115 verbatim
/-- The actual adjunction recovers ORIGINAL native coefficient restriction. -/
theorem nativeKernelRestrictionIso_adjoint {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction (boundaryRestriction Y J h)).homEquiv _ _
      (nativeKernelRestrictionIso Y J h d).hom = nativeKernelRestriction Y J h d :=
  Equiv.apply_symm_apply _ _


-- @@ L117-122 verbatim
/-- Equality of coefficient homomorphisms retains the actual graded restriction. -/
theorem nativeRestriction_coeff_congr {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) {f f' : A →+* B} (e : f = f') (K : Ideal B) (h : I.map f = K) :
    grRestrictionOfEq I f K h = grRestrictionOfEq I f' K (e ▸ h) := by
  subst e
  rfl


-- @@ L124-129 verbatim
/-- Actual original affine coefficient restriction is identity. -/
theorem nativeRestriction_coeff_id (U : Y.affineOpens) :
    nativeGradedRestriction Y J (le_refl U) = GradedRingHom.id (ReesBlowup.grGrade (J.ideal U)) := by
  unfold nativeGradedRestriction
  rw [nativeRestriction_coeff_congr _ (GlobalBlowup.res_refl Y U)]
  exact grRestrictionOfEq_id _


-- @@ L131-138 verbatim
/-- Actual original coefficient maps compose with their literal affine order. -/
theorem nativeRestriction_coeff_comp {U V W : Y.affineOpens} (h : U ≤ V) (k : V ≤ W) :
    (nativeGradedRestriction Y J h).comp (nativeGradedRestriction Y J k) =
      nativeGradedRestriction Y J (h.trans k) := by
  unfold nativeGradedRestriction
  rw [nativeRestriction_coeff_congr _ (GlobalBlowup.res_comp Y h k)]
  exact grRestrictionOfEq_comp (J.ideal W) (GlobalBlowup.res Y k) (J.ideal V)
    (J.map_ideal k) (GlobalBlowup.res Y h) (J.ideal U) (J.map_ideal h)


-- @@ L140-143 verbatim
/-- ORIGINAL affine boundary maps retain the genuine identity law. -/
theorem nativeRestriction_scheme_id (U : Y.affineOpens) :
    boundaryRestriction Y J (le_refl U) = 𝟙 (ReesBlowup.grScheme (J.ideal U)) :=
  (projectiveConeFunctor Y J).map_id U


-- @@ L145-150 verbatim
/-- ORIGINAL affine boundary maps retain the genuine composition law. -/
@[reassoc] theorem nativeRestriction_scheme_comp {U V W : Y.affineOpens}
    (h : U ≤ V) (k : V ≤ W) :
    boundaryRestriction Y J h ≫ boundaryRestriction Y J k =
      boundaryRestriction Y J (h.trans k) :=
  ((projectiveConeFunctor Y J).map_comp (homOfLE h) (homOfLE k)).symm


-- @@ L152-158 verbatim
/-- Identity coefficient restriction fixes each actual degree-one generator. -/
theorem nativeRestriction_image_id (U : Y.affineOpens) (x : ReesBlowup.grGrade (J.ideal U) 1) :
    nativeRestrictionImageFamily Y J (le_refl U) x = x := by
  apply Subtype.ext
  change nativeGradedRestriction Y J (le_refl U) x.val = x.val
  rw [nativeRestriction_coeff_id]
  rfl


-- @@ L160-166 verbatim
/-- Literal original image-family composition on true affine refinements. -/
theorem nativeRestriction_image_comp {U V W : Y.affineOpens} (h : U ≤ V) (k : V ≤ W)
    (x : ReesBlowup.grGrade (J.ideal W) 1) :
    nativeRestrictionImageFamily Y J h (nativeRestrictionImageFamily Y J k x) =
      nativeRestrictionImageFamily Y J (h.trans k) x := by
  apply Subtype.ext
  exact GradedRingHom.congr_fun (nativeRestriction_coeff_comp Y J h k) x.val


-- @@ L168-172 verbatim
/-- Cancellation of the actual inverse selection through a literal Iso boundary. -/
theorem nativeInverseSelection_cancel {𝒞 : Type*} [Category 𝒞]
    {P Q R : 𝒞} (a : P ⟶ R) (e : Q ≅ R) : (a ≫ e.inv) ≫ e.hom = a :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun q => a ≫ q) e.inv_hom_id).trans (Category.comp_id a))


-- @@ L174-174 verbatim
section NativeSelection

-- @@ L175-181 verbatim
variable {R S σ τ ι : Type u} [CommRing R] [CommRing S]
  [SetLike σ R] [AddSubgroupClass σ R] [SetLike τ S] [AddSubgroupClass τ S]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (g : 𝒜 →+*ᵍ ℬ) (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
  (f : ι → 𝒜 1) (d : ℤ)
  (hcover : (Opens.grothendieckTopology (Proj 𝒜)).CoversTop
    (fun i => InfinityNormalBundleTwistLineRecovery.Native.generatorOpen 𝒜 (f i)))


-- @@ L183-199 verbatim
/-- The actual all-target native mate recovers the ORIGINAL image-family kernel map. -/
theorem nativeAllTargetRestrictionMate_selection :
    ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map g hg)).homEquiv _ _).symm
      (nativeKernelToPushforward 𝒜 ℬ g hg f d ≫
        (Scheme.Modules.pushforward (Proj.map g hg)).map
          (@asIso _ _ _ _ (NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
            (imageDegreeOneFamily 𝒜 ℬ g f) d)
            (allDegreeOneToImage_isIso 𝒜 ℬ g hg f d hcover)).inv) ≫
      NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
        (imageDegreeOneFamily 𝒜 ℬ g f) d = nativeKernelPullbackHom 𝒜 ℬ g hg f d := by
  let S := @asIso _ _ _ _ (NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
    (imageDegreeOneFamily 𝒜 ℬ g f) d) (allDegreeOneToImage_isIso 𝒜 ℬ g hg f d hcover)
  have hm := nativeMate_postcomp
    (Scheme.Modules.pullbackPushforwardAdjunction (Proj.map g hg))
    (nativeKernelToPushforward 𝒜 ℬ g hg f d) S.inv
  exact (congrArg (fun q => q ≫ S.hom) hm).trans
    (nativeInverseSelection_cancel (nativeKernelPullbackHom 𝒜 ℬ g hg f d) S)


-- @@ L201-201 verbatim
end NativeSelection


-- @@ L203-214 verbatim
/-- The ORIGINAL affine restriction mate retains its ORIGINAL image-kernel selection. -/
theorem nativeKernelRestrictionMate_selection {U V : Y.affineOpens} (h : U ≤ V) (d : ℤ) :
    @nativeKernelRestrictionMate Y J U V h d ≫
      NativeFamily.kernelSelection (ReesBlowup.grGrade (J.ideal U)) (fun x => x)
        (nativeRestrictionImageFamily Y J h) d =
      nativeKernelPullbackHom (ReesBlowup.grGrade (J.ideal V)) (ReesBlowup.grGrade (J.ideal U))
        (nativeGradedRestriction Y J h) (nativeGradedRestriction_irrelevant Y J h)
        (fun x => x) d := by
  native_cache_exact (nativeAllTargetRestrictionMate_selection
    (ReesBlowup.grGrade (J.ideal V)) (ReesBlowup.grGrade (J.ideal U))
    (nativeGradedRestriction Y J h) (nativeGradedRestriction_irrelevant Y J h)
    (fun x => x) d (affineNativeGenerator_covers Y J V))


-- @@ L216-216 verbatim
section NativeChartRecovery

-- @@ L217-223 verbatim
variable {R S σ τ ι : Type u} [CommRing R] [CommRing S]
  [SetLike σ R] [AddSubgroupClass σ R] [SetLike τ S] [AddSubgroupClass τ S]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (g : 𝒜 →+*ᵍ ℬ) (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
  (f : ι → 𝒜 1) (d : ℤ)
  (hcover : (Opens.grothendieckTopology (Proj 𝒜)).CoversTop
    (fun i => InfinityNormalBundleTwistLineRecovery.Native.generatorOpen 𝒜 (f i)))


-- @@ L225-247 verbatim
/-- Actual selected native mate recovers the prescribed ORIGINAL chart unit. -/
theorem nativeAllTargetRestrictionMate_unitRecovery (i : ι) :
    (Scheme.Modules.pullback
      (InfinityNormalBundleTwistLineRecovery.Native.generatorOpen ℬ
        (imageDegreeOneFamily 𝒜 ℬ g f i)).ι).map
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map g hg)).homEquiv _ _).symm
        (nativeKernelToPushforward 𝒜 ℬ g hg f d ≫
          (Scheme.Modules.pushforward (Proj.map g hg)).map
            (@asIso _ _ _ _ (NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
              (imageDegreeOneFamily 𝒜 ℬ g f) d)
              (allDegreeOneToImage_isIso 𝒜 ℬ g hg f d hcover)).inv)) ≫
        NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
          (imageDegreeOneFamily 𝒜 ℬ g f) d) ≫
      InfinityNormalBundleTwistNativeRecovery.nativeComponentMate ℬ
        (imageDegreeOneFamily 𝒜 ℬ g f) d i =
      (nativeProjKernelChartUnitIso 𝒜 ℬ g hg f d i).hom :=
  (congrArg (fun q => (Scheme.Modules.pullback
    (InfinityNormalBundleTwistLineRecovery.Native.generatorOpen ℬ
      (imageDegreeOneFamily 𝒜 ℬ g f i)).ι).map q ≫
      InfinityNormalBundleTwistNativeRecovery.nativeComponentMate ℬ
        (imageDegreeOneFamily 𝒜 ℬ g f) d i)
    (nativeAllTargetRestrictionMate_selection 𝒜 ℬ g hg f d hcover)).trans
    (InfinityNormalBundleTwistNativeRecovery.nativeKernelPullbackHom_unitRecovery 𝒜 ℬ g hg f d i)


-- @@ L249-267 verbatim
/-- Actual selected native mate restricts to the ORIGINAL prescribed kernel chart Iso. -/
theorem nativeAllTargetRestrictionMate_chartRecovery (i : ι) :
    (Scheme.Modules.restrictFunctor
      (InfinityNormalBundleTwistLineRecovery.Native.generatorOpen ℬ
        (imageDegreeOneFamily 𝒜 ℬ g f i)).ι).map
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map g hg)).homEquiv _ _).symm
        (nativeKernelToPushforward 𝒜 ℬ g hg f d ≫
          (Scheme.Modules.pushforward (Proj.map g hg)).map
            (@asIso _ _ _ _ (NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
              (imageDegreeOneFamily 𝒜 ℬ g f) d)
              (allDegreeOneToImage_isIso 𝒜 ℬ g hg f d hcover)).inv)) ≫
        NativeFamily.kernelSelection ℬ (fun x : ℬ 1 => x)
          (imageDegreeOneFamily 𝒜 ℬ g f) d) =
      (nativeProjKernelChartIso 𝒜 ℬ g hg f d i).hom :=
  (congrArg (fun q => (Scheme.Modules.restrictFunctor
    (InfinityNormalBundleTwistLineRecovery.Native.generatorOpen ℬ
      (imageDegreeOneFamily 𝒜 ℬ g f i)).ι).map q)
    (nativeAllTargetRestrictionMate_selection 𝒜 ℬ g hg f d hcover)).trans
    (InfinityNormalBundleTwistNativeRecovery.nativeKernelPullbackHom_chartRecovery 𝒜 ℬ g hg f d i)

-- @@ L268-268 verbatim
end NativeChartRecovery


-- @@ L270-287 verbatim
/-- ORIGINAL affine native mate's true unit recovery on each actual image chart. -/
theorem nativeKernelRestrictionMate_unitRecovery {U V : Y.affineOpens} (h : U ≤ V)
    (d : ℤ) (x : ReesBlowup.grGrade (J.ideal V) 1) :
    (Scheme.Modules.pullback
      (InfinityNormalBundleTwistLineRecovery.Native.generatorOpen (ReesBlowup.grGrade (J.ideal U))
        (nativeRestrictionImageFamily Y J h x)).ι).map
      (@nativeKernelRestrictionMate Y J U V h d ≫
        NativeFamily.kernelSelection (ReesBlowup.grGrade (J.ideal U)) (fun x => x)
          (nativeRestrictionImageFamily Y J h) d) ≫
      InfinityNormalBundleTwistNativeRecovery.nativeComponentMate (ReesBlowup.grGrade (J.ideal U))
        (nativeRestrictionImageFamily Y J h) d x =
      (nativeProjKernelChartUnitIso (ReesBlowup.grGrade (J.ideal V))
        (ReesBlowup.grGrade (J.ideal U)) (nativeGradedRestriction Y J h)
        (nativeGradedRestriction_irrelevant Y J h) (fun x => x) d x).hom := by
  native_cache_exact (nativeAllTargetRestrictionMate_unitRecovery
    (ReesBlowup.grGrade (J.ideal V)) (ReesBlowup.grGrade (J.ideal U))
    (nativeGradedRestriction Y J h) (nativeGradedRestriction_irrelevant Y J h)
    (fun x => x) d (affineNativeGenerator_covers Y J V) x)


-- @@ L289-304 verbatim
/-- ORIGINAL affine native mate's literal selected-chart restriction recovery. -/
theorem nativeKernelRestrictionMate_chartRecovery {U V : Y.affineOpens} (h : U ≤ V)
    (d : ℤ) (x : ReesBlowup.grGrade (J.ideal V) 1) :
    (Scheme.Modules.restrictFunctor
      (InfinityNormalBundleTwistLineRecovery.Native.generatorOpen (ReesBlowup.grGrade (J.ideal U))
        (nativeRestrictionImageFamily Y J h x)).ι).map
      (@nativeKernelRestrictionMate Y J U V h d ≫
        NativeFamily.kernelSelection (ReesBlowup.grGrade (J.ideal U)) (fun x => x)
          (nativeRestrictionImageFamily Y J h) d) =
      (nativeProjKernelChartIso (ReesBlowup.grGrade (J.ideal V))
        (ReesBlowup.grGrade (J.ideal U)) (nativeGradedRestriction Y J h)
        (nativeGradedRestriction_irrelevant Y J h) (fun x => x) d x).hom := by
  native_cache_exact (nativeAllTargetRestrictionMate_chartRecovery
    (ReesBlowup.grGrade (J.ideal V)) (ReesBlowup.grGrade (J.ideal U))
    (nativeGradedRestriction Y J h) (nativeGradedRestriction_irrelevant Y J h)
    (fun x => x) d (affineNativeGenerator_covers Y J V) x)


-- @@ L306-306 verbatim
end SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityComponentIntersectionNormalBundleTwistChartRecovery
