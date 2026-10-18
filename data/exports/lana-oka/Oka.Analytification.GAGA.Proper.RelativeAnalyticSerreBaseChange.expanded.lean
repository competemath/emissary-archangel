/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.Proper.RelativeSerreLocalModel


-- @@ L8-26 verbatim
/-!
# The analytic base change morphism for projective morphisms

Let `π : Y' ⟶ Y` and `j : Y' ⟶ ℙᴺ` be morphisms of schemes locally of finite type over `ℂ` such
that `(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion, and let `G` be coherent on `Y'`. For an affine
open `V ⊆ Y` we show that the base change morphism `(π_* G(m))^an ⟶ (π^an)_* G(m)^an` is bijective
on the stalks at the points of `V^an` for `m ≫ 0`
(`ComplexAnalytic.exists_bijective_bcStalk_twistAlong`).

With `A = Γ(Y, V)` and a presentation `ℂ[y₀, …, y_{r-1}] → A`, the stalks are compared along
`Y' ⟶ Y ×_ℂ ℙᴺ` (a closed immersion, where base change is an isomorphism), the open immersion
`ℙ(N; A) ⟶ Y ×_ℂ ℙᴺ` over `Spec A ⟶ Y`, and the closed immersions `ℙ(N; A) ⟶ P` over
`Spec A ⟶ 𝔸ʳ`, where `P = ℙ(N; ℂ[y₀, …, y_{r-1}])`, using
`Oka/Analytification/GAGA/Proper/BaseChangeLocal.lean`. On `P` the statement is
`ComplexAnalytic.relProjectiveSpaceAn.exists_bijective_bcStalk_twist`, applied to the coherent
sheaf obtained by pushing `G` forward to `Y ×_ℂ ℙᴺ`, restricting to `ℙ(N; A)` and pushing forward to
`P`; twisting commutes with all of these (`ComplexAnalytic.pushforwardTwistAlongIso`,
`ComplexAnalytic.pushforwardMapTwistIso`).
-/


-- @@ L28-28 verbatim
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

-- @@ L29-29 verbatim
open AlgebraicGeometry.Scheme.Modules


-- @@ L31-31 verbatim
universe u


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace ComplexAnalytic


-- @@ L37-37 verbatim
open ProjectiveSpace


-- @@ L39-39 verbatim
variable {Y Y' : SchemeLFTℂ.{u}} (π : Y' ⟶ Y) {N : ℕ} (j : Y' ⟶ projectiveSpace.{u} N)


-- @@ L41-47 verbatim
/-- Twisting along `j = pr₂ ∘ (π, j)` commutes with pushforward along `(π, j)`. -/
def pushforwardTwistAlongIso (G : Y'.obj.left.Modules) (m : ℤ) :
    (pushforward (Y.relProjLift π j).hom.left).obj (ProjectiveSpace.twistAlong j.hom.left G m) ≅
      ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left
        ((pushforward (Y.relProjLift π j).hom.left).obj G) m :=
  (pushforward _).mapIso (twistComapIsoOfEq (pullback.lift_snd _ _ _).symm _ G ≪≫
    (twistComapCompIso _ _ _ G).symm) ≪≫ pushforwardTwistComapIso _ _ G


-- @@ L49-57 expanded
/-- Twisting commutes with pushforward along the embedding of `ℙ(N; A)` given by a
presentation `ℂ[y₀, …, y_{r-1}] → A`. -/
def pushforwardMapTwistIso {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (F : (ProjectiveSpace N A).Modules) (m : ℤ) :
    (pushforward (ProjectiveSpace.map (n := N) f)).obj (ProjectiveSpace.twist F m) ≅
      ProjectiveSpace.twist ((pushforward (ProjectiveSpace.map f)).obj F) m :=
  (pushforward _).mapIso
      (twistIsoOfIsPullback (map f) (fun i ↦ (map_preimage_U f i).symm) (cocycle N R ^ m)
          (cocycle N A ^ m) ((cocycle_isPullback f).zpow m) F).symm ≪≫
    pushforwardTwistComapIso _ _ F


-- @@ L60-64 verbatim
/-- Schemes locally of finite type over `ℂ` are locally noetherian. -/
lemma SchemeLFTℂ.isLocallyNoetherian (X : SchemeLFTℂ.{u}) : IsLocallyNoetherian X.obj.left := by
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  exact LocallyOfFiniteType.isLocallyNoetherian X.obj.hom


-- @@ L66-66 verbatim
variable [IsClosedImmersion (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j))]


-- @@ L68-70 verbatim
instance : IsClosedImmersion (Y.relProjLift π j).hom.left :=
  inferInstanceAs (IsClosedImmersion
    (pullback.lift π.hom.left j.hom.left (hom_left_comp_obj_hom_eq π j)))


-- @@ L72-119 expanded
/-- **The analytic base change morphism for `G(m)`, `m ≫ 0`, over an affine open**: for coherent `G`
on `Y'` and an affine open `V ⊆ Y` there is `m₀` such that `(π_* G(m))^an ⟶ (π^an)_* G(m)^an` is
bijective on the stalks at the points of `V^an` for `m ≥ m₀`. -/
theorem exists_bijective_bcStalk_twistAlong
    (G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf) [hG : G.IsCoherent]
    {V : Y.obj.left.Opens} (hV : IsAffineOpen V) :
    ∃ m₀ : ℤ,
      ∀ m : ℤ,
        m₀ ≤ m →
          ∀ v : analytification.obj (Y.affineSpec hV),
            Function.Bijective
              (bcStalk π (twistAlong j G m)
                ((analytification.map (Y.affineSpecι hV)).toLRSHom.base v)) :=
  by
  obtain ⟨r, s, hsurj, hs⟩ := Y.exists_presentation hV
  haveI := Y'.isLocallyNoetherian
  haveI := (Y.relProj N).isLocallyNoetherian
  haveI := (Y.affineProj N hV).isLocallyNoetherian
  haveI := (relProjectiveSpace.{u} r N).isLocallyNoetherian
  haveI := Y.isClosedImmersion_affineSpecEmb hV hs hsurj
  haveI := Y.isClosedImmersion_affineProjEmb (N := N) hV hs hsurj
  haveI : SheafOfModules.IsCoherent (R := Y'.obj.left.ringCatSheaf) G := hG
  let F := (pushforward (Y.relProjLift π j).hom.left).obj G
  haveI : F.IsCoherent := isCoherent_pushforward _ G
  let FA := F.restrict (Y.affineProjChart N hV).hom.left
  haveI : FA.IsCoherent := isCoherent_restrict _ F
  let H := (pushforward (Y.affineProjEmb N hV hs).hom.left).obj FA
  haveI : H.IsCoherent := isCoherent_pushforward _ FA
  haveI : SheafOfModules.IsCoherent (R := (ProjectiveSpace N (RelBase.{u} r)).ringCatSheaf) H := ‹_›
  obtain ⟨n₀, hn₀⟩ := relProjectiveSpaceAn.exists_bijective_bcStalk_twist (m := r) (N := N) H
  refine ⟨n₀, fun m hm v ↦ ?_⟩
  have h7 :
    Function.Bijective
      (bcStalk (Y.affineProjEmb N hV hs ≫ relProjectiveSpaceToAffine r N)
        (ProjectiveSpace.twist FA m)
        ((analytification.map (Y.affineSpecEmb hV hs)).toLRSHom.base v)) :=
    bijective_bcStalk_comp _ _ _ _
      ((bijective_bcStalk_iff_of_iso _ (pushforwardMapTwistIso s FA m) _).2 (hn₀ m hm _))
  have h6 : Function.Bijective (bcStalk (Y.affineProjToSpec N hV) (ProjectiveSpace.twist FA m) v) :=
    bijective_bcStalk_of_comp _ _ _ v (by rw [← Y.affineProjEmb_comp]; exact h7)
  have h5 :
    Function.Bijective
      (bcStalk (Y.affineProjToSpec N hV)
        ((Y.affineProjChart N hV).hom.left.toLRSHom.pullbackModules.obj
          (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m))
        v) :=
    let e5 :
      (Y.affineProjChart N hV).hom.left.toLRSHom.pullbackModules.obj
          (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m) ≅
        ProjectiveSpace.twist FA m :=
      ((restrictFunctorIsoPullbackModules (Y.affineProjChart N hV).hom.left).app
            (ProjectiveSpace.twistAlong (Y.relProjSnd N).hom.left F m)).symm ≪≫
        restrictTwistIso Y.obj.hom hV (Y.relProjLift π j).hom.left G m
    (bijective_bcStalk_iff_of_iso _ e5 v).2 h6
  have h4 :=
    bijective_bcStalk_of_isOpenImmersion (Y.relProjFst N) (Y.affineProjToSpec N hV)
      (Y.affineSpecι hV) (Y.affineProjChart N hV) (Y.affineProjToSpec_comp_affineSpecι hV)
      (fun z hz ↦ Y.mem_range_affineProjChart hV z hz) _ v h5
  have h2 :=
    bijective_bcStalk_comp (Y.relProjLift π j) (Y.relProjFst N) (twistAlong j G m) _
      ((bijective_bcStalk_iff_of_iso _ (pushforwardTwistAlongIso π j G m) _).2 h4)
  rwa [Y.relProjLift_fst] at h2


-- @@ L121-121 verbatim
end ComplexAnalytic
