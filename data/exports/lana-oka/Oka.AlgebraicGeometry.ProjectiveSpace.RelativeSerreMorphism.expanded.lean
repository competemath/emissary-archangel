/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.Modules.CoherentPushforward
import Oka.AlgebraicGeometry.Modules.CocycleTwistComap
import Oka.AlgebraicGeometry.Modules.ToAb
import Oka.AlgebraicGeometry.ProjectiveSpace.RelativeChart
import Oka.AlgebraicGeometry.ProjectiveSpace.RelativeSerre
import Oka.AlgebraicGeometry.Modules.Coherent
import Oka.Geometry.RingedSpace.LocallyRingedSpace.PullbackCoherent


-- @@ L14-37 verbatim
/-!
# Relative Serre vanishing for projective morphisms

Let `K` be a ring, `y : Y ⟶ Spec K` a locally noetherian quasi-compact scheme over `K`, and let
`π : Y' ⟶ Y`, `j : Y' ⟶ ℙ(n; K)` be morphisms over `K` such that
`ι = (π, j) : Y' ⟶ P = Y ×_K ℙ(n; K)` is a closed immersion. For a sheaf of modules `G` on `Y'`
let `G(m) = G ⊗ j^* O(m)` (`ProjectiveSpace.twistAlong j G m`), the twist of `G` by the pullback
along `j` of the `m`-th power of the standard cocycle of `ℙ(n; K)`.

**Relative Serre vanishing** (`ProjectiveSpace.exists_isPushforwardAcyclic_twistAlong`): for
coherent `G` there is `m₀` such that `G(m)` is `π`-acyclic for all `m ≥ m₀`.

Proof: `π`-acyclicity can be checked on the preimages of the basic opens `D(g)` of the members `V`
of an affine open cover of `Y` (`AlgebraicGeometry.isPushforwardAcyclic_of_basicOpen`). Over an
affine open `V` with ring `A`, `P` restricts to `ℙ(n; A)` (`ProjectiveSpace.affineChart`), and
`Hᵠ(π⁻¹ D(g), G(m)) ≅ Hᵠ(ℙ(n; A)_g, F(m))` with `F` the restriction to `ℙ(n; A)` of the coherent
sheaf `ι_* G` (`ProjectiveSpace.H_twistAlong_eq_zero_of_affineChart`): pushforward along the
closed immersion `ι` and restriction along the open immersion `ℙ(n; A) ⟶ P` preserve cohomology
and commute with twists. The uniform vanishing on the basic opens of `ℙ(n; A)`
(`ProjectiveSpace.exists_H_basicOpen_twist_eq_zero`) and quasi-compactness of `Y` conclude.

We also record that pushforwards along closed immersions and restrictions along open immersions
preserve coherence (`Scheme.Modules.isCoherent_pushforward`, `Scheme.Modules.isCoherent_restrict`).
-/


-- @@ L39-39 verbatim
open CategoryTheory Limits


-- @@ L41-41 verbatim
universe u


-- @@ L43-43 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L45-45 verbatim
variable {X Y : Scheme.{u}} (e : Y ⟶ X) [IsOpenImmersion e]


-- @@ L47-51 verbatim
/-- Restriction along an open immersion is the pullback of sheaves of modules along the
underlying morphism of locally ringed spaces. -/
noncomputable def restrictFunctorIsoPullbackModules :
    restrictFunctor e ≅ e.toLRSHom.pullbackModules :=
  (restrictAdjunction e).leftAdjointUniq e.toLRSHom.pullbackModulesAdj


-- @@ L53-62 verbatim
/-- **Restrictions of coherent sheaves along open immersions are coherent.** -/
theorem isCoherent_restrict [IsLocallyNoetherian Y] (F : X.Modules) [F.IsCoherent] :
    (F.restrict e).IsCoherent := by
  haveI : SheafOfModules.IsCoherent (R := X.toLocallyRingedSpace.ringSheaf) F := ‹_›
  have h := LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf
    (Scheme.isCoherentStructureSheaf (X := Y)) e.toLRSHom F
  haveI : SheafOfModules.IsCoherent (R := Y.ringCatSheaf)
    (e.toLRSHom.pullbackModules.obj F) := h
  exact SheafOfModules.IsCoherent.of_iso.{u}
    (((restrictFunctorIsoPullbackModules e).app F).symm : (_ : Y.Modules) ≅ _)


-- @@ L64-70 verbatim
/-- **Pushforwards of coherent sheaves along closed immersions are coherent**, in the
`Scheme.Modules` spelling. -/
theorem isCoherent_pushforward {Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι]
    [IsLocallyNoetherian X] (G : Z.Modules) [G.IsCoherent] :
    ((pushforward ι).obj G).IsCoherent := by
  haveI : SheafOfModules.IsCoherent (R := Z.toLocallyRingedSpace.ringSheaf) G := ‹_›
  exact isCoherent_pushforward_of_isClosedImmersion ι G


-- @@ L72-72 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L74-74 verbatim
namespace AlgebraicGeometry.ProjectiveSpace


-- @@ L76-76 verbatim
open Scheme.Modules


-- @@ L78-78 verbatim
variable {n : ℕ} {K : Type u} [CommRing K] {Y Y' : Scheme.{u}}


-- @@ L80-84 verbatim
/-- The twist `G(m) = G ⊗ j^* O(m)` of a sheaf of modules `G` on `Y'` along a morphism
`j : Y' ⟶ ℙ(n; K)`: the twist by the pullback along `j` of the `m`-th power of the standard
cocycle. -/
noncomputable abbrev twistAlong (j : Y' ⟶ ℙ(n; K)) (G : Y'.Modules) (m : ℤ) : Y'.Modules :=
  Scheme.Modules.twist G ((cocycle n K ^ m).comap j)


-- @@ L86-88 verbatim
lemma eq_zero_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (h : ∀ b : B, b = 0) (a : A) : a = 0 :=
  e.injective (by rw [h (e a), map_zero])


-- @@ L90-91 verbatim
variable (y : Y ⟶ Spec (.of K)) (π : Y' ⟶ Y) (j : Y' ⟶ ℙ(n; K)) (w : π ≫ y = j ≫ toSpec n K)
  [IsClosedImmersion (pullback.lift π j w)]


-- @@ L93-135 verbatim
/-- Over an affine open `V ⊆ Y` with ring `A`, the cohomology of `G(m)` on the preimage of a
basic open `D(g) ⊆ V` vanishes if the cohomology of `F(m)` on the basic open of `g` in `ℙ(n; A)`
does, where `F` is the pushforward of `G` to `Y ×_K ℙ(n; K)` restricted to `ℙ(n; A)`. -/
lemma H_twistAlong_eq_zero_of_affineChart {V : Y.Opens} (hV : IsAffineOpen V) (G : Y'.Modules)
    (m : ℤ) (g : Γ(Y, V)) (q : ℕ)
    (h : ∀ x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (ℙ(n; Γ(Y, V)).basicOpen
      ((toSpec n _).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv g)))).obj
        ((SheafOfModules.toSheaf ℙ(n; Γ(Y, V)).ringCatSheaf).obj
          (twist (((pushforward (pullback.lift π j w)).obj G).restrict
            (affineChart n y hV)) m))) (q + 1), x = 0)
    (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (π ⁻¹ᵁ Y.basicOpen g)).obj
      ((SheafOfModules.toSheaf Y'.ringCatSheaf).obj (twistAlong j G m))) (q + 1)) : x = 0 := by
  let ι := pullback.lift π j w
  let e := affineChart n y hV
  let F := (pushforward ι).obj G
  let W := pullback.fst y (toSpec n K) ⁻¹ᵁ Y.basicOpen g
  let d := (cocycle n K ^ m).comap (pullback.snd y (toSpec n K))
  have hπ : π ⁻¹ᵁ Y.basicOpen g = ι ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_fst]
  have hW : W ≤ e.opensRange := by
    rw [opensRange_affineChart]
    exact Scheme.Hom.preimage_mono _ (Y.basicOpen_le g)
  let e₁ : twistAlong j G m ≅ Scheme.Modules.twist G (d.comap ι) :=
    twistComapIsoOfEq (pullback.lift_snd π j w).symm _ G ≪≫ (twistComapCompIso ι _ _ G).symm
  let e₃ : (Scheme.Modules.twist F d).restrict e ≅
      Scheme.Modules.twist (F.restrict e) (cocycle n Γ(Y, V) ^ m) :=
    restrictTwistComapIso e d F ≪≫ twistComapCompIso e _ _ _ ≪≫
      twistComapIsoOfEq (affineChart_snd y hV) _ _ ≪≫
      twistIsoOfIsPullback (map (structureRingHom y hV)) (fun i ↦ (map_preimage_U _ i).symm)
        (cocycle n K ^ m) (cocycle n Γ(Y, V) ^ m) ((cocycle_isPullback _).zpow m) _
  revert x
  rw [hπ]
  intro x
  refine eq_zero_of_addEquiv
    (((((TopCat.Sheaf.H.restrictOpenAddEquivOfIso _ ((toAbFunctor Y').mapIso e₁) (q + 1)).trans
      (hRestrictOpenPushforwardAddEquiv ι _ W (q + 1))).trans
      (TopCat.Sheaf.H.restrictOpenAddEquivOfIso _
        ((toAbFunctor _).mapIso (pushforwardTwistComapIso ι d G)) (q + 1))).trans
      (hRestrictOpenRestrictAddEquiv e _ W hW (q + 1))).trans
      (TopCat.Sheaf.H.restrictOpenAddEquivOfIso _ ((toAbFunctor _).mapIso e₃) (q + 1))) ?_ x
  have he : e ⁻¹ᵁ W = _ := affineChart_preimage_basicOpen y hV g
  rw [he]
  exact h


-- @@ L137-175 verbatim
include w in
/-- **Relative Serre vanishing.** Let `π : Y' ⟶ Y` and `j : Y' ⟶ ℙ(n; K)` be morphisms over
`Spec K` such that `(π, j) : Y' ⟶ Y ×_K ℙ(n; K)` is a closed immersion, with `Y` locally
noetherian and quasi-compact. For every coherent `G` on `Y'` there is `m₀` such that
`G(m) = G ⊗ j^* O(m)` is `π`-acyclic for all `m ≥ m₀`: the higher direct images `Rᵠ π_* G(m)`
vanish. -/
theorem exists_isPushforwardAcyclic_twistAlong [IsLocallyNoetherian Y] [CompactSpace Y]
    (G : Y'.Modules) [G.IsCoherent] :
    ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → TopCat.Sheaf.IsPushforwardAcyclic π.base
      ((SheafOfModules.toSheaf Y'.ringCatSheaf).obj (twistAlong j G m)) := by
  haveI : IsLocallyNoetherian (pullback y (toSpec n K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst y (toSpec n K))
  haveI := isCoherent_pushforward (pullback.lift π j w) G
  have key : ∀ V : Y.affineOpens, ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∀ (g : Γ(Y, V)) (q : ℕ)
      (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (π ⁻¹ᵁ Y.basicOpen g)).obj
        ((SheafOfModules.toSheaf Y'.ringCatSheaf).obj (twistAlong j G m))) (q + 1)), x = 0 := by
    intro V
    haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian V
    haveI : IsLocallyNoetherian ℙ(n; Γ(Y, V)) :=
      LocallyOfFiniteType.isLocallyNoetherian (toSpec n _)
    haveI := isCoherent_restrict (affineChart n y V.2)
      ((pushforward (pullback.lift π j w)).obj G)
    obtain ⟨m₀, h⟩ := exists_H_basicOpen_twist_eq_zero
      (((pushforward (pullback.lift π j w)).obj G).restrict (affineChart n y V.2))
    exact ⟨m₀, fun m hm g q x ↦
      H_twistAlong_eq_zero_of_affineChart y π j w V.2 G m g q (h m hm _ q) x⟩
  choose m₁ hm₁ using key
  obtain ⟨t, ht⟩ := (_root_.isCompact_univ (X := Y)).elim_finite_subcover
    (fun V : Y.affineOpens ↦ (V : Set Y))
    (fun V ↦ V.1.isOpen) fun x _ ↦ by
      have hx : x ∈ (⨆ V : Y.affineOpens, (V : Y.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨V, hV⟩
  refine ⟨∑ V ∈ t, |m₁ V|, fun m hm ↦ isPushforwardAcyclic_of_basicOpen π _ fun s ↦ ?_⟩
  obtain ⟨V, hVt, hsV⟩ : ∃ V ∈ t, s ∈ (V : Set Y) := by
    simpa using ht (Set.mem_univ s)
  exact ⟨V, V.2, hsV, fun g q x ↦ hm₁ V m ((le_abs_self _).trans
    ((Finset.single_le_sum (fun V _ ↦ abs_nonneg (m₁ V)) hVt).trans hm)) g q x⟩


-- @@ L177-177 verbatim
end AlgebraicGeometry.ProjectiveSpace
