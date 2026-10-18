/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.ProjectiveLineCoherentGenerators
import Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Stability


-- @@ L9-22 verbatim
/-!
# Direct images of coherent sheaves under `U × ℙ¹ → U`

Let `𝒢` be a coherent sheaf on `U × ℙ¹ ⊆ P^an`, `K ⊆ U` a nonempty closed box and `σᵢ` finitely
many sections of `𝒢` over `B × ℙ¹`, `K ⊆ B`, generating `𝒢` locally. We show that for `e ≫ 0`
the map `𝒪(e)^I → 𝒢(e)` given by the `σᵢ` is surjective on sections over `V × ℙ¹`, `V` an open
box near `K`, i.e. `π_* 𝒪(e)^I → π_* 𝒢(e)` is surjective over `V`
(`ComplexAnalytic.relProjectiveLine.exists_surjective_twistMod_extendFreeMap`).

The kernel `𝒦` of `𝒪^I → 𝒢` (after extending `𝒢|_{B × ℙ¹}` to `P^an` by
`LocallyRingedSpace.extendMod`) is coherent over `B × ℙ¹`, so `H¹(V × ℙ¹, 𝒦(e)) = 0` for `e ≫ 0`
(`ComplexAnalytic.relProjectiveLine.exists_H_tube_twistMod_eq_zero`), and the long exact
cohomology sequence of `0 → 𝒦(e) → 𝒪(e)^I → 𝒢(e) → 0` over `V × ℙ¹` gives the surjectivity.
-/


-- @@ L24-24 verbatim
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

-- @@ L25-25 verbatim
open AlgebraicGeometry.LocallyRingedSpace


-- @@ L27-27 verbatim
universe u


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace AlgebraicGeometry.LocallyRingedSpace


-- @@ L33-33 verbatim
variable {Y : LocallyRingedSpace.{u}}


-- @@ L35-39 verbatim
/-- The sheaf `W ↦ M(W ∩ O)`, which agrees with `M` on `O`: the twist of `M` by the trivial
cocycle on the one-element family `O`. -/
abbrev extendMod (M : SheafOfModules.{u} Y.ringSheaf) (O : Opens Y.toPresheafedSpace) :
    SheafOfModules.{u} Y.ringSheaf :=
  modTwist M (1 : ModCocycle fun _ : Unit ↦ O)


-- @@ L41-41 verbatim
variable {M : SheafOfModules.{u} Y.ringSheaf} {O : Opens Y.toPresheafedSpace}


-- @@ L43-46 verbatim
/-- A section of `M` over `O` as a global section of `extendMod M O`. -/
def extendSection (s : M.val.obj (op O)) : (extendMod M O).val.obj (op ⊤) :=
  modTwistMk (fun _ ↦ modRes s (⊤ ⊓ O) inf_le_right) fun i j ↦ by
    simp only [modRes_res, ModCocycle.one_g, yres_one, one_smul]


-- @@ L48-52 verbatim
lemma extendSection_restrict (s : M.val.obj (op O)) {W : Opens Y.toPresheafedSpace} (hW : W ≤ O) :
    modTwistSectionsEquiv (1 : ModCocycle fun _ : Unit ↦ O) () hW
      (modRes (extendSection s) W le_top) = modRes s W hW := by
  rw [modTwistSectionsEquiv_apply, modTwistComp_res, extendSection, modTwistComp_modTwistMk,
    modRes_res, modRes_res]


-- @@ L54-60 verbatim
/-- `extendMod M O` is coherent on `O` if `M` is. -/
lemma isCoherent_restrictModules_extendMod
    (hM : ((Y.restrictModules O).obj M).IsCoherent) :
    ((Y.restrictModules O).obj (extendMod M O)).IsCoherent := by
  rw [← isCoherent_over_iff_isCoherent_restrictModules] at hM ⊢
  exact @SheafOfModules.IsCoherent.of_iso.{u} _ _ _ _ _ _ _ _ _ _
    (modTwistOverIso M (1 : ModCocycle fun _ : Unit ↦ O) ()).symm hM


-- @@ L62-62 verbatim
section FreeMap


-- @@ L64-64 verbatim
variable {I : Type u} [Fintype I] (σ : I → M.val.obj (op O))


-- @@ L66-68 verbatim
/-- The morphism `𝒪^I ⟶ extendMod M O` given by sections `σ` of `M` over `O`. -/
def extendFreeMap : SheafOfModules.free I ⟶ extendMod M O :=
  freeMkTop (extendMod M O) fun i ↦ extendSection (σ i)


-- @@ L70-80 verbatim
lemma extendFreeMap_app [DecidableEq I] {W : Opens Y.toPresheafedSpace} (hW : W ≤ O)
    (f : (SheafOfModules.free (R := Y.ringSheaf) I).val.obj (op W)) :
    modTwistSectionsEquiv (1 : ModCocycle fun _ : Unit ↦ O) () hW
      ((extendFreeMap σ).val.app (op W) f) =
      ∑ i, SheafOfModules.freeEval (op W) f i • modRes (σ i) W hW := by
  rw [SheafOfModules.val_app_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_freeHomEquiv_eq_map, extendFreeMap, generatorSection_freeMkTop]
  exact ((modTwistSectionsEquiv (1 : ModCocycle fun _ : Unit ↦ O) () hW).map_smul
    (show Y.presheaf.obj (op W) from SheafOfModules.freeEval (op W) f i) _).trans
    (congrArg (_ • ·) (extendSection_restrict (σ i) hW))


-- @@ L82-82 verbatim
variable {σ}


-- @@ L84-99 verbatim
/-- If the `σᵢ` generate `M` locally on `O`, then `𝒪^I ⟶ extendMod M O` is locally surjective
on `O`. -/
lemma exists_extendFreeMap_eq (hσ : ComplexAnalytic.GeneratesLocally σ)
    {W : Opens Y.toPresheafedSpace} (hW : W ≤ O) (t : (extendMod M O).val.obj (op W)) {y : Y}
    (hy : y ∈ W) :
    ∃ (W' : Opens Y.toPresheafedSpace) (h : W' ≤ W), y ∈ W' ∧
      ∃ f : (SheafOfModules.free (R := Y.ringSheaf) I).val.obj (op W'),
        (extendFreeMap σ).val.app (op W') f = modRes t W' h := by
  classical
  obtain ⟨W', h, hy', c, hc⟩ := hσ W hW
    (modTwistSectionsEquiv (1 : ModCocycle fun _ : Unit ↦ O) () hW t) y hy
  refine ⟨W', h, hy', SheafOfModules.freeEvalSymm (op W') c, ?_⟩
  apply (modTwistSectionsEquiv (1 : ModCocycle fun _ : Unit ↦ O) () (h.trans hW)).injective
  rw [extendFreeMap_app, SheafOfModules.freeEval_freeEvalSymm,
    modTwistSectionsEquiv_res _ () hW h t, hc]
  rfl


-- @@ L101-101 verbatim
end FreeMap


-- @@ L103-114 verbatim
/-- If `0 → M₁ → M₂ → M₃` is exact, `M₂ → M₃` is an epimorphism of sheaves on `W` and
`H¹(W, M₁) = 0`, then `M₂(W) → M₃(W)` is surjective. -/
lemma surjective_app_of_exact_of_H_one {S : ShortComplex (SheafOfModules.{u} Y.ringSheaf)}
    (hS : S.Exact) [Mono S.f] (W : Opens Y.toPresheafedSpace)
    (hepi : Epi ((TopCat.Sheaf.restrictOpen W).map ((modulesToAb Y).map S.g)))
    (hH : ∀ x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj S.X₁.toAb) 1, x = 0) :
    Function.Surjective (S.g.val.app (op W)) := by
  let F := modulesToAb Y ⋙ TopCat.Sheaf.restrictOpen W
  have hT : (S.map F).ShortExact :=
    { exact := hS.map F, mono_f := F.map_mono S.f, epi_g := hepi }
  exact (TopCat.Sheaf.surjective_restrictOpen_map_app_top_iff _ _).1
    (TopCat.Sheaf.surjective_of_H_one hT hH)


-- @@ L116-116 verbatim
end AlgebraicGeometry.LocallyRingedSpace


-- @@ L118-118 verbatim
namespace TopCat.Sheaf


-- @@ L120-148 verbatim
/-- A morphism of abelian sheaves which is locally surjective over the opens inside `U` restricts
to an epimorphism on `U`. -/
lemma epi_restrictOpen_map_of_locally {X : TopCat.{u}} {F G : AbSheaf X} (φ : F ⟶ G)
    (U : Opens X)
    (h : ∀ (W : Opens X), W ≤ U → ∀ (t : G.obj.obj (op W)) (x : X), x ∈ W →
      ∃ (W' : Opens X) (hW' : W' ≤ W), x ∈ W' ∧ ∃ s : F.obj.obj (op W'),
        φ.hom.app (op W') s = G.obj.map (homOfLE hW').op t) :
    Epi ((restrictOpen U).map φ) := by
  rw [← Sheaf.isLocallySurjective_iff_epi_addCommGrp]
  refine (TopCat.Presheaf.isLocallySurjective_iff _).2 fun V t x hx ↦ ?_
  have hVU : U.isOpenEmbedding.isOpenMap.functor.obj V ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨W', hW', hxW', s, hs⟩ := h _ hVU t x.1 ⟨x, hx, rfl⟩
  let V' : Opens ((Opens.toTopCat X).obj U) := (Opens.map U.inclusion').obj W'
  have hV'V : V' ≤ V := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hW' hy
    rwa [← U.isOpenEmbedding.injective hzy]
  have hV'W : U.isOpenEmbedding.isOpenMap.functor.obj V' = W' := by
    ext y
    refine ⟨?_, fun hy ↦ ⟨⟨y, hVU (hW' hy)⟩, hy, rfl⟩⟩
    rintro ⟨z, hz, rfl⟩
    exact hz
  refine ⟨V', hV'V, ⟨F.obj.map (homOfLE hV'W.le).op s, ?_⟩, hxW'⟩
  change φ.hom.app _ (F.obj.map _ s) = G.obj.map _ t
  rw [← ConcreteCategory.comp_apply, φ.hom.naturality, ConcreteCategory.comp_apply, hs,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl


-- @@ L150-150 verbatim
end TopCat.Sheaf


-- @@ L152-152 verbatim
namespace ComplexAnalytic.relProjectiveLine


-- @@ L154-154 verbatim
open relProjectiveSpaceAn


-- @@ L156-156 verbatim
variable {m : ℕ}


-- @@ L158-160 verbatim
set_option hygiene false in
/-- Sections of `𝒪` over an open of `P^an`. -/
local notation "Γₚ(" W ")" => (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)


-- @@ L162-162 verbatim
variable (ℋ : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.ringSheaf)


-- @@ L164-168 verbatim
lemma exists_stdOpen_mem (x : relProjectiveSpaceAn.{u} m 1) :
    ∃ i : Fin 2, x ∈ stdOpen.{u} m 1 i := by
  have : x ∈ (⊤ : (relProjectiveSpaceAn.{u} m 1).Opens) := trivial
  rw [← iSup_stdOpen] at this
  exact Opens.mem_iSup.1 this


-- @@ L170-190 verbatim
/-- The twisted morphism `𝒪(e)^I ⟶ (extendMod ℋ O)(e)` is locally surjective on `O`, if the
`σᵢ` generate `ℋ` locally on `O`. -/
lemma exists_twistMod_extendFreeMap_eq {O : (relProjectiveSpaceAn.{u} m 1).Opens} {I : Type u}
    [Fintype I] {σ : I → ℋ.val.obj (op O)} (hσ : GeneratesLocally σ) (e : ℤ)
    {W : (relProjectiveSpaceAn.{u} m 1).Opens} (hW : W ≤ O)
    (t : (twistMod (extendMod ℋ O) e).val.obj (op W)) {x : relProjectiveSpaceAn.{u} m 1}
    (hx : x ∈ W) :
    ∃ (W' : (relProjectiveSpaceAn.{u} m 1).Opens) (h : W' ≤ W), x ∈ W' ∧
      ∃ f : (twistMod (SheafOfModules.free I) e).val.obj (op W'),
        ((twistModFunctor m 1 e).map (extendFreeMap σ)).val.app (op W') f = modRes t W' h := by
  obtain ⟨j, hj⟩ := exists_stdOpen_mem x
  have hW₁ : W ⊓ stdOpen.{u} m 1 j ≤ stdOpen.{u} m 1 j := inf_le_right
  obtain ⟨W₂, h₂, hx₂, f, hf⟩ := exists_extendFreeMap_eq hσ (inf_le_left.trans hW)
    (modTwistSectionsEquiv (twistModCocycle.{u} m 1 e) j hW₁ (modRes t _ inf_le_left)) ⟨hx, hj⟩
  refine ⟨W₂, h₂.trans inf_le_left, hx₂,
    (modTwistSectionsEquiv (twistModCocycle.{u} m 1 e) j (h₂.trans hW₁)).symm f, ?_⟩
  apply (modTwistSectionsEquiv (twistModCocycle.{u} m 1 e) j (h₂.trans hW₁)).injective
  rw [modTwistFunctor_map]
  erw [modTwistSectionsEquiv_modTwistMap (twistModCocycle.{u} m 1 e) j (h₂.trans hW₁)
    (extendFreeMap σ)]
  rw [LinearEquiv.apply_symm_apply, hf, ← modTwistSectionsEquiv_res _ j hW₁ h₂, modRes_res]


-- @@ L192-201 verbatim
/-- The twisted morphism `𝒪(e)^I ⟶ (extendMod ℋ O)(e)` restricts to an epimorphism of abelian
sheaves on every open `W ⊆ O`. -/
lemma epi_restrictOpen_twistMod_extendFreeMap {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    {I : Type u} [Fintype I] {σ : I → ℋ.val.obj (op O)} (hσ : GeneratesLocally σ) (e : ℤ)
    {W : (relProjectiveSpaceAn.{u} m 1).Opens} (hW : W ≤ O) :
    Epi ((TopCat.Sheaf.restrictOpen W).map
      ((modulesToAb (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace).map
        ((twistModFunctor m 1 e).map (extendFreeMap σ)))) :=
  TopCat.Sheaf.epi_restrictOpen_map_of_locally _ _ fun _ hW' t _ hx ↦
    exists_twistMod_extendFreeMap_eq ℋ hσ e (hW'.trans hW) t hx


-- @@ L203-222 verbatim
/-- The kernel of `𝒪^I ⟶ extendMod ℋ O` is coherent over `O` if `ℋ` is. -/
lemma isCoherent_restrictModules_kernel_extendFreeMap {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (hℋ : (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules O).obj
      ℋ).IsCoherent) {I : Type u} [Finite I] (σ : I → ℋ.val.obj (op O)) :
    (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules O).obj
      (kernel (extendFreeMap σ))).IsCoherent := by
  haveI := Fintype.ofFinite I
  set X := (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace
  haveI : (SheafOfModules.unit X.ringSheaf).IsCoherent :=
    isCoherentStructureSheaf_of_hasLocalRelations (AnalyticSpace.hasLocalRelations _)
  haveI : (SheafOfModules.free (R := X.ringSheaf) I).IsCoherent :=
    SheafOfModules.IsCoherent.free I
  haveI : PreservesFiniteLimits (X.restrictModules O) :=
    (X.ofRestrict O.isOpenEmbedding).preservesFiniteLimits_pullbackModules
      (flat_stalkMap_of_isIso _)
  haveI := isCoherent_restrictModules (SheafOfModules.free (R := X.ringSheaf) I) O
  haveI := isCoherent_restrictModules_extendMod hℋ
  haveI := SheafOfModules.IsCoherent.kernel ((X.restrictModules O).map (extendFreeMap σ))
  exact @SheafOfModules.IsCoherent.of_iso.{u} _ _ _ _ _ _ _ _ _ _
    (PreservesKernel.iso _ (extendFreeMap σ)).symm this


-- @@ L224-251 verbatim
/-- **Surjectivity of `π_* 𝒪(e)^I → π_* ℋ(e)` for `e ≫ 0`.** Let `ℋ` be coherent over `B × ℙ¹`
and `σᵢ` finitely many sections of `ℋ` over `B × ℙ¹` generating `ℋ` locally, and let `K ⊆ B` be a
nonempty closed box. There are an open box `B'` with `K ⊆ B' ⊆ B` and `e₀` such that for all
`e ≥ e₀` and all open boxes `V ⊆ B'`, the map `𝒪(e)^I → (extendMod ℋ (B × ℙ¹))(e)` given by the
`σᵢ` is surjective on sections over `V × ℙ¹`. -/
theorem exists_surjective_twistMod_extendFreeMap {B : Opens (Fin m → ℂ)}
    (hℋ : (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) B)).obj ℋ).IsCoherent)
    {a b : Fin m → ℂ} (hKB : Complex.closedBox a b ⊆ B) (hne : (Complex.closedBox a b).Nonempty)
    {I : Type u} [Fintype I] {σ : I → ℋ.val.obj (op (tube.{u} (N := 1) B))}
    (hσ : GeneratesLocally σ) :
    ∃ a' b' : Fin m → ℂ, Complex.closedBox a b ⊆ Complex.openBox a' b' ∧
      Complex.openBox a' b' ⊆ B ∧ ∃ e₀ : ℤ, ∀ e : ℤ, e₀ ≤ e → ∀ a'' b'' : Fin m → ℂ,
        Complex.openBox a'' b'' ⊆ Complex.openBox a' b' →
        Function.Surjective (((twistModFunctor m 1 e).map (extendFreeMap σ)).val.app
          (op (tube.{u} (N := 1) (boxOpens a'' b'')))) := by
  have h𝒦 := isCoherent_restrictModules_kernel_extendFreeMap ℋ hℋ σ
  obtain ⟨a', b', hab', hB'B, e₀, he₀⟩ := exists_H_tube_twistMod_eq_zero _ h𝒦 hKB hne
  refine ⟨a', b', hab', hB'B, e₀, fun e he a'' b'' hV ↦ ?_⟩
  have hVB : tube.{u} (N := 1) (boxOpens a'' b'') ≤ tube.{u} (N := 1) B :=
    fun y hy ↦ hB'B (hV hy)
  let S := ShortComplex.mk (kernel.ι (extendFreeMap σ)) (extendFreeMap σ)
    (kernel.condition (extendFreeMap σ))
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  haveI : Mono S.f := inferInstanceAs (Mono (kernel.ι _))
  haveI : Mono (S.map (twistModFunctor m 1 e)).f := (twistModFunctor m 1 e).map_mono S.f
  exact surjective_app_of_exact_of_H_one (hS.map (twistModFunctor m 1 e)) _
    (epi_restrictOpen_twistMod_extendFreeMap ℋ hσ e hVB) (he₀ e he a'' b'' hV 0)


-- @@ L253-253 verbatim
end ComplexAnalytic.relProjectiveLine


-- @@ L255-255 verbatim
end
