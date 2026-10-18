/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.Modules.CocycleTwistPullbackModules
import Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkSurjective


-- @@ L9-25 verbatim
/-!
# Local properties of twists of sheaves of modules on locally ringed spaces

Let `Y` be a locally ringed space, `c` a cocycle on a family of opens `V` covering `Y`, and `N` a
sheaf of `𝒪_Y`-modules. On each `Vᵢ` the twist `N ⊗ L_c` (`LocallyRingedSpace.modTwist`) agrees
with `N`. We deduce:

- `LocallyRingedSpace.modTwistOverIso`: `(N ⊗ L_c).over Vᵢ ≅ N.over Vᵢ`;
- `LocallyRingedSpace.isCoherent_modTwist`: twisting preserves coherence;
- `LocallyRingedSpace.subsingleton_stalk_modTwist_iff`: `(N ⊗ L_c)_y = 0` iff `N_y = 0`.

Pullback of cocycles along a morphism to a scheme is multiplicative
(`LocallyRingedSpace.cocycleComap_mul`, `LocallyRingedSpace.cocycleComap_one`). We also define
multiplication by a global section of a twisted structure sheaf,
`LocallyRingedSpace.modTwistMulSection : N ⊗ L_c ⟶ N ⊗ L_{cd}`, `(sᵢ) ↦ (hᵢ sᵢ)`, for a family
`hᵢ ∈ Γ(Y, Vᵢ)` with `hᵢ = dᵢⱼ hⱼ`.
-/


-- @@ L27-27 verbatim
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

-- @@ L28-28 verbatim
open AlgebraicGeometry.Scheme.Modules


-- @@ L30-30 verbatim
universe u


-- @@ L32-32 verbatim
namespace AlgebraicGeometry.LocallyRingedSpace


-- @@ L34-36 verbatim
set_option hygiene false in
/-- Sections of the structure sheaf of `Y` over `W`. -/
local notation "Γᵧ(" W ")" => Y.presheaf.obj (op W)


-- @@ L38-40 verbatim
/-- Restriction of a section of a sheaf of modules, the inclusion being proved by `order`. -/
local macro:80 x:term:80 " |ₘ " W:term:81 : term =>
  `(modRes $x $W (by order))


-- @@ L42-42 verbatim
section Comap


-- @@ L44-48 verbatim
/-- Pullback of cocycles is multiplicative. -/
lemma cocycleComap_mul {Y : LocallyRingedSpace.{u}} {X : Scheme.{u}}
    (f : Y ⟶ X.toLocallyRingedSpace) {ι : Type} {U : ι → X.Opens} (c d : Cocycle U) :
    cocycleComap f (c * d) = cocycleComap f c * cocycleComap f d :=
  ModCocycle.ext fun _ _ ↦ pbSec_mul f _ _


-- @@ L50-54 verbatim
/-- The pullback of the trivial cocycle is trivial. -/
lemma cocycleComap_one {Y : LocallyRingedSpace.{u}} {X : Scheme.{u}}
    (f : Y ⟶ X.toLocallyRingedSpace) {ι : Type} {U : ι → X.Opens} :
    cocycleComap f (1 : Cocycle U) = 1 :=
  ModCocycle.ext fun _ _ ↦ pbSec_one f


-- @@ L56-56 verbatim
end Comap


-- @@ L58-58 verbatim
variable {Y : LocallyRingedSpace.{u}} {ι : Type} {V : ι → Opens Y.toPresheafedSpace}


-- @@ L60-60 verbatim
section MulSection


-- @@ L62-63 expanded
variable (N : SheafOfModules.{u} Y.ringSheaf) (c d : ModCocycle V) (h : ∀ i, Γᵧ(V i))
  (hh :
    ∀ i j,
      (TopCat.Presheaf.restrictOpen (h i) (V i ⊓ V j) (by order)) =
        d.g i j * (TopCat.Presheaf.restrictOpen (h j) (V i ⊓ V j) (by order)))


-- @@ L65-69 expanded
include hh in
lemma modMulSection_compat (i j : ι) (W : Opens Y.toPresheafedSpace) (hW : W ≤ V i ⊓ V j) :
    (TopCat.Presheaf.restrictOpen (h i) W (by order)) =
      (TopCat.Presheaf.restrictOpen (d.g i j) W (by order)) *
        (TopCat.Presheaf.restrictOpen (h j) W (by order)) :=
  by
  have := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen x W hW) (hh i j)
  simpa only [yres_mul, yres_res] using this


-- @@ L71-91 expanded
/-- **Multiplication by a global section of `L_d`**: a family `hᵢ ∈ Γ(Y, Vᵢ)` with
`hᵢ = dᵢⱼ hⱼ` on `Vᵢ ∩ Vⱼ` gives `N ⊗ L_c ⟶ N ⊗ L_{cd}`, `(sᵢ) ↦ (hᵢ sᵢ)`. -/
noncomputable def modTwistMulSection : modTwist N c ⟶ modTwist N (c * d) :=
  modHomMk
    (fun W ↦
      { toFun
          s :=
          modTwistMk
            (fun i ↦ (TopCat.Presheaf.restrictOpen (h i) (W ⊓ V i) (by order)) • modTwistComp s i)
            fun i j ↦
            by
            rw [modRes_smul, modRes_smul, modTwistComp_compat, yres_res, yres_res,
              modMulSection_compat d h hh i j _ (by order), smul_smul, smul_smul, ModCocycle.mul_g,
              yres_mul]
            congr 1
            ring
        map_zero' := by ext i; simp
        map_add' s t := by ext i; simp [smul_add] })
    (fun W r t ↦ by
      ext i
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, modTwistComp_modTwistMk, modTwistComp_smul]
      rw [smul_smul, smul_smul, mul_comm])
    (fun W W' hW t ↦ by
      ext i
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, modTwistComp_modTwistMk, modTwistComp_res,
        modRes_smul, yres_res])


-- @@ L93-98 expanded
@[simp]
lemma modTwistComp_modTwistMulSection_app {W : Opens Y.toPresheafedSpace}
    (s : (modTwist N c).val.obj (op W)) (i : ι) :
    modTwistComp ((modTwistMulSection N c d h hh).val.app (op W) s) i =
      (TopCat.Presheaf.restrictOpen (h i) (W ⊓ V i) (by order)) • modTwistComp s i :=
  rfl


-- @@ L100-106 verbatim
@[reassoc]
lemma modTwistMulSection_naturality {M : SheafOfModules.{u} Y.ringSheaf} (φ : N ⟶ M) :
    modTwistMap c φ ≫ modTwistMulSection M c d h hh =
      modTwistMulSection N c d h hh ≫ modTwistMap (c * d) φ :=
  modHom_ext fun W t ↦ by
    ext i
    simp


-- @@ L108-108 verbatim
end MulSection


-- @@ L110-110 verbatim
section Over


-- @@ L112-115 verbatim
variable {P Q : SheafOfModules.{u} Y.ringSheaf} (O : Opens Y.toPresheafedSpace)
  (e : ∀ W, W ≤ O → (P.val.obj (op W) ≃ₗ[Γᵧ(W)] Q.val.obj (op W)))
  (he : ∀ W W' (hW : W ≤ O) (h : W' ≤ W) (x : P.val.obj (op W)),
    e W' (h.trans hW) (modRes x W' h) = modRes (e W hW x) W' h)


-- @@ L117-122 verbatim
include he in
lemma overIsoOfLinearEquiv_symm_naturality (W W' : Opens Y.toPresheafedSpace) (hW : W ≤ O)
    (h : W' ≤ W) (y : Q.val.obj (op W)) :
    (e W' (h.trans hW)).symm (modRes y W' h) = modRes ((e W hW).symm y) W' h := by
  apply (e W' (h.trans hW)).injective
  rw [LinearEquiv.apply_symm_apply, he _ _ hW, LinearEquiv.apply_symm_apply]


-- @@ L124-146 verbatim
/-- An isomorphism `P.over O ≅ Q.over O` from linear equivalences `P(W) ≃ Q(W)`, `W ≤ O`,
compatible with restriction. -/
noncomputable def overIsoOfLinearEquiv : P.over O ≅ Q.over O where
  hom := ⟨PresheafOfModules.homMk
    { app Z := AddCommGrpCat.ofHom (e Z.unop.left (leOfHom Z.unop.hom)).toAddMonoidHom
      naturality Z Z' g := by
        ext x
        exact (he _ _ _ (leOfHom g.unop.left) x) }
    (fun Z r x ↦ (e Z.unop.left (leOfHom Z.unop.hom)).map_smul r x)⟩
  inv := ⟨PresheafOfModules.homMk
    { app Z := AddCommGrpCat.ofHom (e Z.unop.left (leOfHom Z.unop.hom)).symm.toAddMonoidHom
      naturality Z Z' g := by
        ext x
        exact overIsoOfLinearEquiv_symm_naturality O e he _ _ _ (leOfHom g.unop.left) x }
    (fun Z r x ↦ (e Z.unop.left (leOfHom Z.unop.hom)).symm.map_smul r x)⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    ext Z x
    exact (e Z.unop.left (leOfHom Z.unop.hom)).symm_apply_apply x
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    ext Z x
    exact (e Z.unop.left (leOfHom Z.unop.hom)).apply_symm_apply x


-- @@ L148-148 verbatim
end Over


-- @@ L150-150 verbatim
section Stalk


-- @@ L152-177 verbatim
/-- **Vanishing of a stalk in terms of sections**: `P_y = 0` if and only if every section of `P`
over an open `W ∋ y` inside a fixed neighbourhood `O` of `y` vanishes near `y`. -/
lemma subsingleton_stalk_iff (P : SheafOfModules.{u} Y.ringSheaf) {y : Y}
    {O : Opens Y.toPresheafedSpace} (hyO : y ∈ O) :
    Subsingleton ((Y.stalkFunctor y).obj P) ↔
      ∀ W, W ≤ O → y ∈ W → ∀ s : P.val.obj (op W),
        ∃ (W' : Opens Y.toPresheafedSpace) (h : W' ≤ W), y ∈ W' ∧ modRes s W' h = 0 := by
  constructor
  · intro hP W _ hy s
    have h0 : TopCat.Presheaf.germ P.val.presheaf W y hy s =
        TopCat.Presheaf.germ P.val.presheaf W y hy 0 :=
      @Subsingleton.elim ((Y.stalkFunctor y).obj P) hP _ _
    obtain ⟨W', hyW', i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq P.val.presheaf y hy hy s 0 h0
    refine ⟨W', i₁.le, hyW', ?_⟩
    refine (congrArg (fun g ↦ (P.val.presheaf.map g.op) s) (Subsingleton.elim _ i₁)).trans ?_
    exact heq.trans (map_zero _)
  · intro h
    have hzero : ∀ m : (Y.stalkFunctor y).obj P, m = 0 := by
      intro m
      obtain ⟨W, hyW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.val.presheaf m
      obtain ⟨W', hW', hyW', hs⟩ := h (W ⊓ O) inf_le_right ⟨hyW, hyO⟩ (modRes s (W ⊓ O) inf_le_left)
      rw [modRes_res] at hs
      rw [← TopCat.Presheaf.germ_res_apply P.val.presheaf (homOfLE (hW'.trans inf_le_left)) y
        hyW' s]
      exact (congrArg (TopCat.Presheaf.germ P.val.presheaf W' y hyW') hs).trans (map_zero _)
    exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩


-- @@ L179-182 verbatim
variable {P Q : SheafOfModules.{u} Y.ringSheaf} {O : Opens Y.toPresheafedSpace}
  (e : ∀ W, W ≤ O → (P.val.obj (op W) ≃ₗ[Γᵧ(W)] Q.val.obj (op W)))
  (he : ∀ W W' (hW : W ≤ O) (h : W' ≤ W) (x : P.val.obj (op W)),
    e W' (h.trans hW) (modRes x W' h) = modRes (e W hW x) W' h)


-- @@ L184-197 verbatim
include he in
/-- Sheaves with compatibly isomorphic sections near `y` have simultaneously vanishing stalks
at `y`. -/
lemma subsingleton_stalk_iff_of_linearEquiv {y : Y} (hyO : y ∈ O) :
    Subsingleton ((Y.stalkFunctor y).obj P) ↔ Subsingleton ((Y.stalkFunctor y).obj Q) := by
  rw [subsingleton_stalk_iff P hyO, subsingleton_stalk_iff Q hyO]
  refine forall_congr' fun W ↦ forall_congr' fun hW ↦ forall_congr' fun hy ↦ ?_
  refine ⟨fun hP t ↦ ?_, fun hQ s ↦ ?_⟩
  · obtain ⟨W', h, hyW', hs⟩ := hP ((e W hW).symm t)
    refine ⟨W', h, hyW', ?_⟩
    rw [← LinearEquiv.apply_symm_apply (e W hW) t, ← he _ _ hW h, hs, map_zero]
  · obtain ⟨W', h, hyW', ht⟩ := hQ (e W hW s)
    refine ⟨W', h, hyW', (e W' (h.trans hW)).injective ?_⟩
    rw [he _ _ hW h, ht, map_zero]


-- @@ L199-199 verbatim
end Stalk


-- @@ L201-201 verbatim
section Local


-- @@ L203-203 verbatim
variable (N : SheafOfModules.{u} Y.ringSheaf) (c : ModCocycle V)


-- @@ L205-208 verbatim
/-- **The twist is trivial on `Vᵢ`**: `(N ⊗ L_c).over Vᵢ ≅ N.over Vᵢ`. -/
noncomputable def modTwistOverIso (i : ι) : (modTwist N c).over (V i) ≅ N.over (V i) :=
  overIsoOfLinearEquiv (V i) (fun _ hW ↦ modTwistSectionsEquiv c i hW)
    (fun _ _ hW h x ↦ modTwistSectionsEquiv_res c i hW h x)


-- @@ L210-219 verbatim
/-- **Twisting preserves coherence**, for a cocycle on an open cover. -/
theorem isCoherent_modTwist (hV : ⨆ i, V i = ⊤) [N.IsCoherent] : (modTwist N c).IsCoherent := by
  haveI (i : ULift.{u} ι) : SheafOfModules.IsCoherent.{u, u, u} ((modTwist N c).over (V i.down)) :=
    haveI := SheafOfModules.IsCoherent.over N (V i.down)
    SheafOfModules.IsCoherent.of_iso.{u} (modTwistOverIso N c i.down).symm
  refine SheafOfModules.IsCoherent.of_coversTop (modTwist N c)
    (fun i : ULift.{u} ι ↦ V i.down) ((Opens.coversTop_iff _ _).2 ?_)
  rw [IsOpenCover, ← hV]
  exact le_antisymm (iSup_le fun i ↦ le_iSup V i.down)
    (iSup_le fun i ↦ le_iSup (fun i : ULift.{u} ι ↦ V i.down) ⟨i⟩)


-- @@ L221-227 verbatim
/-- **The twist has the same vanishing stalks**: for `y ∈ Vᵢ`, `(N ⊗ L_c)_y = 0` if and only if
`N_y = 0`. -/
lemma subsingleton_stalk_modTwist_iff {i : ι} {y : Y} (hy : y ∈ V i) :
    Subsingleton ((Y.stalkFunctor y).obj (modTwist N c)) ↔
      Subsingleton ((Y.stalkFunctor y).obj N) :=
  subsingleton_stalk_iff_of_linearEquiv (fun _ hW ↦ modTwistSectionsEquiv c i hW)
    (fun _ _ hW h x ↦ modTwistSectionsEquiv_res c i hW h x) hy


-- @@ L229-229 verbatim
end Local


-- @@ L231-231 verbatim
end AlgebraicGeometry.LocallyRingedSpace
