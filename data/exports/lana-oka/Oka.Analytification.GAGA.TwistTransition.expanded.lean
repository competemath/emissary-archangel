/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.ProjectiveSpaceAnFunctions
import Oka.AlgebraicGeometry.ProjectiveSpace.AwayEval
import Oka.AlgebraicGeometry.ProjectiveSpace.TwistSections
import Oka.Analytification.GAGA.SheafAnalytification


-- @@ L11-23 verbatim
/-!
# Values of pulled back sections on `ℙⁿ_an`; the transition functions of `𝒪(k)^an`

For a scheme `X` locally of finite type over `ℂ`, the comparison morphism `π : X^an ⟶ X` is
`ℂ`-linear (`ComplexAnalytic.comapAlgMap_analytificationπ_schemeConst`), and the stalk maps of `π`
are local; hence the value at `y` of `π^♯ a` is `c` as soon as `a - c` is not a unit at `π y`
(`ComplexAnalytic.eval_analytificationπ_eq`).

On `ℙⁿ_an` this computes the values of the pulled back sections `awayToSection a` of `𝒪_{ℙⁿ}` over
`D₊(Xᵢ)` at the point `[v]`: they are `a(v)` (`projectiveSpaceAn.eval_π_awayToSection`). In
particular `π^♯ (Xⱼ / Xᵢ)` has value `vⱼ / vᵢ` at `[v]`, and the pulled back transition functions
`(Xⱼ / Xᵢ)ᵏ` of `𝒪(k)` have value `(vⱼ / vᵢ)ᵏ` (`projectiveSpaceAn.evπ_cocycle_zpow`).
-/


-- @@ L25-25 verbatim
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace


-- @@ L27-27 verbatim
universe u


-- @@ L29-29 verbatim
namespace ComplexAnalytic


-- @@ L31-31 verbatim
open AnalyticSpace


-- @@ L33-41 verbatim
/-- The value at `z` of a pulled back section vanishes iff the germ at `g z` is not a unit. -/
lemma eval_c_app_eq_zero_iff {Z : AnalyticSpace.{u}} {T : LocallyRingedSpace.{u}}
    (g : Z.toLocallyRingedSpace ⟶ T) {V : Opens T} (z : Z) (hz : g.base z ∈ V)
    (a : T.presheaf.obj (op V)) :
    Z.eval z (show z ∈ (Opens.map g.base).obj V from hz) (g.c.app (op V) a) = 0 ↔
      ¬ IsUnit (T.presheaf.germ V (g.base z) hz a) := by
  haveI : IsLocalHom (g.stalkMap z).hom := g.prop z
  rw [AnalyticSpace.eval_apply, ← LocallyRingedSpace.stalkMap_germ_apply g V z hz a, ← not_ne_iff,
    AnalyticSpace.evalStalk_ne_zero_iff_isUnit, isUnit_map_iff]


-- @@ L43-47 verbatim
/-- The constants of a scheme `X` locally of finite type over `ℂ`: the pullback of
`ULift ℂ = Γ(Spec ℂ)` along the structure morphism. -/
noncomputable def schemeConst (X : SchemeLFTℂ.{u}) :
    ULift.{u} ℂ →+* X.obj.left.presheaf.obj (op ⊤) :=
  LocallyRingedSpace.comapAlgMap X.obj.hom.toLRSHom (toSpecΓ (CommRingCat.of (ULift.{u} ℂ))).hom


-- @@ L49-57 verbatim
/-- **The comparison morphism `X^an ⟶ X` is `ℂ`-linear**: it pulls the constants of `X` back to
the constants of `X^an`. -/
lemma comapAlgMap_analytificationπ_schemeConst (X : SchemeLFTℂ.{u}) :
    LocallyRingedSpace.comapAlgMap (analytificationπLRS X) (schemeConst X) =
      uliftAlgMap (analytification.obj X).algebraMap := by
  apply LocallyRingedSpace.toSpecOfAlgMap_injective
  rw [schemeConst, ← LocallyRingedSpace.comapAlgMap_comp]
  exact (LocallyRingedSpace.toSpecOfAlgMap_comapAlgMap
    (analytificationπLRS X ≫ X.obj.hom.toLRSHom)).trans (analytificationπ X).w



-- @@ L60-85 verbatim
/-- **Values of pulled back sections**: if `a` differs near `π y` from the constant `c` by a
non-unit germ, then the value of `π^♯ a` at `y` is `c`. -/
lemma eval_analytificationπ_eq {X : SchemeLFTℂ.{u}} {V : X.obj.left.Opens}
    (a : X.obj.left.presheaf.obj (op V)) (y : analytification.obj X)
    (hy : (analytificationπLRS X).base y ∈ V) (c : ℂ)
    (h : ¬ IsUnit (X.obj.left.presheaf.germ V _ hy
      (a - TopCat.Presheaf.restrictOpen (schemeConst X (ULift.up c)) V le_top))) :
    (analytification.obj X).eval y (show y ∈ (Opens.map (analytificationπLRS X).base).obj V
      from hy) ((analytificationπLRS X).c.app (op V) a) = c := by
  have h0 := (eval_c_app_eq_zero_iff (analytificationπLRS X) y hy _).2 h
  rw [map_sub] at h0
  have h1 := sub_eq_zero.1 ((map_sub ((analytification.obj X).eval y (show y ∈
    (Opens.map (analytificationπLRS X).base).obj V from hy)) _ _).symm.trans h0)
  rw [h1]
  have hc := congrArg (fun γ ↦ γ (ULift.up c)) (comapAlgMap_analytificationπ_schemeConst X)
  simp only [LocallyRingedSpace.comapAlgMap, RingHom.coe_comp, Function.comp_apply] at hc
  have key : (analytificationπLRS X).c.app (op V)
      (TopCat.Presheaf.restrictOpen (schemeConst X (ULift.up c)) V le_top) =
      TopCat.Presheaf.restrictOpen (F := (analytification.obj X).presheaf)
        ((analytificationπLRS X).c.app (op ⊤)
        (schemeConst X (ULift.up c))) ((Opens.map (analytificationπLRS X).base).obj V) le_top :=
    congr($((analytificationπLRS X).c.naturality (homOfLE (le_top : V ≤ ⊤)).op).hom
      (schemeConst X (ULift.up c)))
  rw [key, AnalyticSpace.eval_restrictOpen]
  refine (congrArg _ hc).trans ?_
  exact AnalyticSpace.eval_algebraMap _ y c



-- @@ L88-88 verbatim
end ComplexAnalytic



-- @@ L91-91 verbatim
namespace ComplexAnalytic.projectiveSpaceAn


-- @@ L93-93 verbatim
open AlgebraicGeometry.ProjectiveSpace HomogeneousLocalization MvPolynomial

-- @@ L94-94 verbatim
open AlgebraicGeometry.Scheme.Modules


-- @@ L96-96 verbatim
variable {n : ℕ}


-- @@ L98-100 verbatim
set_option hygiene false in
set_option quotPrecheck false in
local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℂ)


-- @@ L102-104 verbatim
lemma eval₂_φ_X (v : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    eval₂ φ.{u} v (X i) = v i :=
  eval₂_X _ _ _


-- @@ L106-111 verbatim
/-- The comparison morphism at the point `[v]` of the chart `i`. -/
lemma π_pointOfVec (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (i : Fin (n + 1)) (hi : v i ≠ 0) :
    π n (pointOfVec.{u} v hv) =
      (Proj.awayι 𝒜 (X i) (X_mem_homogeneousSubmodule_one i) Nat.one_pos).base
        (awayPoint (φ := φ.{u}) v (X i) (by rwa [eval₂_φ_X])) := by
  rw [pointOfVec_eq _ _ i hi, π_chart, toFin_ofFin, chart_base_evalPoint]


-- @@ L113-116 verbatim
lemma π_pointOfVec_mem_U (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (i : Fin (n + 1)) (hi : v i ≠ 0) :
    π n (pointOfVec.{u} v hv) ∈ U n (ULift.{u} ℂ) i := by
  rw [← SetLike.mem_coe, ← Set.mem_preimage, ← range_chart, mem_range_chart_pointOfVec_iff]
  exact hi


-- @@ L118-142 expanded
/-- **Values of the pulled-back sections `awayToSection a` of `𝒪_{ℙⁿ}` over `D₊(Xᵢ)`**: the value
of `π^♯ a` at `[v]` is `a(v)`. -/
theorem eval_π_awayToSection (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (i : Fin (n + 1)) (hi : v i ≠ 0)
    (a : Away 𝒜 (X i)) :
    (projectiveSpaceAn.{u} n).eval (pointOfVec.{u} v hv) (π_pointOfVec_mem_U v hv i hi)
        ((analytificationπLRS (projectiveSpace.{u} n)).c.app (op (U n _ i))
          (Proj.awayToSection 𝒜 (X i) a)) =
      awayEval (φ := φ.{u}) v (X i) (by rwa [eval₂_φ_X]) a :=
  by
  refine
    eval_analytificationπ_eq (X := projectiveSpace.{u} n) (V := U n _ i) _ _
      (π_pointOfVec_mem_U v hv i hi) _ ?_
  have hi' : eval₂ φ.{u} v (X i) ≠ 0 := by rwa [eval₂_φ_X]
  set c := awayEval (φ := φ.{u}) v (X i) hi' a
  have hconst :
    TopCat.Presheaf.restrictOpen (schemeConst (projectiveSpace.{u} n) (ULift.up c)) (U n _ i)
        le_top =
      Proj.awayToSection 𝒜 (X i) (awayXBase _ i (ULift.up c)) :=
    restrict_toSpec_appTop (X_mem_homogeneousSubmodule_one i) Nat.one_pos (ULift.up c)
  intro hu
  have hmem :
    π n (pointOfVec.{u} v hv) ∈
      (ProjectiveSpace n (ULift.{u} ℂ)).basicOpen
        (Proj.awayToSection 𝒜 (X i) (a - awayXBase _ i (ULift.up c))) :=
    by
    have := (Scheme.mem_basicOpen (ProjectiveSpace n (ULift.{u} ℂ)) _ _ _).2 hu
    rw [hconst] at this
    rw [map_sub]
    exact this
  rw [π_pointOfVec v hv i hi, awayι_awayPoint_mem_basicOpen_iff, map_sub,
    awayEval_awayXBase] at hmem
  exact hmem (sub_self _)


-- @@ L145-151 expanded
/-- Evaluation at `[v]` of the pullback to `ℙⁿ_an` of a section of `𝒪_{ℙⁿ}`. -/
noncomputable def evπ {W : (ProjectiveSpace n (ULift.{u} ℂ)).Opens} (v : Fin (n + 1) → ℂ)
    (hv : v ≠ 0) (hW : π n (pointOfVec.{u} v hv) ∈ W) :
    (ProjectiveSpace n (ULift.{u} ℂ)).presheaf.obj (op W) →+* ℂ :=
  ((projectiveSpaceAn.{u} n).eval (U :=
        (Opens.map (analytificationπLRS (projectiveSpace.{u} n)).base).obj W) (pointOfVec.{u} v hv)
        hW).comp
    ((analytificationπLRS (projectiveSpace.{u} n)).c.app (op W)).hom


-- @@ L153-165 unexpanded
lemma evπ_restrictOpen {W W' : ℙ(n; ULift.{u} ℂ).Opens} (h : W' ≤ W) (v : Fin (n + 1) → ℂ)
    (hv : v ≠ 0) (hW' : π n (pointOfVec.{u} v hv) ∈ W')
    (x : ℙ(n; ULift.{u} ℂ).presheaf.obj (op W)) :
    evπ.{u} v hv hW' (TopCat.Presheaf.restrictOpen x W' h) = evπ v hv (h hW') x := by
  have key : (analytificationπLRS (projectiveSpace.{u} n)).c.app (op W')
      (TopCat.Presheaf.restrictOpen x W' h) =
      TopCat.Presheaf.restrictOpen (F := (projectiveSpaceAn.{u} n).presheaf)
        ((analytificationπLRS (projectiveSpace.{u} n)).c.app (op W) x)
        ((Opens.map (analytificationπLRS (projectiveSpace.{u} n)).base).obj W')
        ((Opens.map (analytificationπLRS (projectiveSpace.{u} n)).base).monotone h) :=
    congr($((analytificationπLRS (projectiveSpace.{u} n)).c.naturality (homOfLE h).op).hom x)
  simp only [evπ, RingHom.coe_comp, Function.comp_apply]
  exact (congrArg _ key).trans (AnalyticSpace.eval_restrictOpen _ _ _ _ _)


-- @@ L167-170 verbatim
lemma evπ_xDiv (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (i j : Fin (n + 1)) (hi : v i ≠ 0) :
    evπ.{u} v hv (π_pointOfVec_mem_U v hv i hi) (xDiv i j) = v j / v i := by
  refine (eval_π_awayToSection v hv i hi (awayXDiv _ i j)).trans ?_
  exact awayEval_awayXDiv (φ := φ.{u}) v i j _


-- @@ L172-186 expanded
/-- **The transition functions of `𝒪(k)^an`**: the value at `[v]` of the pullback of the
cocycle `(Xⱼ / Xᵢ)ᵏ` is `(vⱼ / vᵢ)ᵏ`. -/
lemma evπ_cocycle_zpow (k : ℤ) (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (i j : Fin (n + 1)) (hi : v i ≠ 0)
    (hW : π n (pointOfVec.{u} v hv) ∈ U n _ i ⊓ U n _ j) :
    evπ.{u} v hv hW ((cocycle n (ULift.{u} ℂ) ^ k).g i j) = (v j / v i) ^ k :=
  by
  have hg := cocycle_zpow_g_res (R := ULift.{u} ℂ) k i j (U n _ i ⊓ U n _ j) le_rfl
  rw [ores_self] at hg
  rw [hg]
  set u := xDivUnit (R := ULift.{u} ℂ) i j (U n _ i ⊓ U n _ j) le_rfl
  refine (Units.coe_map (evπ v hv hW).toMonoidHom (u ^ k)).symm.trans ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
  congr 1
  change evπ v hv hW (TopCat.Presheaf.restrictOpen (xDiv i j) (U n _ i ⊓ U n _ j) (by order)) = _
  rw [evπ_restrictOpen]
  exact evπ_xDiv v hv i j hi


-- @@ L188-188 verbatim
end ComplexAnalytic.projectiveSpaceAn
