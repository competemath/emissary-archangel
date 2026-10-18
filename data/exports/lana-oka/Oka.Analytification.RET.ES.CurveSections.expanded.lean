/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.CurveExtension
import Oka.Analytification.GAGA.AnalytificationStalkSections
import Oka.Analytification.GAGA.TwistTransition
import Oka.Analytification.GAGA.ProjectiveGAGA3
import Oka.AlgebraicGeometry.ProjectiveSpace.TheoremA


-- @@ L12-28 verbatim
/-!
# Sections of an algebraisation of the canonical extension over `U₀`

Keep the notation of `Oka/Analytification/RET/ES/CurveExtension.lean`: `ρ₀ : W ⟶ ℂ¹`,
`ρ : W ⟶ ℙ¹_an` its composite with the chart `0` and `𝒞̄` the sheaf of sections of `ρ_* 𝒪_W`
bounded near `∞`. Let `F` be a coherent sheaf on `ℙ¹` with an isomorphism `e : F^an ≅ 𝒞̄`. A
section `m` of `F` over `U₀ = D₊(X₀)` gives the function `e(m^an)` on `W`
(`ComplexAnalytic.ProjectiveLine.sectionFun`). We show that these are exactly the functions of
polynomial growth in the coordinate `z` (`ComplexAnalytic.ProjectiveLine.HasPolyGrowth`):

- `ComplexAnalytic.ProjectiveLine.hasPolyGrowth_sectionFun`: some `(X₀ / X₁)ᵏ m` extends to a
  section of `F` over `U₁`, whose image in `𝒞̄` is bounded near `∞`;
- `ComplexAnalytic.ProjectiveLine.exists_sectionFun_eq`: a function `f` with `‖f‖ ≤ C ‖z‖ᵏ` near
  `∞` gives a morphism `𝒪(-k)^an ⟶ 𝒞̄`, `t ↦ t₀ f` (`ComplexAnalytic.ProjectiveLine.psi`); by
  GAGA-2 it is the analytification of a morphism `𝒪(-k) ⟶ F`, and the image of the frame of
  `𝒪(-k)` over `U₀` is a section of `F` mapping to `f`.
-/


-- @@ L30-30 verbatim
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology Filter


-- @@ L32-32 verbatim
universe u


-- @@ L34-34 verbatim
namespace ComplexAnalytic.ProjectiveLine


-- @@ L36-36 verbatim
open AnalyticSpace projectiveSpaceAn LocallyRingedSpace AlgebraicGeometry.ProjectiveSpace

-- @@ L37-37 verbatim
open AlgebraicGeometry.Scheme.Modules


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
variable {W : AnalyticSpace.{u}} (ρ₀ : W ⟶ AnalyticSpace.complexAffineSpace.{u} 1)


-- @@ L43-46 verbatim
/-- The comparison morphism `ℙ¹_an ⟶ ℙ¹`. -/
abbrev πP : (projectiveSpaceAn.{u} 1).toLocallyRingedSpace ⟶
    (projectiveSpace.{u} 1).obj.left.toLocallyRingedSpace :=
  analytificationπLRS (projectiveSpace.{u} 1)


-- @@ L48-49 verbatim
/-- The standard affine open `Uᵢ = D₊(Xᵢ)` of `ℙ¹`. -/
abbrev stdU (i : Fin 2) : (projectiveSpace.{u} 1).obj.left.Opens := U 1 (ULift.{u} ℂ) i


-- @@ L51-55 verbatim
lemma πP_chart_mem (i : Fin 2) (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    πP.base (chart i z) ∈ stdU.{u} i := by
  have : chart i z ∈ Set.range (chart i) := ⟨z, rfl⟩
  rw [range_chart] at this
  exact this


-- @@ L57-59 verbatim
lemma preimOpen_stdU_zero :
    (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj (preimOpen πP.{u} (stdU 0)) = ⊤ :=
  eq_top_iff.2 fun w _ ↦ πP_chart_mem 0 (ρ₀.toLRSHom.base w)


-- @@ L61-65 verbatim
/-- A global section of `𝒪_W` has **polynomial growth** if `‖f‖ ≤ C ‖z‖ᵏ` for `‖z‖ > R`,
`z = ρ₀` the coordinate. -/
def HasPolyGrowth (f : W.presheaf.obj (op ⊤)) : Prop :=
  ∃ (k : ℕ) (C R : ℝ), ∀ w : W, R < ‖coord (ρ₀.toLRSHom.base w)‖ →
    ‖W.eval (U := ⊤) w trivial f‖ ≤ C * ‖coord (ρ₀.toLRSHom.base w)‖ ^ k


-- @@ L67-70 verbatim
/-- The underlying section of `𝒪_W` of a section of the extension. -/
abbrev extVal {V : (projectiveSpaceAn.{u} 1).Opens} (s : (extension ρ₀).val.obj (op V)) :
    W.presheaf.obj (op ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj V)) :=
  s.1


-- @@ L72-76 verbatim
/-- Pulling back a section of `𝒪_{ℙ¹_an}` to `W`. -/
abbrev ρPull {V : (projectiveSpaceAn.{u} 1).Opens}
    (r : (projectiveSpaceAn.{u} 1).presheaf.obj (op V)) :
    W.presheaf.obj (op ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj V)) :=
  (toProjectiveLine ρ₀).toLRSHom.c.app (op V) r


-- @@ L78-81 verbatim
lemma extVal_smul {V : (projectiveSpaceAn.{u} 1).Opens}
    (r : (projectiveSpaceAn.{u} 1).presheaf.obj (op V)) (s : (extension ρ₀).val.obj (op V)) :
    extVal ρ₀ (r • s) = ρPull ρ₀ r * extVal ρ₀ s :=
  rfl


-- @@ L83-88 verbatim
lemma extVal_modRes {V V' : (projectiveSpaceAn.{u} 1).Opens} (h : V' ≤ V)
    (s : (extension ρ₀).val.obj (op V)) :
    extVal ρ₀ (modRes s V' h) =
      W.presheaf.map (homOfLE ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).monotone h)).op
        (extVal ρ₀ s) :=
  rfl


-- @@ L90-91 verbatim
variable (F : (projectiveSpace.{u} 1).obj.left.Modules)
  (e : (analytificationModules (projectiveSpace.{u} 1)).obj F ≅ extension ρ₀)


-- @@ L93-97 verbatim
/-- The unit `F ⟶ π_* F^an`. -/
def unitη : F ⟶ ((SheafOfModules.pushforward πP.toRingSheafHom).obj
    ((analytificationModules (projectiveSpace.{u} 1)).obj F) :
      (projectiveSpace.{u} 1).obj.left.Modules) :=
  (analytificationModulesAdj (projectiveSpace.{u} 1)).unit.app F


-- @@ L99-102 verbatim
/-- The section of the extension over `π⁻¹ V` induced by a section of `F` over `V`. -/
def extensionSection (V : (projectiveSpace.{u} 1).obj.left.Opens) (m : Γ(F, V)) :
    (extension ρ₀).val.obj (op (preimOpen πP V)) :=
  e.hom.val.app (op _) (pfSec (unitη F) V m)


-- @@ L104-107 verbatim
/-- **The functions on `W` given by sections of `F` over `U₀`**: `m ↦ (e(m^an))|_W`. -/
def sectionFun (m : Γ(F, stdU 0)) : W.presheaf.obj (op ⊤) :=
  W.presheaf.map (homOfLE (preimOpen_stdU_zero ρ₀).ge).op
    (extVal ρ₀ (extensionSection ρ₀ F e (stdU 0) m))


-- @@ L109-112 verbatim
/-- Pulling back sections of `𝒪_{ℙ¹}` over `U₀` to global sections of `𝒪_W`. -/
def toSections : Γ((projectiveSpace.{u} 1).obj.left, stdU 0) →+* W.presheaf.obj (op ⊤) :=
  (W.presheaf.map (homOfLE (preimOpen_stdU_zero ρ₀).ge).op).hom.comp
    (((toProjectiveLine ρ₀).toLRSHom.c.app (op _)).hom.comp (πP.c.app (op (stdU 0))).hom)


-- @@ L114-119 verbatim
lemma extensionSection_smul (V : (projectiveSpace.{u} 1).obj.left.Opens)
    (r : Γ((projectiveSpace.{u} 1).obj.left, V)) (m : Γ(F, V)) :
    extVal ρ₀ (extensionSection ρ₀ F e V (r • m)) =
      ρPull ρ₀ (πP.c.app (op V) r) * extVal ρ₀ (extensionSection ρ₀ F e V m) := by
  rw [extensionSection, pfSec_smul, modHom_smul]
  rfl


-- @@ L121-127 verbatim
lemma extensionSection_res {V V' : (projectiveSpace.{u} 1).obj.left.Opens} (h : V' ≤ V)
    (m : Γ(F, V)) :
    extVal ρ₀ (extensionSection ρ₀ F e V' (TopCat.Presheaf.restrictOpen m V' h)) =
      W.presheaf.map (homOfLE ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).monotone
        ((Opens.map πP.base).monotone h))).op (extVal ρ₀ (extensionSection ρ₀ F e V m)) := by
  rw [extensionSection, pfSec_res, modHom_modRes]
  rfl


-- @@ L129-133 verbatim
lemma sectionFun_add (m m' : Γ(F, stdU 0)) :
    sectionFun ρ₀ F e (m + m') = sectionFun ρ₀ F e m + sectionFun ρ₀ F e m' := by
  simp only [sectionFun, extensionSection]
  rw [pfSec_add, map_add]
  exact map_add (W.presheaf.map _).hom _ _


-- @@ L135-139 verbatim
lemma sectionFun_smul (r : Γ((projectiveSpace.{u} 1).obj.left, stdU 0)) (m : Γ(F, stdU 0)) :
    sectionFun ρ₀ F e (r • m) = toSections ρ₀ r * sectionFun ρ₀ F e m := by
  simp only [sectionFun]
  rw [extensionSection_smul, map_mul]
  rfl


-- @@ L141-144 verbatim
lemma eval_congr_point {X : AnalyticSpace.{u}} {O : X.Opens} {p q : X} (h : p = q) (hp : p ∈ O)
    (hq : q ∈ O) (s : X.presheaf.obj (op O)) : X.eval p hp s = X.eval q hq s := by
  subst h
  rfl


-- @@ L146-159 verbatim
/-- The value at `w` of the pullback of `X₀ / X₁` is `1 / z`. -/
lemma eval_ρPull_xDiv (w : W) (hz : coord (ρ₀.toLRSHom.base w) ≠ 0)
    (hw : (toProjectiveLine ρ₀).toLRSHom.base w ∈ preimOpen πP.{u} (stdU 1)) :
    W.eval w hw (ρPull ρ₀ (πP.c.app (op (stdU 1)) (xDiv 1 0))) =
      (coord (ρ₀.toLRSHom.base w))⁻¹ := by
  rw [eval_c_app _ (toProjectiveLine ρ₀).isCLinear w hw]
  have hpt : (toProjectiveLine ρ₀).toLRSHom.base w =
      pointOfVec.{u} ![1, coord (ρ₀.toLRSHom.base w)] (by simp) :=
    chart_zero_eq_pointOfVec _
  have h1 : (![1, coord (ρ₀.toLRSHom.base w)] : Fin 2 → ℂ) 1 ≠ 0 := by simpa using hz
  have := evπ_xDiv.{u} (n := 1) ![1, coord (ρ₀.toLRSHom.base w)] (by simp) 1 0 h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_div] at this
  rw [← this, evπ, RingHom.comp_apply]
  exact eval_congr_point hpt _ _ _


-- @@ L161-168 verbatim
lemma eval_ρPull_res {V V' : (projectiveSpaceAn.{u} 1).Opens} (h : V' ≤ V)
    (r : (projectiveSpaceAn.{u} 1).presheaf.obj (op V)) (w : W)
    (hw : (toProjectiveLine ρ₀).toLRSHom.base w ∈ V') :
    W.eval w hw (ρPull ρ₀ ((projectiveSpaceAn.{u} 1).presheaf.map (homOfLE h).op r)) =
      W.eval w (h hw) (ρPull ρ₀ r) := by
  rw [eval_c_app _ (toProjectiveLine ρ₀).isCLinear w hw,
    eval_c_app _ (toProjectiveLine ρ₀).isCLinear w (h hw),
    eval_presheaf_map]


-- @@ L170-175 verbatim
lemma eval_extVal_res {V V' : (projectiveSpaceAn.{u} 1).Opens} (h : V' ≤ V)
    (s : W.presheaf.obj (op ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj V))) (w : W)
    (hw : (toProjectiveLine ρ₀).toLRSHom.base w ∈ V') :
    W.eval w hw (W.presheaf.map (homOfLE ((Opens.map
      (toProjectiveLine ρ₀).toLRSHom.base).monotone h)).op s) = W.eval w (h hw) s :=
  eval_presheaf_map _ _ _ _ _


-- @@ L177-251 verbatim
/-- **Sections of `F` over `U₀` have polynomial growth**: a section over `U₀` times a power of
`X₀ / X₁` extends to `U₁`, and sections of the extension over a neighbourhood of `∞` are bounded
there. -/
theorem hasPolyGrowth_sectionFun
    (hF : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} 1).obj.left.toLocallyRingedSpace.ringSheaf) F)
    (m : Γ(F, stdU 0)) :
    HasPolyGrowth ρ₀ (sectionFun ρ₀ F e m) := by
  have hqc := @Scheme.Modules.isQuasicoherent_of_isCoherent _ F hF
  have hD : (projectiveSpace.{u} 1).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) 1 0) =
      stdU 1 ⊓ stdU 0 := basicOpen_xDiv 1 0
  have hD0 : (projectiveSpace.{u} 1).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) 1 0) ≤
      stdU 0 := hD.le.trans inf_le_right
  have hD1 : (projectiveSpace.{u} 1).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) 1 0) ≤
      stdU 1 := hD.le.trans inf_le_left
  obtain ⟨k, t, ht⟩ := @IsAffineOpen.exists_restrictOpen_eq_pow_smul _ _
    (isAffineOpen_U (n := 1) (R := ULift.{u} ℂ) 1) F hqc (xDiv 1 0)
    (TopCat.Presheaf.restrictOpen m _ hD0)
  have hinf : infty ∈ preimOpen πP.{u} (stdU 1) := πP_chart_mem 1 (ofCoord 0)
  obtain ⟨N, hN, C, hC⟩ := (extensionSection ρ₀ F e (stdU 1) t).2 infty hinf rfl
  obtain ⟨R, hR, hRN⟩ := exists_forall_chart_zero_mem hN
  refine ⟨k, C, R, fun w hw ↦ ?_⟩
  set z := coord (ρ₀.toLRSHom.base w)
  have hz0 : z ≠ 0 := norm_pos_iff.1 (hR.trans hw)
  have hwD : (toProjectiveLine ρ₀).toLRSHom.base w ∈ preimOpen πP.{u}
      ((projectiveSpace.{u} 1).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) 1 0)) := by
    change πP.base (chart 0 (ρ₀.toLRSHom.base w)) ∈
      ((projectiveSpace.{u} 1).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) 1 0) : Set _)
    rw [hD]
    refine ⟨?_, πP_chart_mem 0 _⟩
    rw [chart_zero_eq_chart_one _ hz0]
    exact πP_chart_mem 1 _
  have key := congrArg (fun m' ↦ W.eval w hwD (extVal ρ₀ (extensionSection ρ₀ F e _ m'))) ht
  have e1 : W.eval w hwD (extVal ρ₀ (extensionSection ρ₀ F e _
      (TopCat.Presheaf.restrictOpen t _ hD1))) =
      W.eval w ((Opens.map πP.base).monotone hD1 hwD)
        (extVal ρ₀ (extensionSection ρ₀ F e (stdU 1) t)) := by
    erw [extensionSection_res, eval_extVal_res]
  have e2 : W.eval w hwD (extVal ρ₀ (extensionSection ρ₀ F e _
      ((show Γ((projectiveSpace.{u} 1).obj.left, _) from
        TopCat.Presheaf.restrictOpen (xDiv (R := ULift.{u} ℂ) 1 0) _ hD1) ^ k •
        TopCat.Presheaf.restrictOpen m _ hD0))) =
      W.eval w hwD (ρPull ρ₀ (πP.c.app (op _)
        ((show Γ((projectiveSpace.{u} 1).obj.left, _) from
          TopCat.Presheaf.restrictOpen (xDiv (R := ULift.{u} ℂ) 1 0) _ hD1) ^ k))) *
      W.eval w ((Opens.map πP.base).monotone hD0 hwD)
        (extVal ρ₀ (extensionSection ρ₀ F e (stdU 0) m)) := by
    erw [extensionSection_smul, map_mul, extensionSection_res, eval_extVal_res]
  have key' := e1.symm.trans (key.trans e2)
  have e3 : W.eval w hwD (ρPull ρ₀ (πP.c.app (op _)
      ((show Γ((projectiveSpace.{u} 1).obj.left, _) from
        TopCat.Presheaf.restrictOpen (xDiv (R := ULift.{u} ℂ) 1 0) _ hD1) ^ k))) = z⁻¹ ^ k := by
    dsimp only
    erw [map_pow]
    simp only [ρPull]
    erw [map_pow, map_pow]
    congr 1
    change W.eval w hwD (ρPull ρ₀ (πP.c.app (op _) (LocallyRingedSpace.res _ hD1 _))) = _
    rw [c_app_res]
    exact (eval_ρPull_res ρ₀ _ _ w hwD).trans (eval_ρPull_xDiv ρ₀ w hz0 _)
  have e4 : W.eval (U := ⊤) w trivial (sectionFun ρ₀ F e m) =
      W.eval w ((Opens.map πP.base).monotone hD0 hwD)
        (extVal ρ₀ (extensionSection ρ₀ F e (stdU 0) m)) := eval_presheaf_map _ _ _ _ _
  rw [e3] at key'
  rw [e4]
  have hbd := hC w ((Opens.map πP.base).monotone hD1 hwD) (hRN _ hw)
  have hz : ‖z‖ ^ k * ‖z⁻¹‖ ^ k = 1 := by
    rw [← mul_pow, ← norm_mul, mul_inv_cancel₀ hz0, norm_one, one_pow]
  calc _ = ‖z‖ ^ k * ‖z⁻¹ ^ k * W.eval w ((Opens.map πP.base).monotone hD0 hwD)
        (extVal ρ₀ (extensionSection ρ₀ F e (stdU 0) m))‖ := by
          rw [norm_mul, norm_pow, ← mul_assoc, hz, one_mul]
    _ ≤ ‖z‖ ^ k * C := by
          rw [← key']
          exact mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = C * ‖z‖ ^ k := mul_comm _ _


-- @@ L253-253 verbatim
/-! ### Sections with polynomial growth come from `F` -/


-- @@ L255-257 verbatim
/-- The cocycle `(Xⱼ / Xᵢ)⁻ᵏ` of `𝒪(-k)`. -/
abbrev twistCocycle (k : ℕ) : Cocycle (U 1 (ULift.{u} ℂ)) :=
  cocycle 1 (ULift.{u} ℂ) ^ (-(k : ℤ))


-- @@ L259-277 verbatim
/-- On the overlap, the `0`-th component of a section of `𝒪(-k)^an` at `[1 : z]` is `z⁻ᵏ` times
the `1`-st component. -/
lemma eval_pbComp_zero (k : ℕ) {V : (projectiveSpaceAn.{u} 1).Opens}
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) (z : ℂ)
    (hp0 : pointOfVec.{u} ![1, z] (by simp) ∈ V ⊓ preimOpen πP (stdU 0))
    (hp1 : pointOfVec.{u} ![1, z] (by simp) ∈ V ⊓ preimOpen πP (stdU 1)) :
    (projectiveSpaceAn.{u} 1).eval _ hp0 (pbComp t 0) =
      z ^ (-(k : ℤ)) * (projectiveSpaceAn.{u} 1).eval _ hp1 (pbComp t 1) := by
  have hp : pointOfVec.{u} ![1, z] (by simp) ∈
      V ⊓ (preimOpen πP (stdU 0) ⊓ preimOpen πP (stdU 1)) := ⟨hp0.1, hp0.2, hp1.2⟩
  have h := congrArg ((projectiveSpaceAn.{u} 1).eval _ hp) (pbComp_compat t 0 1)
  rw [AnalyticSpace.eval_restrictOpen, map_mul, AnalyticSpace.eval_restrictOpen,
    AnalyticSpace.eval_restrictOpen] at h
  rw [h]
  congr 1
  have h1 : (![1, z] : Fin 2 → ℂ) 0 ≠ 0 := by simp
  have := evπ_cocycle_zpow.{u} (n := 1) (-(k : ℤ)) ![1, z] (by simp) 0 1 h1 ⟨hp0.2, hp1.2⟩
  refine this.trans ?_
  simp


-- @@ L279-283 verbatim
lemma preimage_inf_stdU_zero (V : (projectiveSpaceAn.{u} 1).Opens) :
    (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj (V ⊓ preimOpen πP (stdU 0)) =
      (Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj V := by
  ext w
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, πP_chart_mem 0 _⟩⟩


-- @@ L285-290 verbatim
/-- The section `t₀ · f` of `𝒪_W` over `ρ⁻¹ V`, for a section `t` of `𝒪(-k)^an` over `V`. -/
def growthVal (f : W.presheaf.obj (op ⊤)) (k : ℕ) {V : (projectiveSpaceAn.{u} 1).Opens}
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    W.presheaf.obj (op ((Opens.map (toProjectiveLine ρ₀).toLRSHom.base).obj V)) :=
  W.presheaf.map (homOfLE (preimage_inf_stdU_zero ρ₀ V).ge).op (ρPull ρ₀ (pbComp t 0)) *
    W.presheaf.map (homOfLE le_top).op f


-- @@ L292-299 verbatim
lemma eval_growthVal (f : W.presheaf.obj (op ⊤)) (k : ℕ) {V : (projectiveSpaceAn.{u} 1).Opens}
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) (w : W)
    (hw : (toProjectiveLine ρ₀).toLRSHom.base w ∈ V) :
    W.eval w hw (growthVal ρ₀ f k t) =
      (projectiveSpaceAn.{u} 1).eval _ (show _ ∈ V ⊓ preimOpen πP (stdU 0) from
        ⟨hw, πP_chart_mem 0 _⟩) (pbComp t 0) * W.eval (U := ⊤) w trivial f := by
  rw [growthVal, map_mul, eval_presheaf_map, eval_presheaf_map,
    eval_c_app _ (toProjectiveLine ρ₀).isCLinear]


-- @@ L301-341 verbatim
lemma isBoundedNear_growthVal (f : W.presheaf.obj (op ⊤)) (k : ℕ) (C R : ℝ) (hR : 0 < R)
    (hf : ∀ w : W, R < ‖coord (ρ₀.toLRSHom.base w)‖ →
      ‖W.eval (U := ⊤) w trivial f‖ ≤ C * ‖coord (ρ₀.toLRSHom.base w)‖ ^ k)
    {V : (projectiveSpaceAn.{u} 1).Opens}
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    IsBoundedNear (toProjectiveLine ρ₀) {infty} (growthVal ρ₀ f k t) := by
  rintro _ hy rfl
  have hinf : infty ∈ V ⊓ preimOpen πP (stdU 1) := ⟨hy, πP_chart_mem 1 _⟩
  have h1 : ∀ᶠ p in 𝓝 (⟨infty, hinf⟩ : ↥(V ⊓ preimOpen πP (stdU 1))),
      ‖(projectiveSpaceAn.{u} 1).eval p.1 p.2 (pbComp t 1)‖ <
        ‖(projectiveSpaceAn.{u} 1).eval _ hinf (pbComp t 1)‖ + 1 :=
    ((projectiveSpaceAn.{u} 1).continuousAt_eval (pbComp t 1) ⟨infty, hinf⟩).norm.eventually
      (gt_mem_nhds (lt_add_one _))
  rw [nhds_subtype_eq_comap, eventually_comap] at h1
  set B := ‖(projectiveSpaceAn.{u} 1).eval _ hinf (pbComp t 1)‖ + 1
  refine ⟨_, inter_mem h1 (nbd_mem_nhds hR), B * max C 0, fun w hw hwN ↦ ?_⟩
  set z := coord (ρ₀.toLRSHom.base w)
  have hzR : R < ‖z‖ := (chart_zero_mem_nbd_iff hR _).1 hwN.2
  have hz0 : z ≠ 0 := norm_pos_iff.1 (hR.trans hzR)
  have hpt : (toProjectiveLine ρ₀).toLRSHom.base w = pointOfVec.{u} ![1, z] (by simp) :=
    chart_zero_eq_pointOfVec _
  have hw1 : (toProjectiveLine ρ₀).toLRSHom.base w ∈ V ⊓ preimOpen πP (stdU 1) := by
    refine ⟨hw, ?_⟩
    have := πP_chart_mem 1 (ofCoord z⁻¹)
    rw [← chart_zero_eq_chart_one _ hz0] at this
    exact this
  have hbdt := hwN.1 ⟨_, hw1⟩ rfl
  rw [eval_growthVal]
  have e0 := eval_pbComp_zero k t z (hpt ▸ ⟨hw, πP_chart_mem 0 _⟩) (hpt ▸ hw1)
  rw [eval_congr_point hpt _ (hpt ▸ ⟨hw, πP_chart_mem 0 _⟩), e0, norm_mul, norm_mul,
    ← eval_congr_point hpt hw1 (hpt ▸ hw1)]
  have hzk : ‖z ^ (-(k : ℤ))‖ * ‖z‖ ^ k = 1 := by
    rw [norm_zpow, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hz0))]
  calc ‖z ^ (-(k : ℤ))‖ * ‖(projectiveSpaceAn.{u} 1).eval _ hw1 (pbComp t 1)‖ *
        ‖W.eval (U := ⊤) w trivial f‖
      ≤ ‖z ^ (-(k : ℤ))‖ * B * (max C 0 * ‖z‖ ^ k) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hbdt.le (norm_nonneg _)) ?_
          (norm_nonneg _) (by positivity)
        exact (hf w hzR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    _ = B * max C 0 * (‖z ^ (-(k : ℤ))‖ * ‖z‖ ^ k) := by ring
    _ = B * max C 0 := by rw [hzk, mul_one]


-- @@ L343-343 verbatim
section Psi


-- @@ L345-347 verbatim
variable (f : W.presheaf.obj (op ⊤)) (k : ℕ) (C R : ℝ) (hR : 0 < R)
  (hf : ∀ w : W, R < ‖coord (ρ₀.toLRSHom.base w)‖ →
    ‖W.eval (U := ⊤) w trivial f‖ ≤ C * ‖coord (ρ₀.toLRSHom.base w)‖ ^ k)


-- @@ L349-356 verbatim
lemma growthVal_add {V : (projectiveSpaceAn.{u} 1).Opens}
    (t t' : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    growthVal ρ₀ f k (t + t') = growthVal ρ₀ f k t + growthVal ρ₀ f k t' := by
  simp only [growthVal, pbComp_add]
  rw [← add_mul]
  congr 1
  exact (congrArg (W.presheaf.map _).hom
    (map_add (((toProjectiveLine ρ₀).toLRSHom.c.app _).hom) _ _)).trans (map_add _ _ _)


-- @@ L358-366 verbatim
lemma ρPull_restrict_inf (V : (projectiveSpaceAn.{u} 1).Opens)
    (r : (projectiveSpaceAn.{u} 1).presheaf.obj (op V)) :
    W.presheaf.map (homOfLE (preimage_inf_stdU_zero ρ₀ V).ge).op
      (ρPull ρ₀ (TopCat.Presheaf.restrictOpen r (V ⊓ preimOpen πP (stdU 0)) inf_le_left)) =
      ρPull ρ₀ r := by
  have := c_app_res (M := W.toLocallyRingedSpace) (toProjectiveLine ρ₀).toLRSHom
    (inf_le_left : V ⊓ preimOpen πP (stdU 0) ≤ V) r
  refine (congrArg (W.presheaf.map (homOfLE (preimage_inf_stdU_zero ρ₀ V).ge).op).hom this).trans ?_
  exact presheaf_map_map_of_le (X := W) _ _ _


-- @@ L368-378 verbatim
lemma growthVal_smul {V : (projectiveSpaceAn.{u} 1).Opens}
    (r : (projectiveSpaceAn.{u} 1).presheaf.obj (op V))
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    growthVal ρ₀ f k (r • t) = ρPull ρ₀ r * growthVal ρ₀ f k t := by
  simp only [growthVal, pbComp_smul]
  refine (congrArg (· * _) ((congrArg (W.presheaf.map _).hom
    (map_mul (((toProjectiveLine ρ₀).toLRSHom.c.app _).hom) _ _)).trans
      (map_mul _ _ _))).trans ?_
  rw [mul_assoc]
  congr 1
  exact ρPull_restrict_inf ρ₀ V r


-- @@ L380-395 verbatim
lemma growthVal_res {V V' : (projectiveSpaceAn.{u} 1).Opens} (h : V' ≤ V)
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    growthVal ρ₀ f k (modRes t V' h) = W.presheaf.map (homOfLE ((Opens.map
      (toProjectiveLine ρ₀).toLRSHom.base).monotone h)).op (growthVal ρ₀ f k t) := by
  simp only [growthVal]
  refine (congrArg₂ (· * ·) ?_ ?_).trans (map_mul _ _ _).symm
  · have := c_app_res (M := W.toLocallyRingedSpace) (toProjectiveLine ρ₀).toLRSHom
      (inf_le_inf_right _ h : V' ⊓ preimOpen πP (stdU 0) ≤ V ⊓ preimOpen πP (stdU 0)) (pbComp t 0)
    refine (congrArg (W.presheaf.map _).hom this).trans ?_
    change W.presheaf.map _ (W.presheaf.map _ _) = W.presheaf.map _ (W.presheaf.map _ _)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← W.presheaf.map_comp,
      ← W.presheaf.map_comp]
    rfl
  · change _ = W.presheaf.map _ (W.presheaf.map _ f)
    rw [← ConcreteCategory.comp_apply, ← W.presheaf.map_comp]
    rfl


-- @@ L397-408 verbatim
include hR hf in
/-- The section of the extension given by `t₀ · f`. -/
def psiApp (V : (projectiveSpaceAn.{u} 1).Opens) :
    (pbTwist πP (twistCocycle.{u} k)).val.obj (op V) →+ (extension ρ₀).val.obj (op V) where
  toFun t := (⟨growthVal ρ₀ f k t, isBoundedNear_growthVal ρ₀ f k C R hR hf t⟩ :
    (boundedSubmodule (toProjectiveLine ρ₀) {infty}).obj (op V))
  map_zero' := Subtype.ext (by
    change growthVal ρ₀ f k 0 = 0
    have h := growthVal_add ρ₀ f k (0 : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) 0
    rw [add_zero] at h
    exact left_eq_add.1 h)
  map_add' t t' := Subtype.ext (growthVal_add ρ₀ f k t t')


-- @@ L410-415 verbatim
/-- **The morphism `𝒪(-k)^an ⟶ 𝒞̄` given by a function `f` with `‖f‖ ≤ C ‖z‖ᵏ`**:
`t ↦ t₀ · f`. -/
def psi : pbTwist πP (twistCocycle.{u} k) ⟶ extension ρ₀ :=
  modHomMk (psiApp ρ₀ f k C R hR hf)
    (fun _ r t ↦ Subtype.ext (growthVal_smul ρ₀ f k r t))
    (fun _ _ h t ↦ Subtype.ext (growthVal_res ρ₀ f k h t))


-- @@ L417-417 verbatim
end Psi


-- @@ L419-432 verbatim
lemma psi_frame (f : W.presheaf.obj (op ⊤)) (k : ℕ) (C R : ℝ) (hR : 0 < R)
    (hf : ∀ w : W, R < ‖coord (ρ₀.toLRSHom.base w)‖ →
      ‖W.eval (U := ⊤) w trivial f‖ ≤ C * ‖coord (ρ₀.toLRSHom.base w)‖ ^ k) :
    W.presheaf.map (homOfLE (preimOpen_stdU_zero ρ₀).ge).op
      (extVal ρ₀ ((psi ρ₀ f k C R hR hf).val.app (op (preimOpen πP (stdU 0)))
        (pfSec (toPushforwardPbTwist πP (twistCocycle.{u} k)) (stdU 0)
          (twistFrame (twistCocycle.{u} k) 0)))) = f := by
  change W.presheaf.map _ (growthVal ρ₀ f k _) = f
  simp only [growthVal]
  erw [pbComp_twistFrame_self]
  refine (congrArg (W.presheaf.map _).hom (congrArg (· * _) ((congrArg (W.presheaf.map _).hom
    (map_one ((toProjectiveLine ρ₀).toLRSHom.c.app _).hom)).trans (map_one _)))).trans ?_
  rw [one_mul]
  exact presheaf_map_map_of_le (X := W) _ _ f


-- @@ L434-483 unexpanded
/-- **Sections with polynomial growth come from `F`**: if `‖f‖ ≤ C ‖z‖ᵏ` near `∞`, then
`t ↦ t₀ · f` is a morphism `𝒪(-k)^an ⟶ 𝒞̄ ≅ F^an`, which by GAGA-2 is the analytification of a
morphism `𝒪(-k) ⟶ F`; its value on the frame of `𝒪(-k)` over `U₀` is a section of `F` over `U₀`
mapping to `f`. -/
theorem exists_sectionFun_eq
    (hF : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} 1).obj.left.toLocallyRingedSpace.ringSheaf) F)
    (f : W.presheaf.obj (op ⊤)) (hf : HasPolyGrowth ρ₀ f) :
    ∃ m : Γ(F, stdU 0), sectionFun ρ₀ F e m = f := by
  obtain ⟨k, C, R₀, hf⟩ := hf
  set R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hf' : ∀ w : W, R < ‖coord (ρ₀.toLRSHom.base w)‖ →
      ‖W.eval (U := ⊤) w trivial f‖ ≤ C * ‖coord (ρ₀.toLRSHom.base w)‖ ^ k :=
    fun w hw ↦ hf w ((le_max_left _ _).trans_lt hw)
  haveI : IsLocallyNoetherian ℙ(1; ULift.{u} ℂ) :=
    LocallyOfFiniteType.isLocallyNoetherian (toSpec 1 (ULift.{u} ℂ))
  haveI := Scheme.isCoherent_unit (X := ℙ(1; ULift.{u} ℂ))
  have hL : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} 1).obj.left.toLocallyRingedSpace.ringSheaf)
      (twistUnit (twistCocycle.{u} k)) :=
    isCoherent_twist (SheafOfModules.unit _) (-(k : ℤ))
  obtain ⟨α, hα⟩ := (gaga₂_projectiveSpace 1 (twistUnit (twistCocycle.{u} k)) F).2
    ((pullbackTwistUnitIso πP (twistCocycle.{u} k) (iSup_U 1 _)).hom ≫
      psi ρ₀ f k C R hR hf' ≫ e.inv)
  refine ⟨Scheme.Modules.Hom.app (M := twistUnit (twistCocycle.{u} k)) (N := F) α (stdU 0)
    (twistFrame (twistCocycle.{u} k) 0), ?_⟩
  have hnat := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ (stdU 0)
    (twistFrame (twistCocycle.{u} k) 0))
    ((analytificationModulesAdj (projectiveSpace.{u} 1)).unit.naturality α)
  have h1 : pfSec (unitη F) (stdU 0) (Scheme.Modules.Hom.app (M := twistUnit (twistCocycle.{u} k))
      (N := F) α (stdU 0) (twistFrame (twistCocycle.{u} k) 0)) =
      ((analytificationModules (projectiveSpace.{u} 1)).map α).val.app _
        (twistFrameη πP (twistCocycle.{u} k) 0) := hnat
  rw [sectionFun, extensionSection, h1, hα]
  have h2 : e.hom.val.app (op (preimOpen πP (stdU 0)))
      (((pullbackTwistUnitIso πP (twistCocycle.{u} k) (iSup_U 1 _)).hom ≫
        psi ρ₀ f k C R hR hf' ≫ e.inv).val.app _ (twistFrameη πP (twistCocycle.{u} k) 0)) =
      (psi ρ₀ f k C R hR hf').val.app _ (pfSec (toPushforwardPbTwist πP (twistCocycle.{u} k))
        (stdU 0) (twistFrame (twistCocycle.{u} k) 0)) := by
    have hinv := congrArg (fun φ ↦ φ.val.app (op (preimOpen πP (stdU 0)))
      ((psi ρ₀ f k C R hR hf').val.app _ ((pullbackToPbTwist πP (twistCocycle.{u} k)).val.app _
        (twistFrameη πP (twistCocycle.{u} k) 0)))) e.inv_hom_id
    refine hinv.trans ?_
    change (psi ρ₀ f k C R hR hf').val.app _ ((pullbackToPbTwist πP (twistCocycle.{u} k)).val.app _
        (pfSec (twistUnitη πP (twistCocycle.{u} k)) (stdU 0)
          (twistFrame (twistCocycle.{u} k) 0))) = _
    rw [pullbackToPbTwist_pfSec]
  exact (congrArg (fun s ↦ W.presheaf.map (homOfLE (preimOpen_stdU_zero ρ₀).ge).op
    (extVal ρ₀ s)) h2).trans (psi_frame ρ₀ f k C R hR hf')


-- @@ L485-485 verbatim
end

-- @@ L486-486 verbatim
end ComplexAnalytic.ProjectiveLine
