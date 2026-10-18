/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.RET.ES.SmoothExtension
import Oka.Analytification.RET.ES.CurveSections


-- @@ L9-26 verbatim
/-!
# Sections of an algebraisation of the canonical extension over `U₀ ⊆ ℙⁿ`

Keep the notation of `Oka/Analytification/RET/ES/SmoothExtension.lean`: `ρ₀ : W ⟶ ℂⁿ`,
`ρ : W ⟶ ℙⁿ_an` its composite with the chart `0` and `𝒞̄` the sheaf of sections of `ρ_* 𝒪_W`
bounded near the hyperplane at infinity `H_∞`. Let `F` be a coherent sheaf on `ℙⁿ` with an
isomorphism `e : F^an ≅ 𝒞̄`. A section `m` of `F` over `U₀ = D₊(X₀)` gives the function `e(m^an)`
on `W` (`ComplexAnalytic.ProjectiveCompletion.sectionFun`). These are exactly the functions of
polynomial growth in `z = ρ₀` (`ComplexAnalytic.ProjectiveCompletion.HasPolyGrowth`):

- `ComplexAnalytic.ProjectiveCompletion.hasPolyGrowth_sectionFun`: for every `i`, some
  `(X₀ / Xᵢ)ᵏ m` extends to a section of `F` over `Uᵢ`, whose image in `𝒞̄` is bounded near
  `H_∞ ∩ Uᵢ`; finitely many such neighbourhoods cover the compact `H_∞`;
- `ComplexAnalytic.ProjectiveCompletion.exists_sectionFun_eq`: a function `f` with
  `‖f‖ ≤ C ‖z‖ᵏ` near `H_∞` gives a morphism `𝒪(-k)^an ⟶ 𝒞̄`, `t ↦ t₀ f`
  (`ComplexAnalytic.ProjectiveCompletion.psi`); by GAGA-2 it is the analytification of a morphism
  `𝒪(-k) ⟶ F`, and the image of the frame of `𝒪(-k)` over `U₀` is a section of `F` mapping to `f`.
-/


-- @@ L28-28 verbatim
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology Filter


-- @@ L30-30 verbatim
universe u


-- @@ L32-32 verbatim
namespace ComplexAnalytic.ProjectiveCompletion


-- @@ L34-34 verbatim
open AnalyticSpace projectiveSpaceAn LocallyRingedSpace AlgebraicGeometry.ProjectiveSpace

-- @@ L35-35 verbatim
open AlgebraicGeometry.Scheme.Modules


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
variable {n : ℕ} {W : AnalyticSpace.{u}} (ρ₀ : W ⟶ AnalyticSpace.complexAffineSpace.{u} n)


-- @@ L41-44 verbatim
/-- The comparison morphism `ℙⁿ_an ⟶ ℙⁿ`. -/
abbrev πP : (projectiveSpaceAn.{u} n).toLocallyRingedSpace ⟶
    (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace :=
  analytificationπLRS (projectiveSpace.{u} n)


-- @@ L46-47 verbatim
/-- The standard affine open `Uᵢ = D₊(Xᵢ)` of `ℙⁿ`. -/
abbrev stdU (i : Fin (n + 1)) : (projectiveSpace.{u} n).obj.left.Opens := U n (ULift.{u} ℂ) i


-- @@ L49-52 verbatim
lemma mem_preimOpen_stdU_iff (i : Fin (n + 1)) (x : projectiveSpaceAn.{u} n) :
    x ∈ preimOpen πP.{u} (stdU i) ↔ x ∈ Set.range (chart i) := by
  rw [range_chart]
  rfl


-- @@ L54-56 verbatim
lemma πP_chart_mem (i : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    πP.base (chart i z) ∈ stdU.{u} i :=
  (mem_preimOpen_stdU_iff i _).2 ⟨z, rfl⟩


-- @@ L58-63 verbatim
lemma chart_zero_mem_preimOpen_iff (i : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    chart 0 z ∈ preimOpen πP.{u} (stdU i) ↔ homogCoord 0 z i ≠ 0 := by
  rw [mem_preimOpen_stdU_iff]
  change (projectiveSpaceAnChart.{u} 0).toLRSHom.base z ∈ _ ↔ _
  rw [chart_eq_pointOfVec]
  exact mem_range_chart_pointOfVec_iff _ _ i


-- @@ L65-67 verbatim
lemma preimOpen_stdU_zero :
    (Opens.map (toProj ρ₀).toLRSHom.base).obj (preimOpen πP.{u} (stdU 0)) = ⊤ :=
  eq_top_iff.2 fun w _ ↦ πP_chart_mem 0 (ρ₀.toLRSHom.base w)


-- @@ L69-73 verbatim
/-- A global section of `𝒪_W` has **polynomial growth** if `‖f‖ ≤ C ‖z‖ᵏ` for `‖z‖ > R`,
`z = ρ₀`. -/
def HasPolyGrowth (f : W.presheaf.obj (op ⊤)) : Prop :=
  ∃ (k : ℕ) (C R : ℝ), ∀ w : W, R < vnorm (ρ₀.toLRSHom.base w) →
    ‖W.eval (U := ⊤) w trivial f‖ ≤ C * vnorm (ρ₀.toLRSHom.base w) ^ k


-- @@ L75-78 verbatim
/-- The underlying section of `𝒪_W` of a section of the extension. -/
abbrev extVal {V : (projectiveSpaceAn.{u} n).Opens} (s : (extension ρ₀).val.obj (op V)) :
    W.presheaf.obj (op ((Opens.map (toProj ρ₀).toLRSHom.base).obj V)) :=
  s.1


-- @@ L80-84 verbatim
/-- Pulling back a section of `𝒪_{ℙⁿ_an}` to `W`. -/
abbrev ρPull {V : (projectiveSpaceAn.{u} n).Opens}
    (r : (projectiveSpaceAn.{u} n).presheaf.obj (op V)) :
    W.presheaf.obj (op ((Opens.map (toProj ρ₀).toLRSHom.base).obj V)) :=
  (toProj ρ₀).toLRSHom.c.app (op V) r


-- @@ L86-89 verbatim
lemma extVal_smul {V : (projectiveSpaceAn.{u} n).Opens}
    (r : (projectiveSpaceAn.{u} n).presheaf.obj (op V)) (s : (extension ρ₀).val.obj (op V)) :
    extVal ρ₀ (r • s) = ρPull ρ₀ r * extVal ρ₀ s :=
  rfl


-- @@ L91-96 verbatim
lemma extVal_modRes {V V' : (projectiveSpaceAn.{u} n).Opens} (h : V' ≤ V)
    (s : (extension ρ₀).val.obj (op V)) :
    extVal ρ₀ (modRes s V' h) =
      W.presheaf.map (homOfLE ((Opens.map (toProj ρ₀).toLRSHom.base).monotone h)).op
        (extVal ρ₀ s) :=
  rfl


-- @@ L98-99 verbatim
variable (F : (projectiveSpace.{u} n).obj.left.Modules)
  (e : (analytificationModules (projectiveSpace.{u} n)).obj F ≅ extension ρ₀)


-- @@ L101-105 verbatim
/-- The unit `F ⟶ π_* F^an`. -/
def unitη : F ⟶ ((SheafOfModules.pushforward πP.toRingSheafHom).obj
    ((analytificationModules (projectiveSpace.{u} n)).obj F) :
      (projectiveSpace.{u} n).obj.left.Modules) :=
  (analytificationModulesAdj (projectiveSpace.{u} n)).unit.app F


-- @@ L107-110 verbatim
/-- The section of the extension over `π⁻¹ V` induced by a section of `F` over `V`. -/
def extensionSection (V : (projectiveSpace.{u} n).obj.left.Opens) (m : Γ(F, V)) :
    (extension ρ₀).val.obj (op (preimOpen πP V)) :=
  e.hom.val.app (op _) (pfSec (unitη F) V m)


-- @@ L112-115 verbatim
/-- **The functions on `W` given by sections of `F` over `U₀`**: `m ↦ (e(m^an))|_W`. -/
def sectionFun (m : Γ(F, stdU 0)) : W.presheaf.obj (op ⊤) :=
  W.presheaf.map (homOfLE (preimOpen_stdU_zero ρ₀).ge).op
    (extVal ρ₀ (extensionSection ρ₀ F e (stdU 0) m))


-- @@ L117-120 verbatim
/-- Pulling back sections of `𝒪_{ℙⁿ}` over `U₀` to global sections of `𝒪_W`. -/
def toSections : Γ((projectiveSpace.{u} n).obj.left, stdU 0) →+* W.presheaf.obj (op ⊤) :=
  (W.presheaf.map (homOfLE (preimOpen_stdU_zero ρ₀).ge).op).hom.comp
    (((toProj ρ₀).toLRSHom.c.app (op _)).hom.comp (πP.c.app (op (stdU 0))).hom)


-- @@ L122-127 verbatim
lemma extensionSection_smul (V : (projectiveSpace.{u} n).obj.left.Opens)
    (r : Γ((projectiveSpace.{u} n).obj.left, V)) (m : Γ(F, V)) :
    extVal ρ₀ (extensionSection ρ₀ F e V (r • m)) =
      ρPull ρ₀ (πP.c.app (op V) r) * extVal ρ₀ (extensionSection ρ₀ F e V m) := by
  rw [extensionSection, pfSec_smul, modHom_smul]
  rfl


-- @@ L129-135 verbatim
lemma extensionSection_res {V V' : (projectiveSpace.{u} n).obj.left.Opens} (h : V' ≤ V)
    (m : Γ(F, V)) :
    extVal ρ₀ (extensionSection ρ₀ F e V' (TopCat.Presheaf.restrictOpen m V' h)) =
      W.presheaf.map (homOfLE ((Opens.map (toProj ρ₀).toLRSHom.base).monotone
        ((Opens.map πP.base).monotone h))).op (extVal ρ₀ (extensionSection ρ₀ F e V m)) := by
  rw [extensionSection, pfSec_res, modHom_modRes]
  rfl


-- @@ L137-141 verbatim
lemma sectionFun_add (m m' : Γ(F, stdU 0)) :
    sectionFun ρ₀ F e (m + m') = sectionFun ρ₀ F e m + sectionFun ρ₀ F e m' := by
  simp only [sectionFun, extensionSection]
  rw [pfSec_add, map_add]
  exact map_add (W.presheaf.map _).hom _ _


-- @@ L143-147 verbatim
lemma sectionFun_smul (r : Γ((projectiveSpace.{u} n).obj.left, stdU 0)) (m : Γ(F, stdU 0)) :
    sectionFun ρ₀ F e (r • m) = toSections ρ₀ r * sectionFun ρ₀ F e m := by
  simp only [sectionFun]
  rw [extensionSection_smul, map_mul]
  rfl


-- @@ L149-163 verbatim
/-- The value at `w` of the pullback of `X₀ / Xᵢ` is `1 / zᵢ`, `(1, z) = homogCoord 0 (ρ₀ w)`. -/
lemma eval_ρPull_xDiv (w : W) (i : Fin (n + 1))
    (hw : (toProj ρ₀).toLRSHom.base w ∈ preimOpen πP.{u} (stdU i)) :
    W.eval w hw (ρPull ρ₀ (πP.c.app (op (stdU i)) (xDiv i 0))) =
      (homogCoord 0 (ρ₀.toLRSHom.base w) i)⁻¹ := by
  rw [eval_c_app _ (toProj ρ₀).isCLinear w hw]
  have hpt : (toProj ρ₀).toLRSHom.base w =
      pointOfVec.{u} (homogCoord 0 (ρ₀.toLRSHom.base w)) (homogCoord_ne_zero _ _) :=
    (toProj_base ρ₀ w).trans (chart_eq_pointOfVec 0 (ρ₀.toLRSHom.base w))
  have hi : homogCoord 0 (ρ₀.toLRSHom.base w) i ≠ 0 :=
    (chart_zero_mem_preimOpen_iff i _).1 hw
  have := evπ_xDiv.{u} (homogCoord 0 (ρ₀.toLRSHom.base w)) (homogCoord_ne_zero _ _) i 0 hi
  rw [homogCoord_self, one_div] at this
  rw [← this, evπ, RingHom.comp_apply]
  exact eval_congr_point hpt _ _ _


-- @@ L165-172 verbatim
lemma eval_ρPull_res {V V' : (projectiveSpaceAn.{u} n).Opens} (h : V' ≤ V)
    (r : (projectiveSpaceAn.{u} n).presheaf.obj (op V)) (w : W)
    (hw : (toProj ρ₀).toLRSHom.base w ∈ V') :
    W.eval w hw (ρPull ρ₀ ((projectiveSpaceAn.{u} n).presheaf.map (homOfLE h).op r)) =
      W.eval w (h hw) (ρPull ρ₀ r) := by
  rw [eval_c_app _ (toProj ρ₀).isCLinear w hw,
    eval_c_app _ (toProj ρ₀).isCLinear w (h hw),
    eval_presheaf_map]


-- @@ L174-179 verbatim
lemma eval_extVal_res {V V' : (projectiveSpaceAn.{u} n).Opens} (h : V' ≤ V)
    (s : W.presheaf.obj (op ((Opens.map (toProj ρ₀).toLRSHom.base).obj V))) (w : W)
    (hw : (toProj ρ₀).toLRSHom.base w ∈ V') :
    W.eval w hw (W.presheaf.map (homOfLE ((Opens.map
      (toProj ρ₀).toLRSHom.base).monotone h)).op s) = W.eval w (h hw) s :=
  eval_presheaf_map _ _ _ _ _


-- @@ L181-239 verbatim
/-- **The identity `tᵢ = (X₀ / Xᵢ)ᵏ m` on `W`**: if `t` extends `(X₀ / Xᵢ)ᵏ m` to `Uᵢ`, then
`m(w) = zᵢᵏ t(w)` on `W` over `Uᵢ`. -/
lemma eval_sectionFun_eq (i : Fin (n + 1)) (m : Γ(F, stdU 0)) (k : ℕ) (t : Γ(F, stdU i))
    (hD0 : (projectiveSpace.{u} n).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) i 0) ≤ stdU 0)
    (hD1 : (projectiveSpace.{u} n).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) i 0) ≤ stdU i)
    (ht : TopCat.Presheaf.restrictOpen t _ hD1 =
      (show Γ((projectiveSpace.{u} n).obj.left, _) from
        TopCat.Presheaf.restrictOpen (xDiv (R := ULift.{u} ℂ) i 0) _ hD1) ^ k •
        TopCat.Presheaf.restrictOpen m _ hD0)
    (w : W) (hw : (toProj ρ₀).toLRSHom.base w ∈ preimOpen πP.{u} (stdU i)) :
    W.eval (U := ⊤) w trivial (sectionFun ρ₀ F e m) =
      homogCoord 0 (ρ₀.toLRSHom.base w) i ^ k *
        W.eval w hw (extVal ρ₀ (extensionSection ρ₀ F e (stdU i) t)) := by
  have hD : (projectiveSpace.{u} n).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) i 0) =
      stdU i ⊓ stdU 0 := basicOpen_xDiv i 0
  have hwD : (toProj ρ₀).toLRSHom.base w ∈ preimOpen πP.{u}
      ((projectiveSpace.{u} n).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) i 0)) := by
    change πP.base _ ∈ (projectiveSpace.{u} n).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) i 0)
    rw [hD]
    exact ⟨hw, πP_chart_mem 0 _⟩
  have hi : homogCoord 0 (ρ₀.toLRSHom.base w) i ≠ 0 :=
    (chart_zero_mem_preimOpen_iff i _).1 hw
  have key := congrArg (fun m' ↦ W.eval w hwD (extVal ρ₀ (extensionSection ρ₀ F e _ m'))) ht
  have e1 : W.eval w hwD (extVal ρ₀ (extensionSection ρ₀ F e _
      (TopCat.Presheaf.restrictOpen t _ hD1))) =
      W.eval w ((Opens.map πP.base).monotone hD1 hwD)
        (extVal ρ₀ (extensionSection ρ₀ F e (stdU i) t)) := by
    erw [extensionSection_res, eval_extVal_res]
  have e2 : W.eval w hwD (extVal ρ₀ (extensionSection ρ₀ F e _
      ((show Γ((projectiveSpace.{u} n).obj.left, _) from
        TopCat.Presheaf.restrictOpen (xDiv (R := ULift.{u} ℂ) i 0) _ hD1) ^ k •
        TopCat.Presheaf.restrictOpen m _ hD0))) =
      W.eval w hwD (ρPull ρ₀ (πP.c.app (op _)
        ((show Γ((projectiveSpace.{u} n).obj.left, _) from
          TopCat.Presheaf.restrictOpen (xDiv (R := ULift.{u} ℂ) i 0) _ hD1) ^ k))) *
      W.eval w ((Opens.map πP.base).monotone hD0 hwD)
        (extVal ρ₀ (extensionSection ρ₀ F e (stdU 0) m)) := by
    rw [extensionSection_smul, map_mul]
    congr 1
    rw [extensionSection_res]
    exact eval_extVal_res _ _ _ _ _
  have key' := e1.symm.trans (key.trans e2)
  have e3 : W.eval w hwD (ρPull ρ₀ (πP.c.app (op _)
      ((show Γ((projectiveSpace.{u} n).obj.left, _) from
        TopCat.Presheaf.restrictOpen (xDiv (R := ULift.{u} ℂ) i 0) _ hD1) ^ k))) =
      (homogCoord 0 (ρ₀.toLRSHom.base w) i)⁻¹ ^ k := by
    dsimp only
    erw [map_pow]
    simp only [ρPull]
    erw [map_pow, map_pow]
    congr 1
    change W.eval w hwD (ρPull ρ₀ (πP.c.app (op _) (LocallyRingedSpace.res _ hD1 _))) = _
    rw [c_app_res]
    exact (eval_ρPull_res ρ₀ _ _ w hwD).trans (eval_ρPull_xDiv ρ₀ w i _)
  have e4 : W.eval (U := ⊤) w trivial (sectionFun ρ₀ F e m) =
      W.eval w ((Opens.map πP.base).monotone hD0 hwD)
        (extVal ρ₀ (extensionSection ρ₀ F e (stdU 0) m)) := eval_presheaf_map _ _ _ _ _
  rw [e3] at key'
  rw [e4, key', ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hi, one_pow, one_mul]


-- @@ L241-243 verbatim
lemma norm_homogCoord_zero_le {z : AnalyticSpace.complexAffineSpace.{u} n} (hz : 1 ≤ vnorm z)
    (i : Fin (n + 1)) : ‖homogCoord 0 z i‖ ≤ vnorm z :=
  (norm_homogCoord_apply_le 0 z i).trans (max_le hz le_rfl)


-- @@ L245-295 verbatim
/-- **Sections of `F` over `U₀` have polynomial growth**: for every `i`, a section over `U₀`
times a power of `X₀ / Xᵢ` extends to `Uᵢ`; sections of the extension over a neighbourhood of a
point of `H_∞` are bounded near it; finitely many of these neighbourhoods cover `H_∞`. -/
theorem hasPolyGrowth_sectionFun
    (hF : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) F)
    (m : Γ(F, stdU 0)) :
    HasPolyGrowth ρ₀ (sectionFun ρ₀ F e m) := by
  classical
  have hqc := @Scheme.Modules.isQuasicoherent_of_isCoherent _ F hF
  -- bounds near the points at infinity
  have hbd : ∀ y ∈ infinity.{u} (n := n), ∃ (i : Fin (n + 1)) (N : Set (projectiveSpaceAn.{u} n)),
      IsOpen N ∧ y ∈ N ∧ N ⊆ preimOpen πP (stdU i) ∧ ∃ (k : ℕ) (C : ℝ),
        ∀ w, (toProj ρ₀).toLRSHom.base w ∈ N → ‖W.eval (U := ⊤) w trivial (sectionFun ρ₀ F e m)‖ ≤
          C * ‖homogCoord 0 (ρ₀.toLRSHom.base w) i‖ ^ k := by
    intro y hy
    obtain ⟨i, v, rfl⟩ := exists_mem_range_chart y
    have hD := basicOpen_xDiv (n := n) (R := ULift.{u} ℂ) i 0
    have hD0 : (projectiveSpace.{u} n).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) i 0) ≤
        stdU 0 := hD.le.trans inf_le_right
    have hD1 : (projectiveSpace.{u} n).obj.left.basicOpen (xDiv (R := ULift.{u} ℂ) i 0) ≤
        stdU i := hD.le.trans inf_le_left
    obtain ⟨k, t, ht⟩ := @IsAffineOpen.exists_restrictOpen_eq_pow_smul _ _
      (isAffineOpen_U (n := n) (R := ULift.{u} ℂ) i) F hqc (xDiv i 0)
      (TopCat.Presheaf.restrictOpen m _ hD0)
    have hyU : chart i v ∈ preimOpen πP.{u} (stdU i) := πP_chart_mem i v
    obtain ⟨N, hN, C, hC⟩ := (extensionSection ρ₀ F e (stdU i) t).2 _ hyU hy
    obtain ⟨N', hN'N, hN'o, hyN'⟩ := mem_nhds_iff.1
      (inter_mem hN ((preimOpen πP.{u} (stdU i)).isOpen.mem_nhds hyU))
    refine ⟨i, N', hN'o, hyN', fun x hx ↦ (hN'N hx).2, k, C, fun w hwN ↦ ?_⟩
    have hw : (toProj ρ₀).toLRSHom.base w ∈ preimOpen πP.{u} (stdU i) := (hN'N hwN).2
    rw [eval_sectionFun_eq ρ₀ F e i m k t hD0 hD1 ht w hw, norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC w hw (hN'N hwN).1) (by positivity)
  choose! I N hNo hyN hNU k C hC using hbd
  obtain ⟨T, hT⟩ := isClosed_infinity.isCompact.elim_finite_subcover
    (fun y : infinity.{u} (n := n) ↦ N y) (fun y ↦ hNo y y.2)
    fun y hy ↦ Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyN y hy⟩
  obtain ⟨R, hR⟩ := exists_forall_chart_zero_mem
    (isOpen_biUnion fun (y : infinity.{u} (n := n)) _ ↦ hNo y y.2) hT
  refine ⟨T.sup fun y ↦ k y, ∑ y ∈ T, |C y|, max R 1, fun w hw ↦ ?_⟩
  set z := ρ₀.toLRSHom.base w
  have hz1 : 1 ≤ vnorm z := (le_max_right _ _).trans hw.le
  obtain ⟨y, hyT, hwy⟩ := Set.mem_iUnion₂.1 (hR z ((le_max_left _ _).trans_lt hw))
  have hbound := hC (y : projectiveSpaceAn.{u} n) y.2 w hwy
  refine hbound.trans ?_
  refine mul_le_mul (le_abs_self _ |>.trans
    (Finset.single_le_sum (f := fun y : infinity.{u} (n := n) ↦ |C y|)
      (fun _ _ ↦ abs_nonneg _) hyT)) ?_ (by positivity)
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_homogCoord_zero_le hz1 _) _).trans
    (pow_le_pow_right₀ hz1 (Finset.le_sup (f := fun y : infinity.{u} (n := n) ↦ k y) hyT))


-- @@ L297-297 verbatim
/-! ### Sections with polynomial growth come from `F` -/


-- @@ L299-300 verbatim
lemma continuous_vnorm : Continuous (vnorm.{u} (n := n)) :=
  continuous_norm (E := ULift.{u} (Fin n) → ℂ)


-- @@ L302-304 verbatim
lemma norm_homogCoord_le (i : Fin (n + 1)) (z : AnalyticSpace.complexAffineSpace.{u} n) :
    ‖homogCoord i z‖ ≤ max 1 (vnorm z) :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k ↦ norm_homogCoord_apply_le i z k


-- @@ L306-308 verbatim
/-- The cocycle `(Xⱼ / Xᵢ)⁻ᵏ` of `𝒪(-k)`. -/
abbrev twistCocycle (k : ℕ) : Cocycle (U n (ULift.{u} ℂ)) :=
  cocycle n (ULift.{u} ℂ) ^ (-(k : ℤ))


-- @@ L310-326 verbatim
/-- On the overlap of `U₀` and `Uᵢ`, the `0`-th component of a section of `𝒪(-k)^an` at `[v]` is
`(vᵢ / v₀)⁻ᵏ` times the `i`-th component. -/
lemma eval_pbComp_zero (k : ℕ) {V : (projectiveSpaceAn.{u} n).Opens}
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) (v : Fin (n + 1) → ℂ) (hv : v ≠ 0)
    (i : Fin (n + 1)) (h0 : v 0 ≠ 0)
    (hp0 : pointOfVec.{u} v hv ∈ V ⊓ preimOpen πP (stdU 0))
    (hpi : pointOfVec.{u} v hv ∈ V ⊓ preimOpen πP (stdU i)) :
    (projectiveSpaceAn.{u} n).eval _ hp0 (pbComp t 0) =
      (v i / v 0) ^ (-(k : ℤ)) * (projectiveSpaceAn.{u} n).eval _ hpi (pbComp t i) := by
  have hp : pointOfVec.{u} v hv ∈
      V ⊓ (preimOpen πP (stdU 0) ⊓ preimOpen πP (stdU i)) := ⟨hp0.1, hp0.2, hpi.2⟩
  have h := congrArg ((projectiveSpaceAn.{u} n).eval _ hp) (pbComp_compat t 0 i)
  rw [AnalyticSpace.eval_restrictOpen, map_mul, AnalyticSpace.eval_restrictOpen,
    AnalyticSpace.eval_restrictOpen] at h
  rw [h]
  congr 1
  exact evπ_cocycle_zpow.{u} (-(k : ℤ)) v hv 0 i h0 ⟨hp0.2, hpi.2⟩


-- @@ L328-332 verbatim
lemma preimage_inf_stdU_zero (V : (projectiveSpaceAn.{u} n).Opens) :
    (Opens.map (toProj ρ₀).toLRSHom.base).obj (V ⊓ preimOpen πP (stdU 0)) =
      (Opens.map (toProj ρ₀).toLRSHom.base).obj V := by
  ext w
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, πP_chart_mem 0 _⟩⟩


-- @@ L334-339 verbatim
/-- The section `t₀ · f` of `𝒪_W` over `ρ⁻¹ V`, for a section `t` of `𝒪(-k)^an` over `V`. -/
def growthVal (f : W.presheaf.obj (op ⊤)) (k : ℕ) {V : (projectiveSpaceAn.{u} n).Opens}
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    W.presheaf.obj (op ((Opens.map (toProj ρ₀).toLRSHom.base).obj V)) :=
  W.presheaf.map (homOfLE (preimage_inf_stdU_zero ρ₀ V).ge).op (ρPull ρ₀ (pbComp t 0)) *
    W.presheaf.map (homOfLE le_top).op f


-- @@ L341-348 verbatim
lemma eval_growthVal (f : W.presheaf.obj (op ⊤)) (k : ℕ) {V : (projectiveSpaceAn.{u} n).Opens}
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) (w : W)
    (hw : (toProj ρ₀).toLRSHom.base w ∈ V) :
    W.eval w hw (growthVal ρ₀ f k t) =
      (projectiveSpaceAn.{u} n).eval _ (show _ ∈ V ⊓ preimOpen πP (stdU 0) from
        ⟨hw, πP_chart_mem 0 _⟩) (pbComp t 0) * W.eval (U := ⊤) w trivial f := by
  rw [growthVal, map_mul, eval_presheaf_map, eval_presheaf_map,
    eval_c_app _ (toProj ρ₀).isCLinear]


-- @@ L350-427 verbatim
/-- **`t₀ · f` is bounded near `H_∞`** if `‖f‖ ≤ C ‖z‖ᵏ` for `‖z‖ > R`: near a point `[u₀]ᵢ` of
`H_∞`, `t₀ = zᵢ⁻ᵏ tᵢ` with `tᵢ` bounded and `‖z‖ ≤ L ‖zᵢ‖`. -/
lemma isBoundedNear_growthVal (f : W.presheaf.obj (op ⊤)) (k : ℕ) (C R : ℝ) (hR : 1 ≤ R)
    (hf : ∀ w : W, R < vnorm (ρ₀.toLRSHom.base w) →
      ‖W.eval (U := ⊤) w trivial f‖ ≤ C * vnorm (ρ₀.toLRSHom.base w) ^ k)
    {V : (projectiveSpaceAn.{u} n).Opens}
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    IsBoundedNear (toProj ρ₀) infinity (growthVal ρ₀ f k t) := by
  intro y hyV hyinf
  obtain ⟨i, u₀, rfl⟩ := exists_mem_range_chart y
  have hu0 : homogCoord i u₀ 0 = 0 := (chart_mem_infinity_iff i u₀).1 hyinf
  have hyi : chart i u₀ ∈ V ⊓ preimOpen πP (stdU i) := ⟨hyV, πP_chart_mem i u₀⟩
  have h1 : ∀ᶠ p in 𝓝 (⟨chart i u₀, hyi⟩ : ↥(V ⊓ preimOpen πP (stdU i))),
      ‖(projectiveSpaceAn.{u} n).eval p.1 p.2 (pbComp t i)‖ <
        ‖(projectiveSpaceAn.{u} n).eval _ hyi (pbComp t i)‖ + 1 :=
    ((projectiveSpaceAn.{u} n).continuousAt_eval (pbComp t i) ⟨_, hyi⟩).norm.eventually
      (gt_mem_nhds (lt_add_one _))
  rw [nhds_subtype_eq_comap, eventually_comap] at h1
  set B := ‖(projectiveSpaceAn.{u} n).eval _ hyi (pbComp t i)‖ + 1
  set L := max 1 (vnorm u₀ + 1)
  have hR0 : 0 < R := one_pos.trans_le hR
  let Q : Set (AnalyticSpace.complexAffineSpace.{u} n) :=
    {u | vnorm u < vnorm u₀ + 1 ∧ ‖homogCoord i u 0‖ < R⁻¹}
  have hQo : IsOpen Q := (isOpen_lt continuous_vnorm continuous_const).inter
    (isOpen_lt (continuous_homogCoord i 0).norm continuous_const)
  have hu₀Q : u₀ ∈ Q := ⟨lt_add_one _, by rw [hu0, norm_zero]; exact inv_pos.2 hR0⟩
  refine ⟨_, inter_mem h1 ((isOpenEmbedding_chart i).isOpenMap.image_mem_nhds
    (hQo.mem_nhds hu₀Q)), B * max C 0 * L ^ k, fun w hw hwN ↦ ?_⟩
  obtain ⟨u, ⟨huL, huR⟩, huw⟩ := hwN.2
  set z := ρ₀.toLRSHom.base w
  have huw' : chart i u = chart 0 z := huw
  obtain ⟨hc0, hτ⟩ := eq_transition_of_chart_eq i huw'
  set c := homogCoord i u 0
  have hv : homogCoord 0 z = c⁻¹ • homogCoord i u := by
    rw [hτ]
    exact homogCoord_zero_transition i u hc0
  have hvi : homogCoord 0 z i = c⁻¹ := by
    rw [hv, Pi.smul_apply, homogCoord_self, smul_eq_mul, mul_one]
  have hv0 : homogCoord 0 z 0 = 1 := homogCoord_self 0 z
  have hcpos : 0 < ‖c⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hc0)
  have hcR : R < ‖c⁻¹‖ := by
    rw [norm_inv]
    exact (lt_inv_comm₀ (norm_pos_iff.2 hc0) hR0).1 huR
  have hzR : R < vnorm z := by
    have h := hcR.trans_le ((congrArg norm hvi).symm.le.trans (norm_homogCoord_apply_le 0 z i))
    rcases lt_max_iff.1 h with h' | h'
    · exact absurd (hR.trans_lt h') (lt_irrefl 1)
    · exact h'
  have hzc : vnorm z ≤ ‖c⁻¹‖ * L := by
    refine (vnorm_le_norm_homogCoord 0 z).trans ?_
    rw [hv, norm_smul]
    refine mul_le_mul_of_nonneg_left ((norm_homogCoord_le i u).trans ?_) (norm_nonneg _)
    exact max_le_max le_rfl huL.le
  have hw1 : (toProj ρ₀).toLRSHom.base w ∈ V ⊓ preimOpen πP (stdU i) :=
    ⟨hw, huw ▸ πP_chart_mem i u⟩
  have hbdt := hwN.1 ⟨_, hw1⟩ rfl
  have hpt : (toProj ρ₀).toLRSHom.base w =
      pointOfVec.{u} (homogCoord 0 z) (homogCoord_ne_zero _ _) :=
    (toProj_base ρ₀ w).trans (chart_eq_pointOfVec 0 z)
  rw [eval_growthVal]
  have hp0 : pointOfVec.{u} (homogCoord 0 z) (homogCoord_ne_zero _ _) ∈
      V ⊓ preimOpen πP (stdU 0) := hpt ▸ ⟨hw, πP_chart_mem 0 _⟩
  have e0 := eval_pbComp_zero k t (homogCoord 0 z) (homogCoord_ne_zero _ _) i
    (by rw [hv0]; exact one_ne_zero) hp0 (hpt ▸ hw1)
  rw [eval_congr_point hpt _ hp0, e0, norm_mul, norm_mul,
    ← eval_congr_point hpt hw1 (hpt ▸ hw1), hvi, hv0, div_one]
  have hk : ‖c⁻¹ ^ (-(k : ℤ))‖ * ‖c⁻¹‖ ^ k = 1 := by
    rw [norm_zpow, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hcpos.ne')]
  calc ‖c⁻¹ ^ (-(k : ℤ))‖ * ‖(projectiveSpaceAn.{u} n).eval _ hw1 (pbComp t i)‖ *
        ‖W.eval (U := ⊤) w trivial f‖
      ≤ ‖c⁻¹ ^ (-(k : ℤ))‖ * B * (max C 0 * (‖c⁻¹‖ * L) ^ k) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hbdt.le (norm_nonneg _)) ?_
          (norm_nonneg _) (by positivity)
        refine (hf w hzR).trans ?_
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (vnorm_nonneg _) hzc _)
          (pow_nonneg (vnorm_nonneg _) _) (le_max_right _ _)
    _ = B * max C 0 * L ^ k * (‖c⁻¹ ^ (-(k : ℤ))‖ * ‖c⁻¹‖ ^ k) := by ring
    _ = B * max C 0 * L ^ k := by rw [hk, mul_one]


-- @@ L429-429 verbatim
section Psi


-- @@ L431-433 verbatim
variable (f : W.presheaf.obj (op ⊤)) (k : ℕ) (C R : ℝ) (hR : 1 ≤ R)
  (hf : ∀ w : W, R < vnorm (ρ₀.toLRSHom.base w) →
    ‖W.eval (U := ⊤) w trivial f‖ ≤ C * vnorm (ρ₀.toLRSHom.base w) ^ k)


-- @@ L435-442 verbatim
lemma growthVal_add {V : (projectiveSpaceAn.{u} n).Opens}
    (t t' : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    growthVal ρ₀ f k (t + t') = growthVal ρ₀ f k t + growthVal ρ₀ f k t' := by
  simp only [growthVal, pbComp_add]
  rw [← add_mul]
  congr 1
  exact (congrArg (W.presheaf.map _).hom
    (map_add (((toProj ρ₀).toLRSHom.c.app _).hom) _ _)).trans (map_add _ _ _)


-- @@ L444-453 verbatim
lemma ρPull_restrict_inf (V : (projectiveSpaceAn.{u} n).Opens)
    (r : (projectiveSpaceAn.{u} n).presheaf.obj (op V)) :
    W.presheaf.map (homOfLE (preimage_inf_stdU_zero ρ₀ V).ge).op
      (ρPull ρ₀ (TopCat.Presheaf.restrictOpen r (V ⊓ preimOpen πP (stdU 0)) inf_le_left)) =
      ρPull ρ₀ r := by
  have := c_app_res (M := W.toLocallyRingedSpace) (toProj ρ₀).toLRSHom
    (inf_le_left : V ⊓ preimOpen πP (stdU 0) ≤ V) r
  refine (congrArg (W.presheaf.map (homOfLE (preimage_inf_stdU_zero ρ₀ V).ge).op).hom
    this).trans ?_
  exact ProjectiveLine.presheaf_map_map_of_le (X := W) _ _ _


-- @@ L455-465 verbatim
lemma growthVal_smul {V : (projectiveSpaceAn.{u} n).Opens}
    (r : (projectiveSpaceAn.{u} n).presheaf.obj (op V))
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    growthVal ρ₀ f k (r • t) = ρPull ρ₀ r * growthVal ρ₀ f k t := by
  simp only [growthVal, pbComp_smul]
  refine (congrArg (· * _) ((congrArg (W.presheaf.map _).hom
    (map_mul (((toProj ρ₀).toLRSHom.c.app _).hom) _ _)).trans
      (map_mul _ _ _))).trans ?_
  rw [mul_assoc]
  congr 1
  exact ρPull_restrict_inf ρ₀ V r


-- @@ L467-482 verbatim
lemma growthVal_res {V V' : (projectiveSpaceAn.{u} n).Opens} (h : V' ≤ V)
    (t : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) :
    growthVal ρ₀ f k (modRes t V' h) = W.presheaf.map (homOfLE ((Opens.map
      (toProj ρ₀).toLRSHom.base).monotone h)).op (growthVal ρ₀ f k t) := by
  simp only [growthVal]
  refine (congrArg₂ (· * ·) ?_ ?_).trans (map_mul _ _ _).symm
  · have := c_app_res (M := W.toLocallyRingedSpace) (toProj ρ₀).toLRSHom
      (inf_le_inf_right _ h : V' ⊓ preimOpen πP (stdU 0) ≤ V ⊓ preimOpen πP (stdU 0)) (pbComp t 0)
    refine (congrArg (W.presheaf.map _).hom this).trans ?_
    change W.presheaf.map _ (W.presheaf.map _ _) = W.presheaf.map _ (W.presheaf.map _ _)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← W.presheaf.map_comp,
      ← W.presheaf.map_comp]
    rfl
  · change _ = W.presheaf.map _ (W.presheaf.map _ f)
    rw [← ConcreteCategory.comp_apply, ← W.presheaf.map_comp]
    rfl


-- @@ L484-495 verbatim
include hR hf in
/-- The section of the extension given by `t₀ · f`. -/
def psiApp (V : (projectiveSpaceAn.{u} n).Opens) :
    (pbTwist πP (twistCocycle.{u} k)).val.obj (op V) →+ (extension ρ₀).val.obj (op V) where
  toFun t := (⟨growthVal ρ₀ f k t, isBoundedNear_growthVal ρ₀ f k C R hR hf t⟩ :
    (boundedSubmodule (toProj ρ₀) infinity).obj (op V))
  map_zero' := Subtype.ext (by
    change growthVal ρ₀ f k 0 = 0
    have h := growthVal_add ρ₀ f k (0 : (pbTwist πP (twistCocycle.{u} k)).val.obj (op V)) 0
    rw [add_zero] at h
    exact left_eq_add.1 h)
  map_add' t t' := Subtype.ext (growthVal_add ρ₀ f k t t')


-- @@ L497-502 verbatim
/-- **The morphism `𝒪(-k)^an ⟶ 𝒞̄` given by a function `f` with `‖f‖ ≤ C ‖z‖ᵏ`**:
`t ↦ t₀ · f`. -/
def psi : pbTwist πP (twistCocycle.{u} k) ⟶ extension ρ₀ :=
  modHomMk (psiApp ρ₀ f k C R hR hf)
    (fun _ r t ↦ Subtype.ext (growthVal_smul ρ₀ f k r t))
    (fun _ _ h t ↦ Subtype.ext (growthVal_res ρ₀ f k h t))


-- @@ L504-515 verbatim
lemma psi_frame :
    W.presheaf.map (homOfLE (preimOpen_stdU_zero ρ₀).ge).op
      (extVal ρ₀ ((psi ρ₀ f k C R hR hf).val.app (op (preimOpen πP (stdU 0)))
        (pfSec (toPushforwardPbTwist πP (twistCocycle.{u} k)) (stdU 0)
          (twistFrame (twistCocycle.{u} k) 0)))) = f := by
  change W.presheaf.map _ (growthVal ρ₀ f k _) = f
  simp only [growthVal]
  erw [pbComp_twistFrame_self]
  refine (congrArg (W.presheaf.map _).hom (congrArg (· * _) ((congrArg (W.presheaf.map _).hom
    (map_one ((toProj ρ₀).toLRSHom.c.app _).hom)).trans (map_one _)))).trans ?_
  rw [one_mul]
  exact ProjectiveLine.presheaf_map_map_of_le (X := W) _ _ f


-- @@ L517-517 verbatim
end Psi


-- @@ L519-568 unexpanded
/-- **Sections with polynomial growth come from `F`**: if `‖f‖ ≤ C ‖z‖ᵏ` near `H_∞`, then
`t ↦ t₀ · f` is a morphism `𝒪(-k)^an ⟶ 𝒞̄ ≅ F^an`, which by GAGA-2 is the analytification of a
morphism `𝒪(-k) ⟶ F`; its value on the frame of `𝒪(-k)` over `U₀` is a section of `F` over `U₀`
mapping to `f`. -/
theorem exists_sectionFun_eq
    (hF : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) F)
    (f : W.presheaf.obj (op ⊤)) (hf : HasPolyGrowth ρ₀ f) :
    ∃ m : Γ(F, stdU 0), sectionFun ρ₀ F e m = f := by
  obtain ⟨k, C, R₀, hf⟩ := hf
  set R := max R₀ 1
  have hR : 1 ≤ R := le_max_right _ _
  have hf' : ∀ w : W, R < vnorm (ρ₀.toLRSHom.base w) →
      ‖W.eval (U := ⊤) w trivial f‖ ≤ C * vnorm (ρ₀.toLRSHom.base w) ^ k :=
    fun w hw ↦ hf w ((le_max_left _ _).trans_lt hw)
  haveI : IsLocallyNoetherian ℙ(n; ULift.{u} ℂ) :=
    LocallyOfFiniteType.isLocallyNoetherian (toSpec n (ULift.{u} ℂ))
  haveI := Scheme.isCoherent_unit (X := ℙ(n; ULift.{u} ℂ))
  have hL : SheafOfModules.IsCoherent
      (R := (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
      (twistUnit (twistCocycle.{u} k)) :=
    isCoherent_twist (SheafOfModules.unit _) (-(k : ℤ))
  obtain ⟨α, hα⟩ := (gaga₂_projectiveSpace n (twistUnit (twistCocycle.{u} k)) F).2
    ((pullbackTwistUnitIso πP (twistCocycle.{u} k) (iSup_U n _)).hom ≫
      psi ρ₀ f k C R hR hf' ≫ e.inv)
  refine ⟨Scheme.Modules.Hom.app (M := twistUnit (twistCocycle.{u} k)) (N := F) α (stdU 0)
    (twistFrame (twistCocycle.{u} k) 0), ?_⟩
  have hnat := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ (stdU 0)
    (twistFrame (twistCocycle.{u} k) 0))
    ((analytificationModulesAdj (projectiveSpace.{u} n)).unit.naturality α)
  have h1 : pfSec (unitη F) (stdU 0) (Scheme.Modules.Hom.app (M := twistUnit (twistCocycle.{u} k))
      (N := F) α (stdU 0) (twistFrame (twistCocycle.{u} k) 0)) =
      ((analytificationModules (projectiveSpace.{u} n)).map α).val.app _
        (twistFrameη πP (twistCocycle.{u} k) 0) := hnat
  rw [sectionFun, extensionSection, h1, hα]
  have h2 : e.hom.val.app (op (preimOpen πP (stdU 0)))
      (((pullbackTwistUnitIso πP (twistCocycle.{u} k) (iSup_U n _)).hom ≫
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


-- @@ L570-570 verbatim
end


-- @@ L572-572 verbatim
end ComplexAnalytic.ProjectiveCompletion
