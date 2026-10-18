/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.ProjectiveLineCoherentCartan
import Oka.Geometry.RingedSpace.LocallyRingedSpace.CocycleTwistLocal


-- @@ L9-25 verbatim
/-!
# Twisting sheaves of modules on `P^an` and sections of `𝒪` in the charts of `ℂᵐ × ℙ¹`

For a sheaf of modules `M` on `P^an`, `P = ℙ(N; ℂ[y₀, …, y_{m-1}])`, and `n : ℤ`, the **twist**
`M(n)` (`ComplexAnalytic.relProjectiveSpaceAn.twistMod M n`) is the twist of `M` by the pullback
of the `n`-th power of the standard cocycle `(Xⱼ / Xᵢ)` to the preimages `π⁻¹ Uᵢ` of the standard
charts. On an open `W ⊆ π⁻¹ Uᵢ` it agrees with `M`, as abelian sheaves
(`ComplexAnalytic.relProjectiveSpaceAn.restrictOpenTwistModIso`).

For `N = 1` we describe sections of `𝒪` over opens of the chart `0` (resp. `1`) by the
holomorphic functions `f0 a : (y, z) ↦ a([1 : z]; y)` (resp. `f1 a : (y, w) ↦ a([w : 1]; y)`):
every holomorphic function on an open `S ⊆ ℂᵐ × ℂ` is `f0 a` for a unique section `a` over
`chartBox 0 S` (`ComplexAnalytic.relProjectiveLine.exists_f0_eq`,
`ComplexAnalytic.relProjectiveLine.eq_of_f0_eq`), and similarly in the chart `1`. The transition
function from the chart `1` to the chart `0` of `M(n)` is `zⁿ`
(`ComplexAnalytic.relProjectiveLine.f0_twistModCocycle`).
-/


-- @@ L27-27 verbatim
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

-- @@ L28-28 verbatim
open AlgebraicGeometry.LocallyRingedSpace AlgebraicGeometry.Scheme.Modules


-- @@ L30-30 verbatim
universe u


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace ComplexAnalytic.relProjectiveSpaceAn


-- @@ L36-36 verbatim
open ProjectiveSpace


-- @@ L38-38 verbatim
variable {m N : ℕ}


-- @@ L40-43 verbatim
variable (m N) in
/-- The preimage `π⁻¹ Uᵢ ⊆ P^an` of the standard chart `Uᵢ = D₊(Xᵢ)`. -/
abbrev stdOpen (i : Fin (N + 1)) : (relProjectiveSpaceAn.{u} m N).Opens :=
  preimOpen πL.{u} (U N (RelBase.{u} m) i)


-- @@ L45-46 verbatim
lemma iSup_stdOpen : ⨆ i, stdOpen.{u} m N i = ⊤ :=
  iSup_preimOpen (iSup_U N _)


-- @@ L48-52 verbatim
lemma stdOpen_eq_chartOpens (i : Fin (N + 1)) : stdOpen.{u} m N i = chartOpens i := by
  ext x
  change π m N x ∈ U N (RelBase.{u} m) i ↔ x ∈ Set.range (chartLRS.{u} i).base
  rw [range_chart]
  rfl


-- @@ L54-57 verbatim
variable (m N) in
/-- The cocycle `π^♯ (Xⱼ / Xᵢ)ⁿ` on the `π⁻¹ Uᵢ`. -/
def twistModCocycle (n : ℤ) : ModCocycle (stdOpen.{u} m N) :=
  cocycleComap πL.{u} (cocycle N (RelBase.{u} m) ^ n)


-- @@ L59-62 verbatim
lemma twistModCocycle_add (a b : ℤ) :
    twistModCocycle.{u} m N (a + b) = twistModCocycle m N a * twistModCocycle m N b := by
  rw [twistModCocycle, zpow_add, cocycleComap_mul]
  rfl


-- @@ L64-65 verbatim
lemma twistModCocycle_zero : twistModCocycle.{u} m N 0 = 1 := by
  rw [twistModCocycle, zpow_zero, cocycleComap_one]


-- @@ L67-69 verbatim
lemma twistModCocycle_g (n : ℤ) (i j : Fin (N + 1)) :
    (twistModCocycle.{u} m N n).g i j = pbG πL.{u} (cocycle N (RelBase.{u} m) ^ n) i j :=
  rfl


-- @@ L71-75 verbatim
/-- The twist `M(n)` of a sheaf of modules on `P^an`. -/
abbrev twistMod
    (M : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace.ringSheaf)
    (n : ℤ) : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace.ringSheaf :=
  modTwist M (twistModCocycle m N n)


-- @@ L77-82 verbatim
variable (m N) in
/-- The functor `M ↦ M(n)` on sheaves of modules on `P^an`. -/
abbrev twistModFunctor (n : ℤ) :
    SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace.ringSheaf ⥤
      SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace.ringSheaf :=
  modTwistFunctor (twistModCocycle m N n)


-- @@ L84-89 verbatim
variable (m N) in
/-- `M ↦ M(n)` is an autoequivalence. -/
def twistModEquivalence (n : ℤ) :
    SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace.ringSheaf ≌
      SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace.ringSheaf :=
  modTwistEquivalence (twistModCocycle m N n) iSup_stdOpen


-- @@ L91-92 verbatim
instance (n : ℤ) : (twistModFunctor.{u} m N n).IsEquivalence :=
  (twistModEquivalence m N n).isEquivalence_functor


-- @@ L94-95 verbatim
instance (n : ℤ) : (twistModFunctor.{u} m N n).Additive :=
  Functor.additive_of_preserves_binary_products _


-- @@ L97-97 verbatim
variable (M : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace.ringSheaf)


-- @@ L99-102 verbatim
/-- `M(a)(b) ≅ M(a + b)`. -/
def twistModTwistModIso (a b : ℤ) : twistMod (twistMod M a) b ≅ twistMod M (a + b) :=
  (modTwistFunctorCompIso (twistModCocycle m N a) (twistModCocycle m N b)).app M ≪≫
    (modTwistFunctorCongr (twistModCocycle_add a b).symm).app M


-- @@ L104-106 verbatim
/-- `M(0) ≅ M`. -/
def twistModZeroIso : twistMod M 0 ≅ M :=
  (modTwistFunctorCongr twistModCocycle_zero).app M ≪≫ modTwistOneIso M iSup_stdOpen


-- @@ L108-110 verbatim
/-- `M(a) ≅ M(b)` for `a = b`. -/
def twistModCongr {a b : ℤ} (h : a = b) : twistMod M a ≅ twistMod M b :=
  (modTwistFunctorCongr (congrArg (twistModCocycle m N) h)).app M


-- @@ L112-114 verbatim
/-- **Twists of coherent sheaves on `P^an` are coherent.** -/
theorem isCoherent_twistMod [M.IsCoherent] (n : ℤ) : (twistMod M n).IsCoherent :=
  isCoherent_modTwist M _ iSup_stdOpen


-- @@ L116-132 verbatim
/-- **`M(n)` agrees with `M` on `π⁻¹ Uᵢ`**: for `W ≤ π⁻¹ Uᵢ`, the restrictions of `M(n)` and of
`M` to `W` are isomorphic abelian sheaves (`s ↦ sᵢ`). -/
def restrictOpenTwistModIso (n : ℤ) (W : (relProjectiveSpaceAn.{u} m N).Opens)
    (i : Fin (N + 1)) (hW : W ≤ stdOpen m N i) :
    (TopCat.Sheaf.restrictOpen W).obj (twistMod M n).toAb ≅
      (TopCat.Sheaf.restrictOpen W).obj M.toAb :=
  have hle (V : Opens ((Opens.toTopCat (relProjectiveSpaceAn.{u} m N).toPresheafedSpace).obj W)) :
      W.isOpenEmbedding.isOpenMap.functor.obj V ≤ stdOpen m N i :=
    fun _ ⟨y, _, hy⟩ ↦ hy ▸ hW y.2
  (sheafToPresheaf _ _).preimageIso <| NatIso.ofComponents
    (fun V ↦ AddEquiv.toAddCommGrpIso
      (modTwistSectionsEquiv (N := M) (twistModCocycle m N n) i (hle V.unop)).toAddEquiv)
    (by
      intro V V' h
      ext x
      have h' := (W.isOpenEmbedding.isOpenMap.functor.map h.unop).le
      exact modTwistSectionsEquiv_res (N := M) (twistModCocycle m N n) i (hle V.unop) h' x)


-- @@ L134-140 verbatim
/-- Acyclicity of `M` on `W ≤ π⁻¹ Uᵢ` gives acyclicity of `M(n)` on `W`. -/
lemma subsingleton_H_twistMod (n : ℤ) {W : (relProjectiveSpaceAn.{u} m N).Opens}
    {i : Fin (N + 1)} (hW : W ≤ stdOpen m N i) {q : ℕ}
    (h : Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj M.toAb) q)) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj (twistMod M n).toAb) q) :=
  (TopCat.Sheaf.H.addEquivOfIso (restrictOpenTwistModIso M n W i hW) q).toEquiv
    |>.subsingleton_congr.2 h


-- @@ L142-142 verbatim
end ComplexAnalytic.relProjectiveSpaceAn


-- @@ L144-144 verbatim
namespace ComplexAnalytic.relProjectiveLine


-- @@ L146-146 verbatim
open relProjectiveSpaceAn ProjectiveSpace


-- @@ L148-148 verbatim
variable {m : ℕ}


-- @@ L150-153 verbatim
lemma chartBox_le_stdOpen (i : Fin 2) (S : Opens ((Fin m → ℂ) × ℂ)) :
    chartBox.{u} i S ≤ stdOpen.{u} m 1 i := by
  rw [stdOpen_eq_chartOpens]
  exact chartBox_le_chartOpens i S


-- @@ L155-155 verbatim
/-! ### Sections of `𝒪` in the charts -/


-- @@ L157-157 verbatim
variable {W W' : (relProjectiveSpaceAn.{u} m 1).Opens}


-- @@ L159-161 verbatim
/-- A section of `𝒪` over `W` in the coordinates of the chart `0`: `(y, z) ↦ a([1 : z]; y)`. -/
def f0 (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) (p : (Fin m → ℂ) × ℂ) : ℂ :=
  secFun a (![1, p.2], p.1)


-- @@ L163-165 verbatim
/-- A section of `𝒪` over `W` in the coordinates of the chart `1`: `(y, w) ↦ a([w : 1]; y)`. -/
def f1 (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) (p : (Fin m → ℂ) × ℂ) : ℂ :=
  secFun a (![p.2, 1], p.1)


-- @@ L167-168 verbatim
lemma ne_zero_vec₀ (z : ℂ) : (![1, z] : Fin 2 → ℂ) ≠ 0 :=
  Function.ne_iff.2 ⟨0, by simp⟩


-- @@ L170-171 verbatim
lemma ne_zero_vec₁ (z : ℂ) : (![z, 1] : Fin 2 → ℂ) ≠ 0 :=
  Function.ne_iff.2 ⟨1, by simp⟩


-- @@ L173-175 verbatim
lemma mem_vecCone_of_chartPt_zero {p : (Fin m → ℂ) × ℂ} (hp : chartPt.{u} 0 p ∈ W) :
    ((![1, p.2] : Fin 2 → ℂ), p.1) ∈ vecCone.{u} W :=
  ⟨ne_zero_vec₀ p.2, by rw [← chartPt_zero_eq]; exact hp⟩


-- @@ L177-179 verbatim
lemma mem_vecCone_of_chartPt_one {p : (Fin m → ℂ) × ℂ} (hp : chartPt.{u} 1 p ∈ W) :
    ((![p.2, 1] : Fin 2 → ℂ), p.1) ∈ vecCone.{u} W :=
  ⟨ne_zero_vec₁ p.2, by rw [← chartPt_one_eq]; exact hp⟩


-- @@ L181-184 verbatim
lemma f0_add (a b : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) :
    f0 (a + b) = f0 a + f0 b := by
  funext p
  simp [f0, secFun_add]


-- @@ L186-189 verbatim
lemma f0_mul (a b : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) :
    f0 (a * b) = f0 a * f0 b := by
  funext p
  simp [f0, secFun_mul]


-- @@ L191-196 verbatim
lemma f0_sub (a b : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) :
    f0 (a - b) = f0 a - f0 b := by
  have h := f0_add (a - b) b
  rw [sub_add_cancel] at h
  rw [h]
  ring


-- @@ L198-200 verbatim
lemma f0_one {p : (Fin m → ℂ) × ℂ} (hp : chartPt.{u} 0 p ∈ W) :
    f0 (1 : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) p = 1 := by
  rw [f0, secFun_of_mem _ (ne_zero_vec₀ p.2) (by rw [← chartPt_zero_eq]; exact hp), map_one]


-- @@ L202-204 verbatim
lemma f0_zero : f0 (0 : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) = 0 := by
  funext p
  simp [f0, secFun_zero]


-- @@ L206-212 verbatim
lemma f0_sum {ι : Type*} (s : Finset ι)
    (a : ι → (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)) :
    f0 (∑ i ∈ s, a i) = ∑ i ∈ s, f0 (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [f0_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, f0_add, ih]


-- @@ L214-218 verbatim
lemma f0_restrictOpen (h : W' ≤ W) (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W))
    {p : (Fin m → ℂ) × ℂ} (hp : chartPt.{u} 0 p ∈ W') :
    f0 (TopCat.Presheaf.restrictOpen a W' h) p = f0 a p := by
  rw [f0, secFun_restrictOpen, Set.indicator_of_mem (mem_vecCone_of_chartPt_zero hp)]
  rfl


-- @@ L220-224 verbatim
lemma f1_restrictOpen (h : W' ≤ W) (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W))
    {p : (Fin m → ℂ) × ℂ} (hp : chartPt.{u} 1 p ∈ W') :
    f1 (TopCat.Presheaf.restrictOpen a W' h) p = f1 a p := by
  rw [f1, secFun_restrictOpen, Set.indicator_of_mem (mem_vecCone_of_chartPt_one hp)]
  rfl


-- @@ L226-232 verbatim
/-- On the overlap of the charts, `f1 a (y, z⁻¹) = f0 a (y, z)`. -/
lemma f1_inv_eq_f0 (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W))
    {p : (Fin m → ℂ) × ℂ} (hp : p.2 ≠ 0) : f1 a (p.1, p.2⁻¹) = f0 a p := by
  rw [f1, f0, ← secFun_smul a _ p.1 hp]
  congr 2
  funext k
  fin_cases k <;> simp [hp]


-- @@ L234-240 verbatim
/-- The value of the transition function `(twistModCocycle n).g 0 1` of `M(n)` in the chart `0`
is `zⁿ`. -/
lemma f0_twistModCocycle (n : ℤ) {p : (Fin m → ℂ) × ℂ}
    (hp : chartPt.{u} 0 p ∈ stdOpen.{u} m 1 0 ⊓ stdOpen.{u} m 1 1) :
    f0 ((twistModCocycle.{u} m 1 n).g 0 1) p = p.2 ^ n := by
  rw [f0, twistModCocycle_g, secFun_pbG n 0 1 (mem_vecCone_of_chartPt_zero hp)]
  simp


-- @@ L242-247 verbatim
/-- The value `f0 a p` is the value of `a` at the point `chartPt 0 p`. -/
lemma f0_eq_eval (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W))
    {p : (Fin m → ℂ) × ℂ} (hp : chartPt.{u} 0 p ∈ W) :
    f0 a p = (relProjectiveSpaceAn.{u} m 1).eval (chartPt.{u} 0 p) hp a := by
  rw [f0, secFun_of_mem a (ne_zero_vec₀ p.2) (by rw [← chartPt_zero_eq]; exact hp)]
  exact eval_congr_point (chartPt_zero_eq p).symm _ _ a


-- @@ L249-254 verbatim
/-- The value `f1 a p` is the value of `a` at the point `chartPt 1 p`. -/
lemma f1_eq_eval (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W))
    {p : (Fin m → ℂ) × ℂ} (hp : chartPt.{u} 1 p ∈ W) :
    f1 a p = (relProjectiveSpaceAn.{u} m 1).eval (chartPt.{u} 1 p) hp a := by
  rw [f1, secFun_of_mem a (ne_zero_vec₁ p.2) (by rw [← chartPt_one_eq]; exact hp)]
  exact eval_congr_point (chartPt_one_eq p).symm _ _ a


-- @@ L256-275 verbatim
/-- Sections over `chartBox 0 S` are determined by their functions in the chart `0`. -/
lemma eq_of_f0_eq {S : Opens ((Fin m → ℂ) × ℂ)}
    {a b : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (chartBox.{u} 0 S))}
    (h : ∀ p ∈ S, f0 a p = f0 b p) : a = b := by
  refine eq_of_secFun fun q hq ↦ ?_
  obtain ⟨p, hpS, hp⟩ := hq.2
  have h0 : q.1 0 ≠ 0 := by
    have := (mem_range_chart_pointOfVec_iff q.1 hq.1 q.2 0).1 (hp ▸ ⟨cpt p, rfl⟩)
    exact this
  have hq' : pointOfVec.{u} q.1 hq.1 q.2 = chartPt.{u} 0 (q.2, q.1 1 / q.1 0) :=
    pointOfVec_eq_chartPt_zero q.1 hq.1 q.2 h0
  have hpq : p = (q.2, q.1 1 / q.1 0) := chartPt_injective 0 (hp.trans hq')
  have hvec : (q.1 0)⁻¹ • q.1 = ![1, q.1 1 / q.1 0] := by
    funext k
    fin_cases k <;> simp [h0, div_eq_inv_mul]
  have e (c : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (chartBox.{u} 0 S))) :
      secFun c q = f0 c (q.2, q.1 1 / q.1 0) := by
    rw [f0, ← hvec, secFun_smul c q.1 q.2 (inv_ne_zero h0)]
  rw [e, e, ← hpq]
  exact h p hpS


-- @@ L277-296 verbatim
/-- Sections over `chartBox 1 S` are determined by their functions in the chart `1`. -/
lemma eq_of_f1_eq {S : Opens ((Fin m → ℂ) × ℂ)}
    {a b : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (chartBox.{u} 1 S))}
    (h : ∀ p ∈ S, f1 a p = f1 b p) : a = b := by
  refine eq_of_secFun fun q hq ↦ ?_
  obtain ⟨p, hpS, hp⟩ := hq.2
  have h1 : q.1 1 ≠ 0 := by
    have := (mem_range_chart_pointOfVec_iff q.1 hq.1 q.2 1).1 (hp ▸ ⟨cpt p, rfl⟩)
    exact this
  have hq' : pointOfVec.{u} q.1 hq.1 q.2 = chartPt.{u} 1 (q.2, q.1 0 / q.1 1) :=
    pointOfVec_eq_chartPt_one q.1 hq.1 q.2 h1
  have hpq : p = (q.2, q.1 0 / q.1 1) := chartPt_injective 1 (hp.trans hq')
  have hvec : (q.1 1)⁻¹ • q.1 = ![q.1 0 / q.1 1, 1] := by
    funext k
    fin_cases k <;> simp [h1, div_eq_inv_mul]
  have e (c : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (chartBox.{u} 1 S))) :
      secFun c q = f1 c (q.2, q.1 0 / q.1 1) := by
    rw [f1, ← hvec, secFun_smul c q.1 q.2 (inv_ne_zero h1)]
  rw [e, e, ← hpq]
  exact h p hpS


-- @@ L298-335 verbatim
/-- **Holomorphic functions on `S ⊆ ℂᵐ × ℂ` are sections of `𝒪` over `chartBox 0 S`.** -/
lemma exists_f0_eq (S : Opens ((Fin m → ℂ) × ℂ)) (F : (Fin m → ℂ) × ℂ → ℂ)
    (hF : DifferentiableOn ℂ F S) :
    ∃ a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (chartBox.{u} 0 S)),
      ∀ p ∈ S, f0 a p = F p := by
  have hW : ∀ y ∈ chartBox.{u} 0 S, y ∈ Set.range (chartLRS.{u} (m := m) (N := 1) 0).base := by
    rintro _ ⟨p, -, rfl⟩
    exact ⟨cpt p, rfl⟩
  have hcone : ∀ q ∈ vecCone.{u} (chartBox.{u} 0 S), q.1 0 ≠ 0 ∧ (q.2, q.1 1 / q.1 0) ∈ S := by
    intro q hq
    obtain ⟨p, hpS, hp⟩ := hq.2
    have h0 : q.1 0 ≠ 0 :=
      (mem_range_chart_pointOfVec_iff q.1 hq.1 q.2 0).1 (hp ▸ ⟨cpt p, rfl⟩)
    have hpq : p = (q.2, q.1 1 / q.1 0) :=
      chartPt_injective 0 (hp.trans (pointOfVec_eq_chartPt_zero q.1 hq.1 q.2 h0))
    exact ⟨h0, hpq ▸ hpS⟩
  obtain ⟨a, ha⟩ := exists_secFun_eq (N := 1) 0 hW
    (fun q ↦ F (q.2, q.1 1 / q.1 0)) (by
      intro q hq
      obtain ⟨h0, hS⟩ := hcone q hq
      refine (DifferentiableAt.comp q ?_ ?_).differentiableWithinAt
      · exact (hF _ hS).differentiableAt (S.isOpen.mem_nhds hS)
      · have hc : ∀ k : Fin 2, DifferentiableAt ℂ
            (fun q : (Fin 2 → ℂ) × (Fin m → ℂ) ↦ q.1 k) q :=
          fun k ↦ DifferentiableAt.comp (g := fun v : Fin 2 → ℂ ↦ v k) q
            (differentiableAt_apply k q.1) differentiableAt_fst
        have hd : DifferentiableAt ℂ
            (fun q : (Fin 2 → ℂ) × (Fin m → ℂ) ↦ q.1 1 / q.1 0) q := by
          simp_rw [div_eq_mul_inv]
          exact (hc 1).mul ((hc 0).inv h0)
        exact differentiableAt_snd.prodMk hd)
    (by
      intro q hq c hc
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_div_mul_left _ _ hc])
  refine ⟨a, fun p hp ↦ ?_⟩
  rw [f0, ha _ (mem_vecCone_of_chartPt_zero ⟨p, hp, rfl⟩)]
  simp


-- @@ L337-374 verbatim
/-- **Holomorphic functions on `S ⊆ ℂᵐ × ℂ` are sections of `𝒪` over `chartBox 1 S`.** -/
lemma exists_f1_eq (S : Opens ((Fin m → ℂ) × ℂ)) (F : (Fin m → ℂ) × ℂ → ℂ)
    (hF : DifferentiableOn ℂ F S) :
    ∃ a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (chartBox.{u} 1 S)),
      ∀ p ∈ S, f1 a p = F p := by
  have hW : ∀ y ∈ chartBox.{u} 1 S, y ∈ Set.range (chartLRS.{u} (m := m) (N := 1) 1).base := by
    rintro _ ⟨p, -, rfl⟩
    exact ⟨cpt p, rfl⟩
  have hcone : ∀ q ∈ vecCone.{u} (chartBox.{u} 1 S), q.1 1 ≠ 0 ∧ (q.2, q.1 0 / q.1 1) ∈ S := by
    intro q hq
    obtain ⟨p, hpS, hp⟩ := hq.2
    have h1 : q.1 1 ≠ 0 :=
      (mem_range_chart_pointOfVec_iff q.1 hq.1 q.2 1).1 (hp ▸ ⟨cpt p, rfl⟩)
    have hpq : p = (q.2, q.1 0 / q.1 1) :=
      chartPt_injective 1 (hp.trans (pointOfVec_eq_chartPt_one q.1 hq.1 q.2 h1))
    exact ⟨h1, hpq ▸ hpS⟩
  obtain ⟨a, ha⟩ := exists_secFun_eq (N := 1) 1 hW
    (fun q ↦ F (q.2, q.1 0 / q.1 1)) (by
      intro q hq
      obtain ⟨h1, hS⟩ := hcone q hq
      refine (DifferentiableAt.comp q ?_ ?_).differentiableWithinAt
      · exact (hF _ hS).differentiableAt (S.isOpen.mem_nhds hS)
      · have hc : ∀ k : Fin 2, DifferentiableAt ℂ
            (fun q : (Fin 2 → ℂ) × (Fin m → ℂ) ↦ q.1 k) q :=
          fun k ↦ DifferentiableAt.comp (g := fun v : Fin 2 → ℂ ↦ v k) q
            (differentiableAt_apply k q.1) differentiableAt_fst
        have hd : DifferentiableAt ℂ
            (fun q : (Fin 2 → ℂ) × (Fin m → ℂ) ↦ q.1 0 / q.1 1) q := by
          simp_rw [div_eq_mul_inv]
          exact (hc 0).mul ((hc 1).inv h1)
        exact differentiableAt_snd.prodMk hd)
    (by
      intro q hq c hc
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_div_mul_left _ _ hc])
  refine ⟨a, fun p hp ↦ ?_⟩
  rw [f1, ha _ (mem_vecCone_of_chartPt_one ⟨p, hp, rfl⟩)]
  simp


-- @@ L376-388 verbatim
/-- The function of a section in the chart `0` is holomorphic. -/
lemma differentiableOn_f0 {S : Opens ((Fin m → ℂ) × ℂ)}
    (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (chartBox.{u} 0 S))) :
    DifferentiableOn ℂ (f0 a) S := by
  intro p hp
  have hmem := mem_vecCone_of_chartPt_zero (W := chartBox.{u} 0 S) ⟨p, hp, rfl⟩
  have hd := (differentiableOn_secFun a _ hmem).differentiableAt (isOpen_vecCone.mem_nhds hmem)
  refine (DifferentiableAt.comp p hd ?_).differentiableWithinAt
  refine DifferentiableAt.prodMk ?_ differentiableAt_fst
  refine differentiableAt_pi.2 fun k ↦ ?_
  fin_cases k
  · exact differentiableAt_const _
  · exact differentiableAt_snd


-- @@ L390-402 verbatim
/-- The function of a section in the chart `1` is holomorphic. -/
lemma differentiableOn_f1 {S : Opens ((Fin m → ℂ) × ℂ)}
    (a : (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op (chartBox.{u} 1 S))) :
    DifferentiableOn ℂ (f1 a) S := by
  intro p hp
  have hmem := mem_vecCone_of_chartPt_one (W := chartBox.{u} 1 S) ⟨p, hp, rfl⟩
  have hd := (differentiableOn_secFun a _ hmem).differentiableAt (isOpen_vecCone.mem_nhds hmem)
  refine (DifferentiableAt.comp p hd ?_).differentiableWithinAt
  refine DifferentiableAt.prodMk ?_ differentiableAt_fst
  refine differentiableAt_pi.2 fun k ↦ ?_
  fin_cases k
  · exact differentiableAt_snd
  · exact differentiableAt_const _


-- @@ L404-404 verbatim
end ComplexAnalytic.relProjectiveLine


-- @@ L406-406 verbatim
end
