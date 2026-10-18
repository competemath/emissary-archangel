/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.ProjectiveLineCoherentTheoremA


-- @@ L8-16 verbatim
/-!
# Finitely many generators of `𝒢(n)` near `K × ℙ¹`

Let `𝒢` be a coherent sheaf on `U × ℙ¹ ⊆ P^an` and `K ⊆ U` a nonempty closed box. By relative
Theorem A (`ComplexAnalytic.relProjectiveLine.exists_generates_twistMod`) and the compactness of
`K × ℙ¹`, for `n ≫ 0` there are an open box `B ⊇ K` and finitely many sections of `𝒢(n)` over
`B × ℙ¹` which generate `𝒢(n)` locally on `B × ℙ¹`
(`ComplexAnalytic.relProjectiveLine.exists_finite_generates_twistMod`).
-/


-- @@ L18-18 verbatim
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

-- @@ L19-19 verbatim
open AlgebraicGeometry.LocallyRingedSpace


-- @@ L21-21 verbatim
universe u


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace ComplexAnalytic.relProjectiveLine


-- @@ L27-27 verbatim
open relProjectiveSpaceAn


-- @@ L29-29 verbatim
variable {m : ℕ}


-- @@ L31-33 verbatim
set_option hygiene false in
/-- Sections of `𝒪` over an open of `P^an`. -/
local notation "Γₚ(" W ")" => (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)


-- @@ L35-38 verbatim
/-- The points of `K × ℙ¹` with fibre coordinate of norm `≤ 1` in one of the charts: a compact
set containing `K × ℙ¹`. -/
def tubeCompact (K : Set (Fin m → ℂ)) : Set (relProjectiveSpaceAn.{u} m 1) :=
  chartPt.{u} 0 '' (K ×ˢ Metric.closedBall 0 1) ∪ chartPt.{u} 1 '' (K ×ˢ Metric.closedBall 0 1)


-- @@ L40-43 verbatim
lemma isCompact_tubeCompact {K : Set (Fin m → ℂ)} (hK : IsCompact K) :
    IsCompact (tubeCompact.{u} K) :=
  ((hK.prod (isCompact_closedBall _ _)).image (isOpenEmbedding_chartPt 0).continuous).union
    ((hK.prod (isCompact_closedBall _ _)).image (isOpenEmbedding_chartPt 1).continuous)


-- @@ L45-50 verbatim
lemma tubeCompact_subset_tube {K : Set (Fin m → ℂ)} {B : Opens (Fin m → ℂ)}
    (hKB : K ⊆ B) : tubeCompact.{u} K ⊆ (tube.{u} (N := 1) B : Set _) := by
  rintro _ (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) <;>
  · change baseY _ ∈ B
    rw [baseY_chartPt]
    exact hKB hp.1


-- @@ L52-78 verbatim
/-- **A neighbourhood of `K × ℙ¹` contains `B × ℙ¹` for an open box `B ⊇ K`.** -/
lemma exists_openBox_tube_subset {a b : Fin m → ℂ} {O : (relProjectiveSpaceAn.{u} m 1).Opens}
    (hO : tubeCompact.{u} (Complex.closedBox a b) ⊆ O) {V : Set (Fin m → ℂ)} (hV : IsOpen V)
    (hKV : Complex.closedBox a b ⊆ V) :
    ∃ a' b' : Fin m → ℂ, Complex.closedBox a b ⊆ Complex.openBox a' b' ∧
      Complex.openBox a' b' ⊆ V ∧ tube.{u} (N := 1) (boxOpens a' b') ≤ O := by
  have hA : ∀ i : Fin 2, Complex.closedBox a b ×ˢ Metric.closedBall (0 : ℂ) 1 ⊆
      chartPt.{u} i ⁻¹' O := by
    intro i p hp
    refine hO ?_
    fin_cases i
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  obtain ⟨u₀, v₀, hu₀, -, hKu₀, hv₀, huv₀⟩ := generalized_tube_lemma
    (Complex.isCompact_closedBox a b) (isCompact_closedBall (0 : ℂ) 1)
    (O.isOpen.preimage (isOpenEmbedding_chartPt.{u} (m := m) 0).continuous) (hA 0)
  obtain ⟨u₁, v₁, hu₁, -, hKu₁, hv₁, huv₁⟩ := generalized_tube_lemma
    (Complex.isCompact_closedBox a b) (isCompact_closedBall (0 : ℂ) 1)
    (O.isOpen.preimage (isOpenEmbedding_chartPt.{u} (m := m) 1).continuous) (hA 1)
  obtain ⟨a', b', hab', hsub⟩ := exists_openBox_between ((hu₀.inter hu₁).inter hV)
    (fun x hx ↦ ⟨⟨hKu₀ hx, hKu₁ hx⟩, hKV hx⟩)
  refine ⟨a', b', hab', fun x hx ↦ (hsub hx).2, fun x hx ↦ ?_⟩
  obtain ⟨p, hp1, hp2, hp | hp⟩ := exists_chartPt_norm_le_one hx
  · rw [← hp]
    exact huv₀ ⟨(hsub hp1).1.1, hv₀ (mem_closedBall_zero_iff.2 hp2)⟩
  · rw [← hp]
    exact huv₁ ⟨(hsub hp1).1.2, hv₁ (mem_closedBall_zero_iff.2 hp2)⟩


-- @@ L80-80 verbatim
variable (𝒢 : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.ringSheaf)


-- @@ L82-133 verbatim
/-- **Finitely many generators of `𝒢(n)` near `K × ℙ¹`.** Let `𝒢` be a sheaf of modules on
`P^an = ℂᵐ × ℙ¹` which is coherent over `U × ℙ¹`, and `K ⊆ U` a nonempty closed box. There is `n₀`
such that for every `n ≥ n₀` there are an open box `B` with `K ⊆ B ⊆ U` and finitely many sections
of `𝒢(n)` over `B × ℙ¹` generating `𝒢(n)` locally on `B × ℙ¹`. -/
theorem exists_finite_generates_twistMod {U : Opens (Fin m → ℂ)}
    (h𝒢 : (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) U)).obj 𝒢).IsCoherent)
    {a b : Fin m → ℂ} (hK : Complex.closedBox a b ⊆ U) (hne : (Complex.closedBox a b).Nonempty) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∃ a' b' : Fin m → ℂ,
      Complex.closedBox a b ⊆ Complex.openBox a' b' ∧ Complex.openBox a' b' ⊆ U ∧
      ∃ (I : Type u) (_ : Fintype I)
        (σ : I → (twistMod 𝒢 n).val.obj (op (tube.{u} (N := 1) (boxOpens a' b')))),
        GeneratesLocally σ := by
  classical
  obtain ⟨a₁, b₁, hab₁, hB₁U, n₀, hgen⟩ := exists_generates_twistMod 𝒢 h𝒢 hK hne
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have hCT := tubeCompact_subset_tube.{u} (K := Complex.closedBox a b) (B := boxOpens a₁ b₁) hab₁
  choose I hI σ W hW hxW hgenx using fun x : tubeCompact.{u} (Complex.closedBox a b) ↦
    hgen n hn x (hCT x.2)
  obtain ⟨F, hF⟩ :=
    (isCompact_tubeCompact.{u} (Complex.isCompact_closedBox a b)).elim_finite_subcover
    (fun x ↦ (W x : Set (relProjectiveSpaceAn.{u} m 1))) (fun x ↦ (W x).isOpen)
    (fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩)
  let O : (relProjectiveSpaceAn.{u} m 1).Opens := ⨆ x ∈ F, W x
  have hCO : tubeCompact.{u} (Complex.closedBox a b) ⊆ O := fun y hy ↦ by
    obtain ⟨x, hxF, hyx⟩ := Set.mem_iUnion₂.1 (hF hy)
    exact Opens.mem_iSup.2 ⟨x, Opens.mem_iSup.2 ⟨hxF, hyx⟩⟩
  obtain ⟨a', b', hab', hsub, hBO⟩ := exists_openBox_tube_subset hCO
    (isOpen_openBox a₁ b₁) hab₁
  letI : ∀ x, Fintype (I x) := hI
  have hB₂B₁ : tube.{u} (N := 1) (boxOpens a' b') ≤ tube.{u} (N := 1) (boxOpens a₁ b₁) :=
    fun y hy ↦ hsub hy
  refine ⟨a', b', hab', fun y hy ↦ hB₁U (hsub hy), (Σ x : F, I x.1), inferInstance,
    fun p ↦ modRes (σ p.1.1 p.2) _ hB₂B₁, fun W' hW' τ y hy ↦ ?_⟩
  obtain ⟨x, hxF, hyx⟩ : ∃ x ∈ F, y ∈ W x := by
    have := hBO (hW' hy)
    obtain ⟨x, hx⟩ := Opens.mem_iSup.1 this
    obtain ⟨hxF, hyx⟩ := Opens.mem_iSup.1 hx
    exact ⟨x, hxF, hyx⟩
  obtain ⟨W'', h, hyW'', c, hc⟩ := hgenx x (W' ⊓ W x) inf_le_right
    (modRes τ _ inf_le_left) y ⟨hy, hyx⟩
  refine ⟨W'', h.trans inf_le_left, hyW'', fun p ↦ if hp : p.1.1 = x then
    c (hp ▸ p.2) else 0, ?_⟩
  rw [modRes_res] at hc
  rw [hc, Fintype.sum_sigma, Finset.sum_eq_single (⟨x, hxF⟩ : F)]
  · refine Finset.sum_congr (by rfl) fun i _ ↦ ?_
    simp only [modRes_res, dite_true]
  · intro x' _ hx'
    have hx'' : x'.1 ≠ x := fun h ↦ hx' (Subtype.ext h)
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp only [dif_neg hx'', zero_smul]
  · simp


-- @@ L135-135 verbatim
end ComplexAnalytic.relProjectiveLine


-- @@ L137-137 verbatim
end
