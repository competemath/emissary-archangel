/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.ProjectiveLineCoherentSplitting
import Oka.Analytification.GAGA.ProjectiveLineCoherentTwist
import Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheafLocal


-- @@ L10-29 verbatim
/-!
# Vanishing of `R¹π_* 𝒢(n)` for coherent `𝒢` on `U × ℙ¹`, `n ≫ 0`

Let `𝒢` be a coherent sheaf on `U × ℙ¹ ⊆ P^an` and `K ⊆ U` a closed box. We show that there are
an open box `B₁ ⊇ K` and `n₀` such that `Hᵠ(B × ℙ¹, 𝒢(n)) = 0` for all `q ≥ 1`, `n ≥ n₀` and all
open boxes `B ⊆ B₁` (`ComplexAnalytic.relProjectiveLine.exists_H_tube_twistMod_eq_zero`).

By Cartan's theorems (`ComplexAnalytic.relProjectiveLine.exists_chartGenerators`), `𝒢` is
generated near the chart boxes `V₀ = B₀ × (-S, S)²` and `V₁` (in the chart at infinity) by
sections `s` and `t`, and it is acyclic on `V₀`, `V₁` and `V₀ ∩ V₁`; on `V₀ ∩ V₁` we have
`t = A s` and `s = C t`. The tuples `u₀ = (s, 0)` and `u₁ = (0, t)` then satisfy `M u₀ = u₁` for
the invertible matrix `M = [[1 - CA, -C], [A, 1]]` (`ComplexAnalytic.relProjectiveLine.BundleData`):
`𝒢` is a quotient of the vector bundle `E` with transition function `g = Mᵀ`. For `n ≫ 0`, the
Laurent series argument of `Oka/Analytification/GAGA/ProjectiveLineBundle.lean` splits every
vector valued holomorphic function `h` on the annulus as `h = s₀ - zⁿ g t(z⁻¹)`
(`Complex.ProjectiveLineBundle.exists_vanishing_scaled`); pairing with `u₀` turns this into a
splitting of every section of `𝒢(n)` over `D₀ ∩ D₁`, where `D₀`, `D₁` are discs in the charts
(`ComplexAnalytic.relProjectiveLine.BundleData.exists_split`). By a refinement argument and the
Mayer–Vietoris sequence for `V₀`, `V₁`, `H¹(B × ℙ¹, 𝒢(n)) = 0`.
-/


-- @@ L31-31 verbatim
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

-- @@ L32-32 verbatim
open AlgebraicGeometry.LocallyRingedSpace


-- @@ L34-34 verbatim
universe u


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
namespace AlgebraicGeometry.LocallyRingedSpace


-- @@ L40-40 verbatim
variable {X : LocallyRingedSpace.{u}} (F : SheafOfModules.{u} X.ringSheaf)


-- @@ L42-65 verbatim
/-- Gluing two sections of a sheaf of modules which agree on the intersection. -/
lemma exists_modRes_eq_of_two {W A B : Opens X.toPresheafedSpace} (hW : W ≤ A ⊔ B) (hA : A ≤ W)
    (hB : B ≤ W) (a : F.val.obj (op A)) (b : F.val.obj (op B))
    (hab : modRes a (A ⊓ B) inf_le_left = modRes b (A ⊓ B) inf_le_right) :
    ∃ s : F.val.obj (op W), modRes s A hA = a ∧ modRes s B hB = b := by
  let O : Bool → Opens X.toPresheafedSpace := fun i ↦ bif i then A else B
  let sf : ∀ i, F.val.obj (op (O i)) := fun i ↦ Bool.casesOn (motive := fun i ↦
    F.val.obj (op (O i))) i b a
  have hWO : W ≤ iSup O := by
    refine hW.trans (sup_le ?_ ?_)
    · exact le_iSup O true
    · exact le_iSup O false
  obtain ⟨s, hs, -⟩ := modRes_existsUnique_gluing F O hWO (fun i ↦ by cases i <;> assumption) sf
    (fun i j ↦ by
      cases i <;> cases j
      · rfl
      · change modRes b (B ⊓ A) _ = modRes a (B ⊓ A) _
        have := congrArg (fun x ↦ modRes x (B ⊓ A) (by rw [inf_comm])) hab
        simp only [modRes_res] at this
        exact this.symm
      · change modRes a (A ⊓ B) _ = modRes b (A ⊓ B) _
        exact hab
      · rfl)
  exact ⟨s, hs true, hs false⟩


-- @@ L67-77 verbatim
/-- Sections agreeing on two opens covering `W` are equal. -/
lemma eq_of_modRes_eq_two {W A B : Opens X.toPresheafedSpace} (hW : W ≤ A ⊔ B) (hA : A ≤ W)
    (hB : B ≤ W) (s t : F.val.obj (op W)) (h₁ : modRes s A hA = modRes t A hA)
    (h₂ : modRes s B hB = modRes t B hB) : s = t := by
  let O : Bool → Opens X.toPresheafedSpace := fun i ↦ bif i then A else B
  have hWO : W ≤ iSup O := by
    refine hW.trans (sup_le ?_ ?_)
    · exact le_iSup O true
    · exact le_iSup O false
  exact modRes_eq_of_cover F O hWO (fun i ↦ by cases i <;> assumption) s t
    (fun i ↦ by cases i <;> assumption)


-- @@ L79-81 verbatim
lemma modRes_sub {V W : Opens X.toPresheafedSpace} (h : W ≤ V) (x y : F.val.obj (op V)) :
    modRes (x - y) W h = modRes x W h - modRes y W h :=
  map_sub _ _ _


-- @@ L83-132 verbatim
/-- **Refining a splitting.** Let `D₀ ≤ V₀`, `D₁ ≤ V₁` with `V₀ ∪ V₁ ⊆ D₀ ∪ D₁`. If a section
`σ` over `V₀ ∩ V₁` is, on `D₀ ∩ D₁`, the difference of sections over `D₀` and `D₁`, then it is
the difference of sections over `V₀` and `V₁`. -/
lemma exists_sub_eq_of_refine {V₀ V₁ D₀ D₁ : Opens X.toPresheafedSpace} (hD₀ : D₀ ≤ V₀)
    (hD₁ : D₁ ≤ V₁) (hcov : V₀ ⊔ V₁ ≤ D₀ ⊔ D₁) (σ : F.val.obj (op (V₀ ⊓ V₁)))
    (Φ₀ : F.val.obj (op D₀)) (Φ₁ : F.val.obj (op D₁))
    (h : modRes σ (D₀ ⊓ D₁) (inf_le_inf hD₀ hD₁) =
      modRes Φ₀ (D₀ ⊓ D₁) inf_le_left - modRes Φ₁ (D₀ ⊓ D₁) inf_le_right) :
    ∃ (σ₀ : F.val.obj (op V₀)) (σ₁ : F.val.obj (op V₁)),
      modRes σ₀ (V₀ ⊓ V₁) inf_le_left - modRes σ₁ (V₀ ⊓ V₁) inf_le_right = σ := by
  have hV₀ : V₀ ≤ D₀ ⊔ (V₀ ⊓ V₁ ⊓ D₁) := by
    intro x hx
    rcases Opens.mem_sup.1 (hcov (Opens.mem_sup.2 (Or.inl hx))) with h0 | h1
    · exact Opens.mem_sup.2 (Or.inl h0)
    · exact Opens.mem_sup.2 (Or.inr ⟨⟨hx, hD₁ h1⟩, h1⟩)
  have hV₁ : V₁ ≤ D₁ ⊔ (V₀ ⊓ V₁ ⊓ D₀) := by
    intro x hx
    rcases Opens.mem_sup.1 (hcov (Opens.mem_sup.2 (Or.inr hx))) with h0 | h1
    · exact Opens.mem_sup.2 (Or.inr ⟨⟨hD₀ h0, hx⟩, h0⟩)
    · exact Opens.mem_sup.2 (Or.inl h1)
  have hV₀₁ : V₀ ⊓ V₁ ≤ (V₀ ⊓ V₁ ⊓ D₀) ⊔ (V₀ ⊓ V₁ ⊓ D₁) := by
    intro x hx
    rcases Opens.mem_sup.1 (hcov (Opens.mem_sup.2 (Or.inl hx.1))) with h0 | h1
    · exact Opens.mem_sup.2 (Or.inl ⟨hx, h0⟩)
    · exact Opens.mem_sup.2 (Or.inr ⟨hx, h1⟩)
  -- `h` restricted to a smaller open
  have hres : ∀ (O : Opens X.toPresheafedSpace) (hO : O ≤ D₀ ⊓ D₁),
      modRes σ O (hO.trans (inf_le_inf hD₀ hD₁)) =
        modRes Φ₀ O (hO.trans inf_le_left) - modRes Φ₁ O (hO.trans inf_le_right) := by
    intro O hO
    have e := congrArg (fun x ↦ modRes x O hO) h
    simp only [modRes_res, modRes_sub] at e
    exact e
  obtain ⟨σ₀, hσ₀D, hσ₀V⟩ := exists_modRes_eq_of_two F hV₀ hD₀ (inf_le_left.trans inf_le_left)
    Φ₀ (modRes σ _ inf_le_left + modRes Φ₁ _ inf_le_right) (by
      rw [modRes_add, modRes_res, modRes_res,
        hres _ (le_inf inf_le_left (inf_le_right.trans inf_le_right)), sub_add_cancel])
  obtain ⟨σ₁, hσ₁D, hσ₁V⟩ := exists_modRes_eq_of_two F hV₁ hD₁ (inf_le_left.trans inf_le_right)
    Φ₁ (modRes Φ₀ _ inf_le_right - modRes σ _ inf_le_left) (by
      rw [modRes_sub, modRes_res, modRes_res,
        hres _ (le_inf (inf_le_right.trans inf_le_right) inf_le_left), sub_sub_cancel])
  refine ⟨σ₀, σ₁, eq_of_modRes_eq_two F hV₀₁ inf_le_left inf_le_left _ _ ?_ ?_⟩
  · have e₀ := congrArg (fun x ↦ modRes x (V₀ ⊓ V₁ ⊓ D₀) inf_le_right) hσ₀D
    have e₁ := congrArg (fun x ↦ modRes x (V₀ ⊓ V₁ ⊓ D₀) le_rfl) hσ₁V
    simp only [modRes_res, modRes_self] at e₀ e₁
    rw [modRes_sub, modRes_res, modRes_res, e₀, e₁, sub_sub_cancel]
  · have e₀ := congrArg (fun x ↦ modRes x (V₀ ⊓ V₁ ⊓ D₁) le_rfl) hσ₀V
    have e₁ := congrArg (fun x ↦ modRes x (V₀ ⊓ V₁ ⊓ D₁) inf_le_right) hσ₁D
    simp only [modRes_res, modRes_self] at e₀ e₁
    rw [modRes_sub, modRes_res, modRes_res, e₀, e₁, add_sub_cancel_right]


-- @@ L134-134 verbatim
end AlgebraicGeometry.LocallyRingedSpace


-- @@ L136-136 verbatim
namespace ComplexAnalytic.relProjectiveLine


-- @@ L138-138 verbatim
open relProjectiveSpaceAn Complex.ProjectiveLineBundle Matrix


-- @@ L140-140 verbatim
variable {m : ℕ}


-- @@ L142-144 verbatim
set_option hygiene false in
/-- Sections of `𝒪` over an open of `P^an`. -/
local notation "Γₚ(" W ")" => (relProjectiveSpaceAn.{u} m 1).presheaf.obj (op W)


-- @@ L146-148 verbatim
/-- The chart box `B × (-S, S)²` in the chart `i`. -/
abbrev sqBox (i : Fin 2) (B : Opens (Fin m → ℂ)) (S : ℝ) : (relProjectiveSpaceAn.{u} m 1).Opens :=
  chartBox.{u} i (prodOpens B (squareOpens S))


-- @@ L150-153 verbatim
/-- The intersection of the two chart boxes over `B × (-S, S)²`, in the coordinates of the
chart `0`. -/
abbrev sqOverlap (B : Opens (Fin m → ℂ)) (S : ℝ) : (relProjectiveSpaceAn.{u} m 1).Opens :=
  chartBox.{u} 0 (overlapOpens (prodOpens B (squareOpens S)) (prodOpens B (squareOpens S)))


-- @@ L155-157 verbatim
lemma sqOverlap_eq (B : Opens (Fin m → ℂ)) (S : ℝ) :
    sqOverlap.{u} B S = sqBox 0 B S ⊓ sqBox 1 B S :=
  (chartBox_inf _ _).symm


-- @@ L159-164 verbatim
lemma sqOverlap_le_sqBox (B : Opens (Fin m → ℂ)) (S : ℝ) (i : Fin 2) :
    sqOverlap.{u} B S ≤ sqBox i B S := by
  rw [sqOverlap_eq]
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right


-- @@ L166-166 verbatim
variable (𝒢 : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.ringSheaf)


-- @@ L168-197 verbatim
/-- **Presentation of `𝒢` as a quotient of a vector bundle near `B₀ × ℙ¹`**: generators `s` of
`𝒢` near `sqBox 0 B₀ S` and `t` near `sqBox 1 B₀ S`, related by `t = A s` and `s = C t` on the
intersection of the chart boxes. -/
structure BundleData (B₀ : Opens (Fin m → ℂ)) (S : ℝ) where
  /-- The open on which the generators `s` are defined. -/
  N₀ : (relProjectiveSpaceAn.{u} m 1).Opens
  /-- The open on which the generators `t` are defined. -/
  N₁ : (relProjectiveSpaceAn.{u} m 1).Opens
  hN₀ : sqBox 0 B₀ S ≤ N₀
  hN₁ : sqBox 1 B₀ S ≤ N₁
  /-- The index type of the generators in the chart `0`. -/
  I₀ : Type u
  /-- The index type of the generators in the chart `1`. -/
  I₁ : Type u
  [fintype₀ : Fintype I₀]
  [fintype₁ : Fintype I₁]
  [decEq₀ : DecidableEq I₀]
  [decEq₁ : DecidableEq I₁]
  /-- The generators in the chart `0`. -/
  s : I₀ → 𝒢.val.obj (op N₀)
  /-- The generators in the chart `1`. -/
  t : I₁ → 𝒢.val.obj (op N₁)
  /-- The generators `t` in terms of `s` on the intersection. -/
  A : Matrix I₁ I₀ Γₚ(sqOverlap B₀ S)
  /-- The generators `s` in terms of `t` on the intersection. -/
  C : Matrix I₀ I₁ Γₚ(sqOverlap B₀ S)
  hA : ∀ l, modRes (t l) (sqOverlap B₀ S) ((sqOverlap_le_sqBox B₀ S 1).trans hN₁) =
    ∑ j, A l j • modRes (s j) (sqOverlap B₀ S) ((sqOverlap_le_sqBox B₀ S 0).trans hN₀)
  hC : ∀ j, modRes (s j) (sqOverlap B₀ S) ((sqOverlap_le_sqBox B₀ S 0).trans hN₀) =
    ∑ l, C j l • modRes (t l) (sqOverlap B₀ S) ((sqOverlap_le_sqBox B₀ S 1).trans hN₁)


-- @@ L199-199 verbatim
namespace BundleData


-- @@ L201-201 verbatim
attribute [instance] fintype₀ fintype₁ decEq₀ decEq₁


-- @@ L203-203 verbatim
variable {𝒢} {B₀ : Opens (Fin m → ℂ)} {S : ℝ} (d : BundleData.{u} 𝒢 B₀ S)


-- @@ L205-206 verbatim
lemma sqOverlap_le_N₀ : sqOverlap.{u} B₀ S ≤ d.N₀ :=
  (sqOverlap_le_sqBox B₀ S 0).trans d.hN₀


-- @@ L208-209 verbatim
lemma sqOverlap_le_N₁ : sqOverlap.{u} B₀ S ≤ d.N₁ :=
  (sqOverlap_le_sqBox B₀ S 1).trans d.hN₁


-- @@ L211-212 verbatim
/-- The tuple `u₀ = (s, 0)`. -/
def u₀ : d.I₀ ⊕ d.I₁ → 𝒢.val.obj (op d.N₀) := Sum.elim d.s 0


-- @@ L214-215 verbatim
/-- The tuple `u₁ = (0, t)`. -/
def u₁ : d.I₀ ⊕ d.I₁ → 𝒢.val.obj (op d.N₁) := Sum.elim 0 d.t


-- @@ L217-219 verbatim
/-- The matrix `M = [[1 - CA, -C], [A, 1]]` with `M u₀ = u₁`. -/
def M : Matrix (d.I₀ ⊕ d.I₁) (d.I₀ ⊕ d.I₁) Γₚ(sqOverlap B₀ S) :=
  fromBlocks (1 - d.C * d.A) (-d.C) d.A 1


-- @@ L221-223 verbatim
/-- The inverse `[[1, C], [-A, 1 - AC]]` of `M`. -/
def Minv : Matrix (d.I₀ ⊕ d.I₁) (d.I₀ ⊕ d.I₁) Γₚ(sqOverlap B₀ S) :=
  fromBlocks 1 d.C (-d.A) (1 - d.A * d.C)


-- @@ L225-226 verbatim
lemma Minv_mul_M : d.Minv * d.M = 1 :=
  fromBlocks_mul_fromBlocks_eq_one d.A d.C


-- @@ L228-246 verbatim
/-- **`M u₀ = u₁`** on the intersection of the chart boxes. -/
lemma sum_M_smul_u₀ (b : d.I₀ ⊕ d.I₁) :
    ∑ a, d.M b a • modRes (d.u₀ a) (sqOverlap B₀ S) d.sqOverlap_le_N₀ =
      modRes (d.u₁ b) (sqOverlap B₀ S) d.sqOverlap_le_N₁ := by
  rcases b with j | l
  · simp only [Fintype.sum_sum_type, M, u₀, u₁, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, modRes_zero, smul_zero, Finset.sum_const_zero,
      add_zero]
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm, d.hC j, sub_eq_zero]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [d.hA l, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [smul_smul]
  · simp only [Fintype.sum_sum_type, M, u₀, u₁, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, modRes_zero, smul_zero, Finset.sum_const_zero,
      add_zero]
    rw [d.hA l]


-- @@ L248-251 verbatim
/-- The transition function `g = Mᵀ` of the vector bundle, in the coordinates of the chart
`0`. -/
def G (p : (Fin m → ℂ) × ℂ) : Matrix (d.I₀ ⊕ d.I₁) (d.I₀ ⊕ d.I₁) ℂ :=
  fun a b ↦ f0 (d.M b a) p


-- @@ L253-253 verbatim
end BundleData


-- @@ L255-255 verbatim
/-! ### Disc charts -/


-- @@ L257-259 verbatim
/-- The open disc of radius `r` in `ℂ`. -/
def ballOpens (r : ℝ) : Opens ℂ :=
  ⟨Metric.ball 0 r, Metric.isOpen_ball⟩


-- @@ L261-263 verbatim
/-- The chart disc `B × {‖z‖ < r}` in the chart `i`. -/
abbrev discBox (i : Fin 2) (B : Opens (Fin m → ℂ)) (r : ℝ) : (relProjectiveSpaceAn.{u} m 1).Opens :=
  chartBox.{u} i (prodOpens B (ballOpens r))


-- @@ L265-268 verbatim
/-- The intersection of `discBox 0 B r₀` and `discBox 1 B r₁`, in the coordinates of the chart
`0`: `B` times the annulus `{r₁⁻¹ < ‖z‖ < r₀}`. -/
abbrev discOverlap (B : Opens (Fin m → ℂ)) (r₀ r₁ : ℝ) : (relProjectiveSpaceAn.{u} m 1).Opens :=
  chartBox.{u} 0 (overlapOpens (prodOpens B (ballOpens r₀)) (prodOpens B (ballOpens r₁)))


-- @@ L270-272 verbatim
lemma discOverlap_eq (B : Opens (Fin m → ℂ)) (r₀ r₁ : ℝ) :
    discOverlap.{u} B r₀ r₁ = discBox 0 B r₀ ⊓ discBox 1 B r₁ :=
  (chartBox_inf _ _).symm


-- @@ L274-285 verbatim
lemma mem_overlapOpens_ballOpens {B : Opens (Fin m → ℂ)} {r₀ r₁ : ℝ} (hr₁ : 0 < r₁)
    {p : (Fin m → ℂ) × ℂ} :
    p ∈ overlapOpens (prodOpens B (ballOpens r₀)) (prodOpens B (ballOpens r₁)) ↔
      p.1 ∈ B ∧ p.2 ∈ annulusSet r₀ r₁ := by
  simp only [mem_overlapOpens, mem_prodOpens, ballOpens, annulusSet, Opens.mem_mk,
    Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq, norm_inv]
  constructor
  · rintro ⟨h0, ⟨hB, h1⟩, -, h2⟩
    exact ⟨hB, (inv_lt_comm₀ (norm_pos_iff.2 h0) hr₁).1 h2, h1⟩
  · rintro ⟨hB, h1, h2⟩
    have h0 : 0 < ‖p.2‖ := (inv_pos.2 hr₁).trans h1
    exact ⟨norm_pos_iff.1 h0, ⟨hB, h2⟩, hB, (inv_lt_comm₀ h0 hr₁).2 h1⟩


-- @@ L287-288 verbatim
lemma ballOpens_le_squareOpens {r S : ℝ} (h : r ≤ S) : ballOpens r ≤ squareOpens S :=
  fun _ hz ↦ ball_subset_squareOpens S (Metric.ball_subset_ball h hz)


-- @@ L290-292 verbatim
lemma overlapOpens_mono {S₀ S₁ T₀ T₁ : Opens ((Fin m → ℂ) × ℂ)} (h₀ : S₀ ≤ T₀) (h₁ : S₁ ≤ T₁) :
    overlapOpens S₀ S₁ ≤ overlapOpens T₀ T₁ :=
  fun _ ⟨hp, h0, h1⟩ ↦ ⟨hp, h₀ h0, h₁ h1⟩


-- @@ L294-296 verbatim
lemma prodOpens_mono {B B' : Opens (Fin m → ℂ)} {O O' : Opens ℂ} (hB : B ≤ B') (hO : O ≤ O') :
    prodOpens B O ≤ prodOpens B' O' :=
  fun _ ⟨h1, h2⟩ ↦ ⟨hB h1, hO h2⟩


-- @@ L298-301 verbatim
lemma discOverlap_le_sqOverlap {B B₀ : Opens (Fin m → ℂ)} (hB : B ≤ B₀) {r₀ r₁ S : ℝ}
    (h₀ : r₀ ≤ S) (h₁ : r₁ ≤ S) : discOverlap.{u} B r₀ r₁ ≤ sqOverlap B₀ S :=
  chartBox_mono (overlapOpens_mono (prodOpens_mono hB (ballOpens_le_squareOpens h₀))
    (prodOpens_mono hB (ballOpens_le_squareOpens h₁)))


-- @@ L303-305 verbatim
lemma discBox_le_sqBox (i : Fin 2) {B B₀ : Opens (Fin m → ℂ)} (hB : B ≤ B₀) {r S : ℝ}
    (h : r ≤ S) : discBox.{u} i B r ≤ sqBox i B₀ S :=
  chartBox_mono (prodOpens_mono hB (ballOpens_le_squareOpens h))


-- @@ L307-310 verbatim
lemma discOverlap_le_stdOpen (B : Opens (Fin m → ℂ)) (r₀ r₁ : ℝ) :
    discOverlap.{u} B r₀ r₁ ≤ stdOpen.{u} m 1 0 ⊓ stdOpen.{u} m 1 1 := by
  rw [discOverlap_eq]
  exact inf_le_inf (chartBox_le_stdOpen 0 _) (chartBox_le_stdOpen 1 _)


-- @@ L312-314 verbatim
/-- The transition function `zᵏ` from the chart `1` to the chart `0` of `𝒢(k)`. -/
abbrev zSec (k : ℤ) : Γₚ(stdOpen.{u} m 1 0 ⊓ stdOpen.{u} m 1 1) :=
  (twistModCocycle.{u} m 1 k).g 0 1


-- @@ L316-316 verbatim
namespace BundleData


-- @@ L318-318 verbatim
variable {𝒢} {B₀ : Opens (Fin m → ℂ)} {S : ℝ} (d : BundleData.{u} 𝒢 B₀ S)


-- @@ L320-408 expanded
open scoped AlgebraicGeometry.Scheme.Modules in
/-- **Splitting sections of `𝒢(k)` from a splitting of the vector bundle.** Let
`B ≤ B₀`, `r₀, r₁ ≤ S`, and let `ĥ` be sections of `𝒪` over `D₀ ∩ D₁`, `D₀ = discBox 0 B r₀`,
`D₁ = discBox 1 B r₁`, whose values split as `ĥ = φ₀ - zᵏ g φ₁(z⁻¹)` with `φ₀` holomorphic on
`B × {‖z‖ < r₀}` and `φ₁` on `B × {‖w‖ < r₁}`. Then `∑ ĥₐ u₀ₐ = Φ₀ - zᵏ Φ₁` on `D₀ ∩ D₁` for
sections `Φ₀` of `𝒢` over `D₀` and `Φ₁` over `D₁`. -/
theorem exists_split {B : Opens (Fin m → ℂ)} (hB : B ≤ B₀) {r₀ r₁ : ℝ} (hr₁ : 0 < r₁)
    (hr₀S : r₀ ≤ S) (hr₁S : r₁ ≤ S) (k : ℕ) (ĥ : d.I₀ ⊕ d.I₁ → Γₚ(discOverlap B r₀ r₁))
    (φ₀ φ₁ : (Fin m → ℂ) × ℂ → d.I₀ ⊕ d.I₁ → ℂ)
    (hφ₀ : DifferentiableOn ℂ φ₀ ((B : Set (Fin m → ℂ)) ×ˢ Metric.ball 0 r₀))
    (hφ₁ : DifferentiableOn ℂ φ₁ ((B : Set (Fin m → ℂ)) ×ˢ Metric.ball 0 r₁))
    (hrel :
      ∀ y ∈ B,
        ∀ w ∈ annulusSet r₀ r₁,
          (fun a ↦ f0 (ĥ a) (y, w)) = φ₀ (y, w) - w ^ k • d.G (y, w) *ᵥ φ₁ (y, w⁻¹)) :
    ∃ (ψ₀ : d.I₀ ⊕ d.I₁ → Γₚ(discBox 0 B r₀)) (ψ₁ : d.I₀ ⊕ d.I₁ → Γₚ(discBox 1 B r₁)),
      (∀ a, ∀ p ∈ prodOpens B (ballOpens r₀), f0 (ψ₀ a) p = φ₀ p a) ∧
        (∀ b, ∀ p ∈ prodOpens B (ballOpens r₁), f1 (ψ₁ b) p = φ₁ p b) ∧
          ∑ a,
              ĥ a •
                modRes (d.u₀ a) (discOverlap B r₀ r₁)
                  ((discOverlap_le_sqOverlap hB hr₀S hr₁S).trans d.sqOverlap_le_N₀) =
            modRes (∑ a, ψ₀ a • modRes (d.u₀ a) _ ((discBox_le_sqBox 0 hB hr₀S).trans d.hN₀))
                (discOverlap B r₀ r₁) ((discOverlap_eq B r₀ r₁).le.trans inf_le_left) -
              TopCat.Presheaf.restrictOpen (zSec k) (discOverlap B r₀ r₁)
                  (discOverlap_le_stdOpen B r₀ r₁) •
                modRes (∑ b, ψ₁ b • modRes (d.u₁ b) _ ((discBox_le_sqBox 1 hB hr₁S).trans d.hN₁))
                  (discOverlap B r₀ r₁) ((discOverlap_eq B r₀ r₁).le.trans inf_le_right) :=
  by
  have hO₀ : discOverlap.{u} B r₀ r₁ ≤ discBox 0 B r₀ :=
    (discOverlap_eq B r₀ r₁).le.trans inf_le_left
  have hO₁ : discOverlap.{u} B r₀ r₁ ≤ discBox 1 B r₁ :=
    (discOverlap_eq B r₀ r₁).le.trans inf_le_right
  have hOS : discOverlap.{u} B r₀ r₁ ≤ sqOverlap B₀ S := discOverlap_le_sqOverlap hB hr₀S hr₁S
  have hD₀ : discBox.{u} 0 B r₀ ≤ d.N₀ := (discBox_le_sqBox 0 hB hr₀S).trans d.hN₀
  have hD₁ : discBox.{u} 1 B r₁ ≤ d.N₁ := (discBox_le_sqBox 1 hB hr₁S).trans d.hN₁
  have hSN₀ := d.sqOverlap_le_N₀
  have hSN₁ := d.sqOverlap_le_N₁
  have hOst := discOverlap_le_stdOpen.{u} B r₀ r₁
  choose ψ₀ hψ₀ using fun a ↦
    exists_f0_eq.{u} (prodOpens B (ballOpens r₀)) (fun p ↦ φ₀ p a) ((differentiableOn_pi.1 hφ₀) a)
  choose ψ₁ hψ₁ using fun a ↦
    exists_f1_eq.{u} (prodOpens B (ballOpens r₁)) (fun p ↦ φ₁ p a) ((differentiableOn_pi.1 hφ₁) a)
  refine
    ⟨ψ₀, ψ₁, hψ₀, hψ₁, ?_⟩
      -- the splitting as sections of `𝒪` over the intersection
      
  have key :
    ∀ a,
      ĥ a =
        (TopCat.Presheaf.restrictOpen (ψ₀ a) (discOverlap B r₀ r₁) (by order)) -
          (TopCat.Presheaf.restrictOpen (zSec k) (discOverlap B r₀ r₁) (by order)) *
            ∑ b,
              (TopCat.Presheaf.restrictOpen (d.M b a) (discOverlap B r₀ r₁) (by order)) *
                (TopCat.Presheaf.restrictOpen (ψ₁ b) (discOverlap B r₀ r₁) (by order)) :=
    by
    intro a
    refine eq_of_f0_eq fun p hp ↦ ?_
    rw [mem_overlapOpens_ballOpens hr₁] at hp
    have hpO : chartPt.{u} 0 p ∈ discOverlap B r₀ r₁ :=
      ⟨p, (mem_overlapOpens_ballOpens hr₁).2 hp, rfl⟩
    have h2 : p.2 ≠ 0 := norm_pos_iff.1 ((inv_pos.2 hr₁).trans hp.2.1)
    have hrela := congrFun (hrel p.1 hp.1 p.2 hp.2) a
    simp only [Prod.mk.eta] at hrela
    rw [hrela, f0_sub, f0_mul, f0_sum]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Pi.mul_apply,
      Finset.sum_apply, f0_mul]
    rw [f0_restrictOpen _ _ hpO, f0_restrictOpen _ _ hpO, f0_twistModCocycle (k : ℤ) (hOst hpO)]
    rw [hψ₀ a p ⟨hp.1, Metric.mem_ball.2 (by simpa using hp.2.2)⟩]
    simp only [zpow_natCast]
    congr 2
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [f0_restrictOpen _ _ hpO, f0_restrictOpen _ _ hpO, ← f1_inv_eq_f0 (ψ₁ b) h2,
      hψ₁ b (p.1, p.2⁻¹) ⟨hp.1, ?_⟩]
    · rfl
    · have h0 : 0 < ‖p.2‖ := norm_pos_iff.2 h2
      change p.2⁻¹ ∈ Metric.ball (0 : ℂ) r₁
      rw [Metric.mem_ball, dist_zero_right, norm_inv]
      exact (inv_lt_comm₀ h0 hr₁).2 hp.2.1
  have hMO :
    ∀ b,
      ∑ a,
          (TopCat.Presheaf.restrictOpen (d.M b a) (discOverlap B r₀ r₁) (by order)) •
            modRes (d.u₀ a) (discOverlap B r₀ r₁) (hOS.trans hSN₀) =
        modRes (d.u₁ b) (discOverlap B r₀ r₁) (hOS.trans hSN₁) :=
    by
    intro b
    have e := congrArg (fun x ↦ modRes x (discOverlap B r₀ r₁) hOS) (d.sum_M_smul_u₀ b)
    simp only [modRes_sum, modRes_smul, modRes_res] at e
    exact e
  have e1 :
    ∀ a,
      ĥ a • modRes (d.u₀ a) (discOverlap B r₀ r₁) (hOS.trans hSN₀) =
        (TopCat.Presheaf.restrictOpen (ψ₀ a) (discOverlap B r₀ r₁) (by order)) •
            modRes (d.u₀ a) (discOverlap B r₀ r₁) (hOS.trans hSN₀) -
          ∑ b,
            ((TopCat.Presheaf.restrictOpen (zSec k) (discOverlap B r₀ r₁) (by order)) *
                (TopCat.Presheaf.restrictOpen (ψ₁ b) (discOverlap B r₀ r₁) (by order))) •
              ((TopCat.Presheaf.restrictOpen (d.M b a) (discOverlap B r₀ r₁) (by order)) •
                modRes (d.u₀ a) (discOverlap B r₀ r₁) (hOS.trans hSN₀)) :=
    by
    intro a
    rw [key a, sub_smul, Finset.mul_sum, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [smul_smul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun a _ ↦ e1 a, Finset.sum_sub_distrib, Finset.sum_comm]
  simp_rw [← Finset.smul_sum, hMO]
  rw [modRes_sum, modRes_sum, Finset.smul_sum]
  simp only [modRes_smul, modRes_res, mul_smul]


-- @@ L410-424 verbatim
/-- The transition function `g = Mᵀ` has invertible values on the intersection of the chart
boxes. -/
lemma isUnit_G {p : (Fin m → ℂ) × ℂ}
    (hp : p ∈ overlapOpens (prodOpens B₀ (squareOpens S)) (prodOpens B₀ (squareOpens S))) :
    IsUnit (d.G p) := by
  have hx : chartPt.{u} 0 p ∈ sqOverlap B₀ S := ⟨p, hp, rfl⟩
  set φ := (relProjectiveSpaceAn.{u} m 1).eval (chartPt.{u} 0 p) hx
  have hG : d.G p = (d.M.map φ)ᵀ := by
    funext a b
    simp only [G, transpose_apply, map_apply, φ]
    exact f0_eq_eval _ hx
  have h1 : d.Minv.map φ * d.M.map φ = 1 := by
    rw [← Matrix.map_mul, d.Minv_mul_M, Matrix.map_one _ (map_zero φ) (map_one φ)]
  rw [hG]
  exact (Matrix.isUnit_transpose _).2 (IsUnit.of_mul_eq_one_right _ h1)


-- @@ L426-431 verbatim
/-- The transition function `g = Mᵀ` is holomorphic on the intersection of the chart boxes. -/
lemma differentiableOn_G :
    DifferentiableOn ℂ d.G
      (overlapOpens (prodOpens B₀ (squareOpens S)) (prodOpens B₀ (squareOpens S))) := by
  change DifferentiableOn ℂ (fun p a b ↦ f0 (d.M b a) p) _
  exact differentiableOn_pi.2 fun a ↦ differentiableOn_pi.2 fun b ↦ differentiableOn_f0 (d.M b a)


-- @@ L433-433 verbatim
end BundleData


-- @@ L435-443 verbatim
/-- The generators `g` of `𝒢` over `N` generate the sections of `𝒢` over every open `W ⊆ N` on
which `𝒪` is acyclic, and `𝒢` is acyclic on such `W`. -/
def IsAcyclicGenerating {N : (relProjectiveSpaceAn.{u} m 1).Opens} {I : Type u} [Fintype I]
    (g : I → 𝒢.val.obj (op N)) : Prop :=
  ∀ (W : (relProjectiveSpaceAn.{u} m 1).Opens) (hW : W ≤ N),
    (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj
      (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) q)) →
    (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj 𝒢.toAb) q)) ∧
    ∀ σ : 𝒢.val.obj (op W), ∃ c : I → Γₚ(W), σ = ∑ k, c k • modRes (g k) W hW


-- @@ L445-487 verbatim
/-- **The vector bundle presentation near `K × ℙ¹`.** Let `𝒢` be coherent over `U × ℙ¹`, `K ⊆ U`
a nonempty closed box and `S > 1`. There are an open box `B₀` with `K ⊆ B₀ ⊆ U` and
`BundleData` over `B₀` whose generators are acyclic generating. -/
theorem exists_bundleData {U : Opens (Fin m → ℂ)}
    (h𝒢 : (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) U)).obj 𝒢).IsCoherent)
    {a b : Fin m → ℂ} (hK : Complex.closedBox a b ⊆ U) (hne : (Complex.closedBox a b).Nonempty)
    {S : ℝ} (hS : 1 < S) :
    ∃ a₀ b₀ : Fin m → ℂ, Complex.closedBox a b ⊆ Complex.openBox a₀ b₀ ∧
      Complex.openBox a₀ b₀ ⊆ U ∧ ∃ d : BundleData.{u} 𝒢 (boxOpens a₀ b₀) S,
        IsAcyclicGenerating 𝒢 d.s ∧ IsAcyclicGenerating 𝒢 d.t := by
  classical
  have hS0 : 0 < S := zero_lt_one.trans hS
  obtain ⟨B₀', hKB₀, hB₀U, N₀, hN₀, I₀, _, s, hs⟩ := exists_chartGenerators 𝒢 h𝒢 hK hne hS0 0
  obtain ⟨B₁', hKB₁, hB₁U, N₁, hN₁, I₁, _, t, ht⟩ := exists_chartGenerators 𝒢 h𝒢 hK hne hS0 1
  obtain ⟨a₀, b₀, hab, hsub⟩ := exists_openBox_between (B₀' ⊓ B₁').isOpen
    (fun x hx ↦ ⟨hKB₀ hx, hKB₁ hx⟩)
  have hB₀ : boxOpens a₀ b₀ ≤ B₀' := fun x hx ↦ (hsub hx).1
  have hB₁ : boxOpens a₀ b₀ ≤ B₁' := fun x hx ↦ (hsub hx).2
  have hN₀' : sqBox.{u} 0 (boxOpens a₀ b₀) S ≤ N₀ :=
    (chartBox_mono (prodOpens_mono hB₀ le_rfl)).trans hN₀
  have hN₁' : sqBox.{u} 1 (boxOpens a₀ b₀) S ≤ N₁ :=
    (chartBox_mono (prodOpens_mono hB₁ le_rfl)).trans hN₁
  have hgen₀ : IsAcyclicGenerating 𝒢 s := fun W hW hWa ↦ by
    obtain ⟨h1, h2⟩ := hs W hW hWa
    exact ⟨h1, h2⟩
  have hgen₁ : IsAcyclicGenerating 𝒢 t := fun W hW hWa ↦ by
    obtain ⟨h1, h2⟩ := ht W hW hWa
    exact ⟨h1, h2⟩
  have hov : ∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (sqOverlap.{u} (boxOpens a₀ b₀) S)).obj
        (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) q) := by
    intro q hq
    rw [sqOverlap_eq]
    exact subsingleton_H_chartBox_square_inf a₀ b₀ hS hq
  have hov₀ : sqOverlap.{u} (boxOpens a₀ b₀) S ≤ N₀ :=
    (sqOverlap_le_sqBox _ S 0).trans hN₀'
  have hov₁ : sqOverlap.{u} (boxOpens a₀ b₀) S ≤ N₁ :=
    (sqOverlap_le_sqBox _ S 1).trans hN₁'
  choose A hA using fun l ↦ (hgen₀ _ hov₀ hov).2 (modRes (t l) _ hov₁)
  choose C hC using fun j ↦ (hgen₁ _ hov₁ hov).2 (modRes (s j) _ hov₀)
  exact ⟨a₀, b₀, hab, fun x hx ↦ hB₀U (hB₀ hx),
    ⟨N₀, N₁, hN₀', hN₁', I₀, I₁, s, t, Matrix.of A, Matrix.of C, hA, hC⟩, hgen₀, hgen₁⟩


-- @@ L489-490 verbatim
lemma zero_mem_ballOpens {r : ℝ} (hr : 0 < r) : (0 : ℂ) ∈ ballOpens r :=
  Metric.mem_ball_self hr


-- @@ L492-504 verbatim
lemma ballOpens_or_inv {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr : 1 < r₀ * r₁) (z : ℂ) (hz : z ≠ 0) :
    z ∈ ballOpens r₀ ∨ z⁻¹ ∈ ballOpens r₁ := by
  by_cases h : ‖z‖ < r₀
  · exact Or.inl (by simpa [ballOpens] using h)
  · refine Or.inr ?_
    change z⁻¹ ∈ Metric.ball (0 : ℂ) r₁
    rw [Metric.mem_ball, dist_zero_right, norm_inv]
    push Not at h
    have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    have : r₀⁻¹ < r₁ := by
      rw [inv_lt_iff_one_lt_mul₀ hr₀, mul_comm]
      exact hr
    exact (inv_anti₀ hr₀ h).trans_lt this


-- @@ L506-506 verbatim
namespace BundleData


-- @@ L508-508 verbatim
variable {𝒢} {B₀ : Opens (Fin m → ℂ)} {S : ℝ} (d : BundleData.{u} 𝒢 B₀ S)


-- @@ L510-586 verbatim
/-- **Splitting sections of `𝒢(k)` over the intersection of the chart boxes.** If the
vector-valued holomorphic functions on `B × {l / ρ < ‖z‖ < l ρ}` split along the transition
function `g` of `d` (for twist `k`), then every section of `𝒢(k)` over
`sqBox 0 B S ∩ sqBox 1 B S` is a difference of sections over `sqBox 0 B S` and `sqBox 1 B S`. -/
theorem exists_sub_eq (hs : IsAcyclicGenerating 𝒢 d.s) {B : Opens (Fin m → ℂ)} (hBB₀ : B ≤ B₀)
    (hov : ∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (sqBox.{u} 0 B S ⊓ sqBox 1 B S)).obj
        (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) q))
    (hS : 1 < S) {l ρ : ℝ} (hr₀ : 0 < l * ρ) (hr₁ : 0 < ρ / l) (hr : 1 < l * ρ * (ρ / l))
    (hr₀S : l * ρ ≤ S)
    (hr₁S : ρ / l ≤ S) (k : ℕ)
    (hsplit : ∀ h : (Fin m → ℂ) × ℂ → d.I₀ ⊕ d.I₁ → ℂ,
      DifferentiableOn ℂ h ((B : Set (Fin m → ℂ)) ×ˢ annulusSet (l * ρ) (ρ / l)) →
      ∃ s₀ t : (Fin m → ℂ) × ℂ → d.I₀ ⊕ d.I₁ → ℂ,
        DifferentiableOn ℂ s₀ ((B : Set (Fin m → ℂ)) ×ˢ Metric.ball 0 (l * ρ)) ∧
        DifferentiableOn ℂ t ((B : Set (Fin m → ℂ)) ×ˢ Metric.ball 0 (ρ / l)) ∧
        ∀ z ∈ (B : Set (Fin m → ℂ)), ∀ w ∈ annulusSet (l * ρ) (ρ / l),
          h (z, w) = s₀ (z, w) - w ^ k • d.G (z, w) *ᵥ t (z, w⁻¹))
    (σ : (twistMod 𝒢 k).val.obj (op (sqBox.{u} 0 B S ⊓ sqBox 1 B S))) :
    ∃ (σ₀ : (twistMod 𝒢 k).val.obj (op (sqBox.{u} 0 B S)))
      (σ₁ : (twistMod 𝒢 k).val.obj (op (sqBox.{u} 1 B S))),
      modRes σ₀ _ inf_le_left - modRes σ₁ _ inf_le_right = σ := by
  classical
  have hV₀N : sqBox.{u} 0 B S ≤ d.N₀ := (chartBox_mono (prodOpens_mono hBB₀ le_rfl)).trans d.hN₀
  have hV₀st : sqBox.{u} 0 B S ≤ stdOpen.{u} m 1 0 := chartBox_le_stdOpen 0 _
  have hV₁st : sqBox.{u} 1 B S ≤ stdOpen.{u} m 1 1 := chartBox_le_stdOpen 1 _
  have hW0 : sqBox.{u} 0 B S ⊓ sqBox 1 B S ≤ stdOpen.{u} m 1 0 := inf_le_left.trans hV₀st
  obtain ⟨cf, hcf⟩ := (hs _ (inf_le_left.trans hV₀N) hov).2
    (modTwistSectionsEquiv (N := 𝒢) (twistModCocycle.{u} m 1 k) 0 hW0 σ)
  have hOD : discOverlap.{u} B (l * ρ) (ρ / l) = discBox 0 B (l * ρ) ⊓ discBox 1 B (ρ / l) :=
    discOverlap_eq B _ _
  have hD₀V : discBox.{u} 0 B (l * ρ) ≤ sqBox 0 B S := discBox_le_sqBox 0 le_rfl hr₀S
  have hD₁V : discBox.{u} 1 B (ρ / l) ≤ sqBox 1 B S := discBox_le_sqBox 1 le_rfl hr₁S
  have hOV : discOverlap.{u} B (l * ρ) (ρ / l) ≤ sqBox 0 B S ⊓ sqBox 1 B S :=
    hOD.le.trans (inf_le_inf hD₀V hD₁V)
  let ĥ : d.I₀ ⊕ d.I₁ → Γₚ(discOverlap.{u} B (l * ρ) (ρ / l)) :=
    Sum.elim (fun j ↦ TopCat.Presheaf.restrictOpen (cf j) _ hOV) 0
  have hĥ : DifferentiableOn ℂ (fun p a ↦ f0 (ĥ a) p)
      ((B : Set (Fin m → ℂ)) ×ˢ annulusSet (l * ρ) (ρ / l)) :=
    differentiableOn_pi.2 fun a ↦ (differentiableOn_f0 (ĥ a)).mono fun p hp ↦
      (mem_overlapOpens_ballOpens hr₁).2 hp
  obtain ⟨φ₀, φ₁, hφ₀, hφ₁, hrel⟩ := hsplit _ hĥ
  obtain ⟨ψ₀, ψ₁, -, -, hΦ⟩ := d.exists_split hBB₀ hr₁ hr₀S hr₁S k ĥ φ₀ φ₁ hφ₀ hφ₁
    fun y hy w hw ↦ hrel y hy w hw
  set Φ₀ := ∑ a, ψ₀ a • modRes (d.u₀ a) _ ((discBox_le_sqBox 0 hBB₀ hr₀S).trans d.hN₀)
  set Φ₁ := ∑ b, ψ₁ b • modRes (d.u₁ b) _ ((discBox_le_sqBox 1 hBB₀ hr₁S).trans d.hN₁)
  have hsum : ∑ a, ĥ a • modRes (d.u₀ a) (discOverlap.{u} B (l * ρ) (ρ / l))
      ((discOverlap_le_sqOverlap hBB₀ hr₀S hr₁S).trans d.sqOverlap_le_N₀) =
      modRes (modTwistSectionsEquiv (N := 𝒢) (twistModCocycle.{u} m 1 k) 0 hW0 σ) _ hOV := by
    rw [hcf, modRes_sum, Fintype.sum_sum_type]
    simp only [ĥ, BundleData.u₀, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero, modRes_smul, modRes_res]
  have hD₀st : discBox.{u} 0 B (l * ρ) ≤ stdOpen.{u} m 1 0 := hD₀V.trans hV₀st
  have hD₁st : discBox.{u} 1 B (ρ / l) ≤ stdOpen.{u} m 1 1 := hD₁V.trans hV₁st
  have hWst : discBox.{u} 0 B (l * ρ) ⊓ discBox 1 B (ρ / l) ≤ stdOpen.{u} m 1 0 :=
    inf_le_left.trans hD₀st
  have hWst1 : discBox.{u} 0 B (l * ρ) ⊓ discBox 1 B (ρ / l) ≤ stdOpen.{u} m 1 1 :=
    inf_le_right.trans hD₁st
  obtain ⟨Φ₀', hΦ₀'⟩ : ∃ Φ₀', modTwistSectionsEquiv (N := 𝒢) (twistModCocycle.{u} m 1 k) 0
      hD₀st Φ₀' = Φ₀ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  obtain ⟨Φ₁', hΦ₁'⟩ : ∃ Φ₁', modTwistSectionsEquiv (N := 𝒢) (twistModCocycle.{u} m 1 k) 1
      hD₁st Φ₁' = Φ₁ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  have hkey : modRes σ (discBox 0 B (l * ρ) ⊓ discBox 1 B (ρ / l)) (inf_le_inf hD₀V hD₁V) =
      modRes Φ₀' _ inf_le_left - modRes Φ₁' _ inf_le_right := by
    apply (modTwistSectionsEquiv (N := 𝒢) (twistModCocycle.{u} m 1 k) 0 hWst).injective
    rw [map_sub, modTwistSectionsEquiv_change _ 0 hWst 1 hWst1 (modRes Φ₁' _ _),
      modTwistSectionsEquiv_res _ 0 hW0 (inf_le_inf hD₀V hD₁V) σ,
      modTwistSectionsEquiv_res _ 0 hD₀st inf_le_left Φ₀',
      modTwistSectionsEquiv_res _ 1 hD₁st inf_le_right Φ₁', hΦ₀', hΦ₁']
    have e := congrArg (fun y ↦ modRes y (discBox 0 B (l * ρ) ⊓ discBox 1 B (ρ / l)) hOD.ge) hΦ
    rw [hsum] at e
    simp only [modRes_sub, modRes_smul] at e
    rw [modRes_res, modRes_res, modRes_res, yres_res] at e
    exact e
  refine exists_sub_eq_of_refine (twistMod 𝒢 k) hD₀V hD₁V ?_ σ Φ₀' Φ₁' hkey
  rw [chartBox_square_sup B hS, chartBox_sup B (ballOpens (l * ρ)) (ballOpens (ρ / l))
    (zero_mem_ballOpens hr₀) (zero_mem_ballOpens hr₁) (ballOpens_or_inv hr₀ hr)]


-- @@ L588-588 verbatim
end BundleData


-- @@ L590-659 verbatim
/-- **Vanishing of `R¹π_* 𝒢(n)` for `n ≫ 0`, uniformly in sub-boxes.** Let `𝒢` be a sheaf of
modules on `P^an = ℂᵐ × ℙ¹` which is coherent over `U × ℙ¹`, and `K ⊆ U` a nonempty closed box.
There are an open box `B₁` with `K ⊆ B₁ ⊆ U` and `n₀` such that `Hᵠ(B × ℙ¹, 𝒢(n)) = 0` for all
`q ≥ 1`, `n ≥ n₀` and all open boxes `B ⊆ B₁`. -/
theorem exists_H_tube_twistMod_eq_zero {U : Opens (Fin m → ℂ)}
    (h𝒢 : (((relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.restrictModules
      (tube.{u} (N := 1) U)).obj 𝒢).IsCoherent)
    {a b : Fin m → ℂ} (hK : Complex.closedBox a b ⊆ U) (hne : (Complex.closedBox a b).Nonempty) :
    ∃ a' b' : Fin m → ℂ, Complex.closedBox a b ⊆ Complex.openBox a' b' ∧
      Complex.openBox a' b' ⊆ U ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ a'' b'' : Fin m → ℂ,
        Complex.openBox a'' b'' ⊆ Complex.openBox a' b' → ∀ q : ℕ,
          ∀ x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
            (tube.{u} (N := 1) (boxOpens a'' b''))).obj (twistMod 𝒢 n).toAb) (q + 1), x = 0 := by
  obtain ⟨a₀, b₀, hab₀, hB₀U, d, hs, ht⟩ := exists_bundleData 𝒢 h𝒢 hK hne (S := 2) (by norm_num)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 3 / 2 := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := by rw [hρ]; norm_num
  have hr₀ : 0 < 1 * ρ := by rw [hρ]; norm_num
  have hr₁ : 0 < ρ / 1 := by rw [hρ]; norm_num
  have hr₀S : 1 * ρ ≤ 2 := by rw [hρ]; norm_num
  have hr₁S : ρ / 1 ≤ 2 := by rw [hρ]; norm_num
  have hr : 1 < 1 * ρ * (ρ / 1) := by rw [hρ]; norm_num
  have hann : (boxOpens a₀ b₀ : Set (Fin m → ℂ)) ×ˢ annulusSet (1 * ρ) (ρ / 1) ⊆
      overlapOpens (prodOpens (boxOpens a₀ b₀) (squareOpens 2))
        (prodOpens (boxOpens a₀ b₀) (squareOpens 2)) := fun p hp ↦
    overlapOpens_mono (prodOpens_mono le_rfl (ballOpens_le_squareOpens hr₀S))
      (prodOpens_mono le_rfl (ballOpens_le_squareOpens hr₁S))
      ((mem_overlapOpens_ballOpens hr₁).2 hp)
  obtain ⟨U', hU'o, hKU', hU'U, k₀, hk₀⟩ := exists_vanishing_scaled one_pos hρ1
    (isOpen_openBox a₀ b₀) (d.differentiableOn_G.mono hann) (fun p hp ↦ d.isUnit_G (hann hp))
    (Complex.isCompact_closedBox a b) hab₀
  obtain ⟨a', b', hab', hsub'⟩ := exists_openBox_between hU'o hKU'
  refine ⟨a', b', hab', fun x hx ↦ hB₀U (hU'U (hsub' hx)), k₀, fun n hn a'' b'' hB q ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
  have hk : k₀ ≤ k := by omega
  have hBB₀ : boxOpens a'' b'' ≤ boxOpens a₀ b₀ := fun y hy ↦ hU'U (hsub' (hB hy))
  have hBU' : (boxOpens a'' b'' : Set (Fin m → ℂ)) ⊆ U' := fun y hy ↦ hsub' (hB hy)
  have hsup : sqBox.{u} 0 (boxOpens a'' b'') 2 ⊔ sqBox 1 (boxOpens a'' b'') 2 =
      tube.{u} (N := 1) (boxOpens a'' b'') :=
    chartBox_square_sup _ (by norm_num)
  have hV₀N : sqBox.{u} 0 (boxOpens a'' b'') 2 ≤ d.N₀ :=
    (chartBox_mono (prodOpens_mono hBB₀ le_rfl)).trans d.hN₀
  have hV₁N : sqBox.{u} 1 (boxOpens a'' b'') 2 ≤ d.N₁ :=
    (chartBox_mono (prodOpens_mono hBB₀ le_rfl)).trans d.hN₁
  have hov : ∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (sqBox.{u} 0 (boxOpens a'' b'') 2 ⊓ sqBox 1 (boxOpens a'' b'') 2)).obj
        (relProjectiveSpaceAn.{u} m 1).toLocallyRingedSpace.structureSheafAb) q) :=
    fun q hq ↦ subsingleton_H_chartBox_square_inf a'' b'' (by norm_num) hq
  have H₀ : ∀ q, 0 < q → ∀ y : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (sqBox.{u} 0 (boxOpens a'' b'') 2)).obj (twistMod 𝒢 k).toAb) q, y = 0 := fun q hq y ↦ by
    haveI := subsingleton_H_twistMod 𝒢 k (chartBox_le_stdOpen 0 _)
      ((hs _ hV₀N fun q hq ↦ subsingleton_H_chartBox 0 a'' b'' _ _ hq).1 q hq)
    exact Subsingleton.elim _ _
  have H₁ : ∀ q, 0 < q → ∀ y : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (sqBox.{u} 1 (boxOpens a'' b'') 2)).obj (twistMod 𝒢 k).toAb) q, y = 0 := fun q hq y ↦ by
    haveI := subsingleton_H_twistMod 𝒢 k (chartBox_le_stdOpen 1 _)
      ((ht _ hV₁N fun q hq ↦ subsingleton_H_chartBox 1 a'' b'' _ _ hq).1 q hq)
    exact Subsingleton.elim _ _
  rcases q with _ | q
  · intro x
    refine TopCat.Sheaf.H_one_sup_eq_zero _ hsup (fun σ ↦ ?_) (H₀ 1 one_pos) (H₁ 1 one_pos) x
    exact d.exists_sub_eq hs hBB₀ hov (by norm_num) hr₀ hr₁ hr hr₀S hr₁S k
      (hk₀ k hk _ hBU' (boxOpens a'' b'').isOpen) σ
  · have H₀₁ : ∀ y : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
        (sqBox.{u} 0 (boxOpens a'' b'') 2 ⊓ sqBox 1 (boxOpens a'' b'') 2)).obj
          (twistMod 𝒢 k).toAb) (q + 1), y = 0 := fun y ↦ by
      haveI := subsingleton_H_twistMod 𝒢 k (inf_le_left.trans (chartBox_le_stdOpen 0 _))
        ((hs _ (inf_le_left.trans hV₀N) hov).1 (q + 1) (by omega))
      exact Subsingleton.elim _ _
    exact TopCat.Sheaf.H_sup_eq_zero _ hsup rfl H₀₁ (H₀ (q + 2) (by omega))
      (H₁ (q + 2) (by omega))


-- @@ L661-661 verbatim
end ComplexAnalytic.relProjectiveLine


-- @@ L663-663 verbatim
end
