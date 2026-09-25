module

public import SpherePacking.ModularForms.JacobiTheta.MDifferentiable


-- @@ L5-17 verbatim
/-!
# Jacobi theta identities

This file proves the Jacobi identity `H₂ + H₄ = H₃` and the discriminant identity
`Δ = (H₂ * H₃ * H₄)^2 / 256`.

The proof strategy:
1. Define `g := H₂ + H₄ - H₃` and `f := g²`.
2. Show `f` is a weight-4 level-1 modular form.
3. Show `f` vanishes at `i∞` using the asymptotic lemmas from `Basic.lean`.
4. Apply cusp form vanishing in weight 4 to deduce `f = 0`, hence `g = 0`.
5. Use the weight-12 analogue for `(H₂ * H₃ * H₄)^2` to identify `Δ`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open scoped Real MatrixGroups ModularForm

-- @@ L22-22 verbatim
open UpperHalfPlane hiding I

-- @@ L23-24 verbatim
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups


-- @@ L26-26 verbatim
local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

-- @@ L27-27 verbatim
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n


-- @@ L29-29 verbatim
section JacobiIdentity


-- @@ L31-32 verbatim
/-- The difference `g := H₂ + H₄ - H₃`. -/
noncomputable def jacobi_g : ℍ → ℂ := H₂ + H₄ - H₃


-- @@ L34-35 verbatim
/-- The squared difference `f := g²`. -/
noncomputable def jacobi_f : ℍ → ℂ := jacobi_g ^ 2


-- @@ L37-44 verbatim
/-- S-action on `g`: `g|[2]S = -g`. -/
lemma jacobi_g_S_action : (jacobi_g ∣[(2 : ℤ)] S) = -jacobi_g := by
  change ((H₂ + H₄ - H₃) ∣[(2 : ℤ)] S) = -(H₂ + H₄ - H₃)
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_S_action, H₃_S_action, H₄_S_action]
  ext z
  simp only [Pi.add_apply, Pi.neg_apply]
  ring


-- @@ L46-53 verbatim
/-- T-action on `g`: `g|[2]T = -g`. -/
lemma jacobi_g_T_action : (jacobi_g ∣[(2 : ℤ)] T) = -jacobi_g := by
  change ((H₂ + H₄ - H₃) ∣[(2 : ℤ)] T) = -(H₂ + H₄ - H₃)
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_T_action, H₃_T_action, H₄_T_action]
  ext z
  simp only [Pi.add_apply, Pi.neg_apply]
  ring


-- @@ L55-58 verbatim
/-- Rewrite `jacobi_f` as a pointwise product. -/
lemma jacobi_f_eq_mul : jacobi_f = jacobi_g * jacobi_g := by
  ext
  simp [jacobi_f, sq]


-- @@ L60-63 verbatim
/-- S-invariance of `f`: `f|[4]S = f`, because `g|[2]S = -g`. -/
lemma jacobi_f_S_action : (jacobi_f ∣[(4 : ℤ)] S) = jacobi_f := by
  simp only [jacobi_f_eq_mul, show (4 : ℤ) = 2 + 2 by norm_num,
    mul_slash_SL2 2 2 S _ _, jacobi_g_S_action, neg_mul_neg]


-- @@ L65-68 verbatim
/-- T-invariance of `f`: `f|[4]T = f`, because `g|[2]T = -g`. -/
lemma jacobi_f_T_action : (jacobi_f ∣[(4 : ℤ)] T) = jacobi_f := by
  simp only [jacobi_f_eq_mul, show (4 : ℤ) = 2 + 2 by norm_num,
    mul_slash_SL2 2 2 T _ _, jacobi_g_T_action, neg_mul_neg]


-- @@ L70-72 verbatim
/-- Full `SL₂(ℤ)` invariance of `f` with weight 4. -/
lemma jacobi_f_SL2Z_invariant : ∀ γ : SL(2, ℤ), jacobi_f ∣[(4 : ℤ)] γ = jacobi_f :=
  slashaction_generators_SL2Z jacobi_f 4 jacobi_f_S_action jacobi_f_T_action


-- @@ L74-77 verbatim
/-- `jacobi_f` as a slash-invariant form of weight 4 and level `Γ(1)`. -/
noncomputable def jacobi_f_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 4 where
  toFun := jacobi_f
  slash_action_eq' := slashaction_generators_GL2R jacobi_f 4 jacobi_f_S_action jacobi_f_T_action


-- @@ L79-82 verbatim
/-- `jacobi_g` is holomorphic since `H₂`, `H₃`, and `H₄` are. -/
lemma jacobi_g_MDifferentiable : MDiff jacobi_g := by
  unfold jacobi_g
  fun_prop


-- @@ L84-88 verbatim
/-- `jacobi_f` is holomorphic since `jacobi_g` is. -/
lemma jacobi_f_MDifferentiable : MDiff jacobi_f := by
  unfold jacobi_f
  have _ := jacobi_g_MDifferentiable
  fun_prop


-- @@ L90-91 verbatim
/-- `jacobi_f_SIF` is holomorphic. -/
lemma jacobi_f_SIF_MDifferentiable : MDiff jacobi_f_SIF := jacobi_f_MDifferentiable


-- @@ L93-93 verbatim
end JacobiIdentity


-- @@ L95-101 verbatim
/-!
## Jacobi identity proof

We prove that `g := H₂ + H₄ - H₃ → 0` at `i∞`, hence `f := g² → 0`.
Combined with the dimension-vanishing theorem for weight-4 cusp forms, this proves the Jacobi
identity.
-/


-- @@ L103-106 verbatim
/-- The function `g := H₂ + H₄ - H₃` tends to `0` at `i∞`. -/
theorem jacobi_g_tendsto_atImInfty : Tendsto jacobi_g atImInfty (𝓝 0) := by
  change Tendsto (fun z ↦ H₂ z + H₄ z - H₃ z) atImInfty (𝓝 0)
  tendsto_cont [H₂_tendsto_atImInfty, H₃_tendsto_atImInfty, H₄_tendsto_atImInfty]


-- @@ L108-111 verbatim
/-- The function `f := g²` tends to `0` at `i∞`. -/
theorem jacobi_f_tendsto_atImInfty : Tendsto jacobi_f atImInfty (𝓝 0) := by
  change Tendsto (fun z ↦ jacobi_g z ^ 2) atImInfty (𝓝 0)
  tendsto_cont [jacobi_g_tendsto_atImInfty]


-- @@ L113-115 expanded
private noncomputable def jacobi_f_CF : CuspForm (CongruenceSubgroup.Gamma 1) 4 :=
  cuspFormOfSIFTendstoZero jacobi_f_SIF jacobi_f_SIF_MDifferentiable jacobi_f_tendsto_atImInfty


-- @@ L117-120 verbatim
/-- `jacobi_f = 0` by dimension argument: weight-4 cusp forms vanish. -/
theorem jacobi_f_eq_zero : jacobi_f = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 4 (by norm_num)) jacobi_f_CF)


-- @@ L122-125 verbatim
/-- `jacobi_g = 0` as a function, from `g² = 0`. -/
theorem jacobi_g_eq_zero : jacobi_g = 0 := by
  ext z
  simpa [jacobi_f] using congr_fun jacobi_f_eq_zero z


-- @@ L127-130 verbatim
/-- Jacobi identity: `H₂ + H₄ = H₃` (Blueprint Lemma 6.41). -/
theorem jacobi_identity : H₂ + H₄ = H₃ := by
  ext z
  simpa [jacobi_g, sub_eq_zero] using congr_fun jacobi_g_eq_zero z


-- @@ L132-132 verbatim
private noncomputable def theta_prod : ℍ → ℂ := H₂ * H₃ * H₄


-- @@ L134-140 verbatim
private lemma theta_prod_S_action : (theta_prod ∣[(6 : ℤ)] S) = -theta_prod := by
  simp only [theta_prod, show (6 : ℤ) = (2 + 2) + 2 from by norm_num,
    mul_slash_SL2 (2 + 2) 2 S _ _, mul_slash_SL2 2 2 S _ _,
    H₂_S_action, H₃_S_action, H₄_S_action]
  ext z
  simp [Pi.mul_apply, Pi.neg_apply]
  ring


-- @@ L142-148 verbatim
private lemma theta_prod_T_action : (theta_prod ∣[(6 : ℤ)] T) = -theta_prod := by
  simp only [theta_prod, show (6 : ℤ) = (2 + 2) + 2 from by norm_num,
    mul_slash_SL2 (2 + 2) 2 T _ _, mul_slash_SL2 2 2 T _ _,
    H₂_T_action, H₃_T_action, H₄_T_action]
  ext z
  simp [Pi.mul_apply, Pi.neg_apply]
  ring


-- @@ L150-150 verbatim
private noncomputable def theta_prod_sq : ℍ → ℂ := fun z ↦ (H₂ z * H₃ z * H₄ z) ^ 2


-- @@ L152-154 verbatim
private lemma theta_prod_sq_eq_mul : theta_prod_sq = theta_prod * theta_prod := by
  ext z
  simp [theta_prod_sq, theta_prod, sq, Pi.mul_apply]


-- @@ L156-158 verbatim
private lemma theta_prod_sq_S_action : (theta_prod_sq ∣[(12 : ℤ)] S) = theta_prod_sq := by
  rw [theta_prod_sq_eq_mul, show (12 : ℤ) = 6 + 6 from by norm_num,
    mul_slash_SL2 6 6 S _ _, theta_prod_S_action, neg_mul_neg]


-- @@ L160-162 verbatim
private lemma theta_prod_sq_T_action : (theta_prod_sq ∣[(12 : ℤ)] T) = theta_prod_sq := by
  rw [theta_prod_sq_eq_mul, show (12 : ℤ) = 6 + 6 from by norm_num,
    mul_slash_SL2 6 6 T _ _, theta_prod_T_action, neg_mul_neg]


-- @@ L164-167 verbatim
private lemma theta_prod_sq_SL2Z_invariant :
    ∀ γ : SL(2, ℤ), theta_prod_sq ∣[(12 : ℤ)] γ = theta_prod_sq :=
  slashaction_generators_SL2Z theta_prod_sq 12
    theta_prod_sq_S_action theta_prod_sq_T_action


-- @@ L169-171 verbatim
private lemma theta_prod_sq_MDifferentiable : MDiff theta_prod_sq := by
  change MDiff (fun z ↦ (H₂ z * H₃ z * H₄ z) ^ 2)
  exact ((H₂_SIF_MDifferentiable.mul H₃_SIF_MDifferentiable).mul H₄_SIF_MDifferentiable).pow 2


-- @@ L173-175 verbatim
private lemma theta_prod_sq_tendsto_atImInfty : Tendsto theta_prod_sq atImInfty (𝓝 0) := by
  change Tendsto (fun z ↦ (H₂ z * H₃ z * H₄ z) ^ 2) atImInfty (𝓝 0)
  tendsto_cont [H₂_tendsto_atImInfty, H₃_tendsto_atImInfty, H₄_tendsto_atImInfty]


-- @@ L177-181 verbatim
private noncomputable def theta_prod_sq_SIF :
    SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := theta_prod_sq
  slash_action_eq' := slashaction_generators_GL2R theta_prod_sq 12
    theta_prod_sq_S_action theta_prod_sq_T_action


-- @@ L183-185 verbatim
private noncomputable def theta_prod_sq_CF : CuspForm (CongruenceSubgroup.Gamma 1) 12 :=
  cuspFormOfSIFTendstoZero theta_prod_sq_SIF theta_prod_sq_MDifferentiable
    theta_prod_sq_tendsto_atImInfty


-- @@ L187-188 verbatim
private lemma theta_prod_sq_CF_apply (z : ℍ) :
    theta_prod_sq_CF z = theta_prod_sq z := rfl


-- @@ L190-198 expanded
private lemma theta_prod_sq_proportional :
    ∃ c : ℂ, ∀ z : ℍ, c * ModularForm.discriminant z = theta_prod_sq z :=
  by
  suffices h :
    ∀ f : CuspForm (CongruenceSubgroup.Gamma 1) 12,
      ∃ c : ℂ, ∀ z : ℍ, c * ModularForm.discriminant z = f z
    by
    obtain ⟨c, hc⟩ := h theta_prod_sq_CF
    exact ⟨c, fun z ↦ (hc z).trans (theta_prod_sq_CF_apply z)⟩
  rw [CongruenceSubgroup.Gamma_one_coe_eq_SL]
  intro f
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve f
  exact ⟨c, fun z ↦ by simpa using DFunLike.congr_fun hc z⟩


-- @@ L200-203 verbatim
private lemma Θ₂_div_exp_tendsto :
    Tendsto (fun z : ℍ ↦ Θ₂ z / cexp (π * I * ↑z / 4)) atImInfty (nhds 2) := by
  simp_rw [Θ₂_as_jacobiTheta₂, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  exact jacobiTheta₂_half_mul_apply_tendsto_atImInfty


-- @@ L205-218 verbatim
private lemma H₂_div_exp_tendsto :
    Tendsto (fun z : ℍ ↦ H₂ z / cexp (↑π * I * ↑z)) atImInfty (nhds 16) := by
  have h_eq : ∀ z : ℍ, H₂ z / cexp (↑π * I * ↑z) = (jacobiTheta₂ (↑z / 2) ↑z) ^ 4 := by
    intro z
    rw [H₂, Θ₂_as_jacobiTheta₂, mul_pow]
    have he : cexp (↑π * I * ↑z / 4) ^ 4 = cexp (↑π * I * ↑z) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    rw [he, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  simp_rw [h_eq]
  have h16 : (2 : ℂ) ^ 4 = (16 : ℂ) := by norm_num
  rw [← h16]
  exact jacobiTheta₂_half_mul_apply_tendsto_atImInfty.pow 4


-- @@ L220-262 expanded
lemma Δ_eq_H₂_H₃_H₄ (τ : ℍ) :
    ModularForm.discriminant τ = ((H₂ τ) * (H₃ τ) * (H₄ τ)) ^ 2 / (256 : ℂ) :=
  by
  obtain ⟨c, hc_pw⟩ := theta_prod_sq_proportional
  have hc_eq : c = 256 :=
    by
    have hD_asymp :
      Tendsto (fun z : ℍ ↦ ModularForm.discriminant z / cexp (2 * ↑π * I * ↑z)) atImInfty
        (nhds 1) :=
      by
      have h_eq :
        ∀ z : ℍ,
          ModularForm.discriminant z / cexp (2 * ↑π * I * ↑z) =
            ∏' (n : ℕ), (1 - cexp (2 * ↑π * I * (↑n + 1) * ↑z)) ^ 24 :=
        by
        intro z
        rw [Δ_eq_cexp_prod]
        rw [mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
      simp_rw [h_eq]
      exact Δ_boundedfactor
    have hP_asymp :
      Tendsto (fun z : ℍ ↦ theta_prod_sq z / cexp (2 * ↑π * I * ↑z)) atImInfty (nhds 256) :=
      by
      have h_rewrite :
        ∀ z : ℍ,
          theta_prod_sq z / cexp (2 * ↑π * I * ↑z) =
            (H₂ z / cexp (↑π * I * ↑z)) ^ 2 * (H₃ z) ^ 2 * (H₄ z) ^ 2 :=
        by
        intro z
        have hq : cexp (2 * ↑π * I * ↑z) = cexp (↑π * I * ↑z) ^ 2 :=
          by
          rw [← Complex.exp_nat_mul]
          ring_nf
        simp only [theta_prod_sq]
        rw [hq]
        field_simp
      simp_rw [h_rewrite]
      have : (256 : ℂ) = 16 ^ 2 * 1 ^ 2 * 1 ^ 2 := by norm_num
      rw [this]
      exact
        ((H₂_div_exp_tendsto.pow 2).mul (H₃_tendsto_atImInfty.pow 2)).mul
          (H₄_tendsto_atImInfty.pow 2)
    have h_eq_fns :
      ∀ z : ℍ,
        c * (ModularForm.discriminant z / cexp (2 * ↑π * I * ↑z)) =
          theta_prod_sq z / cexp (2 * ↑π * I * ↑z) :=
      by
      intro z
      rw [← mul_div_assoc, hc_pw]
    have hc_lim :
      Tendsto (fun z : ℍ ↦ c * (ModularForm.discriminant z / cexp (2 * ↑π * I * ↑z))) atImInfty
        (nhds c) :=
      by
      have := hD_asymp.const_mul c
      rwa [mul_one] at this
    exact tendsto_nhds_unique (hc_lim.congr h_eq_fns) hP_asymp
  have h := hc_pw τ
  rw [hc_eq] at h
  simp only [theta_prod_sq] at h
  rw [eq_div_iff (show (256 : ℂ) ≠ 0 by norm_num), mul_comm]
  exact h

