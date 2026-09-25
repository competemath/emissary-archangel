module

public import SpherePacking.ModularForms.JacobiTheta.Basic


-- @@ L5-10 verbatim
/-!
# Jacobi theta differentiability

This file contains the `MDiff` results for the Jacobi theta functions and the resulting modular
form constructions `H₂_MF`, `H₃_MF`, and `H₄_MF`.
-/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
open scoped Real MatrixGroups ModularForm

-- @@ L15-15 verbatim
open UpperHalfPlane hiding I

-- @@ L16-17 verbatim
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups


-- @@ L19-19 verbatim
local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

-- @@ L20-20 verbatim
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n


-- @@ L22-22 verbatim
section H_MDifferentiable


-- @@ L24-58 verbatim
lemma H₂_SIF_MDifferentiable : MDiff H₂_SIF := by
  intro τ
  suffices h_diff : DifferentiableAt ℂ (↑ₕH₂) (τ : ℂ) by
    have : (H₂ ∘ ↑ofComplex) ∘ UpperHalfPlane.coe = H₂_SIF := by
      ext x
      simp [H₂_SIF, ofComplex_apply]
    rw [← this]
    exact h_diff.mdifferentiableAt.comp τ τ.mdifferentiable_coe
  have hU : {z : ℂ | 0 < z.im} ∈ 𝓝 (τ : ℂ) := isOpen_upperHalfPlaneSet.mem_nhds τ.2
  let F : ℂ → ℂ := (fun t ↦ cexp (((π : ℂ) * I / 4) * t) * jacobiTheta₂ (t / 2) t) ^ 4
  have hF : DifferentiableAt ℂ F (τ : ℂ) := by
    have h_exp : DifferentiableAt ℂ (fun t : ℂ ↦ cexp ((π * I / 4) * t)) (τ : ℂ) := by
      have : DifferentiableAt ℂ (fun t : ℂ ↦ (π * I / 4) * t) (τ : ℂ) :=
        (differentiableAt_id.const_mul ((π : ℂ) * I / 4))
      exact this.cexp
    have h_theta : DifferentiableAt ℂ (fun t : ℂ ↦ jacobiTheta₂ (t / 2) t) (τ : ℂ) := by
      let f : ℂ → ℂ × ℂ := fun t : ℂ ↦ (t / 2, t)
      let g : ℂ × ℂ → ℂ := fun p ↦ jacobiTheta₂ p.1 p.2
      have hg : DifferentiableAt ℂ g (f (τ : ℂ)) := by
        simpa [f] using (hasFDerivAt_jacobiTheta₂ ((τ : ℂ) / 2) τ.2).differentiableAt
      have hf : DifferentiableAt ℂ f (τ : ℂ) :=
        (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
      simpa [f, g] using (DifferentiableAt.fun_comp' (τ : ℂ) hg hf)
    have h_prod : DifferentiableAt ℂ (fun t : ℂ ↦ cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t)
        (τ : ℂ) := h_exp.mul h_theta
    exact h_prod.pow 4
  have h_ev : F =ᶠ[𝓝 (τ : ℂ)] (↑ₕH₂) := by
    refine Filter.eventually_of_mem hU ?_
    intro z hz
    have h_arg : cexp (((π : ℂ) * I / 4) * z) = cexp (π * I * z / 4) := by
      have : ((π : ℂ) * I / 4) * z = (π * I * z) / 4 := by
        simp [div_eq_mul_inv, mul_comm, mul_assoc]
      simp [this]
    simp [F, H₂, Θ₂_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz, h_arg, Pi.pow_apply]
  exact (DifferentiableAt.congr_of_eventuallyEq hF h_ev.symm)


-- @@ L60-72 verbatim
lemma H₃_SIF_MDifferentiable : MDiff H₃_SIF := by
  rw [mdifferentiable_iff]
  simp only [H₃_SIF, SlashInvariantForm.coe_mk]
  have hθ : DifferentiableOn ℂ (fun z ↦ jacobiTheta₂ (0 : ℂ) z) {z | 0 < z.im} := by
    intro x hx
    exact (differentiableAt_jacobiTheta₂_snd 0 (by simpa using hx)).differentiableWithinAt
  have hθ4 : DifferentiableOn ℂ (fun z ↦ (jacobiTheta₂ (0 : ℂ) z) ^ 4) {z | 0 < z.im} := by
    apply DifferentiableOn.pow
    intro x hx
    exact hθ x hx
  apply hθ4.congr
  intro _ hz
  simp [Function.comp, H₃, Θ₃_as_jacobiTheta₂, ofComplex_apply_of_im_pos hz]


-- @@ L74-101 verbatim
lemma H₄_SIF_MDifferentiable : MDiff H₄_SIF := by
  intro τ
  have hθ : DifferentiableAt ℂ (fun z : ℂ ↦ jacobiTheta₂ (1 / 2 : ℂ) z) (τ : ℂ) :=
    differentiableAt_jacobiTheta₂_snd (1 / 2 : ℂ) τ.2
  have hθpow : DifferentiableAt ℂ (fun z : ℂ ↦ (jacobiTheta₂ (1 / 2 : ℂ) z) ^ 4) (τ : ℂ) :=
    (DifferentiableAt.pow hθ 4)
  have hMD_comp :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        ((fun z : ℂ ↦ (jacobiTheta₂ (1 / 2 : ℂ) z) ^ 4) ∘ UpperHalfPlane.coe) τ :=
    hθpow.mdifferentiableAt.comp τ τ.mdifferentiable_coe
  have hMD_comp_within :
      MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ)
        ((fun z : ℂ ↦ (jacobiTheta₂ (1 / 2 : ℂ) z) ^ 4) ∘ UpperHalfPlane.coe) Set.univ τ := by
    simpa [mdifferentiableWithinAt_univ] using hMD_comp
  have hfun_eq :
      ((fun z : ℂ ↦ (jacobiTheta₂ (1 / 2 : ℂ) z) ^ 4) ∘ UpperHalfPlane.coe)
        = (H₄_SIF : ℍ → ℂ) := by
    ext x
    simp [H₄_SIF, H₄, Θ₄_as_jacobiTheta₂, Function.comp]
  have hMD_within :
      MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ) (⇑H₄_SIF) Set.univ τ :=
    MDifferentiableWithinAt.congr hMD_comp_within (by
      intro x hx
      have := congrArg (fun f : ℍ → ℂ ↦ f x) hfun_eq.symm
      simpa [Function.comp] using this) (by
      have := congrArg (fun f : ℍ → ℂ ↦ f τ) hfun_eq.symm
      simpa [Function.comp] using this)
  simpa [mdifferentiableWithinAt_univ] using hMD_within


-- @@ L103-105 verbatim
@[fun_prop]
lemma H₂_MDifferentiable : MDiff H₂ := by
  simpa [H₂_SIF, SlashInvariantForm.coe_mk] using H₂_SIF_MDifferentiable


-- @@ L107-109 verbatim
@[fun_prop]
lemma H₃_MDifferentiable : MDiff H₃ := by
  simpa [H₃_SIF, SlashInvariantForm.coe_mk] using H₃_SIF_MDifferentiable


-- @@ L111-113 verbatim
@[fun_prop]
lemma H₄_MDifferentiable : MDiff H₄ := by
  simpa [H₄_SIF, SlashInvariantForm.coe_mk] using H₄_SIF_MDifferentiable


-- @@ L115-124 verbatim
/-- Differentiability of `t ↦ jacobiTheta₂(t/2, t)` at points in the upper half-plane. -/
lemma differentiableAt_jacobiTheta₂_half (τ : ℍ) :
    DifferentiableAt ℂ (fun t : ℂ ↦ jacobiTheta₂ (t / 2) t) ↑τ := by
  let f : ℂ → ℂ × ℂ := fun t ↦ (t / 2, t)
  have hf : DifferentiableAt ℂ f ↑τ :=
    (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
  have hg : DifferentiableAt ℂ (fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2) (f ↑τ) := by
    simpa [f] using (hasFDerivAt_jacobiTheta₂ ((τ : ℂ) / 2) τ.2).differentiableAt
  change DifferentiableAt ℂ (((fun p : ℂ × ℂ ↦ jacobiTheta₂ p.1 p.2) ∘ f)) ↑τ
  exact DifferentiableAt.comp (x := (τ : ℂ)) hg hf


-- @@ L126-136 verbatim
lemma Θ₂_MDifferentiable : MDiff Θ₂ := by
  intro τ
  have hΘ₂_diff : DifferentiableAt ℂ
      (fun t : ℂ ↦ cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t) (τ : ℂ) :=
    ((differentiableAt_id.const_mul ((π : ℂ) * I / 4)).cexp).mul
      (differentiableAt_jacobiTheta₂_half τ)
  have hMD := hΘ₂_diff.mdifferentiableAt.comp τ τ.mdifferentiable_coe
  have : (fun t : ℂ ↦ cexp ((π * I / 4) * t) * jacobiTheta₂ (t / 2) t) ∘
      UpperHalfPlane.coe = Θ₂ := by
    ext x; simp only [Function.comp_apply, Θ₂_as_jacobiTheta₂]; ring_nf
  rwa [this] at hMD


-- @@ L138-138 verbatim
end H_MDifferentiable


-- @@ L140-144 expanded
noncomputable def H₂_MF : ModularForm (CongruenceSubgroup.Gamma 2) 2 :=
  { H₂_SIF with
    holo' := H₂_SIF_MDifferentiable
    bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₂_slash }


-- @@ L146-150 expanded
noncomputable def H₃_MF : ModularForm (CongruenceSubgroup.Gamma 2) 2 :=
  { H₃_SIF with
    holo' := H₃_SIF_MDifferentiable
    bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₃_slash }


-- @@ L152-156 expanded
noncomputable def H₄_MF : ModularForm (CongruenceSubgroup.Gamma 2) 2 :=
  { H₄_SIF with
    holo' := H₄_SIF_MDifferentiable
    bdd_at_cusps' hc := bounded_at_cusps_of_bounded_at_infty hc isBoundedAtImInfty_H₄_slash }


-- @@ L158-158 verbatim
@[simp] lemma H₂_MF_coe : (H₂_MF : ℍ → ℂ) = H₂ := rfl


-- @@ L160-160 verbatim
@[simp] lemma H₃_MF_coe : (H₃_MF : ℍ → ℂ) = H₃ := rfl


-- @@ L162-162 verbatim
@[simp] lemma H₄_MF_coe : (H₄_MF : ℍ → ℂ) = H₄ := rfl
