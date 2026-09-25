/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.StateSeparating.Hybrid


-- @@ L10-16 verbatim
/-!
# State-separating handlers: ε-indistinguishability

`QueryImpl.Stateful.IndistAt h₀ s₀ h₁ s₁ ε` bounds the Boolean
distinguishing advantage between two stateful handlers from explicit initial
states.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
universe uₑ uₘ


-- @@ L22-22 verbatim
open OracleSpec OracleComp


-- @@ L24-24 verbatim
namespace QueryImpl.Stateful


-- @@ L26-26 verbatim
variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}


-- @@ L28-33 verbatim
/-- ε-bounded indistinguishability of two stateful handlers from explicit
initial states. -/
def IndistAt {σ₀ σ₁ : Type}
    (h₀ : QueryImpl.Stateful unifSpec E σ₀) (s₀ : σ₀)
    (h₁ : QueryImpl.Stateful unifSpec E σ₁) (s₁ : σ₁) (ε : ℝ) : Prop :=
  ∀ (A : OracleComp E Bool), h₀.advantage s₀ h₁ s₁ A ≤ ε


-- @@ L35-37 verbatim
@[inherit_doc IndistAt]
scoped notation:50 "(" h₀ ", " s₀ ")" " ≈ᵈ[" ε "] " "(" h₁ ", " s₁ ")" =>
  QueryImpl.Stateful.IndistAt h₀ s₀ h₁ s₁ ε


-- @@ L39-39 verbatim
namespace IndistAt


-- @@ L41-41 verbatim
variable {σ σ₀ σ₁ σ₂ : Type}


-- @@ L43-44 verbatim
protected theorem refl (h : QueryImpl.Stateful unifSpec E σ) (s : σ) :
    (h, s) ≈ᵈ[0] (h, s) := fun A => (advantage_self h s A).le


-- @@ L46-50 verbatim
protected theorem symm
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : (h₀, s₀) ≈ᵈ[ε] (h₁, s₁)) : (h₁, s₁) ≈ᵈ[ε] (h₀, s₀) :=
  fun A => advantage_symm h₁ s₁ h₀ s₀ A ▸ h A


-- @@ L52-58 verbatim
protected theorem trans
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {h₂ : QueryImpl.Stateful unifSpec E σ₂} {s₂ : σ₂} {ε₀ ε₁ : ℝ}
    (h₀₁ : (h₀, s₀) ≈ᵈ[ε₀] (h₁, s₁)) (h₁₂ : (h₁, s₁) ≈ᵈ[ε₁] (h₂, s₂)) :
    (h₀, s₀) ≈ᵈ[ε₀ + ε₁] (h₂, s₂) :=
  fun A => (advantage_triangle h₀ s₀ h₁ s₁ h₂ s₂ A).trans (add_le_add (h₀₁ A) (h₁₂ A))


-- @@ L60-60 verbatim
/-! ## ε-monotonicity -/


-- @@ L62-66 verbatim
theorem mono
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε ε' : ℝ}
    (h_le : ε ≤ ε') (h : (h₀, s₀) ≈ᵈ[ε] (h₁, s₁)) :
    (h₀, s₀) ≈ᵈ[ε'] (h₁, s₁) := fun A => (h A).trans h_le


-- @@ L68-69 verbatim
theorem refl_le {ε : ℝ} (h : QueryImpl.Stateful unifSpec E σ) (s : σ) (hε : 0 ≤ ε) :
    (h, s) ≈ᵈ[ε] (h, s) := mono hε (IndistAt.refl h s)


-- @@ L71-71 verbatim
/-! ## Bridge from `DistEquiv` -/


-- @@ L73-77 verbatim
theorem of_distEquiv
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    (h : (h₀, s₀) ≡ᵈ (h₁, s₁)) : (h₀, s₀) ≈ᵈ[0] (h₁, s₁) :=
  fun A => (DistEquiv.advantage_zero h A).le


-- @@ L79-86 verbatim
theorem distEquiv_left
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₀' : QueryImpl.Stateful unifSpec E σ} {s₀' : σ}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : (h₀, s₀) ≡ᵈ (h₀', s₀'))
    (hi : (h₀', s₀') ≈ᵈ[ε] (h₁, s₁)) :
    (h₀, s₀) ≈ᵈ[ε] (h₁, s₁) :=
  fun A => DistEquiv.advantage_left h h₁ s₁ A ▸ hi A


-- @@ L88-95 verbatim
theorem distEquiv_right
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁}
    {h₁' : QueryImpl.Stateful unifSpec E σ} {s₁' : σ} {ε : ℝ}
    (h : (h₁, s₁) ≡ᵈ (h₁', s₁'))
    (hi : (h₀, s₀) ≈ᵈ[ε] (h₁, s₁)) :
    (h₀, s₀) ≈ᵈ[ε] (h₁', s₁') :=
  fun A => DistEquiv.advantage_right h₀ s₀ h A ▸ hi A


-- @@ L97-97 verbatim
/-! ## Bridge to advantage -/


-- @@ L99-103 verbatim
theorem advantage_le
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : (h₀, s₀) ≈ᵈ[ε] (h₁, s₁)) (A : OracleComp E Bool) :
    h₀.advantage s₀ h₁ s₁ A ≤ ε := h A


-- @@ L105-109 verbatim
theorem of_advantage_le
    {h₀ : QueryImpl.Stateful unifSpec E σ₀} {s₀ : σ₀}
    {h₁ : QueryImpl.Stateful unifSpec E σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : ∀ (A : OracleComp E Bool), h₀.advantage s₀ h₁ s₁ A ≤ ε) :
    (h₀, s₀) ≈ᵈ[ε] (h₁, s₁) := h


-- @@ L111-111 verbatim
/-! ## Hybrid and compositional bounds -/


-- @@ L113-117 verbatim
theorem hybrid {n : ℕ} {σ : ℕ → Type} {ε : ℕ → ℝ}
    (h : (i : ℕ) → QueryImpl.Stateful unifSpec E (σ i)) (s : (i : ℕ) → σ i)
    (hh : ∀ i ∈ Finset.range n, (h i, s i) ≈ᵈ[ε i] (h (i + 1), s (i + 1))) :
    (h 0, s 0) ≈ᵈ[∑ i ∈ Finset.range n, ε i] (h n, s n) := fun A =>
  (advantage_hybrid h s A n).trans (Finset.sum_le_sum (fun i hi => hh i hi A))


-- @@ L119-119 verbatim
section LinkCongr


-- @@ L121-121 verbatim
variable {ιₘ : Type uₘ} {M : OracleSpec.{uₘ, 0} ιₘ}

-- @@ L122-122 verbatim
variable {σ_P : Type}


-- @@ L124-131 verbatim
theorem link_inner_congr (outer : QueryImpl.Stateful M E σ_P) (sP : σ_P)
    {inner₀ : QueryImpl.Stateful unifSpec M σ₀} {s₀ : σ₀}
    {inner₁ : QueryImpl.Stateful unifSpec M σ₁} {s₁ : σ₁} {ε : ℝ}
    (h : (inner₀, s₀) ≈ᵈ[ε] (inner₁, s₁)) :
    (outer.link inner₀, (sP, s₀)) ≈ᵈ[ε] (outer.link inner₁, (sP, s₁)) := by
  intro A
  rw [advantage_link_left_eq_advantage_shiftLeft]
  exact h (outer.shiftLeft sP A)


-- @@ L133-133 verbatim
end LinkCongr


-- @@ L135-135 verbatim
end IndistAt


-- @@ L137-137 verbatim
end QueryImpl.Stateful
