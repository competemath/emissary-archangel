/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Hierarchy


-- @@ L10-10 verbatim
/-! # StrictHierarchy -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO


-- @@ L17-17 verbatim
namespace FirstOrder


-- @@ L19-19 verbatim
namespace Arith


-- @@ L21-21 verbatim
section «lp_section_1»


-- @@ L23-23 verbatim
variable {L : Language} [L.LT]


-- @@ L25-35 expanded
/-- Imported declaration from the Incompleteness formalization. -/
inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L μ n → Prop
  | zero {Γ φ} : DeltaZero φ → StrictHierarchy Γ s φ
  |
  sigma {s n} {φ : Semiformula L μ (n + 1)} :
    StrictHierarchy PiSymbol.pi s φ → StrictHierarchy SigmaSymbol.sigma (s + 1) (ExQuantifier.ex φ)
  |
  pi {s n} {φ : Semiformula L μ (n + 1)} :
    StrictHierarchy SigmaSymbol.sigma s φ →
      StrictHierarchy PiSymbol.pi (s + 1) (UnivQuantifier.univ φ)
  |
  ex {s n} {φ : Semiformula L μ (n + 1)} :
    StrictHierarchy SigmaSymbol.sigma (s + 1) φ →
      StrictHierarchy SigmaSymbol.sigma (s + 1) (ExQuantifier.ex φ)
  |
  all {s n} {φ : Semiformula L μ (n + 1)} :
    StrictHierarchy PiSymbol.pi (s + 1) φ →
      StrictHierarchy PiSymbol.pi (s + 1) (UnivQuantifier.univ φ)


-- @@ L37-38 verbatim
lemma _root_.LO.FirstOrder.Arith.DeltaZero.of_open {φ : Semiformula L μ n} :
    φ.Open → DeltaZero φ := Hierarchy.of_open


-- @@ L40-40 verbatim
namespace StrictHierarchy


-- @@ L42-49 expanded
lemma rew {φ : Semiformula L μ₁ n₁} (h : StrictHierarchy Γ s φ) (ω : Rew L μ₁ n₁ μ₂ n₂) :
    StrictHierarchy Γ s (app ω φ) :=
  by
  induction h generalizing μ₂ n₂ <;> try simp only [Rewriting.app_ex, Rewriting.app_all]
  case zero h => exact zero <| (Hierarchy.rew_iff (ω := ω)).mpr h
  case sigma ih => exact (ih ω.q).sigma
  case pi ih => exact (ih ω.q).pi
  case ex ih => exact (ih ω.q).ex
  case all ih => exact (ih ω.q).all


-- @@ L51-72 expanded
lemma rew_iff {φ : Semiformula L μ₁ n₁} (ω : Rew L μ₁ n₁ μ₂ n₂) :
    StrictHierarchy Γ s (app ω φ) ↔ StrictHierarchy Γ s φ :=
  ⟨by
    generalize hq : app ω φ = ψ
    intro h;
    induction h generalizing n₁ <;>
      try simp only [Semiformula.eq_all_iff, Semiformula.eq_ex_iff] at hq ⊢
    case zero ψ h => rcases hq; exact zero (Hierarchy.rew_iff.mp h)
    case sigma h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).sigma
    case pi h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).pi
    case ex h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).ex
    case all ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).all,
    fun h ↦ h.rew ω⟩


-- @@ L74-81 verbatim
lemma succ {Γ} {φ : Semiformula L μ₁ n₁} (h : StrictHierarchy Γ s φ) :
    StrictHierarchy Γ (s + 1) φ := by
  induction h
  case zero h => exact zero h
  case sigma ih => exact ih.sigma
  case pi ih => exact ih.pi
  case ex ih => exact ih.ex
  case all ih => exact ih.all


-- @@ L83-87 verbatim
lemma zero_iff_delta_zero {Γ} {φ : Semiformula L μ n} :
    StrictHierarchy Γ 0 φ ↔ DeltaZero φ := by
  constructor
  · rintro ⟨h⟩; exact h
  · intro h; exact zero h


-- @@ L89-89 verbatim
end StrictHierarchy


-- @@ L91-91 verbatim
end «lp_section_1»


-- @@ L93-93 verbatim
end Arith

-- @@ L94-94 verbatim
end FirstOrder

-- @@ L95-95 verbatim
end LO
