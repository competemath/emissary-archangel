/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Calculus


-- @@ L10-16 verbatim
/-!

# Derivation2

Different characterizations of proof.

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace LO

-- @@ L21-21 verbatim
namespace FirstOrder


-- @@ L23-23 verbatim
variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]


-- @@ L25-25 verbatim
section «lp_section_1»


-- @@ L27-42 expanded
/-- Imported declaration from the Incompleteness formalization. -/
inductive Derivation2 (T : Theory L) : Finset (SyntacticFormula L) → Type _
  | closed (Δ) (φ : SyntacticFormula L) : φ ∈ Δ → Tilde.tilde φ ∈ Δ → Derivation2 T Δ
  | root {Δ} (φ : SyntacticFormula L) : φ ∈ T → φ ∈ Δ → Derivation2 T Δ
  | verum {Δ} : ⊤ ∈ Δ → Derivation2 T Δ
  |
  and {Δ} {φ ψ : SyntacticFormula L} :
    Wedge.wedge φ ψ ∈ Δ → Derivation2 T (insert φ Δ) → Derivation2 T (insert ψ Δ) → Derivation2 T Δ
  |
  or {Δ} {φ ψ : SyntacticFormula L} :
    Vee.vee φ ψ ∈ Δ → Derivation2 T (insert φ (insert ψ Δ)) → Derivation2 T Δ
  |
  all {Δ} {φ : SyntacticSemiformula L 1} :
    UnivQuantifier.univ φ ∈ Δ →
      Derivation2 T (insert (Rewriting.free φ) (Δ.image Rewriting.shift)) → Derivation2 T Δ
  |
  ex {Δ} {φ : SyntacticSemiformula L 1} :
    ExQuantifier.ex φ ∈ Δ →
      (t : SyntacticTerm L) →
        Derivation2 T (insert (LO.FirstOrder.Rewriting.substitute φ ![t]) Δ) → Derivation2 T Δ
  | wk {Δ Γ} : Derivation2 T Δ → Δ ⊆ Γ → Derivation2 T Γ
  | shift {Δ} : Derivation2 T Δ → Derivation2 T (Δ.image Rewriting.shift)
  |
  cut {Δ φ} :
    Derivation2 T (insert φ Δ) → Derivation2 T (insert (Tilde.tilde φ) Δ) → Derivation2 T Δ


-- @@ L44-45 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:45 " ⊢₂ " => Derivation2


-- @@ L47-48 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Derivable2 (T : Theory L) (Γ : Finset (SyntacticFormula L)) := Nonempty (T ⊢₂ Γ)


-- @@ L50-51 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:45 " ⊢₂! " => Derivable2


-- @@ L53-54 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Derivable2SingleConseq (T : Theory L) (φ : SyntacticFormula L) : Prop := T ⊢₂! {φ}


-- @@ L56-57 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix: 45 " ⊢₂.! " => Derivable2SingleConseq


-- @@ L59-59 verbatim
variable {T : Theory L}


-- @@ L61-63 verbatim
lemma shifts_toFinset_eq_image_shift (Δ : Sequent L) :
    (Rewriting.shifts Δ).toFinset = Δ.toFinset.image Rewriting.shift := by
      ext φ; simp [Rewriting.shifts]


-- @@ L65-94 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.toDerivation2 T :
    {Γ : Sequent L} → OneSided.Derivation T Γ → T ⊢₂ Γ.toFinset
  | _, Derivation.axL Δ R v => Derivation2.closed _ (Semiformula.rel R v) (by simp) (by simp)
  | _, Derivation.root (φ := φ) h => Derivation2.root φ h (by simp)
  | _, Derivation.verum Δ => Derivation2.verum (by simp)
  | _, @Derivation.and _ _ Δ φ ψ dp dq =>
    Derivation2.and (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by simp))
      (Derivation2.wk (Derivation.toDerivation2 T dq) (by simp))
  | _, @Derivation.or _ _ Δ φ ψ dpq =>
    Derivation2.or (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dpq) (by simp))
  | _, @Derivation.all _ _ Δ φ dp =>
    Derivation2.all (φ := φ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by simp [shifts_toFinset_eq_image_shift]))
  | _, @Derivation.ex _ _ Δ φ t dp =>
    Derivation2.ex (φ := φ) (by simp) t (Derivation2.wk (Derivation.toDerivation2 T dp) (by simp))
  | _, Derivation.wk d h => Derivation2.wk (Derivation.toDerivation2 T d) (List.toFinset_mono h)
  | _, @Derivation.cut _ _ Δ φ d₁ d₂ =>
    Derivation2.cut (φ := φ) (Derivation2.wk (Derivation.toDerivation2 T d₁) (by simp))
      (Derivation2.wk (Derivation.toDerivation2 T d₂) (by simp))


-- @@ L96-121 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.FirstOrder.Derivation2.toDerivation :
    {Γ : Finset (SyntacticFormula L)} → T ⊢₂ Γ → OneSided.Derivation T Γ.toList
  | _, Derivation2.closed Δ φ hp hn => Derivation.em (φ := φ) (by simp [hp]) (by simp [hn])
  | _, Derivation2.root φ hp h => Tait.wk (Derivation.root hp) (by simp_all)
  | _, Derivation2.verum h => Tait.verum' (by simp [h])
  | _, Derivation2.and (φ := φ) (ψ := ψ) h dp dq =>
    Tait.and' (φ := φ) (ψ := ψ) (by simp [h]) (Tait.wk dp.toDerivation <| by intro x; simp)
      (Tait.wk dq.toDerivation <| by intro x; simp)
  | _, Derivation2.or (φ := φ) (ψ := ψ) h dpq =>
    Tait.or' (φ := φ) (ψ := ψ) (by simp [h]) (Tait.wk dpq.toDerivation <| by intro x; simp)
  | _, Derivation2.all (φ := φ) h d =>
    Derivation.all' (φ := φ) (by simp [h])
      (Tait.wk d.toDerivation <| by intro x; simp [Rewriting.shifts])
  | _, Derivation2.ex (φ := φ) h t d =>
    Derivation.ex' (φ := φ) (by simp [h]) t (Tait.wk d.toDerivation <| by intro x; simp [])
  | _, Derivation2.wk d h =>
    Tait.wk d.toDerivation (by intro x; simp only [Finset.mem_toList]; exact @h x)
  | _, Derivation2.shift d =>
    Tait.wk (Derivation.shift d.toDerivation) <| by intro x; simp [Rewriting.shifts]
  | _, Derivation2.cut (φ := φ) d dn =>
    Tait.cut (φ := φ) (Tait.wk d.toDerivation <| by intro x; simp)
      (Tait.wk dn.toDerivation <| by intro x; simp)


-- @@ L123-126 expanded
lemma derivable_iff_derivable2 {Γ : List (SyntacticFormula L)} :
    OneSided.Derivable T Γ ↔ T ⊢₂! Γ.toFinset :=
  by
  constructor
  · rintro ⟨d⟩; exact ⟨by simpa using Derivation.toDerivation2 T d⟩
  · rintro ⟨d⟩; exact ⟨.wk d.toDerivation (by intro x; simp)⟩


-- @@ L128-129 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma provable_iff_derivable2 {φ} : Provable T φ ↔ T ⊢₂.! φ :=
  derivable_iff_derivable2


-- @@ L131-131 verbatim
end «lp_section_1»


-- @@ L133-133 verbatim
end FirstOrder

-- @@ L134-134 verbatim
end LO
