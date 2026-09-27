/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Lomega1omega.QuantifierClass

-- @@ L9-29 verbatim
/-!
# Signed quantifier *occurrence* (issue #15, budget gate 1)

`QuantifierClass.lean` answers "is **every** quantifier of this sign admissible?"; Feferman's
separator budgets need the dual, positive question: "**does** a quantifier of this sign occur?".

Defining occurrence as `¬ IsUniversal` / `¬ IsExistential` would work extensionally but makes every
budget calculation a double-negation exercise. So occurrence is given its own signed recursion,
with
exact constructor equations, and the two are then related by an exact bridge:

```
universalSigned s φ ↔ ¬ hasQuantSigned (!s) φ
IsUniversal φ ↔ ¬ HasExistential φ      IsExistential φ ↔ ¬ HasUniversal φ
```

The sign discipline is the same as in `QuantifierClass.lean` and `Polarity.lean`: an antecedent
flips, `iSup`/`iInf` preserve and are not quantifiers, and `all` is a *universal* occurrence at the
positive sign only.  Nothing here mentions interpolation; the set-level versions at the end are what
the separator budgets are stated against.
-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
namespace FirstOrder.Language


-- @@ L35-35 verbatim
namespace BoundedFormulaω


-- @@ L37-37 verbatim
variable {L : Language.{0, 0}} {α β : Type}


-- @@ L39-49 verbatim
/-- **Signed quantifier occurrence.**  `hasQuantSigned true φ` says a quantifier occurs
*universally* in `φ`; `hasQuantSigned false φ` says one occurs *existentially* (a negatively
occurring `all`). -/
def hasQuantSigned : ∀ {n : ℕ}, Bool → L.BoundedFormulaω α n → Prop
  | _, _, .falsum => False
  | _, _, .equal _ _ => False
  | _, _, .rel _ _ => False
  | _, s, .imp φ ψ => hasQuantSigned (!s) φ ∨ hasQuantSigned s ψ
  | _, s, .all φ => s = true ∨ hasQuantSigned s φ
  | _, s, .iSup φs => ∃ i, hasQuantSigned s (φs i)
  | _, s, .iInf φs => ∃ i, hasQuantSigned s (φs i)


-- @@ L51-52 verbatim
/-- An existential quantifier occurs in `φ`. -/
abbrev HasExistential {n : ℕ} (φ : L.BoundedFormulaω α n) : Prop := hasQuantSigned false φ


-- @@ L54-54 verbatim
/-! ## Constructor equations -/


-- @@ L56-57 verbatim
@[simp] theorem hasQuantSigned_falsum {n : ℕ} (s : Bool) :
    ¬ hasQuantSigned s (BoundedFormulaω.falsum : L.BoundedFormulaω α n) := id


-- @@ L59-60 verbatim
@[simp] theorem hasQuantSigned_equal {n : ℕ} (s : Bool) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    ¬ hasQuantSigned s (BoundedFormulaω.equal t₁ t₂) := id


-- @@ L62-63 verbatim
@[simp] theorem hasQuantSigned_rel {n l : ℕ} (s : Bool) (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) : ¬ hasQuantSigned s (BoundedFormulaω.rel R ts) := id


-- @@ L65-66 verbatim
@[simp] theorem hasQuantSigned_imp {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    hasQuantSigned s (φ.imp ψ) ↔ hasQuantSigned (!s) φ ∨ hasQuantSigned s ψ := Iff.rfl


-- @@ L68-69 verbatim
@[simp] theorem hasQuantSigned_all {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α (n + 1)) :
    hasQuantSigned s φ.all ↔ s = true ∨ hasQuantSigned s φ := Iff.rfl


-- @@ L71-72 verbatim
@[simp] theorem hasQuantSigned_iSup {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    hasQuantSigned s (BoundedFormulaω.iSup φs) ↔ ∃ i, hasQuantSigned s (φs i) := Iff.rfl


-- @@ L74-75 verbatim
@[simp] theorem hasQuantSigned_iInf {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    hasQuantSigned s (BoundedFormulaω.iInf φs) ↔ ∃ i, hasQuantSigned s (φs i) := Iff.rfl


-- @@ L77-82 verbatim
/-- Negation **exchanges** the two occurrence notions. -/
@[simp] theorem hasQuantSigned_not {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α n) :
    hasQuantSigned s φ.not ↔ hasQuantSigned (!s) φ := by
  change hasQuantSigned (!s) φ ∨ hasQuantSigned s
    (BoundedFormulaω.falsum : L.BoundedFormulaω α n) ↔ _
  simp


-- @@ L84-87 verbatim
@[simp] theorem hasQuantSigned_and {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    hasQuantSigned s (φ.and ψ) ↔ hasQuantSigned s φ ∨ hasQuantSigned s ψ := by
  change hasQuantSigned s ((φ.imp ψ.not).not) ↔ _
  simp


-- @@ L89-93 verbatim
@[simp] theorem hasQuantSigned_ex {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α (n + 1)) :
    hasQuantSigned s φ.ex ↔ s = false ∨ hasQuantSigned s φ := by
  change hasQuantSigned s ((φ.not.all).not) ↔ _
  simp only [hasQuantSigned_not, hasQuantSigned_all]
  cases s <;> simp


-- @@ L95-95 verbatim
/-! ## The exact bridge to the quantifier classes -/


-- @@ L97-117 verbatim
/-- **The bridge.**  Being of a class is exactly the *absence* of an occurrence of the opposite
sign. -/
theorem universalSigned_iff_not_hasQuantSigned :
    ∀ {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α n),
      universalSigned s φ ↔ ¬ hasQuantSigned (!s) φ := by
  intro n s φ
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ =>
    rw [universalSigned_imp, hasQuantSigned_imp, not_or, ihφ (!s), ihψ s, Bool.not_not]
  | all φ ih =>
    rw [universalSigned_all, hasQuantSigned_all, not_or, ih s]
    cases s <;> simp
  | iSup φs ih =>
    rw [universalSigned_iSup, hasQuantSigned_iSup, not_exists]
    exact forall_congr' fun i => ih i s
  | iInf φs ih =>
    rw [universalSigned_iInf, hasQuantSigned_iInf, not_exists]
    exact forall_congr' fun i => ih i s


-- @@ L119-120 verbatim
theorem isUniversal_iff_not_hasExistential {n : ℕ} (φ : L.BoundedFormulaω α n) :
    IsUniversal φ ↔ ¬ HasExistential φ := universalSigned_iff_not_hasQuantSigned true φ


-- @@ L122-122 verbatim
/-! ## Stability under the variable operations -/


-- @@ L124-131 verbatim
theorem hasQuantSigned_relabel (s : Bool) (g : α → β ⊕ Fin n) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k),
      hasQuantSigned s (φ.relabel g) ↔ hasQuantSigned s φ := by
  intro k φ
  have h1 := universalSigned_iff_not_hasQuantSigned (!s) (φ.relabel g)
  have h2 := universalSigned_iff_not_hasQuantSigned (!s) φ
  rw [Bool.not_not] at h1 h2
  rw [← not_iff_not, ← h1, ← h2, universalSigned_relabel]


-- @@ L133-138 verbatim
theorem hasQuantSigned_subst (s : Bool) {n : ℕ} (φ : L.BoundedFormulaω α n) (tf : α → L.Term β) :
    hasQuantSigned s (φ.subst tf) ↔ hasQuantSigned s φ := by
  have h1 := universalSigned_iff_not_hasQuantSigned (!s) (φ.subst tf)
  have h2 := universalSigned_iff_not_hasQuantSigned (!s) φ
  rw [Bool.not_not] at h1 h2
  rw [← not_iff_not, ← h1, ← h2, universalSigned_subst]


-- @@ L140-159 verbatim
theorem hasQuantSigned_openBounds (s : Bool) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n),
      hasQuantSigned s (φ.openBounds) ↔ hasQuantSigned s φ
  | _, .falsum => Iff.rfl
  | _, .equal _ _ => Iff.rfl
  | _, .rel _ _ => Iff.rfl
  | _, .imp φ ψ => by
    change hasQuantSigned (!s) (φ.openBounds) ∨ hasQuantSigned s (ψ.openBounds) ↔ _
    rw [hasQuantSigned_openBounds _ φ, hasQuantSigned_openBounds s ψ]
    exact Iff.rfl
  | _, .all φ => by
    change s = true ∨ hasQuantSigned s ((φ.openBounds).relabel insertLastBound) ↔ _
    rw [hasQuantSigned_relabel, hasQuantSigned_openBounds s φ]
    exact Iff.rfl
  | _, .iSup φs => by
    change (∃ i, hasQuantSigned s ((φs i).openBounds)) ↔ _
    exact exists_congr fun i => hasQuantSigned_openBounds s (φs i)
  | _, .iInf φs => by
    change (∃ i, hasQuantSigned s ((φs i).openBounds)) ↔ _
    exact exists_congr fun i => hasQuantSigned_openBounds s (φs i)


-- @@ L161-161 verbatim
end BoundedFormulaω


-- @@ L163-163 verbatim
/-! ## Set-level occurrence: the budget sources -/


-- @@ L165-165 verbatim
namespace Theoryω


-- @@ L167-167 verbatim
open BoundedFormulaω


-- @@ L169-169 verbatim
variable {L : Language.{0, 0}}


-- @@ L171-172 verbatim
/-- A quantifier of sign `s` occurs somewhere in the set — the *source* of a separator budget. -/
def HasQuantSigned (s : Bool) (T : Set L.Sentenceω) : Prop := ∃ σ ∈ T, hasQuantSigned s σ


-- @@ L174-175 verbatim
/-- An existential quantifier occurs somewhere in `T`. -/
private abbrev HasExistential (T : Set L.Sentenceω) : Prop := HasQuantSigned false T


-- @@ L177-177 verbatim
variable {s : Bool} {T T' : Set L.Sentenceω} {σ : L.Sentenceω}


-- @@ L179-181 verbatim
theorem hasQuantSigned_mono (h : T ⊆ T') (hT : HasQuantSigned s T) : HasQuantSigned s T' := by
  obtain ⟨σ, hσ, hq⟩ := hT
  exact ⟨σ, h hσ, hq⟩


-- @@ L183-184 verbatim
theorem hasQuantSigned_of_mem (hmem : σ ∈ T) (hq : hasQuantSigned s σ) : HasQuantSigned s T :=
  ⟨σ, hmem, hq⟩


-- @@ L186-195 verbatim
@[simp] theorem hasQuantSigned_insert :
    HasQuantSigned s (insert σ T) ↔ hasQuantSigned s σ ∨ HasQuantSigned s T := by
  constructor
  · rintro ⟨ρ, hρ, hq⟩
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact Or.inl hq
    · exact Or.inr ⟨ρ, hρ, hq⟩
  · rintro (hq | ⟨ρ, hρ, hq⟩)
    · exact ⟨σ, Set.mem_insert _ _, hq⟩
    · exact ⟨ρ, Set.mem_insert_of_mem _ hρ, hq⟩


-- @@ L197-202 verbatim
/-- **Non-growth**: inserting a sentence whose `s`-occurrences are already licensed does not enlarge
the budget.  This is the shape every consistency-property branch step needs. -/
theorem hasQuantSigned_insert_of_le (h : hasQuantSigned s σ → HasQuantSigned s T) :
    HasQuantSigned s (insert σ T) ↔ HasQuantSigned s T := by
  rw [hasQuantSigned_insert]
  exact ⟨fun hq => hq.elim h id, Or.inr⟩


-- @@ L204-204 verbatim
end Theoryω


-- @@ L206-206 verbatim
end FirstOrder.Language
