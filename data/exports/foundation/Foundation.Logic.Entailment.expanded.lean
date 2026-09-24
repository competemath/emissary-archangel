module

public import Foundation.Logic.Semantics
public import Foundation.Vorspiel.AdjunctiveSet


-- @@ L6-26 verbatim
/-!
# Basic definitions and properties of proof system related notions

This file defines a characterization of the system/proof/provability/calculus of formulae.
Also defines soundness and completeness.

## Main Definitions
* `FFL.Entailment S F`: a general framework of deductive system `S` for formulae `F`.
* `FFL.Entailment.Inconsistent 𝓢`: a proposition that states that all formulae in `F` is provable from `𝓢`.
* `FFL.Entailment.Consistent 𝓢`: a proposition that states that `𝓢` is not inconsistent.
* `FFL.Entailment.Sound 𝓢 𝓜`: provability from `𝓢` implies satisfiability on `𝓜`.
* `FFL.Entailment.Complete 𝓢 𝓜`: satisfiability on `𝓜` implies provability from `𝓢`.

## Notation
* `𝓢 ⊢! φ`: a type of formalized proofs of `φ : F` from deductive system `𝓢 : S`.
* `𝓢 ⊢ φ`: a proposition that states there is a proof of `φ` from `𝓢`, i.e. `φ` is provable from `𝓢`.
* `𝓢 ⊬ φ`: a proposition that states `φ` is not provable from `𝓢`.
* `𝓢 ⊢!* T`: a type of formalized proofs for each formulae in a set `T` from `𝓢`.
* `𝓢 ⊢* T`: a proposition that states each formulae in `T` is provable from `𝓢`.

-/



-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace FFL


-- @@ L33-35 verbatim
/-- Entailment relation on proof system `S` and formula `F` -/
class Entailment (S : Type*) (F : outParam Type*) where
  Prf : S → F → Type*


-- @@ L37-37 verbatim
infix:45 " ⊢! " => Entailment.Prf


-- @@ L39-39 verbatim
namespace Entailment


-- @@ L41-41 verbatim
variable {F : Type*} {S T U : Type*} [Entailment S F] [Entailment T F] [Entailment U F]


-- @@ L43-43 verbatim
section


-- @@ L45-45 verbatim
variable (𝓢 : S)


-- @@ L47-48 verbatim
/-- Proposition that states `φ` is provable. -/
def Provable (φ : F) : Prop := Nonempty (𝓢 ⊢! φ)


-- @@ L50-51 verbatim
/-- Abbreviation for unprovability. -/
abbrev Unprovable (φ : F) : Prop := ¬Provable 𝓢 φ


-- @@ L53-53 verbatim
infix:45 " ⊢ " => Provable


-- @@ L55-55 verbatim
infix:45 " ⊬ " => Unprovable


-- @@ L57-58 verbatim
/-- Proofs of set of formulae. -/
def PrfSet (s : Set F) : Type _ := ⦃φ : F⦄ → φ ∈ s → 𝓢 ⊢! φ


-- @@ L60-61 verbatim
/-- Proposition for existance of proofs of set of formulae. -/
def ProvableSet (s : Set F) : Prop := ∀ {φ}, φ ∈ s → 𝓢 ⊢ φ


-- @@ L63-63 verbatim
infix:45 " ⊢!* " => PrfSet


-- @@ L65-65 verbatim
infix:45 " ⊢* " => ProvableSet


-- @@ L67-68 verbatim
/-- Set of all provable formulae. -/
def theory : Set F := {φ | 𝓢 ⊢ φ}


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
def cast {𝓢 : S} {φ ψ : F} (b : 𝓢 ⊢! φ) (e : φ = ψ := by simp) : 𝓢 ⊢! ψ := e ▸ b


-- @@ L74-77 verbatim
@[grind ⇒] lemma cast! {𝓢 : S} {φ ψ : F} (b : 𝓢 ⊢ φ) (e : φ = ψ := by simp) : 𝓢 ⊢ ψ := ⟨cast b.some e⟩

lemma unprovable_iff_isEmpty {𝓢 : S} {φ : F} :
    𝓢 ⊬ φ ↔ IsEmpty (𝓢 ⊢! φ) := by simp [Provable, Unprovable]


-- @@ L79-84 verbatim
noncomputable def Provable.get {𝓢 : S} {φ : F} (h : 𝓢 ⊢ φ) : 𝓢 ⊢! φ :=
  Classical.choice h

lemma provableSet_iff {𝓢 : S} {s : Set F} :
    𝓢 ⊢* s ↔ Nonempty (𝓢 ⊢!* s) := by
  simp [ProvableSet, PrfSet, Provable, Classical.nonempty_pi, ←imp_iff_not_or]


-- @@ L86-87 verbatim
noncomputable def ProvableSet.get {𝓢 : S} {s : Set F} (h : 𝓢 ⊢* s) : 𝓢 ⊢!* s :=
  Classical.choice (α := 𝓢 ⊢!* s) (provableSet_iff.mp h : Nonempty (𝓢 ⊢!* s))


-- @@ L89-91 verbatim
/-- Provability strength relation of proof systems -/
class WeakerThan (𝓢 : S) (𝓣 : T) : Prop where
  subset : theory 𝓢 ⊆ theory 𝓣


-- @@ L93-93 verbatim
infix:40 " ⪯ " => WeakerThan


-- @@ L95-98 verbatim
/-- Strict provability strength relation of proof systems -/
class StrictlyWeakerThan (𝓢 : S) (𝓣 : T) : Prop where
   weakerThan : 𝓢 ⪯ 𝓣
   notWT : ¬𝓣 ⪯ 𝓢


-- @@ L100-100 verbatim
infix:40 " ⪱ " => StrictlyWeakerThan


-- @@ L102-104 verbatim
/-- Provability equivalence relation of proof systems -/
class Equiv (𝓢 : S) (𝓣 : T) : Prop where
  eq : theory 𝓢 = theory 𝓣


-- @@ L106-106 verbatim
infix:40 " ≊ " => Equiv


-- @@ L108-108 verbatim
/-! ### Provability strength -/


-- @@ L110-110 verbatim
section WeakerThan


-- @@ L112-112 verbatim
variable {𝓢 : S} {𝓣 : T} {𝓤 : U}


-- @@ L114-118 verbatim
@[instance, simp, refl] protected lemma WeakerThan.refl (𝓢 : S) : 𝓢 ⪯ 𝓢 := ⟨Set.Subset.refl _⟩

lemma WeakerThan.wk (h : 𝓢 ⪯ 𝓣) {φ} : 𝓢 ⊢ φ → 𝓣 ⊢ φ := @h.subset φ

lemma WeakerThan.pbl [h : 𝓢 ⪯ 𝓣] {φ} : 𝓢 ⊢ φ → 𝓣 ⊢ φ := @h.subset φ


-- @@ L120-120 verbatim
@[trans] lemma WeakerThan.trans : 𝓢 ⪯ 𝓣 → 𝓣 ⪯ 𝓤 → 𝓢 ⪯ 𝓤 := fun w₁ w₂ ↦ ⟨Set.Subset.trans w₁.subset w₂.subset⟩


-- @@ L122-149 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ⪯ ·) (· ⪯ ·) (· ⪯ ·) where
  trans := WeakerThan.trans

lemma weakerThan_iff : 𝓢 ⪯ 𝓣 ↔ (∀ {φ}, 𝓢 ⊢ φ → 𝓣 ⊢ φ) :=
  ⟨fun h _ hf ↦ h.subset hf, fun h ↦ ⟨fun _ hf ↦ h hf⟩⟩

lemma not_weakerThan_iff : ¬𝓢 ⪯ 𝓣 ↔ (∃ φ, 𝓢 ⊢ φ ∧ 𝓣 ⊬ φ) := by simp [weakerThan_iff, Unprovable];

lemma strictlyWeakerThan_iff : 𝓢 ⪱ 𝓣 ↔ (∀ {φ}, 𝓢 ⊢ φ → 𝓣 ⊢ φ) ∧ (∃ φ, 𝓢 ⊬ φ ∧ 𝓣 ⊢ φ) := by
  constructor
  · rintro ⟨wt, nwt⟩
    exact ⟨weakerThan_iff.mp wt, by rcases not_weakerThan_iff.mp nwt with ⟨φ, ht, hs⟩; exact ⟨φ, hs, ht⟩⟩
  · rintro ⟨h, φ, hs, ht⟩
    exact ⟨weakerThan_iff.mpr h, not_weakerThan_iff.mpr ⟨φ, ht, hs⟩⟩

lemma swt_of_swt_of_wt : 𝓢 ⪱ 𝓣 → 𝓣 ⪯ 𝓤 → 𝓢 ⪱ 𝓤 := by
  rintro ⟨h₁, nh₁⟩ h₂
  constructor
  . exact WeakerThan.trans h₁ h₂
  · intro h
    exact nh₁ (WeakerThan.trans h₂ h)

lemma swt_of_wt_of_swt : 𝓢 ⪯ 𝓣 → 𝓣 ⪱ 𝓤 → 𝓢 ⪱ 𝓤 := by
  rintro h₁ ⟨h₂, nh₂⟩
  constructor
  . exact WeakerThan.trans h₁ h₂
  · intro h
    exact nh₂ (WeakerThan.trans h h₁)


-- @@ L151-153 verbatim
instance [𝓢 ⪱ 𝓣] : 𝓢 ⪯ 𝓣 := StrictlyWeakerThan.weakerThan

lemma StrictlyWeakerThan.trans : 𝓢 ⪱ 𝓣 → 𝓣 ⪱ 𝓤 → 𝓢 ⪱ 𝓤 := fun h₁ h₂ ↦ swt_of_swt_of_wt h₁ h₂.weakerThan


-- @@ L155-156 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ⪱ ·) (· ⪯ ·) (· ⪱ ·) where
  trans := swt_of_swt_of_wt


-- @@ L158-159 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ⪯ ·) (· ⪱ ·) (· ⪱ ·) where
  trans := swt_of_wt_of_swt


-- @@ L161-170 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ⪱ ·) (· ⪱ ·) (· ⪱ ·) where
  trans := StrictlyWeakerThan.trans

lemma weakening (h : 𝓢 ⪯ 𝓣) {φ} : 𝓢 ⊢ φ → 𝓣 ⊢ φ := weakerThan_iff.mp h

lemma StrictlyWeakerThan.of_unprovable_provable {𝓢 : S} {𝓣 : T} [𝓢 ⪯ 𝓣] {φ : F}
    (hS : 𝓢 ⊬ φ) (hT : 𝓣 ⊢ φ) : 𝓢 ⪱ 𝓣 := ⟨inferInstance, fun h ↦ hS (h.wk hT)⟩

lemma Equiv.iff : 𝓢 ≊ 𝓣 ↔ (∀ φ, 𝓢 ⊢ φ ↔ 𝓣 ⊢ φ) :=
  ⟨fun e ↦ by simpa [Set.ext_iff, theory] using e.eq, fun e ↦ ⟨by simpa [Set.ext_iff, theory] using e⟩⟩


-- @@ L172-172 verbatim
@[instance, simp, refl] protected lemma Equiv.refl (𝓢 : S) : 𝓢 ≊ 𝓢 := ⟨rfl⟩


-- @@ L174-174 verbatim
@[symm, grind .] lemma Equiv.symm : 𝓢 ≊ 𝓣 → 𝓣 ≊ 𝓢 := fun e ↦ ⟨Eq.symm e.eq⟩


-- @@ L176-176 verbatim
@[trans] lemma Equiv.trans : 𝓢 ≊ 𝓣 → 𝓣 ≊ 𝓤 → 𝓢 ≊ 𝓤 := fun e₁ e₂ ↦ ⟨Eq.trans e₁.eq e₂.eq⟩


-- @@ L178-186 verbatim
@[grind =]
lemma Equiv.antisymm_iff : 𝓢 ≊ 𝓣 ↔ 𝓢 ⪯ 𝓣 ∧ 𝓣 ⪯ 𝓢 := by
  constructor
  · intro e
    exact ⟨⟨Set.Subset.antisymm_iff.mp e.eq |>.1⟩, ⟨Set.Subset.antisymm_iff.mp e.eq |>.2⟩⟩
  · rintro ⟨w₁, w₂⟩
    exact ⟨Set.Subset.antisymm w₁.subset w₂.subset⟩

alias ⟨_, Equiv.antisymm⟩ := Equiv.antisymm_iff


-- @@ L188-188 verbatim
@[grind ->] lemma Equiv.le : 𝓢 ≊ 𝓣 → 𝓢 ⪯ 𝓣 := fun e ↦ ⟨by rw [e.eq]⟩


-- @@ L190-191 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ≊ ·) (· ≊ ·) (· ≊ ·) where
  trans := Equiv.trans


-- @@ L193-194 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ≊ ·) (· ⪯ ·) (· ⪯ ·) where
  trans h₁ h₂ := WeakerThan.trans h₁.le h₂


-- @@ L196-197 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ≊ ·) (· ≊ ·) (· ⪯ ·) where
  trans h₁ h₂ := WeakerThan.trans h₁.le h₂.le


-- @@ L199-200 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ⪯ ·) (· ≊ ·) (· ⪯ ·) where
  trans h₁ h₂ := WeakerThan.trans h₁ h₂.le


-- @@ L202-203 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ≊ ·) (· ⪱ ·) (· ⪱ ·) where
  trans h₁ h₂ := swt_of_wt_of_swt h₁.le h₂


-- @@ L205-206 verbatim
instance : Trans (α := S) (β := T) (γ := U) (· ⪱ ·) (· ≊ ·) (· ⪱ ·) where
  trans h₁ h₂ := swt_of_swt_of_wt h₁ h₂.le


-- @@ L208-212 verbatim
@[grind =]
lemma iff_strictlyWeakerThan_weakerThan_not_equiv : 𝓢 ⪱ 𝓣 ↔ 𝓢 ⪯ 𝓣 ∧ ¬(𝓢 ≊ 𝓣) := by
  constructor
  · rintro ⟨_, _⟩; grind;
  · rintro ⟨_, _⟩; constructor <;> grind;


-- @@ L214-224 verbatim
class Incomparable (𝓢 : S) (𝓣 : T) where
  notWT₁ : ¬𝓢 ⪯ 𝓣
  notWT₂ : ¬𝓣 ⪯ 𝓢

lemma Incomparable.of_unprovable
  (h₁ : ∃ φ, 𝓢 ⊢ φ ∧ 𝓣 ⊬ φ)
  (h₂ : ∃ ψ, 𝓣 ⊢ ψ ∧ 𝓢 ⊬ ψ)
  : Incomparable (𝓢 : S) (𝓣 : T) := by
  constructor <;>
  . apply Entailment.not_weakerThan_iff.mpr;
    assumption;


-- @@ L226-226 verbatim
end WeakerThan


-- @@ L228-228 verbatim
/-! ### Consistency and inconsistency -/


-- @@ L230-230 verbatim
@[simp] lemma provableSet_theory (𝓢 : S) : 𝓢 ⊢* theory 𝓢 := fun hf ↦ hf


-- @@ L232-232 verbatim
def Inconsistent (𝓢 : S) : Prop := ∀ φ, 𝓢 ⊢ φ


-- @@ L234-242 verbatim
class Consistent (𝓢 : S) : Prop where
  not_inconsistent : ¬Inconsistent 𝓢

lemma inconsistent_def {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∀ φ, 𝓢 ⊢ φ := by simp [Inconsistent]

lemma inconsistent_iff_theory_eq {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by
  simp [Inconsistent, Set.ext_iff, theory]


-- @@ L244-248 verbatim
@[simp] lemma not_inconsistent_iff_consistent {𝓢 : S} :
    ¬Inconsistent 𝓢 ↔ Consistent 𝓢 :=
  ⟨fun h ↦ ⟨h⟩, by rintro ⟨h⟩; exact h⟩

alias ⟨_, Consistent.not_inc⟩ := not_inconsistent_iff_consistent


-- @@ L250-273 verbatim
@[simp] lemma not_consistent_iff_inconsistent {𝓢 : S} :
    ¬Consistent 𝓢 ↔ Inconsistent 𝓢 := by simp [←not_inconsistent_iff_consistent]

alias ⟨_, Inconsistent.not_con⟩ := not_consistent_iff_inconsistent

lemma consistent_iff_exists_unprovable {𝓢 : S} :
    Consistent 𝓢 ↔ ∃ φ, 𝓢 ⊬ φ := by
  simp [←not_inconsistent_iff_consistent, inconsistent_def]

alias ⟨Consistent.exists_unprovable, _⟩ := consistent_iff_exists_unprovable

lemma Consistent.of_unprovable {𝓢 : S} {φ} (h : 𝓢 ⊬ φ) : Consistent 𝓢 :=
  ⟨fun hp ↦ h (hp φ)⟩

lemma inconsistent_iff_theory_eq_univ {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by simp [inconsistent_def, theory, Set.ext_iff]

alias ⟨Inconsistent.theory_eq, _⟩ := inconsistent_iff_theory_eq_univ

lemma Inconsistent.of_ge {𝓢 : S} {𝓣 : T} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ⪯ 𝓣) : Inconsistent 𝓣 :=
  fun φ ↦ h.subset (h𝓢 φ)

lemma Consistent.of_le {𝓢 : S} {𝓣 : T} (h𝓢 : Consistent 𝓢) (h : 𝓣 ⪯ 𝓢) : Consistent 𝓣 :=
  ⟨fun H ↦ not_consistent_iff_inconsistent.mpr (H.of_ge h) h𝓢⟩


-- @@ L275-275 verbatim
variable (S)


-- @@ L277-278 verbatim
class DeductiveExplosion [LogicalNeutral F] where
  dexp {𝓢 : S} : 𝓢 ⊢! ⊥ → (φ : F) → 𝓢 ⊢! φ


-- @@ L280-280 verbatim
variable {S}


-- @@ L282-282 verbatim
section


-- @@ L284-284 verbatim
variable [LogicalNeutral F] [DeductiveExplosion S]


-- @@ L286-296 verbatim
theorem DeductiveExplosion.dexp! {𝓢 : S} (h : 𝓢 ⊢ ⊥) (φ : F) : 𝓢 ⊢ φ := by
  rcases h with ⟨b⟩; exact ⟨dexp b φ⟩

lemma inconsistent_iff_provable_bot {𝓢 : S} :
    Inconsistent 𝓢 ↔ 𝓢 ⊢ ⊥ := ⟨fun h ↦ h ⊥, fun h φ ↦ DeductiveExplosion.dexp! h φ⟩

alias ⟨_, inconsistent_of_provable⟩ := inconsistent_iff_provable_bot

lemma consistent_iff_unprovable_bot {𝓢 : S} :
    Consistent 𝓢 ↔ 𝓢 ⊬ ⊥ := by
  simp [inconsistent_iff_provable_bot, ←not_inconsistent_iff_consistent]


-- @@ L298-299 verbatim
@[simp, grind .] lemma Consistent.not_bot {𝓢 : S} [Consistent 𝓢] : 𝓢 ⊬ ⊥ :=
  consistent_iff_unprovable_bot.mp inferInstance


-- @@ L301-301 verbatim
end


-- @@ L303-303 verbatim
/-! ### Completeness and incompleteness -/


-- @@ L305-305 verbatim
section


-- @@ L307-307 verbatim
variable [Tilde F] (𝓢 : S)


-- @@ L309-311 verbatim
/-- `𝓢` is complete if, for every formula, either it or its negation is provable by `𝓢`. -/
class Complete : Prop where
  con : ∀ φ, 𝓢 ⊢ φ ∨ 𝓢 ⊢ ∼φ


-- @@ L313-314 verbatim
/-- A formula `φ` is independent from `𝓢` if, neither it nor its negation is provable by `𝓢`. -/
def Independent (φ : F) : Prop := 𝓢 ⊬ φ ∧ 𝓢 ⊬ ∼φ


-- @@ L316-318 verbatim
/-- A proof system is incomplete if and only if there exists a formula that is both unprovable and irrefutable. -/
class Incomplete : Prop where
  indep : ∃ φ, Independent 𝓢 φ


-- @@ L320-326 verbatim
variable {𝓢 : S} {𝓣 : T}

lemma complete_def : Complete 𝓢 ↔ ∀ φ, 𝓢 ⊢ φ ∨ 𝓢 ⊢ ∼φ :=
  ⟨fun h ↦ h.con, Complete.mk⟩

lemma incomplete_def : Incomplete 𝓢 ↔ ∃ φ, Independent 𝓢 φ :=
  ⟨fun h ↦ h.indep, Incomplete.mk⟩


-- @@ L328-337 verbatim
omit [Tilde F] in
lemma Equiv.unprovable (e : 𝓢 ≊ 𝓣) {φ : F} : 𝓢 ⊬ φ ↔ 𝓣 ⊬ φ :=
  not_congr <| Equiv.iff.mp e φ

lemma Equiv.incomplete (e : 𝓢 ≊ 𝓣) : Incomplete 𝓢 → Incomplete 𝓣 := by
  rintro ⟨φ, hφ⟩
  exact ⟨φ, e.unprovable.mp hφ.1, e.unprovable.mp hφ.2⟩

lemma Equiv.incomplete_iff (e : 𝓢 ≊ 𝓣) : Incomplete 𝓢 ↔ Incomplete 𝓣 :=
  ⟨e.incomplete, e.symm.incomplete⟩


-- @@ L339-340 verbatim
@[simp] lemma not_complete_iff_incomplete : ¬Complete 𝓢 ↔ Incomplete 𝓢 := by
  simp [complete_def, incomplete_def, Independent, not_or]


-- @@ L342-343 verbatim
@[simp] lemma not_incomplete_iff_complete : ¬Incomplete 𝓢 ↔ Complete 𝓢 :=
  Iff.symm <| iff_not_comm.mp not_complete_iff_incomplete.symm


-- @@ L345-346 verbatim
instance consistent_of_incomplete [h : Incomplete 𝓢] : Consistent 𝓢 :=
  consistent_iff_exists_unprovable.mpr <| by rcases h.indep with ⟨φ, hφ⟩; exact ⟨φ, hφ.1⟩


-- @@ L348-348 verbatim
end


-- @@ L350-350 verbatim
/-! ### Axiomatized provability -/


-- @@ L352-352 verbatim
variable (S T)


-- @@ L354-358 verbatim
class Axiomatized [AdjunctiveSet F S] where
  prfAxm {𝓢 : S} : 𝓢 ⊢!* AdjunctiveSet.set 𝓢
  weakening {𝓢 𝓣 : S} : 𝓢 ⊆ 𝓣 → 𝓢 ⊢! φ → 𝓣 ⊢! φ

alias wk := Axiomatized.weakening


-- @@ L360-361 verbatim
class StrongCut [AdjunctiveSet F T] where
  cut {𝓢 : S} {𝓣 : T} {φ} : 𝓢 ⊢!* AdjunctiveSet.set 𝓣 → 𝓣 ⊢! φ → 𝓢 ⊢! φ


-- @@ L363-363 verbatim
variable {S T}


-- @@ L365-365 verbatim
section Axiomatized


-- @@ L367-367 verbatim
namespace Axiomatized


-- @@ L369-369 verbatim
variable [AdjunctiveSet F S] [Axiomatized S] {𝓢 𝓣 : S}


-- @@ L371-373 verbatim
def byAxm {𝓢 : S} (h : φ ∈ 𝓢) : 𝓢 ⊢! φ := prfAxm (by simp [h])

lemma by_axm {𝓢 : S} (h : φ ∈ 𝓢) : 𝓢 ⊢ φ := ⟨byAxm h⟩


-- @@ L375-377 verbatim
@[simp] lemma provable_refl (𝓢 : S) : 𝓢 ⊢* AdjunctiveSet.set 𝓢 := fun hf ↦ ⟨prfAxm hf⟩

lemma axm_subset (𝓢 : S) : AdjunctiveSet.set 𝓢 ⊆ theory 𝓢 := fun _ hp ↦ provable_refl 𝓢 hp


-- @@ L379-379 verbatim
protected def adjoin (φ : F) (𝓢 : S) : adjoin φ 𝓢 ⊢! φ := prfAxm (by simp)


-- @@ L381-385 verbatim
@[simp] theorem adjoin! (φ : F) (𝓢 : S) : adjoin φ 𝓢 ⊢ φ := provable_refl _ (by simp)

lemma le_of_subset (h : 𝓢 ⊆ 𝓣) : 𝓢 ⪯ 𝓣 := ⟨by rintro φ ⟨b⟩; exact ⟨weakening h b⟩⟩

lemma weakening! (h : 𝓢 ⊆ 𝓣 := by simp) {φ} : 𝓢 ⊢ φ → 𝓣 ⊢ φ := by rintro ⟨b⟩; exact ⟨weakening h b⟩


-- @@ L387-387 verbatim
abbrev weakerThanOfSubset (h : 𝓢 ⊆ 𝓣) : 𝓢 ⪯ 𝓣 := ⟨fun _ ↦ weakening! h⟩


-- @@ L389-389 verbatim
def toAdjoin {𝓢 : S} : 𝓢 ⊢! ψ → adjoin φ 𝓢 ⊢! ψ := fun b ↦ wk (by simp) b


-- @@ L391-391 verbatim
theorem to_adjoin {𝓢 : S} : 𝓢 ⊢ ψ → adjoin φ 𝓢 ⊢ ψ := fun b ↦ weakening! (by simp) b


-- @@ L393-397 verbatim
end Axiomatized

alias byAxm := Axiomatized.byAxm
alias by_axm := Axiomatized.by_axm
alias wk! := Axiomatized.weakening!


-- @@ L399-399 verbatim
section axiomatized


-- @@ L401-401 verbatim
variable [AdjunctiveSet F S] [AdjunctiveSet F T] [Axiomatized S]


-- @@ L403-409 verbatim
def FiniteAxiomatizable (𝓢 : S) : Prop := ∃ 𝓕 : S, AdjunctiveSet.Finite 𝓕 ∧ 𝓕 ≊ 𝓢

lemma Consistent.of_subset {𝓢 𝓣 : S} (h𝓢 : Consistent 𝓢) (h : 𝓣 ⊆ 𝓢) : Consistent 𝓣 :=
  h𝓢.of_le (Axiomatized.le_of_subset h)

lemma Inconsistent.of_supset {𝓢 𝓣 : S} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ⊆ 𝓣) : Inconsistent 𝓣 :=
  h𝓢.of_ge (Axiomatized.le_of_subset h)


-- @@ L411-411 verbatim
end axiomatized


-- @@ L413-413 verbatim
namespace StrongCut


-- @@ L415-418 verbatim
variable [AdjunctiveSet F T] [StrongCut S T]

lemma cut! {𝓢 : S} {𝓣 : T} {φ : F} (H : 𝓢 ⊢* AdjunctiveSet.set 𝓣) (hp : 𝓣 ⊢ φ) : 𝓢 ⊢ φ := by
  rcases hp with ⟨b⟩; exact ⟨StrongCut.cut H.get b⟩


-- @@ L420-420 verbatim
end StrongCut


-- @@ L422-423 verbatim
noncomputable abbrev WeakerThan.ofAxm! [AdjunctiveSet F S] [StrongCut S S] {𝓢₁ 𝓢₂ : S} (B : 𝓢₂ ⊢* AdjunctiveSet.set 𝓢₁) :
    𝓢₁ ⪯ 𝓢₂ := ⟨fun _ b ↦ StrongCut.cut! B b⟩


-- @@ L425-425 verbatim
abbrev WeakerThan.ofSubset [AdjunctiveSet F S] [Axiomatized S] {𝓢 𝓣 : S} (h : 𝓢 ⊆ 𝓣) : 𝓢 ⪯ 𝓣 := ⟨fun _ ↦ wk! h⟩


-- @@ L427-427 verbatim
/-! ### Compactness -/


-- @@ L429-429 verbatim
variable (S)


-- @@ L431-435 verbatim
class Compact [AdjunctiveSet F S] where
  core {𝓢 : S} {φ : F} : 𝓢 ⊢! φ → S
  corePrf {𝓢 : S} {φ : F} (b : 𝓢 ⊢! φ) : core b ⊢! φ
  core_subset {𝓢 : S} {φ : F} (b : 𝓢 ⊢! φ) : core b ⊆ 𝓢
  core_finite {𝓢 : S} {φ : F} (b : 𝓢 ⊢! φ) : AdjunctiveSet.Finite (core b)


-- @@ L437-437 verbatim
variable {S}


-- @@ L439-439 verbatim
namespace Compact


-- @@ L441-445 verbatim
variable [AdjunctiveSet F S] [Compact S]

lemma finite_provable {𝓢 : S} (h : 𝓢 ⊢ φ) : ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ AdjunctiveSet.Finite 𝓕 ∧ 𝓕 ⊢ φ := by
  rcases h with ⟨b⟩
  exact ⟨core b, core_subset b, core_finite b, ⟨corePrf b⟩⟩


-- @@ L447-447 verbatim
end Compact


-- @@ L449-449 verbatim
end Axiomatized


-- @@ L451-451 verbatim
end Entailment


-- @@ L453-453 verbatim
namespace Entailment


-- @@ L455-455 verbatim
variable {S : Type*} {F : Type*} [LogicalConnective F] [LogicalNeutral F] [Entailment S F]


-- @@ L457-457 verbatim
section


-- @@ L459-459 verbatim
variable [DeductiveExplosion S] [AdjunctiveSet F S] [Axiomatized S] [Compact S]


-- @@ L461-465 verbatim
omit [LogicalConnective F] in
lemma inconsistent_compact {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ AdjunctiveSet.Finite 𝓕 ∧ Inconsistent 𝓕 :=
  ⟨fun H ↦ by rcases Compact.finite_provable (H ⊥) with ⟨𝓕, h𝓕, fin, h⟩; exact ⟨𝓕, h𝓕, fin, inconsistent_of_provable h⟩, by
    rintro ⟨𝓕, h𝓕, _, H⟩; exact H.of_supset h𝓕⟩


-- @@ L467-470 verbatim
omit [LogicalConnective F] in
lemma consistent_compact {𝓢 : S} :
    Consistent 𝓢 ↔ ∀ 𝓕 : S, 𝓕 ⊆ 𝓢 → AdjunctiveSet.Finite 𝓕 → Consistent 𝓕 := by
  simp [←not_inconsistent_iff_consistent, inconsistent_compact (𝓢 := 𝓢)]


-- @@ L472-472 verbatim
end


-- @@ L474-474 verbatim
/-! ### Deduction theorem -/


-- @@ L476-476 verbatim
variable (S)


-- @@ L478-480 verbatim
class Deduction [Adjoin F S] where
  ofInsert {φ ψ : F} {𝓢 : S} : adjoin φ 𝓢 ⊢! ψ → 𝓢 ⊢! φ 🡒 ψ
  inv {φ ψ : F} {𝓢 : S} : 𝓢 ⊢! φ 🡒 ψ → adjoin φ 𝓢 ⊢! ψ


-- @@ L482-482 verbatim
variable {S}


-- @@ L484-484 verbatim
section deduction


-- @@ L486-488 verbatim
variable [Adjoin F S] [Deduction S] {𝓢 : S} {φ ψ : F}

alias deduction := Deduction.ofInsert


-- @@ L490-494 verbatim
omit [LogicalNeutral F] in
lemma Deduction.of_insert! (h : adjoin φ 𝓢 ⊢ ψ) : 𝓢 ⊢ φ 🡒 ψ := by
  rcases h with ⟨b⟩; exact ⟨Deduction.ofInsert b⟩

alias deduction! := Deduction.of_insert!


-- @@ L496-498 verbatim
omit [LogicalNeutral F] in
lemma Deduction.inv! (h : 𝓢 ⊢ φ 🡒 ψ) : adjoin φ 𝓢 ⊢ ψ := by
  rcases h with ⟨b⟩; exact ⟨Deduction.inv b⟩


-- @@ L500-501 verbatim
omit [LogicalNeutral F] in
lemma deduction_iff : adjoin φ 𝓢 ⊢ ψ ↔ 𝓢 ⊢ φ 🡒 ψ := ⟨deduction!, Deduction.inv!⟩


-- @@ L503-503 verbatim
end deduction


-- @@ L505-505 verbatim
end Entailment


-- @@ L507-507 verbatim
/-! ### Soundness and Completeness -/


-- @@ L509-509 verbatim
section


-- @@ L511-511 verbatim
variable {S : Type*} {F : Type*} [Entailment S F] {M : Type*} [Semantics M F]


-- @@ L513-514 verbatim
class Sound (𝓢 : S) (𝓜 : M) : Prop where
  sound : ∀ {φ : F}, 𝓢 ⊢ φ → 𝓜 ⊧ φ


-- @@ L516-517 verbatim
class Complete (𝓢 : S) (𝓜 : M) : Prop where
  complete : ∀ {φ : F}, 𝓜 ⊧ φ → 𝓢 ⊢ φ


-- @@ L519-519 verbatim
namespace Sound


-- @@ L521-521 verbatim
section


-- @@ L523-535 verbatim
variable {𝓢 𝓣 : S} {𝓜 𝓝 : M} [Sound 𝓢 𝓜] [Sound 𝓣 𝓝]

lemma not_provable_of_countermodel {φ : F} (hp : 𝓜 ⊭ φ) : 𝓢 ⊬ φ :=
  fun b ↦ hp (Sound.sound b)

lemma consistent_of_meaningful : Semantics.Meaningful 𝓜 → Entailment.Consistent 𝓢 :=
  fun H ↦ ⟨fun h ↦ by rcases H with ⟨φ, hf⟩; exact hf (Sound.sound (h φ))⟩

lemma consistent_of_model [LogicalNeutral F] [Semantics.Bot M] (𝓜 : M) [Sound 𝓢 𝓜] : Entailment.Consistent 𝓢 :=
  consistent_of_meaningful (𝓜 := 𝓜) inferInstance

lemma modelsSet_of_prfSet {T : Set F} (b : 𝓢 ⊢* T) : 𝓜 ⊧* T :=
  ⟨fun _ hf ↦ sound (b hf)⟩


-- @@ L537-537 verbatim
end


-- @@ L539-539 verbatim
section


-- @@ L541-546 verbatim
variable {𝓢 : S} {T : Set F} [Sound 𝓢 (Semantics.models M T)]

lemma consequence_of_provable {φ : F} : 𝓢 ⊢ φ → T ⊨[M] φ := sound

lemma consistent_of_satisfiable [∀ 𝓜 : M, Semantics.Meaningful 𝓜] : Semantics.Satisfiable M T → Entailment.Consistent 𝓢 :=
  fun H ↦ consistent_of_meaningful (Semantics.meaningful_iff_satisfiableSet.mp H)


-- @@ L548-548 verbatim
end


-- @@ L550-550 verbatim
end Sound


-- @@ L552-552 verbatim
namespace Complete


-- @@ L554-554 verbatim
section


-- @@ L556-566 verbatim
variable {𝓢 : S} {𝓜 : M} [Complete 𝓢 𝓜]

lemma exists_countermodel_of_not_provable {φ : F} (h : 𝓢 ⊬ φ) : 𝓜 ⊭ φ := by
  contrapose! h;
  simpa using Complete.complete (𝓢 := 𝓢) h;

lemma meaningful_of_consistent : Entailment.Consistent 𝓢 → Semantics.Meaningful 𝓜 := by
  contrapose
  suffices (∀ (φ : F), 𝓜 ⊧ φ) → Entailment.Inconsistent 𝓢 by
    simpa [Semantics.not_meaningful_iff, Entailment.not_consistent_iff_inconsistent]
  exact fun h φ ↦ Complete.complete (h φ)


-- @@ L568-568 verbatim
end


-- @@ L570-570 verbatim
section


-- @@ L572-576 verbatim
variable {𝓢 : S} {s : Set F} [Complete 𝓢 (Semantics.models M s)]

lemma provable_of_consequence {φ : F} : s ⊨[M] φ → 𝓢 ⊢ φ := complete

lemma provable_iff_consequence [Sound 𝓢 (Semantics.models M s)] {φ : F} : s ⊨[M] φ ↔ 𝓢 ⊢ φ := ⟨complete, Sound.sound⟩



-- @@ L579-579 verbatim
section


-- @@ L581-592 verbatim
variable [∀ 𝓜 : M, Semantics.Meaningful 𝓜]

lemma satisfiable_of_consistent :
    Entailment.Consistent 𝓢 → Semantics.Satisfiable M s :=
  fun H ↦ Semantics.meaningful_iff_satisfiableSet.mpr (meaningful_of_consistent H)

lemma inconsistent_of_unsatisfiable :
    ¬Semantics.Satisfiable M s → Entailment.Inconsistent 𝓢 := by
  contrapose; simpa [←Entailment.not_consistent_iff_inconsistent] using satisfiable_of_consistent

lemma consistent_iff_satisfiable [Sound 𝓢 (Semantics.models M s)] : Entailment.Consistent 𝓢 ↔ Semantics.Satisfiable M s :=
  ⟨satisfiable_of_consistent, Sound.consistent_of_satisfiable⟩


-- @@ L594-599 verbatim
end

lemma weakerthan_of_models {𝓣 : S} {t : Set F} [Sound 𝓣 (Semantics.models M t)]
    (H : ∀ 𝓜 : M, 𝓜 ⊧* s → 𝓜 ⊧* t) : 𝓣 ⪯ 𝓢 :=
  Entailment.weakerThan_iff.mpr <| fun h ↦ provable_of_consequence <|
    fun 𝓜 h𝓜 ↦ Sound.consequence_of_provable (M := M) (T := t) h (H 𝓜 h𝓜)


-- @@ L601-601 verbatim
end


-- @@ L603-603 verbatim
end Complete


-- @@ L605-605 verbatim
end


-- @@ L607-607 verbatim
namespace Entailment


-- @@ L609-609 verbatim
variable (S : Type*) {F : Type*} [Entailment S F]


-- @@ L611-612 verbatim
structure Pullback (f : G → F) : Type _ where
  forget : S


-- @@ L614-614 verbatim
variable {S}


-- @@ L616-616 verbatim
abbrev pullback (𝓢 : S) (f : G → F) : Pullback S f := ⟨𝓢⟩


-- @@ L618-619 verbatim
instance (f : G → F) : Entailment (Pullback S f) G where
  Prf := fun 𝓢 φ ↦ 𝓢.forget ⊢! f φ


-- @@ L621-621 verbatim
namespace Pullback


-- @@ L623-623 verbatim
section basics


-- @@ L625-625 verbatim
variable {f : G → F}


-- @@ L627-628 verbatim
omit [Entailment S F] in
@[simp] lemma pullback_forget (𝓢 : S) : (pullback 𝓢 f).forget = 𝓢 := rfl


-- @@ L630-630 verbatim
@[simp] lemma provable_iff {𝓢 : S} {φ : G} : pullback 𝓢 f ⊢ φ ↔ 𝓢 ⊢ f φ := by rfl


-- @@ L632-632 verbatim
@[simp] lemma unprovable_iff {𝓢 : S} {φ : G} : pullback 𝓢 f ⊬ φ ↔ 𝓢 ⊬ f φ := by rfl


-- @@ L634-635 verbatim
@[simp] lemma provableSet_iff {𝓢 : S} {s : Set G} : pullback 𝓢 f ⊢* s ↔ 𝓢 ⊢* f '' s := by
  simp [ProvableSet]


-- @@ L637-646 verbatim
@[simp] lemma theory_eq (𝓢 : S) : theory (pullback 𝓢 f) = f ⁻¹' theory 𝓢 := rfl

lemma weakerThan (𝓢 𝓣 : S) (h : 𝓢 ⪯ 𝓣) : pullback 𝓢 f ⪯ pullback 𝓣 f := by
  simp_all [Entailment.weakerThan_iff]

lemma inconsistent {𝓢 : S} : Inconsistent 𝓢 → Inconsistent (pullback 𝓢 f) := by
  simp_all [Inconsistent]

lemma consistent {𝓢 : S} : Consistent (pullback 𝓢 f) → Consistent 𝓢 := by
  contrapose; simpa using inconsistent


-- @@ L648-648 verbatim
end basics


-- @@ L650-650 verbatim
end Pullback


-- @@ L652-652 verbatim
end Entailment


-- @@ L654-654 verbatim
end FFL


-- @@ L656-656 verbatim
end
