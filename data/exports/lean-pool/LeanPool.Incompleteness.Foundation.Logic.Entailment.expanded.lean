/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.Semantics
public import LeanPool.Incompleteness.Foundation.Vorspiel.Collection
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Bound.Init


-- @@ L13-35 verbatim
/-!
# Basic definitions and properties of proof system related notions

This file defines a characterization of the system/proof/provability/calculus of formulae.
Also defines soundness and completeness.

## Main Definitions
* `LO.Entailment F S`: a general framework of deductive system `S` for formulae `F`.
* `LO.Entailment.Inconsistent 𝓢`: a proposition that states that all formulae in `F` is provable
* from `𝓢`.
* `LO.Entailment.Consistent 𝓢`: a proposition that states that `𝓢` is not inconsistent.
* `LO.Entailment.Sound 𝓢 𝓜`: provability from `𝓢` implies satisfiability on `𝓜`.
* `LO.Entailment.Complete 𝓢 𝓜`: satisfiability on `𝓜` implies provability from `𝓢`.

## Notation
* `𝓢 ⊢ φ`: a type of formalized proofs of `φ : F` from deductive system `𝓢 : S`.
* `𝓢 ⊢! φ`: a proposition that states there is a proof of `φ` from `𝓢`, i.e. `φ` is provable from
* `𝓢`.
* `𝓢 ⊬ φ`: a proposition that states `φ` is not provable from `𝓢`.
* `𝓢 ⊢* T`: a type of formalized proofs for each formulae in a set `T` from `𝓢`.
* `𝓢 ⊢!* T`: a proposition that states each formulae in `T` is provable from `𝓢`.

-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
namespace LO


-- @@ L41-44 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Entailment (F : outParam Type*) (S : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Prf : S → F → Type*


-- @@ L46-47 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢ " => Entailment.Prf


-- @@ L49-49 verbatim
namespace Entailment


-- @@ L51-51 verbatim
variable {F : Type*} {S T U : Type*} [Entailment F S] [Entailment F T] [Entailment F U]


-- @@ L53-53 verbatim
section «lp_section_1»


-- @@ L55-55 verbatim
variable (𝓢 : S)


-- @@ L57-58 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Provable (f : F) : Prop :=
  Nonempty (Entailment.Prf 𝓢 f)


-- @@ L60-61 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Unprovable (f : F) : Prop := ¬Provable 𝓢 f


-- @@ L63-64 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢! " => Provable


-- @@ L66-67 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊬ " => Unprovable


-- @@ L69-70 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def PrfSet (s : Set F) : Type _ :=
  {f : F} → f ∈ s → Entailment.Prf 𝓢 f


-- @@ L72-73 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ProvableSet (s : Set F) : Prop :=
  ∀ {f}, f ∈ s → Provable 𝓢 f


-- @@ L75-76 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢* " => PrfSet


-- @@ L78-79 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢!* " => ProvableSet


-- @@ L81-82 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def theory : Set F :=
  {f | Provable 𝓢 f}


-- @@ L84-84 verbatim
end «lp_section_1»


-- @@ L86-87 expanded
lemma unprovable_iff_isEmpty {𝓢 : S} {f : F} : Unprovable 𝓢 f ↔ IsEmpty (Entailment.Prf 𝓢 f) := by
  simp [Provable, Unprovable]


-- @@ L89-91 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.Entailment.Provable.get {𝓢 : S} {f : F} (h : Provable 𝓢 f) :
    Entailment.Prf 𝓢 f :=
  Classical.choice h


-- @@ L93-95 expanded
lemma provableSet_iff {𝓢 : S} {s : Set F} : ProvableSet 𝓢 s ↔ Nonempty (PrfSet 𝓢 s) := by
  simp [ProvableSet, PrfSet, Provable, Classical.nonempty_pi, ← imp_iff_not_or]


-- @@ L97-99 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.Entailment.ProvableSet.get {𝓢 : S} {s : Set F} (h : ProvableSet 𝓢 s) :
    PrfSet 𝓢 s :=
  Classical.choice (α := PrfSet 𝓢 s) (provableSet_iff.mp h : Nonempty (PrfSet 𝓢 s))


-- @@ L101-103 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class WeakerThan (𝓢 : S) (𝓣 : T) : Prop where
  subset : theory 𝓢 ⊆ theory 𝓣


-- @@ L105-106 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " wkn " => WeakerThan


-- @@ L108-111 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class StrictlyWeakerThan (𝓢 : S) (𝓣 : T) : Prop where
  weakerThan : WeakerThan 𝓢 𝓣
  notWT : ¬WeakerThan 𝓣 𝓢


-- @@ L113-114 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " swkn " => StrictlyWeakerThan


-- @@ L116-118 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Equiv (𝓢 : S) (𝓣 : T) : Prop where
  eq : theory 𝓢 = theory 𝓣


-- @@ L120-121 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ≊ " => Equiv


-- @@ L123-123 verbatim
section «lp_section_2»


-- @@ L125-125 verbatim
variable {𝓢 : S} {𝓣 : T} {𝓤 : U}


-- @@ L127-129 expanded
@[instance, simp, refl]
protected lemma _root_.LO.Entailment.WeakerThan.refl (𝓢 : S) : WeakerThan 𝓢 𝓢 :=
  ⟨Set.Subset.refl _⟩


-- @@ L131-131 expanded
lemma _root_.LO.Entailment.WeakerThan.wk (h : WeakerThan 𝓢 𝓣) {φ} : Provable 𝓢 φ → Provable 𝓣 φ :=
  @h.subset φ


-- @@ L133-133 expanded
lemma _root_.LO.Entailment.WeakerThan.pbl [h : WeakerThan 𝓢 𝓣] {φ} : Provable 𝓢 φ → Provable 𝓣 φ :=
  @h.subset φ


-- @@ L135-137 expanded
@[trans]
lemma _root_.LO.Entailment.WeakerThan.trans : WeakerThan 𝓢 𝓣 → WeakerThan 𝓣 𝓤 → WeakerThan 𝓢 𝓤 :=
  fun w₁ w₂ ↦ ⟨Set.Subset.trans w₁.subset w₂.subset⟩


-- @@ L139-140 expanded
lemma weakerThan_iff : WeakerThan 𝓢 𝓣 ↔ (∀ {f}, Provable 𝓢 f → Provable 𝓣 f) :=
  ⟨fun h _ hf ↦ h.subset hf, fun h ↦ ⟨fun _ hf ↦ h hf⟩⟩


-- @@ L142-142 expanded
lemma not_weakerThan_iff : ¬WeakerThan 𝓢 𝓣 ↔ (∃ f, Provable 𝓢 f ∧ Unprovable 𝓣 f) := by
  simp [weakerThan_iff, Unprovable];


-- @@ L144-150 expanded
lemma strictlyWeakerThan_iff :
    StrictlyWeakerThan 𝓢 𝓣 ↔
      (∀ {f}, Provable 𝓢 f → Provable 𝓣 f) ∧ (∃ f, Unprovable 𝓢 f ∧ Provable 𝓣 f) :=
  by
  constructor
  · rintro ⟨wt, nwt⟩
    exact
      ⟨weakerThan_iff.mp wt, by rcases not_weakerThan_iff.mp nwt with ⟨φ, ht, hs⟩;
        exact ⟨φ, hs, ht⟩⟩
  · rintro ⟨h, φ, hs, ht⟩
    exact ⟨weakerThan_iff.mpr h, not_weakerThan_iff.mpr ⟨φ, ht, hs⟩⟩


-- @@ L152-157 expanded
@[trans]
lemma _root_.LO.Entailment.strictlyWeakerThan.trans :
    StrictlyWeakerThan 𝓢 𝓣 → StrictlyWeakerThan 𝓣 𝓤 → StrictlyWeakerThan 𝓢 𝓤 :=
  by
  rintro ⟨h₁, nh₁⟩ ⟨h₂, _⟩
  refine ⟨WeakerThan.trans h₁ h₂, not_weakerThan_iff.mpr ?_⟩
  obtain ⟨f, hf₁, hf₂⟩ := not_weakerThan_iff.mp nh₁
  exact ⟨f, weakerThan_iff.mp h₂ hf₁, hf₂⟩


-- @@ L159-159 expanded
lemma weakening (h : WeakerThan 𝓢 𝓣) {f} : Provable 𝓢 f → Provable 𝓣 f :=
  weakerThan_iff.mp h


-- @@ L161-163 expanded
lemma _root_.LO.Entailment.StrictlyWeakerThan.of_unprovable_provable {𝓢 : S} {𝓣 : T}
    [WeakerThan 𝓢 𝓣] {φ : F} (hS : Unprovable 𝓢 φ) (hT : Provable 𝓣 φ) : StrictlyWeakerThan 𝓢 𝓣 :=
  ⟨inferInstance, fun h ↦ hS (h.wk hT)⟩


-- @@ L165-167 expanded
lemma _root_.LO.Entailment.Equiv.iff : Equiv 𝓢 𝓣 ↔ (∀ f, Provable 𝓢 f ↔ Provable 𝓣 f) :=
  ⟨fun e ↦ by simpa [Set.ext_iff, theory] using e.eq, fun e ↦
    ⟨by simpa [Set.ext_iff, theory] using e⟩⟩


-- @@ L169-169 expanded
@[instance, simp, refl]
protected lemma _root_.LO.Entailment.Equiv.refl (𝓢 : S) : Equiv 𝓢 𝓢 :=
  ⟨rfl⟩


-- @@ L171-171 expanded
@[symm]
lemma _root_.LO.Entailment.Equiv.symm : Equiv 𝓢 𝓣 → Equiv 𝓣 𝓢 := fun e ↦ ⟨Eq.symm e.eq⟩


-- @@ L173-175 expanded
@[trans]
lemma _root_.LO.Entailment.Equiv.trans : Equiv 𝓢 𝓣 → Equiv 𝓣 𝓤 → Equiv 𝓢 𝓤 := fun e₁ e₂ ↦
  ⟨Eq.trans e₁.eq e₂.eq⟩


-- @@ L177-181 expanded
lemma _root_.LO.Entailment.Equiv.antisymm_iff : Equiv 𝓢 𝓣 ↔ WeakerThan 𝓢 𝓣 ∧ WeakerThan 𝓣 𝓢 :=
  by
  refine
    ⟨fun e ↦ ⟨⟨Set.Subset.antisymm_iff.mp e.eq |>.1⟩, ⟨Set.Subset.antisymm_iff.mp e.eq |>.2⟩⟩, ?_⟩
  rintro ⟨w₁, w₂⟩
  exact ⟨Set.Subset.antisymm w₁.subset w₂.subset⟩


-- @@ L183-183 verbatim
alias ⟨_, Equiv.antisymm⟩ := Equiv.antisymm_iff


-- @@ L185-185 expanded
lemma _root_.LO.Entailment.Equiv.le : Equiv 𝓢 𝓣 → WeakerThan 𝓢 𝓣 := fun e ↦ ⟨by rw [e.eq]⟩


-- @@ L187-187 verbatim
end «lp_section_2»


-- @@ L189-189 expanded
@[simp]
lemma provableSet_theory (𝓢 : S) : ProvableSet 𝓢 (theory 𝓢) := fun hf ↦ hf


-- @@ L191-192 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Inconsistent (𝓢 : S) : Prop :=
  ∀ f, Provable 𝓢 f


-- @@ L194-196 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Consistent (𝓢 : S) : Prop where
  not_inconsistent : ¬Inconsistent 𝓢


-- @@ L198-199 expanded
lemma inconsistent_def {𝓢 : S} : Inconsistent 𝓢 ↔ ∀ f, Provable 𝓢 f := by simp [Inconsistent]


-- @@ L201-203 verbatim
lemma inconsistent_iff_theory_eq {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by
  simp [Inconsistent, Set.ext_iff, theory]


-- @@ L205-207 verbatim
lemma not_inconsistent_iff_consistent {𝓢 : S} :
    ¬Inconsistent 𝓢 ↔ Consistent 𝓢 :=
  ⟨fun h ↦ ⟨h⟩, by rintro ⟨h⟩; exact h⟩


-- @@ L209-209 verbatim
alias ⟨_, Consistent.not_inc⟩ := not_inconsistent_iff_consistent


-- @@ L211-212 verbatim
lemma not_consistent_iff_inconsistent {𝓢 : S} :
    ¬Consistent 𝓢 ↔ Inconsistent 𝓢 := by simp [←not_inconsistent_iff_consistent]


-- @@ L214-214 verbatim
alias ⟨_, Inconsistent.not_con⟩ := not_consistent_iff_inconsistent


-- @@ L216-218 expanded
lemma consistent_iff_exists_unprovable {𝓢 : S} : Consistent 𝓢 ↔ ∃ f, Unprovable 𝓢 f := by
  simp [← not_inconsistent_iff_consistent, inconsistent_def]


-- @@ L220-220 verbatim
alias ⟨Consistent.exists_unprovable, _⟩ := consistent_iff_exists_unprovable


-- @@ L222-223 expanded
lemma _root_.LO.Entailment.Consistent.of_unprovable {𝓢 : S} {f} (h : Unprovable 𝓢 f) :
    Consistent 𝓢 :=
  ⟨fun hp ↦ h (hp f)⟩


-- @@ L225-226 verbatim
lemma inconsistent_iff_theory_eq_univ {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by simp [inconsistent_def, theory, Set.ext_iff]


-- @@ L228-228 verbatim
alias ⟨Inconsistent.theory_eq, _⟩ := inconsistent_iff_theory_eq_univ


-- @@ L230-232 expanded
lemma _root_.LO.Entailment.Inconsistent.of_ge {𝓢 : S} {𝓣 : T} (h𝓢 : Inconsistent 𝓢)
    (h : WeakerThan 𝓢 𝓣) : Inconsistent 𝓣 := fun f ↦ h.subset (h𝓢 f)


-- @@ L234-236 expanded
lemma _root_.LO.Entailment.Consistent.of_le {𝓢 : S} {𝓣 : T} (h𝓢 : Consistent 𝓢)
    (h : WeakerThan 𝓣 𝓢) : Consistent 𝓣 :=
  ⟨fun H ↦ not_consistent_iff_inconsistent.mpr (H.of_ge h) h𝓢⟩


-- @@ L238-243 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[ext]
structure Translation {S S' F F'} [Entailment F S] [Entailment F' S'] (𝓢 : S) (𝓣 : S') where
  /-- Imported declaration from the Incompleteness formalization. -/
  toFun : F → F'
  /-- Imported declaration from the Incompleteness formalization. -/
  prf {f} : Entailment.Prf 𝓢 f → Entailment.Prf 𝓣 (toFun f)


-- @@ L245-246 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ↝ " => Translation


-- @@ L248-258 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[ext]
structure Bitranslation {S S' F F'} [Entailment F S] [Entailment F' S'] (𝓢 : S) (𝓣 : S') where
  /-- Imported declaration from the Incompleteness formalization. -/
  r : Translation 𝓢 𝓣
  /-- Imported declaration from the Incompleteness formalization. -/
  l : Translation 𝓣 𝓢
  /-- Imported declaration from the Incompleteness formalization. -/
  r_l : r.toFun ∘ l.toFun = id
  /-- Imported declaration from the Incompleteness formalization. -/
  l_r : l.toFun ∘ r.toFun = id


-- @@ L260-261 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ↭ " => Bitranslation


-- @@ L263-267 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[ext]
structure FaithfulTranslation {S S' F F'} [Entailment F S] [Entailment F' S'] (𝓢 : S)
    (𝓣 : S') extends Translation 𝓢 𝓣 where
  /-- Imported declaration from the Incompleteness formalization. -/
  prfInv {f} : Entailment.Prf 𝓣 (toFun f) → Entailment.Prf 𝓢 f


-- @@ L269-270 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ↝¹ " => FaithfulTranslation


-- @@ L272-272 verbatim
namespace Translation


-- @@ L274-274 verbatim
variable {S S' S'' : Type*} {F F' F'' : Type*} [Entailment F S] [Entailment F' S']

-- @@ L275-275 verbatim
variable [Entailment F'' S'']


-- @@ L277-278 expanded
/-- Imported declaration from the Incompleteness formalization. -/
instance (𝓢 : S) (𝓣 : S') : CoeFun (Translation 𝓢 𝓣) (fun _ ↦ F → F') :=
  ⟨Translation.toFun⟩


-- @@ L280-283 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def id (𝓢 : S) : Translation 𝓢 𝓢
    where
  toFun := id
  prf := id


-- @@ L285-285 verbatim
@[simp] lemma id_app (𝓢 : S) (f : F) : Translation.id 𝓢 f = f := rfl


-- @@ L287-290 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : Translation 𝓣 𝓤) (ψ : Translation 𝓢 𝓣) : Translation 𝓢 𝓤
    where
  toFun := φ.toFun ∘ ψ.toFun
  prf := φ.prf ∘ ψ.prf


-- @@ L292-293 expanded
@[simp]
lemma comp_app {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : Translation 𝓣 𝓤) (ψ : Translation 𝓢 𝓣) (f : F) :
    φ.comp ψ f = φ (ψ f) :=
  rfl


-- @@ L295-295 expanded
lemma provable {𝓢 : S} {𝓣 : S'} (f : Translation 𝓢 𝓣) {φ} (h : Provable 𝓢 φ) : Provable 𝓣 (f φ) :=
  ⟨f.prf h.get⟩


-- @@ L297-297 verbatim
end Translation


-- @@ L299-299 verbatim
namespace Bitranslation


-- @@ L301-301 verbatim
variable {S S' S'' : Type*} {F F' F'' : Type*} [Entailment F S] [Entailment F' S']

-- @@ L302-302 verbatim
variable [Entailment F'' S'']


-- @@ L304-304 expanded
@[simp]
lemma r_l_app {𝓢 : S} {𝓣 : S'} (f : Bitranslation 𝓢 𝓣) (φ : F') : f.r (f.l φ) = φ :=
  congr_fun f.r_l φ


-- @@ L306-306 expanded
@[simp]
lemma l_r_app {𝓢 : S} {𝓣 : S'} (f : Bitranslation 𝓢 𝓣) (φ : F) : f.l (f.r φ) = φ :=
  congr_fun f.l_r φ


-- @@ L308-313 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def id (𝓢 : S) : Bitranslation 𝓢 𝓢
    where
  r := Translation.id 𝓢
  l := Translation.id 𝓢
  r_l := by ext; simp
  l_r := by ext; simp


-- @@ L315-320 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def symm {𝓢 : S} {𝓣 : S'} (φ : Bitranslation 𝓢 𝓣) : Bitranslation 𝓣 𝓢
    where
  r := φ.l
  l := φ.r
  r_l := φ.l_r
  l_r := φ.r_l


-- @@ L322-327 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : Bitranslation 𝓣 𝓤) (ψ : Bitranslation 𝓢 𝓣) :
    Bitranslation 𝓢 𝓤 where
  r := φ.r.comp ψ.r
  l := ψ.l.comp φ.l
  r_l := by ext; simp
  l_r := by ext; simp


-- @@ L329-329 verbatim
end Bitranslation


-- @@ L331-331 verbatim
namespace FaithfulTranslation


-- @@ L333-333 verbatim
variable {S S' S'' : Type*} {F F' F'' : Type*} [Entailment F S] [Entailment F' S']

-- @@ L334-334 verbatim
variable [Entailment F'' S'']


-- @@ L336-336 expanded
instance (𝓢 : S) (𝓣 : S') : CoeFun (FaithfulTranslation 𝓢 𝓣) (fun _ ↦ F → F') :=
  ⟨fun t ↦ t.toFun⟩


-- @@ L338-342 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def id (𝓢 : S) : FaithfulTranslation 𝓢 𝓢
    where
  toFun := id
  prf := id
  prfInv := id


-- @@ L344-344 verbatim
@[simp] lemma id_app (𝓢 : S) (f : F) : FaithfulTranslation.id 𝓢 f = f := rfl


-- @@ L346-350 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : FaithfulTranslation 𝓣 𝓤) (ψ : FaithfulTranslation 𝓢 𝓣) :
    FaithfulTranslation 𝓢 𝓤 where
  toFun := φ.toFun ∘ ψ.toFun
  prf := φ.prf ∘ ψ.prf
  prfInv := ψ.prfInv ∘ φ.prfInv


-- @@ L352-353 expanded
@[simp]
lemma comp_app {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : FaithfulTranslation 𝓣 𝓤)
    (ψ : FaithfulTranslation 𝓢 𝓣) (f : F) : φ.comp ψ f = φ (ψ f) :=
  rfl


-- @@ L355-355 expanded
lemma provable {𝓢 : S} {𝓣 : S'} (f : FaithfulTranslation 𝓢 𝓣) {φ} (h : Provable 𝓢 φ) :
    Provable 𝓣 (f φ) :=
  ⟨f.prf h.get⟩


-- @@ L357-358 expanded
lemma provable_iff {𝓢 : S} {𝓣 : S'} (f : FaithfulTranslation 𝓢 𝓣) {φ} :
    Provable 𝓣 (f φ) ↔ Provable 𝓢 φ :=
  ⟨fun h ↦ ⟨f.prfInv h.get⟩, fun h ↦ ⟨f.prf h.get⟩⟩


-- @@ L360-360 verbatim
end FaithfulTranslation


-- @@ L362-362 verbatim
section «lp_section_3»


-- @@ L364-364 verbatim
variable [LogicalConnective F]


-- @@ L366-366 verbatim
variable (𝓢 : S)


-- @@ L368-369 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Complete : Prop :=
  ∀ f, Provable 𝓢 f ∨ Provable 𝓢 (Tilde.tilde f)


-- @@ L371-372 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Undecidable (f : F) : Prop :=
  Unprovable 𝓢 f ∧ Unprovable 𝓢 (Tilde.tilde f)


-- @@ L374-374 verbatim
end «lp_section_3»


-- @@ L376-377 verbatim
lemma incomplete_iff_exists_undecidable [LogicalConnective F] {𝓢 : S} :
    ¬Entailment.Complete 𝓢 ↔ ∃ f, Undecidable 𝓢 f := by simp [Complete, Undecidable, not_or]


-- @@ L379-379 verbatim
variable (S T)


-- @@ L381-386 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Axiomatized [Collection F S] where
  /-- Imported declaration from the Incompleteness formalization. -/
  prfAxm {𝓢 : S} : PrfSet 𝓢 (Collection.set 𝓢)
  /-- Imported declaration from the Incompleteness formalization. -/
  weakening {𝓢 𝓣 : S} : 𝓢 ⊆ 𝓣 → Entailment.Prf 𝓢 f → Entailment.Prf 𝓣 f


-- @@ L388-388 verbatim
alias byAxm := Axiomatized.prfAxm

-- @@ L389-389 verbatim
alias wk := Axiomatized.weakening


-- @@ L391-394 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class StrongCut [Collection F T] where
  /-- Imported declaration from the Incompleteness formalization. -/
  cut {𝓢 : S} {𝓣 : T} {φ} : PrfSet 𝓢 (Collection.set 𝓣) → Entailment.Prf 𝓣 φ → Entailment.Prf 𝓢 φ


-- @@ L396-396 verbatim
variable {S T}


-- @@ L398-398 verbatim
section «lp_section_4»


-- @@ L400-400 verbatim
namespace Axiomatized


-- @@ L402-402 verbatim
variable [Collection F S] [Axiomatized S] {𝓢 𝓣 : S}


-- @@ L404-404 expanded
@[simp]
lemma provable_axm (𝓢 : S) : ProvableSet 𝓢 (Collection.set 𝓢) := fun hf ↦ ⟨prfAxm hf⟩


-- @@ L406-406 verbatim
lemma axm_subset (𝓢 : S) : Collection.set 𝓢 ⊆ theory 𝓢 := fun _ hp ↦ provable_axm 𝓢 hp


-- @@ L408-408 expanded
lemma le_of_subset (h : 𝓢 ⊆ 𝓣) : WeakerThan 𝓢 𝓣 :=
  ⟨by rintro f ⟨b⟩; exact ⟨weakening h b⟩⟩


-- @@ L410-410 expanded
lemma weakening! (h : 𝓢 ⊆ 𝓣) {f} : Provable 𝓢 f → Provable 𝓣 f := by rintro ⟨b⟩;
  exact ⟨weakening h b⟩


-- @@ L412-413 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma weakerThanOfSubset (h : 𝓢 ⊆ 𝓣) : WeakerThan 𝓢 𝓣 :=
  ⟨fun _ ↦ weakening! h⟩


-- @@ L415-418 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def translation (h : 𝓢 ⊆ 𝓣) : Translation 𝓢 𝓣
    where
  toFun := id
  prf := weakening h


-- @@ L420-420 verbatim
end Axiomatized


-- @@ L422-422 verbatim
alias by_axm := Axiomatized.provable_axm

-- @@ L423-423 verbatim
alias wk! := Axiomatized.weakening!


-- @@ L425-425 verbatim
section «lp_section_5»


-- @@ L427-427 verbatim
variable [Collection F S] [Collection F T] [Axiomatized S]


-- @@ L429-430 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def FiniteAxiomatizable (𝓢 : S) : Prop :=
  ∃ 𝓕 : S, Collection.Finite 𝓕 ∧ Equiv 𝓕 𝓢


-- @@ L432-434 verbatim
lemma _root_.LO.Entailment.Consistent.of_subset {𝓢 𝓣 : S} (h𝓢 : Consistent 𝓢) (h : 𝓣 ⊆ 𝓢) :
    Consistent 𝓣 :=
  h𝓢.of_le (Axiomatized.le_of_subset h)


-- @@ L436-438 verbatim
lemma _root_.LO.Entailment.Inconsistent.of_supset {𝓢 𝓣 : S} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ⊆ 𝓣) :
    Inconsistent 𝓣 :=
  h𝓢.of_ge (Axiomatized.le_of_subset h)


-- @@ L440-440 verbatim
end «lp_section_5»


-- @@ L442-442 verbatim
namespace StrongCut


-- @@ L444-444 verbatim
variable [Collection F T] [StrongCut S T]


-- @@ L446-447 expanded
lemma cut! {𝓢 : S} {𝓣 : T} {φ : F} (H : ProvableSet 𝓢 (Collection.set 𝓣)) (hp : Provable 𝓣 φ) :
    Provable 𝓢 φ := by rcases hp with ⟨b⟩; exact ⟨StrongCut.cut H.get b⟩


-- @@ L449-452 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def translation {𝓢 : S} {𝓣 : T} (B : PrfSet 𝓢 (Collection.set 𝓣)) : Translation 𝓣 𝓢
    where
  toFun := id
  prf := StrongCut.cut B


-- @@ L454-454 verbatim
end StrongCut


-- @@ L456-456 verbatim
namespace WeakerThan


-- @@ L458-460 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma ofAxm! [Collection F S] [StrongCut S S] {𝓢₁ 𝓢₂ : S} (B : ProvableSet 𝓢₂ (Collection.set 𝓢₁)) :
    WeakerThan 𝓢₁ 𝓢₂ :=
  ⟨fun _ b ↦ StrongCut.cut! B b⟩


-- @@ L462-462 verbatim
end WeakerThan


-- @@ L464-468 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma _root_.LO.Entailment.WeakerThan.ofSubset [Collection F S] [Axiomatized S] {𝓢 𝓣 : S}
    (h : 𝓢 ⊆ 𝓣) : WeakerThan 𝓢 𝓣 :=
  ⟨fun _ ↦ wk! h⟩


-- @@ L470-470 verbatim
variable (S)


-- @@ L472-479 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Compact [Collection F S] where
  /-- Imported declaration from the Incompleteness formalization. -/
  φ {𝓢 : S} {f : F} : Entailment.Prf 𝓢 f → S
  /-- Imported declaration from the Incompleteness formalization. -/
  φPrf {𝓢 : S} {f : F} (b : Entailment.Prf 𝓢 f) : Entailment.Prf (φ b) f
  φ_subset {𝓢 : S} {f : F} (b : Entailment.Prf 𝓢 f) : φ b ⊆ 𝓢
  φ_finite {𝓢 : S} {f : F} (b : Entailment.Prf 𝓢 f) : Collection.Finite (φ b)


-- @@ L481-481 verbatim
variable {S}


-- @@ L483-483 verbatim
namespace Compact


-- @@ L485-485 verbatim
variable [Collection F S] [Compact S]


-- @@ L487-489 expanded
lemma finite_provable {𝓢 : S} (h : Provable 𝓢 f) :
    ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ Collection.Finite 𝓕 ∧ Provable 𝓕 f :=
  by
  rcases h with ⟨b⟩
  exact ⟨φ b, φ_subset b, φ_finite b, ⟨φPrf b⟩⟩


-- @@ L491-491 verbatim
end Compact


-- @@ L493-493 verbatim
end «lp_section_4»


-- @@ L495-495 verbatim
end Entailment


-- @@ L497-497 verbatim
namespace Entailment


-- @@ L499-499 verbatim
variable {S : Type*} {F : Type*} [LogicalConnective F] [Entailment F S]


-- @@ L501-501 verbatim
variable (S)


-- @@ L503-506 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class DeductiveExplosion where
  /-- Imported declaration from the Incompleteness formalization. -/
  dexp {𝓢 : S} : Entailment.Prf 𝓢 ⊥ → (φ : F) → Entailment.Prf 𝓢 φ


-- @@ L508-508 verbatim
variable {S}


-- @@ L510-510 verbatim
section «lp_section_6»


-- @@ L512-512 verbatim
variable [DeductiveExplosion S]


-- @@ L514-514 verbatim
namespace DeductiveExplosion


-- @@ L516-518 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma dexp! {𝓢 : S} (h : Provable 𝓢 ⊥) (f : F) : Provable 𝓢 f := by rcases h with ⟨b⟩;
  exact ⟨DeductiveExplosion.dexp b f⟩


-- @@ L520-520 verbatim
end DeductiveExplosion


-- @@ L522-523 expanded
lemma inconsistent_iff_provable_bot {𝓢 : S} : Inconsistent 𝓢 ↔ Provable 𝓢 ⊥ :=
  ⟨fun h ↦ h ⊥, fun h f ↦ DeductiveExplosion.dexp! h f⟩


-- @@ L525-525 verbatim
alias ⟨_, inconsistent_of_provable⟩ := inconsistent_iff_provable_bot


-- @@ L527-529 expanded
lemma consistent_iff_unprovable_bot {𝓢 : S} : Consistent 𝓢 ↔ Unprovable 𝓢 ⊥ := by
  simp [inconsistent_iff_provable_bot, ← not_inconsistent_iff_consistent]


-- @@ L531-531 verbatim
alias ⟨Consistent.not_bot, _⟩ := consistent_iff_unprovable_bot


-- @@ L533-533 verbatim
variable [Collection F S] [Axiomatized S] [Compact S]


-- @@ L535-539 verbatim
lemma inconsistent_compact {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ Collection.Finite 𝓕 ∧ Inconsistent 𝓕 :=
  ⟨fun H ↦ by rcases Compact.finite_provable (H ⊥) with ⟨𝓕, h𝓕, fin, h⟩; exact ⟨𝓕, h𝓕, fin,
    inconsistent_of_provable h⟩, by
    rintro ⟨𝓕, h𝓕, _, H⟩; exact H.of_supset h𝓕⟩


-- @@ L541-543 verbatim
lemma consistent_compact {𝓢 : S} :
    Consistent 𝓢 ↔ ∀ 𝓕 : S, 𝓕 ⊆ 𝓢 → Collection.Finite 𝓕 → Consistent 𝓕 := by
  simp [←not_inconsistent_iff_consistent, inconsistent_compact (𝓢 := 𝓢)]


-- @@ L545-545 verbatim
end «lp_section_6»


-- @@ L547-547 verbatim
variable (S)


-- @@ L549-554 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Deduction [Cons F S] where
  /-- Imported declaration from the Incompleteness formalization. -/
  ofInsert {φ ψ : F} {𝓢 : S} : Entailment.Prf (cons φ 𝓢) ψ → Entailment.Prf 𝓢 (Arrow.arrow φ ψ)
  /-- Imported declaration from the Incompleteness formalization. -/
  inv {φ ψ : F} {𝓢 : S} : Entailment.Prf 𝓢 (Arrow.arrow φ ψ) → Entailment.Prf (cons φ 𝓢) ψ


-- @@ L556-556 verbatim
variable {S}


-- @@ L558-558 verbatim
section «lp_section_7»


-- @@ L560-560 verbatim
variable [Cons F S] [Deduction S] {𝓢 : S} {φ ψ : F}


-- @@ L562-562 verbatim
alias deduction := Deduction.ofInsert


-- @@ L564-564 verbatim
namespace Deduction


-- @@ L566-567 expanded
lemma of_insert! (h : Provable (cons φ 𝓢) ψ) : Provable 𝓢 (Arrow.arrow φ ψ) := by rcases h with ⟨b⟩;
  exact ⟨Deduction.ofInsert b⟩


-- @@ L569-569 verbatim
alias deduction! := Deduction.of_insert!


-- @@ L571-572 expanded
lemma inv! (h : Provable 𝓢 (Arrow.arrow φ ψ)) : Provable (cons φ 𝓢) ψ := by rcases h with ⟨b⟩;
  exact ⟨Deduction.inv b⟩


-- @@ L574-574 verbatim
end Deduction


-- @@ L576-579 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.Deduction.translation (φ : F) (𝓢 : S) : Translation (cons φ 𝓢) 𝓢
    where
  toFun := fun ψ ↦ Arrow.arrow φ ψ
  prf := deduction


-- @@ L581-582 expanded
lemma deduction_iff : Provable (cons φ 𝓢) ψ ↔ Provable 𝓢 (Arrow.arrow φ ψ) :=
  ⟨Deduction.of_insert!, Deduction.inv!⟩


-- @@ L584-584 verbatim
end «lp_section_7»


-- @@ L586-586 verbatim
end Entailment


-- @@ L588-588 verbatim
section «lp_section_8»


-- @@ L590-590 verbatim
variable {S : Type*} {F : Type*} [Entailment F S] {M : Type*} [Semantics F M]


-- @@ L592-594 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Sound (𝓢 : S) (𝓜 : M) : Prop where
  sound : ∀ {f : F}, Provable 𝓢 f → Realize 𝓜 f


-- @@ L596-598 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Complete (𝓢 : S) (𝓜 : M) : Prop where
  complete : ∀ {f : F}, Realize 𝓜 f → Provable 𝓢 f


-- @@ L600-600 verbatim
namespace Sound


-- @@ L602-602 verbatim
section «lp_section_9»


-- @@ L604-604 verbatim
variable {𝓢 𝓣 : S} {𝓜 𝓝 : M} [Sound 𝓢 𝓜] [Sound 𝓣 𝓝]


-- @@ L606-607 expanded
lemma not_provable_of_countermodel {φ : F} (hp : ¬Realize 𝓜 φ) : Unprovable 𝓢 φ := fun b ↦
  hp (Sound.sound b)


-- @@ L609-610 verbatim
lemma consistent_of_meaningful : Semantics.Meaningful 𝓜 → Entailment.Consistent 𝓢 :=
  fun H ↦ ⟨fun h ↦ by rcases H with ⟨f, hf⟩; exact hf (Sound.sound (h f))⟩


-- @@ L612-614 verbatim
lemma consistent_of_model [LogicalConnective F] [Semantics.Bot M] (𝓜 : M) [Sound 𝓢 𝓜] :
    Entailment.Consistent 𝓢 :=
  consistent_of_meaningful (𝓜 := 𝓜) inferInstance


-- @@ L616-617 expanded
lemma realizeSet_of_prfSet {T : Set F} (b : ProvableSet 𝓢 T) : RealizeSet 𝓜 T :=
  ⟨fun _ hf => sound (b hf)⟩


-- @@ L619-619 verbatim
end «lp_section_9»


-- @@ L621-621 verbatim
section «lp_section_10»


-- @@ L623-623 verbatim
variable {𝓢 : S} {T : Set F} [Sound 𝓢 (Semantics.models M T)]


-- @@ L625-625 expanded
lemma consequence_of_provable {f : F} : Provable 𝓢 f → Consequence M T f :=
  sound


-- @@ L627-629 verbatim
lemma consistent_of_satisfiable [∀ 𝓜 : M, Semantics.Meaningful 𝓜] :
    Semantics.Satisfiable M T → Entailment.Consistent 𝓢 :=
  fun H ↦ consistent_of_meaningful (Semantics.meaningful_iff_satisfiableSet.mp H)


-- @@ L631-631 verbatim
end «lp_section_10»


-- @@ L633-633 verbatim
end Sound


-- @@ L635-635 verbatim
namespace Complete


-- @@ L637-637 verbatim
section «lp_section_11»


-- @@ L639-639 verbatim
variable {𝓢 : S} {𝓜 : M} [Complete 𝓢 𝓜]


-- @@ L641-645 expanded
lemma meaningful_of_consistent : Entailment.Consistent 𝓢 → Semantics.Meaningful 𝓜 :=
  by
  contrapose
  suffices (∀ (f : F), Realize 𝓜 f) → Entailment.Inconsistent 𝓢 by
    simpa [Semantics.not_meaningful_iff, Entailment.not_consistent_iff_inconsistent]
  exact fun h f ↦ Complete.complete (h f)


-- @@ L647-647 verbatim
end «lp_section_11»


-- @@ L649-649 verbatim
section «lp_section_12»


-- @@ L651-651 verbatim
variable {𝓢 : S} {s : Set F} [Complete 𝓢 (Semantics.models M s)]


-- @@ L653-653 expanded
lemma provable_of_consequence {f : F} : Consequence M s f → Provable 𝓢 f :=
  complete


-- @@ L655-657 expanded
lemma provable_iff_consequence [Sound 𝓢 (Semantics.models M s)] {f : F} :
    Consequence M s f ↔ Provable 𝓢 f :=
  ⟨complete, Sound.sound⟩


-- @@ L660-660 verbatim
section «lp_section_13»


-- @@ L662-662 verbatim
variable [LogicalConnective F] [∀ 𝓜 : M, Semantics.Meaningful 𝓜]


-- @@ L664-667 verbatim
omit [LogicalConnective F] in
lemma satisfiable_of_consistent :
    Entailment.Consistent 𝓢 → Semantics.Satisfiable M s :=
  fun H ↦ Semantics.meaningful_iff_satisfiableSet.mpr (meaningful_of_consistent H)


-- @@ L669-672 verbatim
omit [LogicalConnective F] in
lemma inconsistent_of_unsatisfiable :
    ¬Semantics.Satisfiable M s → Entailment.Inconsistent 𝓢 := by
  contrapose; simpa [←Entailment.not_consistent_iff_inconsistent] using satisfiable_of_consistent


-- @@ L674-677 verbatim
omit [LogicalConnective F] in
lemma consistent_iff_satisfiable [Sound 𝓢 (Semantics.models M s)] :
    Entailment.Consistent 𝓢 ↔ Semantics.Satisfiable M s :=
  ⟨satisfiable_of_consistent, Sound.consistent_of_satisfiable⟩


-- @@ L679-679 verbatim
end «lp_section_13»


-- @@ L681-685 expanded
lemma weakerthan_of_models {𝓣 : S} {t : Set F} [Sound 𝓣 (Semantics.models M t)]
    (H : ∀ 𝓜 : M, RealizeSet 𝓜 s → RealizeSet 𝓜 t) : WeakerThan 𝓣 𝓢 :=
  Entailment.weakerThan_iff.mpr <| fun h ↦
    provable_of_consequence <| fun 𝓜 h𝓜 ↦ Sound.consequence_of_provable (M := M) (T := t) h (H 𝓜 h𝓜)


-- @@ L687-687 verbatim
end «lp_section_12»


-- @@ L689-689 verbatim
end Complete


-- @@ L691-691 verbatim
end «lp_section_8»


-- @@ L693-693 verbatim
end LO
