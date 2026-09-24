module

public import Foundation.FirstOrder.Basic
public import Mathlib.Logic.Equiv.List


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-7 verbatim
namespace FFL


-- @@ L9-9 verbatim
namespace FirstOrder


-- @@ L11-11 verbatim
variable {L : Language.{u}}


-- @@ L13-13 verbatim
/-! ### Finite sublanguage -/


-- @@ L15-15 verbatim
namespace Language


-- @@ L17-20 verbatim
def sublanguage (L : Language) (pFunc : ∀ k, L.Func k → Prop) (pRel : ∀ k, L.Rel k → Prop) :
    Language where
  Func k := Subtype (pFunc k)
  Rel k := Subtype (pRel k)


-- @@ L22-22 verbatim
section sublanguage


-- @@ L24-24 verbatim
variable (L)


-- @@ L26-26 verbatim
variable {pf : (k : ℕ) → L.Func k → Prop} {pr : (k : ℕ) → L.Rel k → Prop}


-- @@ L28-30 verbatim
def unsub : sublanguage L pf pr →ᵥ L where
  func := Subtype.val
  rel  := Subtype.val


-- @@ L32-33 verbatim
@[simp] lemma unsub_onFunc :
    L.unsub.func φ = φ.val := rfl


-- @@ L35-36 verbatim
@[simp] lemma unsub_onRel :
    L.unsub.rel φ = φ.val := rfl


-- @@ L38-38 verbatim
end sublanguage


-- @@ L40-40 verbatim
end Language


-- @@ L42-42 verbatim
namespace Semiterm


-- @@ L44-44 verbatim
open Language

-- @@ L45-45 verbatim
variable [∀ k, DecidableEq (L.Func k)]


-- @@ L47-50 verbatim
def symbols : Semiterm L ξ n → Finset (Σ k, L.Func k)
  |       #_ => ∅
  |       &_ => ∅
  | func f v => insert ⟨_, f⟩ (Finset.biUnion Finset.univ (fun i ↦ symbols (v i)))


-- @@ L52-57 verbatim
@[simp] lemma lang_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    ⟨k, f⟩ ∈ (func f v).symbols := by simp [symbols]

lemma lang_func_ss {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).symbols ⊆ (func f v).symbols := by
  intros x; simp [symbols]; grind


-- @@ L59-64 verbatim
def toSublanguage (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) : ∀ t : Semiterm L ξ n,
    (∀ k f, ⟨k, f⟩ ∈ t.symbols → pf k f) → Semiterm (sublanguage L pf pr) ξ n
  |                    #x, _ => #x
  |                    &x, _ => &x
  | func (arity := k) f v, h => func ⟨f, h k f (by simp)⟩
      (fun i ↦ toSublanguage pf pr (v i) (fun k' f' h' => h k' f' (lang_func_ss f v i h')))


-- @@ L66-72 verbatim
@[simp] lemma lMap_toSublanguage (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop)
  (t : Semiterm L ξ n) (h : ∀ k f, ⟨k, f⟩ ∈ t.symbols → pf k f) :
    (t.toSublanguage pf pr h).lMap L.unsub = t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih => exact congrArg (Semiterm.func f) (funext fun i ↦ ih i _)


-- @@ L74-74 verbatim
end Semiterm


-- @@ L76-76 verbatim
namespace Semiformula


-- @@ L78-78 verbatim
variable [L.DecidableEq]


-- @@ L80-88 verbatim
noncomputable def functionSymbols {n} : Semiformula L ξ n → Finset (Σ k, L.Func k)
  | rel  _ v => Finset.biUnion Finset.univ fun i ↦ (v i).symbols
  | nrel _ v => Finset.biUnion Finset.univ fun i ↦ (v i).symbols
  |        ⊤ => ∅
  |        ⊥ => ∅
  |    φ ⋏ ψ => functionSymbols φ ∪ functionSymbols ψ
  |    φ ⋎ ψ => functionSymbols φ ∪ functionSymbols ψ
  |     ∀¹ φ => functionSymbols φ
  |     ∃¹ φ => functionSymbols φ


-- @@ L90-104 verbatim
noncomputable def relationSymbols {n} : Semiformula L ξ n → Finset (Σ k, L.Rel k)
  | rel  r _ => {⟨_, r⟩}
  | nrel r _ => {⟨_, r⟩}
  |        ⊤ => ∅
  |        ⊥ => ∅
  |    φ ⋏ ψ => relationSymbols φ ∪ relationSymbols ψ
  |    φ ⋎ ψ => relationSymbols φ ∪ relationSymbols ψ
  |     ∀¹ φ => relationSymbols φ
  |     ∃¹ φ => relationSymbols φ

lemma functionSymbols_rel_ss {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).symbols ⊆ (rel r v).functionSymbols := by
  intros x
  simp only [functionSymbols, Finset.mem_biUnion, Finset.mem_univ, true_and]
  intros h; exact ⟨i, h⟩


-- @@ L106-126 verbatim
def toSublanguage (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) {n} :
    (φ : Semiformula L ξ n) →
    (∀ k f, ⟨k, f⟩ ∈ φ.functionSymbols → pf k f) →
    (∀ k r, ⟨k, r⟩ ∈ φ.relationSymbols → pr k r) →
    Semiformula (L.sublanguage pf pr) ξ n
  |  rel r v, hf, hr =>
      rel ⟨r, hr _ r (by simp [relationSymbols])⟩
        fun i ↦ (v i).toSublanguage pf pr fun k f h ↦ hf k f (functionSymbols_rel_ss r v i h)
  | nrel r v, hf, hr =>
      nrel ⟨r, hr _ r (by simp [relationSymbols])⟩
        fun i ↦ (v i).toSublanguage pf pr fun k f h ↦ hf k f (functionSymbols_rel_ss r v i h)
  |        ⊤,  _,  _ => ⊤
  |        ⊥,  _,  _ => ⊥
  |    φ ⋏ ψ,  hf, hr =>
      toSublanguage pf pr φ (fun k f h ↦ hf k f (Finset.mem_union_left _ h)) (fun k r h ↦ hr k r (Finset.mem_union_left _ h)) ⋏
      toSublanguage pf pr ψ (fun k f h ↦ hf k f (Finset.mem_union_right _ h)) (fun k r h ↦ hr k r (Finset.mem_union_right _ h))
  |    φ ⋎ ψ, hf, hr =>
      toSublanguage pf pr φ (fun k f h ↦ hf k f (Finset.mem_union_left _ h)) (fun k r h ↦ hr k r (Finset.mem_union_left _ h)) ⋎
      toSublanguage pf pr ψ (fun k f h ↦ hf k f (Finset.mem_union_right _ h)) (fun k r h ↦ hr k r (Finset.mem_union_right _ h))
  |     ∀¹ φ, hf, hr => ∀¹ toSublanguage pf pr φ hf hr
  |     ∃¹ φ, hf, hr => ∃¹ toSublanguage pf pr φ hf hr


-- @@ L128-140 verbatim
@[simp] lemma lMap_toSublanguage
  (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) {n} (φ : Semiformula L ξ n)
  (hf : ∀ k f, ⟨k, f⟩ ∈ φ.functionSymbols → pf k f) (hr : ∀ k r, ⟨k, r⟩ ∈ φ.relationSymbols → pr k r) :
    lMap L.unsub (φ.toSublanguage pf pr hf hr) = φ := by
  induction φ using rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => exact congrArg (Semiformula.rel r) (funext fun i ↦ Semiterm.lMap_toSublanguage _ _ _ _)
  | hnrel r v => exact congrArg (Semiformula.nrel r) (funext fun i ↦ Semiterm.lMap_toSublanguage _ _ _ _)
  | hand φ ψ ihφ ihψ => simp [*, toSublanguage]
  | hor φ ψ ihφ ihψ => simp [*, toSublanguage]
  | hall φ ih => exact congrArg Semiformula.all (ih hf hr)
  | hexs φ ih => exact congrArg Semiformula.exs (ih hf hr)


-- @@ L142-142 verbatim
variable (φ : Semiformula L ξ n)


-- @@ L144-146 verbatim
/-- A language consists of the function and relation symbols appearing in a given finite set of formulas. -/
abbrev sublanguage : Language :=
  Language.sublanguage L (fun k f ↦ ⟨k, f⟩ ∈ φ.functionSymbols) (fun k r ↦ ⟨k, r⟩ ∈ φ.relationSymbols)


-- @@ L148-149 verbatim
noncomputable instance (k) : Fintype (φ.sublanguage.Func k) :=
  Fintype.subtype (φ.functionSymbols.preimage (⟨k, ·⟩) (Set.injOn_of_injective sigma_mk_injective)) (by simp)


-- @@ L151-152 verbatim
noncomputable instance (k) : Fintype (φ.sublanguage.Rel k) :=
  Fintype.subtype (φ.relationSymbols.preimage (⟨k, ·⟩) (Set.injOn_of_injective sigma_mk_injective)) (by simp)


-- @@ L154-156 verbatim
noncomputable instance : φ.sublanguage.Encodable where
  func _ := Fintype.toEncodable _
  rel  _ := Fintype.toEncodable _


-- @@ L158-159 verbatim
def toSubLanguageSelf (φ : Semiformula L ξ n) : Semiformula φ.sublanguage ξ n :=
  φ.toSublanguage _ _ (fun _ _ ↦ id) (fun _ _ ↦ id)


-- @@ L161-163 verbatim
@[simp] lemma lMap_toSubLanguage {φ : Semiformula L ξ n} :
    φ.toSubLanguageSelf.lMap L.unsub = φ :=
  lMap_toSublanguage _ _ _ _ _


-- @@ L165-165 verbatim
end Semiformula


-- @@ L167-167 verbatim
/-! ### Structure induced by an injective language homomorphism -/


-- @@ L169-169 verbatim
namespace Language


-- @@ L171-173 verbatim
class Hom.Injective (Φ : L₁ →ᵥ L₂) : Prop where
  func : ∀ k, Function.Injective (Φ.func : L₁.Func k → L₂.Func k)
  rel  : ∀ k, Function.Injective (Φ.rel  : L₁.Rel k → L₂.Rel k)


-- @@ L175-177 verbatim
instance unsub_injective (pf : ∀ k, L.Func k → Prop) (pr : ∀ k, L.Rel k → Prop) :
    (L.unsub : L.sublanguage pf pr →ᵥ L).Injective :=
  ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ Subtype.val_injective⟩


-- @@ L179-179 verbatim
end Language


-- @@ L181-181 verbatim
namespace Structure


-- @@ L183-185 verbatim
noncomputable abbrev extendStructure (Φ : L₁ →ᵥ L₂) {M : Type*} [Nonempty M] (s : Structure L₁ M) : Structure L₂ M where
  func {k} f₂ v := Classical.epsilon (∃ f₁ : L₁.Func k, Φ.func f₁ = f₂ ∧ · = s.func f₁ v)
  rel {k} r₂ v := ∃ r₁ : L₁.Rel k, Φ.rel r₁ = r₂ ∧ s.rel r₁ v


-- @@ L187-187 verbatim
namespace extendStructure


-- @@ L189-189 verbatim
variable {M : Type*} [Nonempty M] (s₁ : Structure L₁ M)


-- @@ L191-197 verbatim
protected lemma func
    (Φ : L₁ →ᵥ L₂) [hΦ : Φ.Injective]
    (f₁ : L₁.Func k) (v : Fin k → M) :
    (s₁.extendStructure Φ).func (Φ.func f₁) v = s₁.func f₁ v := by
  have : ∃ y, ∃ f₁' : L₁.Func k, Φ.func f₁' = Φ.func f₁ ∧ y = s₁.func f₁' v := ⟨s₁.func f₁ v, f₁, rfl, rfl⟩
  rcases Classical.epsilon_spec this with ⟨f', f'eq, h⟩
  rcases hΦ.func k f'eq with rfl; exact h


-- @@ L199-214 verbatim
protected lemma rel
    (Φ : L₁ →ᵥ L₂) [hΦ : Φ.Injective]
    (r₁ : L₁.Rel k) (v : Fin k → M) :
    (s₁.extendStructure Φ).rel (Φ.rel r₁) v ↔ s₁.rel r₁ v := by
  refine ⟨by intros h; rcases h with ⟨r₁', bv, h⟩; rcases hΦ.rel k bv with rfl; exact h, by intros h; refine ⟨r₁, rfl, h⟩⟩

lemma val_lMap
    (Φ : L₁ →ᵥ L₂) [Φ.Injective]
    (bv : Fin n → M) (fv : ξ → M)
    (t : Semiterm L₁ ξ n) :
    (t.lMap Φ).val (s := s₁.extendStructure Φ) bv fv = t.val bv fv := by
  induction t
  case func k f v ih =>
    simpa [ih, Function.comp_def] using extendStructure.func s₁ Φ f fun i ↦ (v i).val bv fv
  case _ => simp [*]
  case _ => simp [*]


-- @@ L216-239 verbatim
open Semiformula

lemma eval_lMap (Φ : L₁ →ᵥ L₂) [Φ.Injective]
    (bv : Fin n → M) (fv : ξ → M)
    {φ : Semiformula L₁ ξ n} :
    (lMap Φ φ).Eval (s := s₁.extendStructure Φ) bv fv ↔ φ.Eval bv fv := by
  induction φ using Semiformula.rec'
  case hrel k r v =>
    simp only [Semiformula.lMap_rel, eval_rel, val_lMap s₁ Φ bv fv, Function.comp_def]
    exact extendStructure.rel s₁ Φ r (fun i ↦ (v i).val bv fv)
  case hnrel k r v =>
    simp only [lMap_nrel, eval_nrel, val_lMap s₁ Φ bv fv, Function.comp_def]
    simpa [not_iff_not] using
      extendStructure.rel s₁ Φ r (fun i ↦ (v i).val bv fv)
  case _ => simp [*]
  case _ => simp [*]
  case _ => simp [*]
  case _ => simp [*]
  case _ => simp [*]
  case _ => simp [*]

lemma models_lMap (Φ : L₁ →ᵥ L₂) [Φ.Injective] (φ : Sentence L₁) :
    (s₁.extendStructure Φ).toStruc ⊧ φ.lMap Φ ↔ s₁.toStruc ⊧ φ := by
  simp [Semantics.Models, eval_lMap s₁ Φ]


-- @@ L241-241 verbatim
end extendStructure


-- @@ L243-243 verbatim
end Structure


-- @@ L245-245 verbatim
section lMap


-- @@ L247-266 verbatim
variable {L₁ : Language.{u}} {L₂ : Language.{u}}

lemma lMap_models_lMap_iff (Φ : L₁ →ᵥ L₂) [Φ.Injective] {T : Theory L₁} {φ : Sentence L₁} :
    T.lMap Φ ⊨ φ.lMap Φ ↔ T ⊨ φ := by
  constructor
  · intro h s₁ hs₁
    refine (Structure.extendStructure.models_lMap s₁.struc Φ φ).mp <| h ?_
    suffices ∀ σ ∈ T, (Structure.extendStructure Φ s₁.struc).toStruc ⊧ σ.lMap Φ by
      simpa [Semantics.modelsSet_iff, Theory.lMap, Semantics.models]
    intro σ hσ
    exact (Structure.extendStructure.models_lMap s₁.struc Φ σ).mpr (hs₁.models _ hσ)
  · exact lMap_models_lMap

lemma satisfiable_lMap (Φ : L₁ →ᵥ L₂) [Φ.Injective] {T : Theory L₁} (s : Satisfiable T) :
    Satisfiable (T.lMap Φ) := by
  rcases s with ⟨⟨M, i, s⟩, hM⟩
  exact ⟨⟨M, i, s.extendStructure Φ⟩, by
    have : ∀ φ ∈ T, (Structure.extendStructure Φ s).toStruc ⊧ φ.lMap Φ :=
      fun φ hφ ↦ (Structure.extendStructure.models_lMap s Φ φ).mpr (hM.models _ hφ)
    simpa [Theory.lMap] using this⟩


-- @@ L268-268 verbatim
end lMap


-- @@ L270-270 verbatim
end FirstOrder


-- @@ L272-272 verbatim
end FFL
