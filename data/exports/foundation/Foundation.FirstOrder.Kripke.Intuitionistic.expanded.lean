module

public import Foundation.FirstOrder.Intuitionistic.LJ
public import Foundation.FirstOrder.Kripke.Basic


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-7 verbatim
/-! # Kripke semantics for intuitionistic first-order logic -/


-- @@ L9-9 verbatim
namespace FFL.FirstOrder


-- @@ L11-11 verbatim
variable {L : Language} [L.Relational]


-- @@ L13-13 verbatim
namespace KripkeModel


-- @@ L15-15 verbatim
variable {W : Type*} [Preorder W] {C : Type*} [KripkeModel L W C]


-- @@ L17-24 expanded
def Forces {n} (w : W) (bv : Fin n → C) (fv : ξ → C) : Semiformulaᵢ L ξ n → Prop
  | .rel R t => Rel w R fun i ↦ (t i).relationalVal bv fv
  | ⊥ => False
  | binop% HWedge.hWedge φ ψ => Forces w bv fv φ ∧ Forces w bv fv ψ
  | binop% HVee.hVee φ ψ => Forces w bv fv φ ∨ Forces w bv fv ψ
  | binop% HArrow.hArrow φ ψ => ∀ v ≤ w, Forces v bv fv φ → Forces v bv fv ψ
  | UnivQuantifier.all φ => ∀ v ≤ w, ∀ x : v, Forces v (vecCons x.val bv) fv φ
  | ExsQuantifier.exs φ => ∃ x : w, Forces w (vecCons x.val bv) fv φ


-- @@ L26-26 verbatim
scoped notation:45 w " ⊩[" bv "|" fv "] " φ:46 => Forces w bv fv φ


-- @@ L28-28 verbatim
abbrev Forcesb {n} (w : W) (bv : Fin n → C) : Semisentenceᵢ L n → Prop := Forces w bv Empty.elim


-- @@ L30-30 verbatim
scoped notation:45 w " ⊩/" bv φ:46 => Forcesb w bv φ


-- @@ L32-32 verbatim
namespace Forces


-- @@ L34-34 verbatim
variable (w v : W) (bv : Fin n → C) (fv : ξ → C)


-- @@ L36-36 verbatim
@[simp] lemma verum : w ⊩[bv|fv] ⊤ := fun v _ ↦ by rintro ⟨⟩


-- @@ L38-38 verbatim
@[simp] lemma falsum : ¬w ⊩[bv|fv] ⊥ := by rintro ⟨⟩


-- @@ L40-40 verbatim
variable {w v bv fv}


-- @@ L42-43 verbatim
@[simp] lemma rel {k} {R : L.Rel k} {t} :
    w ⊩[bv|fv] .rel R t ↔ Rel w R fun i ↦ (t i).relationalVal bv fv := by rfl


-- @@ L45-45 expanded
@[simp]
lemma and {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] binop% HWedge.hWedge φ ψ ↔ w ⊩[bv|fv] φ ∧ w ⊩[bv|fv] ψ := by rfl


-- @@ L47-47 expanded
@[simp]
lemma or {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] binop% HVee.hVee φ ψ ↔ w ⊩[bv|fv] φ ∨ w ⊩[bv|fv] ψ := by rfl


-- @@ L49-50 expanded
@[simp]
lemma imply {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] binop% HArrow.hArrow φ ψ ↔ ∀ v ≤ w, Forces v bv fv φ → Forces v bv fv ψ := by rfl


-- @@ L52-53 expanded
@[simp]
lemma not {φ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] unop% HTilde.hTilde φ ↔ ∀ v ≤ w, ¬Forces v bv fv φ := by rfl


-- @@ L55-57 expanded
@[simp]
lemma iff {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] LogicalConnective.iff φ ψ ↔ ∀ v ≤ w, Forces v bv fv φ ↔ Forces v bv fv ψ := by
  simp [LogicalConnective.iff]; grind


-- @@ L59-60 expanded
@[simp]
lemma all {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] UnivQuantifier.all φ ↔ ∀ v ≤ w, ∀ x : v, Forces v (vecCons x.val bv) fv φ := by rfl


-- @@ L62-63 expanded
@[simp]
lemma ex {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ExsQuantifier.exs φ ↔ ∃ x : w, w ⊩[vecCons (↑x) bv|fv] φ := by rfl


-- @@ L65-70 expanded
@[simp]
lemma conj {Γ : List (Semiformulaᵢ L ξ n)} : w ⊩[bv|fv] List.conj₂ Γ ↔ ∀ φ ∈ Γ, w ⊩[bv|fv] φ :=
  match Γ with
  | [] => by simp
  | [φ] => by simp
  | φ :: ψ :: Γ => by simp [conj (Γ := ψ :: Γ)]


-- @@ L72-77 expanded
@[simp]
lemma disj {Γ : List (Semiformulaᵢ L ξ n)} : w ⊩[bv|fv] disj₂ Γ ↔ ∃ φ ∈ Γ, w ⊩[bv|fv] φ :=
  match Γ with
  | [] => by simp
  | [φ] => by simp
  | φ :: ψ :: Γ => by simp [disj (Γ := ψ :: Γ)]


-- @@ L79-99 expanded
lemma rew {bv : Fin n₂ → C} {fv : ξ₂ → C} {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformulaᵢ L ξ₁ n₁} :
    w ⊩[bv|fv] (app ω φ) ↔
      w ⊩[fun x ↦ (ω #x).relationalVal bv fv|fun x ↦ (ω &x).relationalVal bv fv] φ :=
  by
  induction φ using Semiformulaᵢ.rec' generalizing n₂ w
  case hRel k R t =>
    simp only [Semiformulaᵢ.rew_rel, rel]
    apply iff_of_eq; congr; funext x
    simp [Semiterm.relationalVal_rew ω (t x), Function.comp_def]
  case hImp φ ψ ihφ ihψ => simp [*]
  case hAnd φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hOr φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hFalsum => simp
  case hAll φ
    ih =>
    have (x : C) :
      (fun i ↦ (ω.q #i).relationalVal (vecCons x bv) fv) =
        (vecCons x fun i ↦ (ω #i).relationalVal bv fv) :=
      by funext i; cases i using Fin.cases <;> simp
    simp [ih, this]
  case hExs φ
    ih =>
    have (x : C) :
      (fun i ↦ (ω.q #i).relationalVal (vecCons x bv) fv) =
        (vecCons x fun i ↦ (ω #i).relationalVal bv fv) :=
      by funext i; cases i using Fin.cases <;> simp
    simp [ih, this]


-- @@ L101-105 expanded
@[simp]
lemma free {v : W} {fv : ℕ → C} {φ : Semipropositionᵢ L (n + 1)} :
    v ⊩[bv|cases (↑x) fv] Rewriting.free φ ↔ v ⊩[vecConsLast bv x|fv] φ :=
  by
  have :
    (fun i ↦ Semiterm.relationalVal (L := L) bv (cases x fv) (Rew.free #i)) = (vecConsLast bv x) :=
    by ext i; cases i using Fin.lastCases <;> simp
  simp [Rewriting.free, Forces.rew, this]


-- @@ L107-109 expanded
lemma subst {v : W} (w : Fin k → Semiterm L ξ n) (φ : Semiformulaᵢ L ξ k) :
    v ⊩[bv|fv] (FFL.FirstOrder.Rewriting.subst φ w) ↔ v ⊩[fun i ↦ (w i).relationalVal bv fv|fv] φ :=
  by simp [Rewriting.subst, Forces.rew]


-- @@ L111-113 expanded
@[simp]
lemma subst₀ (φ : Formulaᵢ L ξ) : v ⊩[bv|fv] FFL.FirstOrder.Rewriting.subst φ ![] ↔ v ⊩[![]|fv] φ :=
  by simp [Forces.subst, Matrix.empty_eq]


-- @@ L115-117 expanded
@[simp]
lemma forces_subst₁ (t : Semiterm L ξ n) (φ : Semiformulaᵢ L ξ 1) :
    v ⊩[bv|fv] FFL.FirstOrder.Rewriting.subst φ ![t] ↔ v ⊩[![t.relationalVal bv fv]|fv] φ := by
  simp [Forces.subst, Matrix.constant_eq_singleton]


-- @@ L119-121 verbatim
@[simp] lemma forces_emb {φ : Semisentenceᵢ L n} :
    v ⊩[bv|fv] (Rewriting.emb φ) ↔ v ⊩[bv|Empty.elim] φ := by
  simp [Rewriting.emb, Forces.rew, Empty.eq_elim]


-- @@ L123-140 expanded
lemma monotone {n} {bv : Fin n → C} {fv : ξ → C} {φ} : w ⊩[bv|fv] φ → ∀ v ≤ w, v ⊩[bv|fv] φ :=
  match φ with
  | .rel R v => rel_monotone
  | ⊥ => by rintro ⟨⟩
  | binop% HWedge.hWedge φ ψ => by
    rintro ⟨hl, hr⟩ v h
    exact ⟨hl.monotone _ h, hr.monotone _ h⟩
  | binop% HVee.hVee φ ψ => by
    rintro (hl | hr) v h
    · left; exact hl.monotone _ h
    · right; exact hr.monotone _ h
  | binop% HArrow.hArrow φ ψ => fun Hw v' h v hvv' Hv ↦ Hw v (le_trans hvv' h) Hv
  | UnivQuantifier.all φ => fun Hw w h v' hvv' x ↦ Hw v' (le_trans hvv' h) x
  | ExsQuantifier.exs φ => by
    rintro ⟨x, Hw⟩ v h
    exact ⟨⟨x, domain_antimonotone h x.prop⟩, Hw.monotone _ h⟩


-- @@ L142-149 verbatim
@[simp] lemma triple_negation_elim {φ : Semiformulaᵢ L ξ n} :
    (∀ v ≤ w, ∃ x ≤ v, ∀ y ≤ x, ¬y ⊩[bv|fv] φ) ↔ (∀ v ≤ w, ¬v ⊩[bv|fv] φ) := by
  constructor
  · intro h v hvw Hv
    rcases h v hvw with ⟨x, hxv, Hx⟩
    exact Hx x (by rfl) (Hv.monotone x hxv)
  · intro h v hvw
    refine ⟨v, by rfl, fun x hxv ↦ h x (le_trans hxv hvw)⟩


-- @@ L151-157 expanded
@[simp]
lemma all_of_constantDomain [ConstantDomain W] {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] UnivQuantifier.all φ ↔ ∀ x : C, w ⊩[vecCons x bv|fv] φ :=
  by
  constructor
  · intro h x
    exact all.mp h w (by rfl) ⟨x, by simp⟩
  · rintro h v hvw ⟨x, _⟩
    simpa using monotone (h x) v hvw


-- @@ L159-160 expanded
@[simp]
lemma ex_of_constantDomain [ConstantDomain W] {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ExsQuantifier.exs φ ↔ ∃ x : C, w ⊩[vecCons x bv|fv] φ := by simp


-- @@ L162-164 verbatim
def ForcesHead (w : W) (fv : ℕ → C) : LJ.Head L → Prop
  | none   => False
  | some φ => w ⊩[![]|fv] φ


-- @@ L166-166 verbatim
@[simp] lemma forcesHead_none (w : W) (fv : ℕ → C) : ForcesHead w fv none = False := rfl


-- @@ L168-169 verbatim
@[simp] lemma forcesHead_some (w : W) (fv : ℕ → C) (φ : Propositionᵢ L) :
    ForcesHead w fv (some φ) = (w ⊩[![]|fv] φ) := rfl


-- @@ L171-235 expanded
/-- Soundness of LJ with respect to intuitionistic Kripke forcing.
- [Min00, Chapter 2]
-/
theorem sound {Γ : LJ.Sequent L} {Ξ : LJ.Head L} :
    (d : Derivation Γ Ξ) →
      (w : W) →
        (fv : ℕ → C) →
          (∀ i, ForcingExists.Forces w (fv i)) → (∀ φ ∈ Γ, w ⊩[![]|fv] φ) → ForcesHead w fv Ξ
  | .identity R v, w, fv, _, hΓ => hΓ _ (by simp)
  | .cut dφ d, w, fv, hfv, hΓ =>
    by
    obtain ⟨hΓ, hΔ⟩ := Multiset.forall_mem_add.mp hΓ
    exact sound d w fv hfv <| Multiset.forall_mem_add.mpr ⟨hΔ, by simpa using sound dφ w fv hfv hΓ⟩
  | .contraction (Ξ := Ξ) d hΔ hΞ, w, fv, hfv, hΓ =>
    by
    have hd := sound d w fv hfv fun φ hφ ↦ hΓ φ (hΔ hφ)
    cases Ξ <;> cases hΞ <;> simp_all [ForcesHead]
  | .verum, _, _, _, _ => by simp [ForcesHead]
  | .falsum, _, _, _, hΓ => hΓ (⊥ : Propositionᵢ L) (by simp)
  | .positiveImply d, w, fv, hfv, hΓ => by
    intro v hvw hφ
    exact
      sound d v fv (fun i ↦ domain_monotone (hfv i) v hvw) <|
        Multiset.forall_mem_add.mpr ⟨fun θ hθ ↦ (hΓ θ hθ).monotone v hvw, by simpa using hφ⟩
  | .negativeImply dφ dψ, w, fv, hfv, hΓ =>
    by
    obtain ⟨⟨hΓ, hΔ⟩, hi⟩ :=
      (by simpa only [Multiset.forall_mem_add, Multiset.forall_mem_atom] using hΓ)
    exact
      sound dψ w fv hfv <|
        Multiset.forall_mem_add.mpr ⟨hΔ, by simpa using hi w (by rfl) (sound dφ w fv hfv hΓ)⟩
  | .positiveAnd dφ dψ, w, fv, hfv, hΓ => ⟨sound dφ w fv hfv hΓ, sound dψ w fv hfv hΓ⟩
  | .negativeAnd d, w, fv, hfv, hΓ =>
    sound d w fv hfv
      (by simpa only [Multiset.forall_mem_add, Multiset.forall_mem_atom, and] using hΓ)
  | .positiveOrLeft d, w, fv, hfv, hΓ => Or.inl <| sound d w fv hfv hΓ
  | .positiveOrRight d, w, fv, hfv, hΓ => Or.inr <| sound d w fv hfv hΓ
  | .negativeOr dφ dψ, w, fv, hfv, hΓ =>
    by
    obtain ⟨hΓ, hφ | hψ⟩ :=
      (by simpa only [Multiset.forall_mem_add, Multiset.forall_mem_atom] using hΓ)
    · exact sound dφ w fv hfv <| Multiset.forall_mem_add.mpr ⟨hΓ, by simpa using hφ⟩
    · exact sound dψ w fv hfv <| Multiset.forall_mem_add.mpr ⟨hΓ, by simpa using hψ⟩
  | .positiveForall d, w, fv, hfv, hΓ => by
    intro v hvw x
    simpa [ForcesHead] using
      sound d v (cases x.val fv)
        (by rintro (i | i) <;> simp [fun i ↦ domain_monotone (hfv i) v hvw])
        (fun θ hθ ↦ by
          rcases Multiset.mem_map.mp hθ with ⟨ψ, hψ, rfl⟩
          simpa [Rewriting.shift, Forces.rew] using (hΓ ψ hψ).monotone v hvw)
  | .negativeForall (φ := φ) (t := t) d, w, fv, hfv, hΓ =>
    by
    obtain ⟨x, ht⟩ := t.fvar_of_relational
    have hAll : w ⊩[![]|fv] UnivQuantifier.all φ := hΓ _ (by simp)
    have hφ := hAll w (by rfl) ⟨fv x, hfv x⟩
    exact
      sound d w fv hfv
        (by
          simpa [ht, or_imp, forall_and] using
            And.intro (fun θ hθ ↦ hΓ θ (Multiset.mem_add.mpr (Or.inl hθ))) hφ)
  | .positiveExists (t := t) d, w, fv, hfv, hΓ =>
    by
    obtain ⟨x, ht⟩ := t.fvar_of_relational
    exact ⟨⟨fv x, hfv x⟩, by simpa [ht] using sound d w fv hfv hΓ⟩
  | .negativeExists (φ := φ) (Ξ := Ξ) d, w, fv, hfv, hΓ =>
    by
    have hEx : w ⊩[![]|fv] ExsQuantifier.exs φ := hΓ _ (by simp)
    rcases hEx with ⟨x, hx⟩
    have hd :=
      sound d w (cases x.val fv) (by rintro (i | i) <;> simp [hfv])
        (fun θ hθ ↦ by
          rcases Multiset.mem_add.mp hθ with hθ | hθ
          · rcases Multiset.mem_map.mp hθ with ⟨ψ, hψ, rfl⟩
            simpa [Rewriting.shift, Forces.rew] using hΓ ψ (by simp [hψ])
          · have : θ = Rewriting.free φ := by simpa using hθ
            simpa [this] using hx)
    cases Ξ with
    | none => exact hd
    | some ψ => simpa [ForcesHead, LJ.Head.shift, Rewriting.shift, Forces.rew] using hd


-- @@ L237-237 verbatim
end Forces


-- @@ L239-239 verbatim
abbrev Forces₀ (w : W) (φ : Sentenceᵢ L) : Prop := w ⊩[![]|Empty.elim] φ


-- @@ L241-241 verbatim
instance : ForcingRelation W (Sentenceᵢ L) := ⟨Forces₀⟩


-- @@ L243-243 expanded
lemma forces₀_def {w : W} {φ : Sentenceᵢ L} : ForcingRelation.Forces w φ ↔ w ⊩[![]|Empty.elim] φ :=
  by rfl


-- @@ L245-245 verbatim
namespace Forces₀


-- @@ L247-248 expanded
lemma monotone {w : W} {φ} : ForcingRelation.Forces w φ → ∀ v ≤ w, ForcingRelation.Forces v φ :=
  fun h hw ↦ Forces.monotone h hw


-- @@ L250-257 verbatim
instance : ForcingRelation.IntKripke W (· ≥ ·) where
  verum w := by rintro _ _ ⟨⟩
  falsum w := by rintro ⟨⟩
  and w := by simp [forces₀_def]
  or w := by simp [forces₀_def]
  imply w := by simp [forces₀_def, Forces.imply]
  not w := by simp [forces₀_def, Forces.not]
  monotone := monotone


-- @@ L259-259 verbatim
open Semantics


-- @@ L261-267 expanded
lemma sound {T : Theoryᵢ L} (b : Provable T φ) : AllForcesSet W T → AllForces W φ := fun H w ↦
  by
  rcases domain_nonempty' w with ⟨x, hx⟩
  rcases b with ⟨Γ, hΓ, d⟩
  have hd :=
    Forces.sound d w (fun _ ↦ x) (by simpa using hx) fun ψ hψ ↦
      by
      rcases Multiset.mem_map.mp hψ with ⟨σ, hσ, rfl⟩
      simpa [forces₀_def] using H σ (hΓ σ hσ) w
  simpa [forces₀_def, Forces.ForcesHead] using hd


-- @@ L269-269 verbatim
end Forces₀


-- @@ L271-275 verbatim
end KripkeModel

-- `World`'s and `Carrier`'s universes only occur together (via `Domain : World → Set Carrier`),
-- which is intentional here rather than a sign of an unnecessary parameter; keeping them
-- separate documents that the two carriers need not live in the same universe.

-- @@ L276-287 verbatim
set_option linter.checkUnivs false in
/-- Kripke model for intuitionistic first-order logic -/
structure IntKripke (L : Language) [L.Relational] where
  World : Type*
  [nonempty : Nonempty World]
  [preorder : Preorder World]
  Carrier : Type*
  Domain : World → Set Carrier
  domain_nonempty : ∀ w, ∃ x, x ∈ Domain w
  domain_antimonotone : w ≥ v → Domain w ⊆ Domain v
  Rel (w : World) {k : ℕ} (R : L.Rel k) : (Fin k → Carrier) → Prop
  rel_monotone : Rel w R t → ∀ v ≤ w, Rel v R t


-- @@ L289-289 verbatim
namespace IntKripke


-- @@ L291-291 verbatim
variable (𝓚 : IntKripke L)


-- @@ L293-293 verbatim
instance : CoeSort (IntKripke L) (Type _) := ⟨fun 𝓚 ↦ 𝓚.World⟩


-- @@ L295-295 verbatim
instance : CoeSort 𝓚 (Type _) := ⟨fun w ↦ 𝓚.Domain w⟩


-- @@ L297-297 verbatim
instance : Nonempty 𝓚 := 𝓚.nonempty


-- @@ L299-299 verbatim
instance : Preorder 𝓚 := 𝓚.preorder


-- @@ L301-301 verbatim
instance : ForcingExists 𝓚 𝓚.Carrier := ⟨fun p x ↦ x ∈ 𝓚.Domain p⟩


-- @@ L303-308 verbatim
instance kripke : KripkeModel L 𝓚 𝓚.Carrier where
  Domain := 𝓚.Domain
  domain_nonempty := 𝓚.domain_nonempty
  domain_antimonotone := 𝓚.domain_antimonotone
  Rel := 𝓚.Rel
  rel_monotone := 𝓚.rel_monotone


-- @@ L310-310 verbatim
open KripkeModel


-- @@ L312-312 expanded
instance : Semantics (IntKripke L) (Sentenceᵢ L) :=
  ⟨fun 𝓚 φ ↦ AllForces 𝓚 φ⟩


-- @@ L314-314 verbatim
variable {𝓚}


-- @@ L316-316 expanded
lemma models_def : Models 𝓚 φ ↔ AllForces 𝓚 φ := by rfl


-- @@ L318-319 expanded
lemma sound {T : Theoryᵢ L} (b : Provable T φ) : ModelsSet 𝓚 T → Models 𝓚 φ := fun H ↦
  Forces₀.sound (W := 𝓚) b fun _ hφ ↦ H.models_set hφ


-- @@ L321-322 verbatim
instance (T : Theoryᵢ L) : Sound T (Semantics.models (IntKripke L) T) :=
  ⟨fun b _ H ↦ sound b H⟩


-- @@ L324-324 expanded
lemma sound_empty (b : Provable (∅ : Theoryᵢ L) φ) : Models 𝓚 φ :=
  𝓚.sound b (by simp)


-- @@ L326-326 verbatim
instance : Semantics.Top (IntKripke L) := ⟨fun 𝓚 ↦ by simpa [models_def] using ForcingRelation.AllForces.verum⟩


-- @@ L328-330 verbatim
instance : Semantics.Bot (IntKripke L) := ⟨fun 𝓚 ↦ by
  have : Inhabited 𝓚 := Classical.inhabited_of_nonempty'
  simp [models_def]⟩


-- @@ L332-332 verbatim
instance : Semantics.And (IntKripke L) := ⟨by simp [models_def]⟩


-- @@ L334-334 verbatim
end IntKripke


-- @@ L336-336 verbatim
end FFL.FirstOrder
