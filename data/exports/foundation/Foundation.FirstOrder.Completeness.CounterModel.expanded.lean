module

public import Foundation.FirstOrder.Completeness.CanonicalModel
public import Foundation.FirstOrder.Completeness.CountableSublanguage
public import Foundation.FirstOrder.Ultraproduct
public import Foundation.Vorspiel.Order.Dense
public import Mathlib.Logic.Equiv.List
public import Mathlib.Logic.Encodable.Basic


-- @@ L10-10 verbatim
/-! # Completeness theorem -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
/-! ### Generic filters -/


-- @@ L16-16 verbatim
namespace FFL.FirstOrder.Derivation.Canonical


-- @@ L18-18 verbatim
open Order


-- @@ L20-20 verbatim
variable {K : Language}


-- @@ L22-22 verbatim
local notation "ℙ" => ConsistentSequent K


-- @@ L24-24 verbatim
open Classical

-- @@ L25-31 verbatim
def decidablePoints (φ : Proposition K) : DenseSet ℙ where
  set := {p | p ⊩ᶜ φ ∨ p ⊩ᶜ ∼φ}
  is_dense := by
    intro p
    have : p ⊩ᶜ φ ⋎ ∼φ := IsWeaklyForced.complete.mpr Entailment.lem p
    have : ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ ∨ r ⊩ᶜ ∼φ := by simpa using this
    simpa using this p (by rfl)


-- @@ L33-34 verbatim
@[simp] lemma mem_decidablePoints_def (p : ℙ) (φ : Proposition K) :
    p ∈ decidablePoints φ ↔ p ⊩ᶜ φ ∨ p ⊩ᶜ ∼φ := by rfl


-- @@ L36-51 verbatim
def henkinPoints (φ : Semiproposition K 1) : DenseSet ℙ where
  set := {p | ∀ q ≤ p, q ⊩ᶜ ∃¹ φ → ∃ t, q ⊩ᶜ φ/[t]}
  is_dense := by
    intro p
    suffices ∃ q ≤ p, ∀ q_1 ≤ q, (∀ q ≤ q_1, ∃ r ≤ q, ∃ t, r ⊩ᶜ φ/[t]) → ∃ t, q_1 ⊩ᶜ φ/[t] by
      simpa only [IsWeaklyForced.exs, Set.mem_ofPred_eq]
    have : p ⊩ᶜ (∃¹ φ) ⋎ (∀¹ ∼φ) := IsWeaklyForced.complete.mpr Entailment.lem p
    have : ∀ q ≤ p, ∃ r ≤ q, (∀ q ≤ r, ∃ r ≤ q, ∃ t, r ⊩ᶜ φ/[t]) ∨ (∀ t, ∀ q ≤ r, ¬q ⊩ᶜ φ/[t]) := by simpa using this
    rcases this p (by rfl) with ⟨q, hqp, (h | h)⟩
    · rcases h q (by rfl) with ⟨r, hrq, t, ht⟩
      refine ⟨r, le_trans hrq hqp, fun s hsr _ ↦ ⟨t, IsWeaklyForced.monotone hsr ht⟩⟩
    · refine ⟨q, hqp, ?_⟩
      intro r hrq hA
      rcases hA r (by rfl) with ⟨s, hsr, u, hu⟩
      have : ¬s ⊩ᶜ φ/[u] := h u s (le_trans hsr hrq)
      contradiction


-- @@ L53-54 verbatim
@[simp] lemma mem_henkinPoints_def (p : ℙ) (φ : Semiproposition K 1) :
    p ∈ henkinPoints φ ↔ ∀ q ≤ p, q ⊩ᶜ ∃¹ φ → ∃ t, q ⊩ᶜ φ/[t] := by rfl


-- @@ L56-56 verbatim
abbrev denseSets : Set (DenseSet ℙ) := Set.range decidablePoints ∪ Set.range henkinPoints


-- @@ L58-58 verbatim
variable [K.Encodable]


-- @@ L60-63 verbatim
theorem exists_genericFilter (p : ℙ) :
    ∃ G : PFilter ℙ, G.IsGeneric denseSets ∧ p ∈ G :=
  PFilter.exists_genericFilter_of_countable denseSets
    (Set.countable_union.mpr ⟨Set.countable_range decidablePoints, Set.countable_range henkinPoints⟩) p


-- @@ L65-65 verbatim
noncomputable def genericFilter (p : ℙ) : PFilter ℙ := Classical.choose (exists_genericFilter p)


-- @@ L67-68 verbatim
instance genericFilter_isGeneric (p : ℙ) : (genericFilter p).IsGeneric denseSets :=
  Classical.choose_spec (exists_genericFilter p) |>.1


-- @@ L70-71 verbatim
@[simp] lemma mem_genericFilter (p : ℙ) : p ∈ genericFilter p :=
  Classical.choose_spec (exists_genericFilter p) |>.2


-- @@ L73-73 verbatim
def GenericForces (p : ℙ) (φ : Proposition K) : Prop := ∃ q ∈ genericFilter p, q ⊩ᶜ φ


-- @@ L75-84 verbatim
local infix: 60 " ⊫ " => GenericForces

lemma GenericForces.em (p : ℙ) (φ : Proposition K) : p ⊫ φ ∨ p ⊫ ∼φ := by
  have : ∃ q ∈ genericFilter p, q ∈ decidablePoints φ :=
    (genericFilter_isGeneric p).isGeneric (decidablePoints φ) (by simp)
  rcases this with ⟨q, hqG, hq⟩
  have : q ⊩ᶜ φ ∨ q ⊩ᶜ ∼φ := by simpa using hq
  rcases this with (em | em)
  · left; refine ⟨q, hqG, em⟩
  · right; refine ⟨q, hqG, em⟩


-- @@ L86-95 verbatim
@[simp] lemma GenericForces.neg {p : ℙ} {φ : Proposition K} : p ⊫ ∼φ ↔ ¬p ⊫ φ := by
  suffices p ⊫ ∼φ → p ⊫ φ → False by
    have := GenericForces.em p φ
    grind
  rintro ⟨q₀, hG₀, h₀⟩
  rintro ⟨q₁, hG₁, h₁⟩
  rcases (genericFilter p).directed _ hG₀ _ hG₁ with ⟨r, hG, hr₀, hr₁⟩
  have : r ⊩ᶜ φ := h₁.monotone hr₁
  have : ¬r ⊩ᶜ φ := IsWeaklyForced.not.mp h₀ r (by assumption)
  contradiction


-- @@ L97-98 verbatim
@[simp] lemma GenericForces.verum (p : ℙ) : p ⊫ ⊤ :=
  ⟨p, by simp⟩


-- @@ L100-101 verbatim
@[simp] lemma GenericForces.not_falsum (p : ℙ) : ¬p ⊫ ⊥ := by
  rintro ⟨q, hq⟩; simp_all


-- @@ L103-115 verbatim
@[simp] lemma GenericForces.nrel {p : ℙ} : p ⊫ .nrel R v ↔ ¬p ⊫ .rel R v := calc
  p ⊫ .nrel R v ↔ p ⊫ ∼(.rel R v) := by simp
  _         ↔ ¬p ⊫ .rel R v := by rw [GenericForces.neg]

lemma GenericForces.henkin {p : ℙ} {φ : Semiproposition K 1} : p ⊫ ∃¹ φ → ∃ t, p ⊫ φ/[t] := by
  have : ∃ q ∈ genericFilter p, ∀ r ≤ q, r ⊩ᶜ ∃¹ φ → ∃ t, r ⊩ᶜ φ/[t] :=
    (genericFilter_isGeneric p).isGeneric (henkinPoints φ) (by simp)
  rcases this with ⟨q, hqG, H⟩
  rintro ⟨r, hrG, hr⟩
  rcases (genericFilter p).directed _ hqG _ hrG with ⟨z, hGz, hzq, hzr⟩
  have : ∃ t, z ⊩ᶜ φ/[t] := H z hzq (hr.monotone hzr)
  rcases this with ⟨t, hzt⟩
  refine ⟨t, ⟨z, hGz, hzt⟩⟩


-- @@ L117-124 verbatim
@[simp] lemma GenericForces.exs {p : ℙ} : p ⊫ ∃¹ φ ↔ ∃ t, p ⊫ φ/[t] := by
  constructor
  · exact GenericForces.henkin
  · rintro ⟨t, q, hqG, h⟩
    refine ⟨q, hqG, ?_⟩
    suffices ∀ r ≤ q, ∃ s ≤ r, ∃ t, s ⊩ᶜ φ/[t] by simpa
    intro r hrq
    refine ⟨r, by simp, t, h.monotone hrq⟩


-- @@ L126-129 verbatim
@[simp] lemma GenericForces.fal {p : ℙ} : p ⊫ ∀¹ φ ↔ ∀ t, p ⊫ φ/[t] := calc
  p ⊫ ∀¹ φ ↔ p ⊫ ∼(∃¹ ∼φ) := by simp
  _         ↔ ¬p ⊫ ∃¹ ∼φ := by rw [GenericForces.neg]
  _         ↔ ∀ t, p ⊫ φ/[t] := by simp [GenericForces.exs]


-- @@ L131-142 verbatim
@[simp] lemma GenericForces.and {p : ℙ} {φ ψ : Proposition K} : p ⊫ φ ⋏ ψ ↔ p ⊫ φ ∧ p ⊫ ψ := by
  constructor
  · rintro ⟨q, hqG, hq⟩
    have : q ⊩ᶜ φ ∧ q ⊩ᶜ ψ := by simpa using hq
    rcases this with ⟨hφ, hψ⟩
    exact ⟨⟨q, hqG, hφ⟩, ⟨q, hqG, hψ⟩⟩
  · rintro ⟨⟨q₁, hG₁, h₁⟩, ⟨q₂, hG₂, h₂⟩⟩
    rcases (genericFilter p).directed _ hG₁ _ hG₂ with ⟨r, hGr, hr₁, hr₂⟩
    refine ⟨r, hGr, ?_⟩
    have : r ⊩ᶜ φ := h₁.monotone hr₁
    have : r ⊩ᶜ ψ := h₂.monotone hr₂
    simp_all


-- @@ L144-147 verbatim
@[simp] lemma GenericForces.or {p : ℙ} {φ ψ : Proposition K} : p ⊫ φ ⋎ ψ ↔ p ⊫ φ ∨ p ⊫ ψ := calc
  p ⊫ φ ⋎ ψ ↔ p ⊫ ∼(∼φ ⋏ ∼ψ) := by simp
  _         ↔ ¬p ⊫ ∼φ ⋏ ∼ψ := by rw [GenericForces.neg]
  _         ↔ p ⊫ φ ∨ p ⊫ ψ := by simp; tauto


-- @@ L149-151 verbatim
abbrev termModelOf (p : ℙ) : Structure K (Term K ℕ) where
  func _ f v := .func f v
  rel _ R v := p ⊫ .rel R v


-- @@ L153-154 verbatim
@[simp] lemma termModel_func_def (f : K.Func k) (v : Fin k → (Term K ℕ)) :
    (termModelOf p).func f v = Semiterm.func f v := rfl


-- @@ L156-157 verbatim
@[simp] lemma termModel_rel_def (R : K.Rel k) (v) :
    (termModelOf p).rel R v ↔ p ⊫ .rel R v := by rfl


-- @@ L159-178 verbatim
@[simp] lemma termModel_val_eq (t : Semiterm K ξ n) (fv : ξ → (Term K ℕ)) (bv : Fin n → (Term K ℕ)) :
    t.val (s := termModelOf p) bv fv = Rew.bind bv fv t := by
  induction t <;> simp [*, Function.comp_def]

lemma forcing_lemma (φ : Semiformula K ξ n) {fv : ξ → (Term K ℕ)} {bv : Fin n → (Term K ℕ)} :
    φ.Eval (s := termModelOf p) bv fv ↔ p ⊫ Rew.bind bv fv ▹ φ :=
  have e (t : Term K ℕ) (φ : Semiformula K ξ (n + 1)) : ((Rew.bind bv fv).q ▹ φ)/[t] = Rew.bind (t :> bv) fv ▹ φ := by
    unfold Rewriting.subst; rw [←TransitiveRewriting.comp_app]
    congr; ext x
    · cases x using Fin.cases <;> simp [Rew.comp_app]
    · simp [Rew.comp_app]
  match φ with
  | .rel R v | .nrel R v => by simp [Function.comp_def]
  | ⊤ | ⊥ => by simp
  | φ ⋏ ψ | φ ⋎ ψ => by simp [forcing_lemma φ, forcing_lemma ψ]
  | ∀¹ φ | ∃¹ φ => by simp [e, forcing_lemma φ]

lemma refl (φ : Proposition K) (h : 𝐋𝐊¹ ⊬ ∼φ) :
    φ.Evalf (s := termModelOf (ConsistentSequent.ofUnprovable φ h)) (&·) :=
  (forcing_lemma φ).mpr ⟨ConsistentSequent.ofUnprovable φ h, by simp, by simpa using IsWeaklyForced.refl φ h⟩


-- @@ L180-180 verbatim
end Derivation.Canonical


-- @@ L182-182 verbatim
/-! ### Completeness theorem -/


-- @@ L184-184 verbatim
namespace LK


-- @@ L186-186 verbatim
open Classical Derivation.Canonical


-- @@ L188-201 verbatim
variable {L : Language}

lemma satisfiable_of_irrefutable (σ : Sentence L) (h : 𝐋𝐊¹ ⊬ ∼(σ : Proposition L)) :
    Satisfiable {σ} := by
  let K := σ.sublanguage
  let π : Sentence K := σ.toSubLanguageSelf
  have : 𝐋𝐊¹ ⊬ ∼(π : Proposition K) := fun h ↦ by
    have : 𝐋𝐊¹ ⊢ ∼(σ : Proposition L) := by
      simpa [Semiformula.lMap_emb, π] using LK.Proof.lMap L.unsub h
    contradiction
  have : Satisfiable {π} :=
    ⟨⟨_, inferInstance, termModelOf (ConsistentSequent.ofUnprovable π (by simpa using this))⟩, by
      simpa [models_iff] using refl (π : Proposition K) (by simpa using this)⟩
  simpa [Theory.lMap, π] using satisfiable_lMap L.unsub this


-- @@ L203-203 verbatim
end LK


-- @@ L205-205 verbatim
namespace Theory


-- @@ L207-207 verbatim
open Classical FFL.Entailment


-- @@ L209-209 verbatim
variable {L : Language.{u}} {T : Theory L}


-- @@ L211-230 verbatim
/-- Completeness theorem (I) -/
theorem small_satisfiable_of_consistent :
    Consistent T → Satisfiable T := fun consistent ↦ compact.mpr fun u hu ↦ by
  let σ := ⋀u.toList
  have : T ⊢ σ := Conj₂_intro fun φ hφ ↦ by_axm <| hu (by simpa using hφ)
  have : 𝐋𝐊¹ ⊬ ∼(σ : Proposition L) := fun h ↦
    have : T ⊢ ∼σ := Theory.Proof.of_LK_provable (φ := ∼σ) (by simpa using h)
    have : T ⊢ ⊥ := neg_mdp this (by assumption)
    consistent_iff_unprovable_bot.mp consistent this
  have : Satisfiable {σ} := LK.satisfiable_of_irrefutable σ this
  simpa [σ] using this

lemma satisfiable_iff_consistent :
    Semantics.Satisfiable (Struc.{max u w} L) T ↔ Consistent T := by
  constructor
  · exact consistent_of_satisfiable
  · intro h
    let ⟨M, _, _, h⟩ := satisfiable_iff.mp (small_satisfiable_of_consistent h)
    exact satisfiable_iff.mpr
      ⟨ULift.{w} M, inferInstance, inferInstance, ((uLift_elementaryEquiv L M).modelsTheory).mpr h⟩


-- @@ L232-241 verbatim
/-- Completeness theorem (II) -/
theorem Proof.complete :
    T ⊨[Struc.{max u w} L] φ → T ⊢ φ := by
  contrapose!
  intro h
  have : Consistent (insert (∼φ) T) := unprovable_iff_consistent_adjoin.mp h
  have : Semantics.Satisfiable (Struc.{max u w} L) (insert (∼φ) T) := satisfiable_iff_consistent.mpr this
  rcases this with ⟨⟨M, i, s⟩, hM⟩
  have : ¬M↓[L] ⊧ φ ∧ M↓[L] ⊧* T := by simpa using hM
  simpa [consequence_iff] using ⟨M, i.some, s, this.2, this.1⟩


-- @@ L243-243 verbatim
theorem Proof.small_complete : T ⊨ φ → T ⊢ φ := Proof.complete


-- @@ L245-245 verbatim
theorem Proof.complete_iff : T ⊨ φ ↔ T ⊢ φ := ⟨fun h ↦ Proof.complete h, Proof.sound⟩


-- @@ L247-253 verbatim
instance Proof.isComplete (T : Theory L) : Complete T (Semantics.models (Struc.{max u w} L) T) := ⟨Proof.complete⟩

lemma satisfiable_iff_satisfiable : Semantics.Satisfiable (Struc.{max u w} L) T ↔ Satisfiable T := by
  simp [satisfiable_iff_consistent.{u, w}, satisfiable_iff_consistent.{u, u}]

lemma consequence_iff_consequence : T ⊨[Struc.{max u w} L] φ ↔ T ⊨ φ := by
  simp [consequence_iff_unsatisfiable, satisfiable_iff_satisfiable.{u, w}]


-- @@ L255-255 verbatim
end Theory


-- @@ L257-257 verbatim
/-! ### Corollaries -/


-- @@ L259-259 verbatim
namespace ModelsTheory


-- @@ L261-269 verbatim
variable {L : Language.{u}} (M : Type w) [Nonempty M] [Structure L M] (T U V : Theory L)

lemma of_provably_subtheory [le : T ⪯ U] (h : M↓[L] ⊧* U) : M↓[L] ⊧* T := ⟨fun φ hφ ↦
  have : U ⊢ φ := le.pbl (Entailment.by_axm hφ)
  consequence_iff'.{u, w}.mp (Theory.Proof.sound this) M⟩

lemma of_add_left [M↓[L] ⊧* T ∪ U] : M↓[L] ⊧* T := models_of_ss inferInstance (show T ⊆ T ∪ U from by simp)

lemma of_add_right [M↓[L] ⊧* T ∪ U] : M↓[L] ⊧* U := models_of_ss inferInstance (show U ⊆ T ∪ U from by simp)


-- @@ L271-271 verbatim
end ModelsTheory


-- @@ L273-286 verbatim
variable {L : Language.{u}} [L.Eq] {T : Theory L} [𝗘𝗤 L ⪯ T]

lemma Theory.Proof.complete_on_eq_models
    (φ : Sentence L)
    (H : ∀ (M : Type (max u v))
      [Nonempty M]
      [Structure L M] [Structure.Eq L M]
      [M↓[L] ⊧* T],
      M↓[L] ⊧ φ) :
    T ⊢ φ :=
  have : T ⊨ φ := Theory.consequence_iff_consequence.mp <| consequence_iff_eq.mpr fun M _ _ _ hT ↦
    letI : (Structure.Model L M)↓[L] ⊧* T := Structure.ElementaryEquiv.modelsTheory.mp hT
    Structure.ElementaryEquiv.models.mpr (H (Structure.Model L M))
  Theory.Proof.complete this


-- @@ L288-288 verbatim
end FFL.FirstOrder
