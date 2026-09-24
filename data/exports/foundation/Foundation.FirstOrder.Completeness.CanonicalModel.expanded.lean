module

public import Foundation.FirstOrder.Hauptsatz
public import Foundation.Logic.ForcingRelation


-- @@ L6-10 verbatim
/-!
# Canonical model for classical first-order logic

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination [Avi01]
 -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace FFL.FirstOrder.Derivation.Canonical


-- @@ L16-16 verbatim
variable {L : Language}


-- @@ L18-18 verbatim
variable (L)


-- @@ L20-20 verbatim
def ConsistentSequent := {Γ : Sequent L // IsEmpty (⊢ᴸᴷ¹ ∼Γ)}


-- @@ L22-22 verbatim
variable {L}


-- @@ L24-24 verbatim
local notation "ℙ" => ConsistentSequent L


-- @@ L26-26 verbatim
namespace ConsistentSequent


-- @@ L28-31 verbatim
instance : Preorder ℙ where
  le q p := Nonempty (q.val ≼ p.val)
  le_refl p := ⟨StrongerThan.refl p.val⟩
  le_trans _ _ _ hqp hrq := ⟨hqp.some.trans hrq.some⟩


-- @@ L33-33 verbatim
def nil : ℙ := ⟨0, by simp⟩


-- @@ L35-39 verbatim
instance : OrderTop ℙ where
  top := nil
  le_top := by
    rintro ⟨Γ, hΓ⟩
    exact ⟨StrongerThan.ofSubset <| by simp [nil]⟩


-- @@ L41-41 verbatim
def ofUnprovable (φ : Proposition L) (h : 𝐋𝐊¹ ⊬ ∼φ) : ℙ := ⟨⦃φ⦄, by simpa [LK.Proof.unprovable_def] using h⟩


-- @@ L43-43 verbatim
end ConsistentSequent


-- @@ L45-45 verbatim
abbrev IsForced (p : ℙ) (φ : Propositionᵢ L) := Nonempty (Forces p.val φ)


-- @@ L47-47 verbatim
instance : ForcingRelation ℙ (Propositionᵢ L) := ⟨IsForced⟩


-- @@ L49-49 verbatim
instance : WeakForcingRelation ℙ (Proposition L) := ⟨fun p φ ↦ p ⊩ φᴺ⟩


-- @@ L51-51 verbatim
open Classical


-- @@ L53-53 verbatim
namespace IsForced


-- @@ L55-62 verbatim
@[simp] lemma rel {p : ℙ} {k} {R : L.Rel k} {v} : p ⊩ .rel R v ↔ Nonempty (⊢ᴸᴷ¹ ∼p.val + ⦃.rel R v⦄) := by
  constructor
  · rintro ⟨b⟩
    have ⟨d, hd⟩ := b.relEquiv
    exact ⟨d⟩
  · rintro ⟨d⟩
    let ⟨b, hb⟩ := hauptsatz d
    exact ⟨Forces.relEquiv.symm ⟨b, hb⟩⟩


-- @@ L64-69 verbatim
@[simp] lemma fal {p : ℙ} : p ⊩ ∀¹ φ ↔ ∀ t, p ⊩ φ/[t] := by
  constructor
  · rintro ⟨b⟩ t
    exact ⟨b.allEquiv t⟩
  · rintro h
    exact ⟨Forces.allEquiv.symm fun t ↦ (h t).some⟩


-- @@ L71-77 verbatim
@[simp] lemma and {p : ℙ} {φ ψ : Propositionᵢ L} : p ⊩ φ ⋏ ψ ↔ p ⊩ φ ∧ p ⊩ ψ := by
  constructor
  · rintro ⟨b⟩
    have ⟨bφ, bψ⟩ := b.andEquiv
    exact ⟨⟨bφ⟩, ⟨bψ⟩⟩
  · rintro ⟨⟨bφ⟩, ⟨bψ⟩⟩
    exact ⟨Forces.andEquiv.symm ⟨bφ, bψ⟩⟩


-- @@ L79-86 verbatim
@[simp] lemma or {p : ℙ} {φ ψ : Propositionᵢ L} : p ⊩ φ ⋎ ψ ↔ p ⊩ φ ∨ p ⊩ ψ := by
  constructor
  · rintro ⟨b⟩
    have b' := b.orEquiv
    exact b'.rec (fun bφ ↦ .inl ⟨bφ⟩) (fun bψ ↦ .inr ⟨bψ⟩)
  · rintro (⟨⟨hφ⟩⟩ | ⟨⟨hψ⟩⟩)
    · exact ⟨Forces.orEquiv.symm <| .inl hφ⟩
    · exact ⟨Forces.orEquiv.symm <| .inr hψ⟩


-- @@ L88-107 verbatim
@[simp] lemma not_falsum (p : ℙ) : ¬p ⊩ ⊥ := by
  rintro ⟨b⟩
  have ⟨d, hd⟩ := b.falsumEquiv
  exact p.prop.false d

lemma imply {p : ℙ} {φ ψ : Propositionᵢ L} : p ⊩ φ 🡒 ψ ↔ (∀ q ≤ p, q ⊩ φ → q ⊩ ψ) := by
  constructor
  · rintro ⟨b⟩ q ⟨sqp⟩ ⟨bφ⟩
    exact ⟨b.implyEquiv _ sqp bφ⟩
  · rintro h
    refine ⟨Forces.implyEquiv.symm fun q sqp hφ ↦ ?_⟩
    by_cases hq : IsEmpty (⊢ᴸᴷ¹ ∼q)
    · exact (h ⟨q, hq⟩ ⟨sqp⟩ ⟨hφ⟩).some
    · have : Nonempty (⊢ᴸᴷ¹ ∼q) := by simpa using hq
      have d : ⊢ᴸᴷ¹ ∼q := this.some
      let ⟨b, hb⟩ := hauptsatz d
      exact (Forces.falsumEquiv.symm ⟨b, hb⟩).explosion ψ

lemma not {p : ℙ} {φ : Propositionᵢ L} : p ⊩ ∼φ ↔ (∀ q ≤ p, ¬q ⊩ φ) := by
  simp [Semiformulaᵢ.neg_def, imply]


-- @@ L109-118 verbatim
@[simp] lemma exs {p : ℙ} : p ⊩ ∃¹ φ ↔ ∃ t, p ⊩ φ/[t] := by
  constructor
  · rintro ⟨b⟩
    have ⟨t, f⟩ := b.exsEquiv
    exact ⟨t, ⟨f⟩⟩
  · rintro ⟨t, h⟩
    exact ⟨Forces.exsEquiv.symm ⟨t, h.some⟩⟩

lemma monotone {p q : ℙ} (hqp : q ≤ p) {φ : Propositionᵢ L} (hφ : p ⊩ φ) : q ⊩ φ :=
  ⟨Forces.monotone hqp.some hφ.some⟩


-- @@ L120-130 verbatim
instance : ForcingRelation.IntKripke ℙ (· ≥ ·) where
  verum _ := ⟨Forces.implyEquiv.symm fun _ _ d ↦ d⟩
  falsum _ := by simp
  and _ := and
  or _ := or
  imply _ := imply
  not _ := not
  monotone hφ _ hpq := hφ.monotone hpq

lemma sound [L.DecidableEq] {φ : Propositionᵢ L} : 𝐋𝐉¹ ⊢ φ → ℙ ∀⊩ φ := by
  rintro ⟨d⟩ p; exact ⟨Forces.ljSound d p.val⟩


-- @@ L132-132 verbatim
end IsForced


-- @@ L134-134 verbatim
namespace IsWeaklyForced


-- @@ L136-147 verbatim
open IsForced

lemma iff_isForced {φ : Proposition L} {p : ℙ} : p ⊩ᶜ φ ↔ p ⊩ φᴺ := by rfl

lemma dn_neg_iff {φ : Proposition L} {p : ℙ} : p ⊩ᶜ ∼φ ↔ p ⊩ ∼φᴺ := by
  let : L.DecidableEq := ⟨fun _ ↦ Classical.decEq _, fun _ ↦ Classical.decEq _⟩
  have e := LJ.Derivation.negDoubleNegation φ
  constructor
  · rintro ⟨h⟩
    exact ⟨Forces.sound e.2 p.val fun ψ hψ ↦ h.cast (Multiset.mem_atom_iff.mp hψ).symm⟩
  · rintro ⟨h⟩
    exact ⟨Forces.sound e.1 p.val fun ψ hψ ↦ h.cast (Multiset.mem_atom_iff.mp hψ).symm⟩


-- @@ L149-149 verbatim
@[simp] lemma verum (p : ℙ) : p ⊩ᶜ ⊤ := by simp [iff_isForced, IsForced.not]


-- @@ L151-151 verbatim
@[simp] lemma falsum (p : ℙ) : ¬p ⊩ᶜ ⊥ := by simp [iff_isForced]


-- @@ L153-154 verbatim
@[simp] lemma not {φ : Proposition L} {p : ℙ} : p ⊩ᶜ ∼φ ↔ ∀ q ≤ p, ¬q ⊩ᶜ φ := by
  simp [IsForced.not, dn_neg_iff,]; rfl


-- @@ L156-157 verbatim
@[simp] lemma and {φ ψ : Proposition L} {p : ℙ} : p ⊩ᶜ φ ⋏ ψ ↔ p ⊩ᶜ φ ∧ p ⊩ᶜ ψ := by
  simp [iff_isForced, ]


-- @@ L159-160 verbatim
@[simp] lemma or {φ ψ : Proposition L} {p : ℙ} : p ⊩ᶜ φ ⋎ ψ ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ ∨ r ⊩ᶜ ψ := by
  simp [iff_isForced, IsForced.not, ]; grind


-- @@ L162-163 verbatim
@[simp] lemma all {φ : Semiproposition L 1} {p : ℙ} : p ⊩ᶜ ∀¹ φ ↔ ∀ t, p ⊩ᶜ φ/[t] := by
  simp [iff_isForced, Semiformula.subst_doubleNegation]


-- @@ L165-186 verbatim
@[simp] lemma exs {φ : Semiproposition L 1} {p : ℙ} : p ⊩ᶜ ∃¹ φ ↔ ∀ q ≤ p, ∃ r ≤ q, ∃ t, r ⊩ᶜ φ/[t] := by
  simp [iff_isForced, IsForced.not, Semiformula.subst_doubleNegation]; grind

lemma monotone {φ : Proposition L} {p q : ℙ} (h : q ≤ p) : p ⊩ᶜ φ → q ⊩ᶜ φ := IsForced.monotone h

lemma gnericity {φ : Proposition L} {p : ℙ} : p ⊩ᶜ φ ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ := calc
  p ⊩ᶜ φ ↔ p ⊩ᶜ ∼∼φ := by simp
  _      ↔ ∀ q ≤ p, ∃ r ≤ q, r ⊩ᶜ φ := by rw [not]; simp [not]

lemma complete {φ : Proposition L} : ℙ ∀⊩ᶜ φ ↔ 𝐋𝐊¹ ⊢ φ := by
  constructor
  · intro h
    by_contra b
    let p : ℙ := ⟨⦃∼φ⦄, ⟨fun bφ ↦ b ⟨by simpa using! bφ⟩⟩⟩
    have hp : p ⊩ φᴺ := h p
    have hn : p ⊩ᶜ ∼φ := ⟨Forces.refl (∼φ)⟩
    have : ∀ q ≤ p, ¬q ⊩ φᴺ := by simpa [not] using! hn
    have : ¬p ⊩ φᴺ := this p (by simp)
    contradiction
  · intro b
    let : L.DecidableEq := ⟨fun _ ↦ Classical.decEq _, fun _ ↦ Classical.decEq _⟩
    exact IsForced.sound <| Provable.gödel_gentzen b


-- @@ L188-189 verbatim
protected lemma refl (φ : Proposition L) (h : 𝐋𝐊¹ ⊬ ∼φ) :
    ConsistentSequent.ofUnprovable φ h ⊩ᶜ φ := ⟨Forces.refl φ⟩


-- @@ L191-191 verbatim
end IsWeaklyForced


-- @@ L193-193 verbatim
end Canonical


-- @@ L195-195 verbatim
end FFL.FirstOrder.Derivation
