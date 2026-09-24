module

public import Foundation.FirstOrder.Intuitionistic.LJ


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-6 verbatim
namespace FFL.FirstOrder


-- @@ L8-8 verbatim
namespace Semiformula


-- @@ L10-18 verbatim
def doubleNegation {n} : Semiformula L ξ n → Semiformulaᵢ L ξ n
  |  rel r v => ∼∼(.rel r v)
  | nrel r v => ∼(.rel r v)
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.doubleNegation ⋏ ψ.doubleNegation
  |    φ ⋎ ψ => ∼(∼φ.doubleNegation ⋏ ∼ψ.doubleNegation)
  |     ∀¹ φ => ∀¹ φ.doubleNegation
  |     ∃¹ φ => ∼(∀¹ ∼φ.doubleNegation)


-- @@ L20-20 verbatim
scoped[FFL.FirstOrder] 
-- @@ L20-20 verbatim
postfix:max "ᴺ" => Semiformula.doubleNegation


-- @@ L22-22 verbatim
@[simp] lemma doubleNegation_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v)ᴺ = ∼∼(.rel r v) := rfl


-- @@ L24-24 verbatim
@[simp] lemma doubleNegation_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v)ᴺ = ∼(.rel r v) := rfl


-- @@ L26-26 verbatim
@[simp] lemma doubleNegation_verum : (⊤ : Semiformula L ξ n)ᴺ = ∼⊥ := rfl


-- @@ L28-28 verbatim
@[simp] lemma doubleNegation_falsum : (⊥ : Semiformula L ξ n)ᴺ = ⊥ := rfl


-- @@ L30-30 verbatim
@[simp] lemma doubleNegation_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ)ᴺ = φᴺ ⋏ ψᴺ := rfl


-- @@ L32-32 verbatim
@[simp] lemma doubleNegation_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ)ᴺ = ∼(∼φᴺ ⋏ ∼ψᴺ) := rfl


-- @@ L34-34 verbatim
@[simp] lemma doubleNegation_all (φ : Semiformula L ξ (n + 1)) : (∀¹ φ)ᴺ = ∀¹ φᴺ := rfl


-- @@ L36-38 verbatim
@[simp] lemma doubleNegation_ex (φ : Semiformula L ξ (n + 1)) : (∃¹ φ)ᴺ = ∼(∀¹ ∼φᴺ) := rfl

lemma doubleNegation_imply (φ ψ : Semiformula L ξ n) : (φ 🡒 ψ)ᴺ = ∼(∼(∼φ)ᴺ ⋏ ∼ψᴺ) := by simp [imp_eq]


-- @@ L40-41 verbatim
@[simp] lemma doubleNegation_isNegative (φ : Semiformula L ξ n) : φᴺ.IsNegative := by
  induction φ using rec' <;> simp [*]


-- @@ L43-60 verbatim
@[simp] lemma doubleNegation_conj₂ (Γ : List (Semiformula L ξ n)) :
    (Γ.conj₂)ᴺ = (Γ.map Semiformula.doubleNegation).conj₂ :=
  match Γ with
  |          [] => by simp; rfl
  |         [φ] => by simp
  | φ :: ψ :: Γ => by simp [doubleNegation_conj₂ (ψ :: Γ)]

lemma doubleNegation_fconj (s : Finset (Semiformula L ξ n)) :
    (s.conj)ᴺ = (s.toList.map Semiformula.doubleNegation).conj₂ := doubleNegation_conj₂ _

lemma rew_doubleNegation (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : ω ▹ φᴺ = (ω ▹ φ)ᴺ := by
  induction φ using rec' generalizing n₂ <;> simp [Semiformulaᵢ.rew_rel, *, Function.comp_def]

lemma subst_doubleNegation (φ : Semiformula L ξ n₁) (v : Fin n₁ → Semiterm L ξ n₂) :
    φᴺ ⇜ v = (φ ⇜ v)ᴺ := rew_doubleNegation _ _

lemma emb_doubleNegation (φ : Semisentence L n₁) :
    Rewriting.emb (φᴺ) = (Rewriting.emb φ : Semiformula L ξ n₁)ᴺ := rew_doubleNegation _ _


-- @@ L62-62 verbatim
end Semiformula


-- @@ L64-64 verbatim
namespace Sequent


-- @@ L66-67 verbatim
def doubleNegation (Γ : Sequent L) : LJ.Sequent L :=
  Γ.map Semiformula.doubleNegation


-- @@ L69-69 verbatim
scoped[FFL.FirstOrder] 
-- @@ L69-69 verbatim
postfix:max "ᴺ" => Sequent.doubleNegation


-- @@ L71-71 verbatim
@[simp] lemma doubleNegation_zero : (0 : Sequent L)ᴺ = 0 := rfl


-- @@ L73-74 verbatim
@[simp] lemma doubleNegation_atom (φ : Proposition L) :
    (⦃φ⦄ : Sequent L)ᴺ = ⦃φᴺ⦄ := by simp [doubleNegation]


-- @@ L76-80 verbatim
@[simp] lemma doubleNegation_add (Γ Δ : Sequent L) : (Γ + Δ)ᴺ = Γᴺ + Δᴺ := by
  simp [doubleNegation]

lemma shift_doubleNegation (Γ : Sequent L) : (Γᴺ)⁺ = (Γ⁺)ᴺ := by
  simp [Sequent.doubleNegation, Rewriting.shifts, Semiformula.rew_doubleNegation]


-- @@ L82-82 verbatim
end Sequent


-- @@ L84-85 verbatim
def Theory.doubleNegation (T : Theory L) : Theoryᵢ L :=
  Semiformula.doubleNegation '' T


-- @@ L87-87 verbatim
namespace LJ.Derivation


-- @@ L89-89 verbatim
open Rewriting LawfulSyntacticRewriting


-- @@ L91-91 verbatim
variable {L : Language} [L.DecidableEq]


-- @@ L93-123 verbatim
def negDoubleNegation : (φ : Proposition L) →
    InterDerivation L (∼φᴺ) (∼φ)ᴺ
  | .rel R v => InterDerivation.dne (by simp)
  | .nrel R v => InterDerivation.refl _
  | ⊤ => by
      constructor
      · exact negElim (eta (∼(⊤ : Propositionᵢ L))) <|
          weakening verum (by simp)
      · apply positiveNeg
        exact assumption (by simp)
  | ⊥ => InterDerivation.refl _
  | φ ⋏ ψ => by
      have eφ := (negDoubleNegation φ).iffnegOfNegIff (by simp)
      have eψ := (negDoubleNegation ψ).iffnegOfNegIff (by simp)
      simpa using (eφ.and eψ).neg
  | φ ⋎ ψ => by
      have e := (negDoubleNegation φ).and (negDoubleNegation ψ)
      exact (InterDerivation.dne (by simp)).trans e
  | ∀¹ φ => by
      have e := (negDoubleNegation (Rewriting.free φ)).iffnegOfNegIff (by simp)
      have e : InterDerivation L (Rewriting.free φᴺ)
          (Rewriting.free (∼(∼φ)ᴺ)) :=
        by simpa [Semiformula.rew_doubleNegation] using e
      simpa using (InterDerivation.all e).neg
  | ∃¹ φ => by
      have e := negDoubleNegation (Rewriting.free φ)
      have e : InterDerivation L (Rewriting.free (∼φᴺ))
          (Rewriting.free ((∼φ)ᴺ)) :=
        by simpa [Semiformula.rew_doubleNegation] using e
      exact (InterDerivation.dne (by simp)).trans (InterDerivation.all e)
  termination_by φ => φ.complexity


-- @@ L125-127 verbatim
def negDoubleNegation' (φ : Proposition L) :
    InterDerivation L (∼(∼φ)ᴺ) φᴺ := by
  simpa using negDoubleNegation (∼φ)


-- @@ L129-129 verbatim
end LJ.Derivation


-- @@ L131-131 verbatim
namespace Derivation


-- @@ L133-133 verbatim
open Rewriting LawfulSyntacticRewriting


-- @@ L135-135 verbatim
variable {L : Language} [L.DecidableEq]


-- @@ L137-142 verbatim
/-- Discharges a translated negated formula from an LJ contradiction derivation. -/
def deductNeg {Γ : Sequent L} {φ : Proposition L}
    (d : (∼(Γ + ⦃φ⦄))ᴺ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L)) :
    (∼Γ)ᴺ ⊢ᴸᴶ¹ (∼(∼φ)ᴺ : Propositionᵢ L) :=
  LJ.Derivation.positiveNeg (Γ := (∼Γ)ᴺ) (φ := (∼φ)ᴺ) <|
    d.cast (by simp)


-- @@ L144-191 verbatim
def gödelGentzen {Γ : Sequent L} : ⊢ᴸᴷ¹ Γ → (∼Γ)ᴺ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L)
  | identity R v => by
      exact LJ.Derivation.contraction
        (LJ.Derivation.eta (∼(.rel R v) : Propositionᵢ L)).negativeNeg
        (by simp [Sequent.doubleNegation]) (by simp)
  | verum => by
      simpa [Sequent.doubleNegation] using LJ.Derivation.eta (⊥ : Propositionᵢ L)
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dφ dψ => by
      have dφ : (∼Γ)ᴺ ⊢ᴸᴶ¹ (∼(∼φ)ᴺ : Propositionᵢ L) :=
        deductNeg (gödelGentzen dφ)
      have dψ : (∼Γ)ᴺ ⊢ᴸᴶ¹ (∼(∼ψ)ᴺ : Propositionᵢ L) :=
        deductNeg (gödelGentzen dψ)
      have dAnd := LJ.Derivation.positiveAnd dφ dψ
      exact LJ.Derivation.contraction dAnd.negativeNeg
        (by simp [Sequent.doubleNegation]) (by simp)
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
      (LJ.Derivation.negativeAnd (Γ := (∼Γ)ᴺ) (φ := (∼φ)ᴺ)
        (ψ := (∼ψ)ᴺ) (Ξ := (⊥ : Propositionᵢ L)) <|
        (gödelGentzen d).cast (by simp)).cast (by simp [Sequent.doubleNegation])
  | all (Γ := Γ) (φ := φ) d => by
      have hshift : (∼Γ⁺)ᴺ = ((∼Γ)ᴺ)⁺ := by
        rw [←Rewriting.shifts_neg, Sequent.shift_doubleNegation]
      have dFree : ((∼Γ)ᴺ)⁺ ⊢ᴸᴶ¹
          (∼Rewriting.free ((∼φ)ᴺ) : Propositionᵢ L) :=
        (deductNeg (gödelGentzen d)).cast
          (by simp [hshift]) (by simp [Semiformula.rew_doubleNegation])
      have dAll := LJ.Derivation.positiveForall (Γ := (∼Γ)ᴺ)
        (φ := ∼(∼φ)ᴺ) <|
        dFree.cast (heq := by simp [Semiformula.rew_doubleNegation])
      exact LJ.Derivation.contraction dAll.negativeNeg
        (by simp [Sequent.doubleNegation]) (by simp)
  | exs (Γ := Γ) (φ := φ) (t := t) d =>
      (LJ.Derivation.negativeForall (Γ := (∼Γ)ᴺ) (φ := (∼φ)ᴺ)
        (t := t) (Ξ := (⊥ : Propositionᵢ L)) <|
        (gödelGentzen d).cast (by simp [Semiformula.rew_doubleNegation]))
        |>.cast (by simp [Sequent.doubleNegation])
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d dn => by
      have ihn := gödelGentzen dn
      have dnφ : (∼Γ)ᴺ ⊢ᴸᴶ¹ (∼(∼φ)ᴺ : Propositionᵢ L) :=
        deductNeg (gödelGentzen d)
      have dφ : (∼Γ)ᴺ ⊢ᴸᴶ¹ φᴺ :=
        LJ.Derivation.cutOne dnφ (LJ.Derivation.negDoubleNegation' φ).1
      exact (LJ.Derivation.cut (Γ := (∼Γ)ᴺ) (Δ := (∼Δ)ᴺ)
        (φ := φᴺ) (Ξ := (⊥ : Propositionᵢ L)) dφ <|
        ihn.cast (by simp)).cast (by simp [Sequent.doubleNegation])
  | contraction d h =>
      LJ.Derivation.weakening (gödelGentzen d) <|
        Multiset.map_subset_map <| Multiset.map_subset_map h


-- @@ L193-193 verbatim
end Derivation


-- @@ L195-202 verbatim
theorem Provable.gödel_gentzen {L : Language.{u}} [L.DecidableEq] {φ : Proposition L} :
    𝐋𝐊¹ ⊢ φ → 𝐋𝐉¹ ⊢ φᴺ := by
  rintro ⟨d⟩
  have d : ⦃(∼φ)ᴺ⦄ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L) := by
    simpa [Sequent.doubleNegation] using Derivation.gödelGentzen d
  have dn : (0 : LJ.Sequent L) ⊢ᴸᴶ¹ (∼(∼φ)ᴺ : Propositionᵢ L) :=
    LJ.Derivation.positiveNeg (φ := (∼φ)ᴺ) d
  exact ⟨LJ.Derivation.cutOne dn (LJ.Derivation.negDoubleNegation' φ).1⟩


-- @@ L204-204 verbatim
end FFL.FirstOrder
