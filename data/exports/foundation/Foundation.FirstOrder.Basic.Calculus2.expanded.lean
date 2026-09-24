module
public import Foundation.FirstOrder.Basic.Calculus

-- @@ L3-3 verbatim
@[expose] public section


-- @@ L5-5 verbatim
/-! # Alternative definition of proof -/


-- @@ L7-7 verbatim
namespace FFL.FirstOrder


-- @@ L9-9 verbatim
variable {L : Language} [L.DecidableEq]


-- @@ L11-11 verbatim
section derivation2


-- @@ L13-23 expanded
inductive Derivation2 (T : Theory L) : Finset (Proposition L) → Type _
  | closed (Γ) (φ : Proposition L) : φ ∈ Γ → unop% HTilde.hTilde φ ∈ Γ → Derivation2 T Γ
  | axm {Γ} (φ : Sentence L) : φ ∈ T → (φ : Proposition L) ∈ Γ → Derivation2 T Γ
  | verum {Γ} : ⊤ ∈ Γ → Derivation2 T Γ
  |
  and {Γ} {φ ψ : Proposition L} :
    binop% HWedge.hWedge φ ψ ∈ Γ →
      Derivation2 T (insert φ Γ) → Derivation2 T (insert ψ Γ) → Derivation2 T Γ
  |
  or {Γ} {φ ψ : Proposition L} :
    binop% HVee.hVee φ ψ ∈ Γ → Derivation2 T (insert φ (insert ψ Γ)) → Derivation2 T Γ
  |
  all {Γ} {φ : Semiproposition L 1} :
    UnivQuantifier.all φ ∈ Γ →
      Derivation2 T (insert (Rewriting.free φ) (Γ.image Rewriting.shift)) → Derivation2 T Γ
  |
  exs {Γ} {φ : Semiproposition L 1} :
    ExsQuantifier.exs φ ∈ Γ →
      (t : SyntacticTerm L) →
        Derivation2 T (insert (FFL.FirstOrder.Rewriting.subst φ ![t]) Γ) → Derivation2 T Γ
  | wk {Δ Γ} : Derivation2 T Δ → Δ ⊆ Γ → Derivation2 T Γ
  | shift {Γ} : Derivation2 T Γ → Derivation2 T (Γ.image Rewriting.shift)
  |
  cut {Γ φ} :
    Derivation2 T (insert φ Γ) → Derivation2 T (insert (unop% HTilde.hTilde φ) Γ) → Derivation2 T Γ


-- @@ L25-25 verbatim
scoped infix:45 " ⟹₂" => Derivation2


-- @@ L27-27 verbatim
abbrev Derivable2 (T : Theory L) (Γ : Finset (Proposition L)) := Nonempty (T ⟹₂ Γ)


-- @@ L29-29 verbatim
scoped infix:45 " ⟹₂! " => Derivable2


-- @@ L31-31 verbatim
abbrev _root_.FFL.FirstOrder.Theory.Proof2 (T : Theory L) (φ : Proposition L) := T ⟹₂ {φ}


-- @@ L33-33 verbatim
scoped infix: 45 " ⊢₂! " => Theory.Proof2


-- @@ L35-35 verbatim
variable {T : Theory L}


-- @@ L37-38 verbatim
lemma shifts_toFinset_eq_image_shift (Γ : Sequent L) :
    Γ⁺.toFinset = Γ.toFinset.image Rewriting.shift := by ext φ; simp [Rewriting.shifts]


-- @@ L40-66 expanded
def Derivation.toDerivation2 (T) {Γ : Sequent L} : Derivation Γ → T ⟹₂Γ.toFinset
  | Derivation.identity R v => Derivation2.closed _ (Semiformula.rel R v) (by simp) (by simp)
  | Derivation.verum => Derivation2.verum (by simp)
  | Derivation.and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq =>
    Derivation2.and (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by intro x hx; simp_all; tauto))
      (Derivation2.wk (Derivation.toDerivation2 T dq) (by intro x hx; simp_all; tauto))
  | Derivation.or (Γ := Γ) (φ := φ) (ψ := ψ) dpq =>
    Derivation2.or (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dpq) (by intro x hx; simp_all; tauto))
  | Derivation.all (Γ := Γ) (φ := φ) dp =>
    Derivation2.all (φ := φ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp)
        (by
          intro x hx
          simp [shifts_toFinset_eq_image_shift] at hx ⊢
          aesop))
  | Derivation.exs (Γ := Γ) (φ := φ) (t := t) dp =>
    Derivation2.exs (φ := φ) (by simp) t
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by intro x hx; simp_all; tauto))
  | Derivation.contraction d h =>
    Derivation2.wk (Derivation.toDerivation2 T d) (Multiset.toFinset_subset.mpr h)
  | Derivation.cut (Γ := Γ) (Δ := Δ) (φ := φ) d₁ d₂ =>
    Derivation2.cut (φ := φ)
      (Derivation2.wk (Derivation.toDerivation2 T d₁) (by intro x hx; simp_all; tauto))
      (Derivation2.wk (Derivation.toDerivation2 T d₂) (by intro x hx; simp_all; tauto))


-- @@ L68-73 expanded
/-- Contracts a principal formula already present in the side context.
This is a routine structural derivation. -/
def Derivation.absorb (d : Derivation (Γ + atom φ)) (h : φ ∈ Γ) : Derivation Γ :=
  d.contra <| by
    intro ψ hψ
    rcases Multiset.mem_add.mp hψ with hψ | hψ <;> simp_all


-- @@ L75-75 verbatim
namespace Derivation2


-- @@ L77-80 expanded
structure ProofData (T : Theory L) (Γ : Finset (Proposition L)) where
  axioms : Multiset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : Derivation (Γ.1 + unop% HTilde.hTilde (Sequent.embed axioms))


-- @@ L82-83 verbatim
noncomputable def cast {Γ Δ : Finset (Proposition L)} (d : T ⟹₂ Γ)
    (h : Γ = Δ := by simp) : T ⟹₂ Δ := h ▸ d


-- @@ L85-88 expanded
omit [L.DecidableEq] in
@[simp]
lemma shifts_tilde_embed (A : Multiset (Sentence L)) :
    (unop% HTilde.hTilde (Sequent.embed A))⁺ = unop% HTilde.hTilde (Sequent.embed A) := by
  simp [Rewriting.shifts, Sequent.embed, Multiset.tilde_def]


-- @@ L90-111 expanded
@[reducible]
noncomputable def cutManyProof (A : Multiset (Sentence L)) (hA : ∀ ψ ∈ A, ψ ∈ T)
    (d : T ⟹₂(insert (φ : Proposition L) (unop% HTilde.hTilde (Sequent.embed A)).toFinset)) :
    T ⟹₂{ φ } :=
  -- Multiset induction cannot eliminate into the Type-valued derivation family.
  
  let rec go :
    (l : List (Sentence L)) →
      (∀ ψ ∈ l, ψ ∈ T) →
        T ⟹₂(insert (φ : Proposition L)
              (unop% HTilde.hTilde (Sequent.embed (l : Multiset _))).toFinset) →
          T ⟹₂{ φ }
    | [], _, d => Derivation2.cast d (by simp)
    | ψ :: l, hl, d =>
      have ax :
        T ⟹₂insert (ψ : Proposition L)
            (insert φ (unop% HTilde.hTilde (Sequent.embed (l : Multiset _))).toFinset) :=
        Derivation2.axm ψ (hl ψ (by simp)) (by simp)
      have dn :
        T ⟹₂insert (unop% HTilde.hTilde (ψ : Proposition L))
            (insert φ (unop% HTilde.hTilde (Sequent.embed (l : Multiset _))).toFinset) :=
        by
        refine Derivation2.cast d ?_
        ext x
        have hneg :
          unop% HTilde.hTilde x = Rewriting.emb ψ ↔ x = unop% HTilde.hTilde (Rewriting.emb ψ) := by
          grind
        simp [Sequent.embed, hneg, or_left_comm]
      have c : T ⟹₂insert φ (unop% HTilde.hTilde (Sequent.embed (l : Multiset _))).toFinset := by
        exact Derivation2.cast (Derivation2.cut ax dn) (by ext x; simp)
      go l (by simp_all) c
  go A.toList (by simpa using hA) <| Derivation2.cast d (by ext x; simp)


-- @@ L113-176 expanded
noncomputable def toProofData : {Γ : Finset (Proposition L)} → T ⟹₂Γ → ProofData T Γ
  | Γ, closed _ φ hp hn =>
    ⟨0, by simp,
      (Derivation.eta φ).contra
        (by
          intro x hx
          rcases Multiset.mem_add.mp hx with hx | hx <;> simp_all)⟩
  | Γ, axm φ hT hΓ =>
    ⟨atom φ, by simp [hT],
      (Derivation.eta (φ : Proposition L)).contra
        (by
          intro x hx
          rcases Multiset.mem_add.mp hx with hx | hx <;> simp_all)⟩
  | Γ, verum h => ⟨0, by simp, Derivation.verum.contra (by intro x hx; simp_all)⟩
  | Γ, and (φ := φ) (ψ := ψ) h dφ dψ =>
    by
    rcases toProofData dφ with ⟨A, hA, bφ⟩
    rcases toProofData dψ with ⟨B, hB, bψ⟩
    refine ⟨A + B, by simp; grind, ?_⟩
    have bφ' : Derivation ((Γ.1 + unop% HTilde.hTilde (Sequent.embed (A + B))) + atom φ) :=
      bφ.contra (by intro x hx; simp_all [Sequent.embed]; aesop)
    have bψ' : Derivation ((Γ.1 + unop% HTilde.hTilde (Sequent.embed (A + B))) + atom ψ) :=
      bψ.contra (by intro x hx; simp_all [Sequent.embed]; aesop)
    exact (Derivation.and bφ' bψ').absorb (Multiset.mem_add.mpr <| Or.inl h)
  | Γ, or (φ := φ) (ψ := ψ) h d =>
    by
    rcases toProofData d with ⟨A, hA, b⟩
    refine ⟨A, hA, ?_⟩
    have b' : Derivation ((Γ.1 + unop% HTilde.hTilde (Sequent.embed A)) + (atom φ + atom ψ)) :=
      b.contra (by intro x hx; simp_all; aesop)
    exact (Derivation.or b').absorb (Multiset.mem_add.mpr <| Or.inl h)
  | Γ, all (φ := φ) h d => by
    rcases toProofData d with ⟨A, hA, b⟩
    refine ⟨A, hA, ?_⟩
    have b' :
      Derivation ((Γ.1 + unop% HTilde.hTilde (Sequent.embed A))⁺ + atom (Rewriting.free φ)) :=
      b.contra
        (by
          rw [Rewriting.shifts_add, shifts_tilde_embed]
          intro x hx
          simp [Rewriting.shifts] at hx ⊢
          aesop)
    exact (Derivation.all b').absorb (Multiset.mem_add.mpr <| Or.inl h)
  | Γ, exs (φ := φ) h t d => by
    rcases toProofData d with ⟨A, hA, b⟩
    refine ⟨A, hA, ?_⟩
    have b' :
      Derivation
        ((Γ.1 + unop% HTilde.hTilde (Sequent.embed A)) +
          atom (FFL.FirstOrder.Rewriting.subst φ ![t])) :=
      b.contra (by intro x hx; simp_all; aesop)
    exact (Derivation.exs (t := t) b').absorb (Multiset.mem_add.mpr <| Or.inl h)
  | Γ, wk d h => by
    rcases toProofData d with ⟨A, hA, b⟩
    exact ⟨A, hA, b.contra (by intro x hx; simp_all; aesop)⟩
  | _, shift (Γ := Γ) d => by
    rcases toProofData d with ⟨A, hA, b⟩
    refine ⟨A, hA, b.shift.contra ?_⟩
    rw [Rewriting.shifts_add, shifts_tilde_embed]
    intro x hx
    simpa [Rewriting.shifts] using hx
  | Γ, cut (φ := φ) d dn => by
    rcases toProofData d with ⟨A, hA, b⟩
    rcases toProofData dn with ⟨B, hB, bn⟩
    refine ⟨A + B, by simp; grind, ?_⟩
    have b' : Derivation ((Γ.1 + unop% HTilde.hTilde (Sequent.embed (A + B))) + atom φ) :=
      b.contra (by intro x hx; simp_all [Sequent.embed]; aesop)
    have bn' :
      Derivation
        ((Γ.1 + unop% HTilde.hTilde (Sequent.embed (A + B))) + atom unop% HTilde.hTilde φ) :=
      bn.contra (by intro x hx; simp_all [Sequent.embed]; aesop)
    exact
      (Derivation.cut (Γ := Γ.1 + unop% HTilde.hTilde (Sequent.embed (A + B))) (Δ :=
            Γ.1 + unop% HTilde.hTilde (Sequent.embed (A + B))) (φ := φ) b' bn').contra
        (by intro x hx; simp_all)


-- @@ L178-178 verbatim
end Derivation2


-- @@ L180-180 verbatim
namespace Theory


-- @@ L182-184 expanded
noncomputable def Proof.toProof2 {φ : Sentence L} (b : Entailment.Prf T φ) :
    T ⊢₂! (φ : Proposition L) :=
  Derivation2.cutManyProof b.axioms b.axioms_mem <|
    Derivation2.cast (Derivation.toDerivation2 T b.derivation) (by ext x; simp [Sequent.embed])


-- @@ L186-188 expanded
noncomputable def Proof2.toProof {φ : Sentence L} (d : T ⊢₂! (φ : Proposition L)) :
    Entailment.Prf T φ :=
  by
  rcases Derivation2.toProofData d with ⟨A, hA, b⟩
  exact ⟨A, hA, Derivation.cast b (by simp [Sequent.embed, Multiset.atom_eq_singleton])⟩


-- @@ L190-190 verbatim
end Theory


-- @@ L192-193 expanded
lemma provable_iff_derivable2 {φ : Sentence L} :
    Provable T φ ↔ Nonempty (T ⊢₂! (φ : Proposition L)) := by
  exact ⟨fun h ↦ ⟨h.get.toProof2⟩, fun ⟨h⟩ ↦ ⟨h.toProof⟩⟩


-- @@ L195-195 verbatim
end derivation2


-- @@ L197-197 verbatim
end FFL.FirstOrder
