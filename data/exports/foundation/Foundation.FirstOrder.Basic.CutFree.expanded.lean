module

public import Foundation.FirstOrder.Basic.Calculus


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-10 verbatim
/-!
# Canonical model of classical first-order logic

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination [Avi01]
 -/


-- @@ L12-12 verbatim
namespace FFL.FirstOrder


-- @@ L14-14 verbatim
variable {L : Language.{u}}


-- @@ L16-16 verbatim
namespace Derivation


-- @@ L18-26 verbatim
inductive IsCutFree : {Γ : Sequent L} → ⊢ᴸᴷ¹ Γ → Prop
  | identity (r : L.Rel k) (v) : IsCutFree (identity r v)
  | verum : IsCutFree verum
  | or {d : ⊢ᴸᴷ¹ Γ + ⦃φ, ψ⦄} : IsCutFree d → IsCutFree d.or
  | and {dφ : ⊢ᴸᴷ¹ Γ + ⦃φ⦄} {dψ : ⊢ᴸᴷ¹ Γ + ⦃ψ⦄} :
      IsCutFree dφ → IsCutFree dψ → IsCutFree (dφ.and dψ)
  | all {d : ⊢ᴸᴷ¹ Γ⁺ + ⦃Rewriting.free φ⦄} : IsCutFree d → IsCutFree d.all
  | exs (t) {d : ⊢ᴸᴷ¹ Γ + ⦃φ/[t]⦄} : IsCutFree d → IsCutFree d.exs
  | contraction {d : ⊢ᴸᴷ¹ Δ} (ss : Δ ⊆ Γ) : IsCutFree d → IsCutFree (d.contraction ss)


-- @@ L28-28 verbatim
attribute [simp] IsCutFree.identity IsCutFree.verum


-- @@ L30-30 verbatim
variable {Γ Δ : Sequent L}


-- @@ L32-40 verbatim
@[simp] lemma isCutFree_or_iff {d : ⊢ᴸᴷ¹ Γ + ⦃φ, ψ⦄} :
    IsCutFree d.or ↔ IsCutFree d := by
  constructor
  · intro h
    refine h.rec
      (motive := fun {_} d _ ↦ match d with | .or d => IsCutFree d | _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp_all
  · exact .or


-- @@ L42-52 verbatim
@[simp] lemma isCutFree_and_iff {dφ : ⊢ᴸᴷ¹ Γ + ⦃φ⦄} {dψ : ⊢ᴸᴷ¹ Γ + ⦃ψ⦄} :
    IsCutFree (dφ.and dψ) ↔ IsCutFree dφ ∧ IsCutFree dψ := by
  constructor
  · rintro h
    refine h.rec
      (motive := fun {_} d _ ↦
        match d with | .and dφ dψ => IsCutFree dφ ∧ IsCutFree dψ | _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp_all
  · rintro ⟨hφ, hψ⟩
    exact hφ.and hψ


-- @@ L54-61 verbatim
@[simp] lemma isCutFree_all_iff {d : ⊢ᴸᴷ¹ Γ⁺ + ⦃Rewriting.free φ⦄} :
    IsCutFree d.all ↔ IsCutFree d := by
  constructor
  · intro h
    refine h.rec (motive := fun {_} d _ ↦ match d with | .all d => IsCutFree d | _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp_all
  · exact .all


-- @@ L63-70 verbatim
@[simp] lemma isCutFree_exs_iff {d : ⊢ᴸᴷ¹ Γ + ⦃φ/[t]⦄} :
    IsCutFree d.exs ↔ IsCutFree d := by
  constructor
  · intro h
    refine h.rec (motive := fun {_} d _ ↦ match d with | .exs d => IsCutFree d | _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp_all
  · exact .exs t


-- @@ L72-80 verbatim
@[simp] lemma isCutFree_contraction_iff {d : ⊢ᴸᴷ¹ Δ} {ss : Δ ⊆ Γ} :
    IsCutFree (d.contraction ss) ↔ IsCutFree d := by
  constructor
  · intro h
    refine h.rec
      (motive := fun {_} d _ ↦ match d with | .contraction d _ => IsCutFree d | _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp_all
  · exact .contraction _


-- @@ L82-83 verbatim
@[simp] lemma IsCutFree.cast {d : ⊢ᴸᴷ¹ Γ} {e : Γ = Δ} :
    IsCutFree (.cast d e) ↔ IsCutFree d := by rcases e; rfl


-- @@ L85-91 verbatim
@[simp] lemma IsCutFree.not_cut (dp : ⊢ᴸᴷ¹ Γ + ⦃φ⦄) (dn : ⊢ᴸᴷ¹ Δ + ⦃∼φ⦄) :
    ¬IsCutFree (dp.cut dn) := by
  intro h
  refine h.rec
    (motive := fun {_} d _ ↦ match d with | .cut _ _ => False | _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp


-- @@ L93-96 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma isCutFree_rewrite_iff_isCutFree {f : ℕ → SyntacticTerm L} {d : ⊢ᴸᴷ¹ Γ} :
    IsCutFree (rewrite f d) ↔ IsCutFree d := by
  induction d generalizing f <;> simp [rewrite, *]


-- @@ L98-99 verbatim
@[simp] lemma isCutFree_map_iff_isCutFree {f : ℕ → ℕ} {d : ⊢ᴸᴷ¹ Γ} :
    IsCutFree (Derivation.map d f) ↔ IsCutFree d := isCutFree_rewrite_iff_isCutFree


-- @@ L101-104 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma IsCutFree.generalizeByNewVar_isCutFree {φ : Semiproposition L 1} (hp : ¬φ.FVar? m)
    (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m) (d : ⊢ᴸᴷ¹ Δ + ⦃φ/[&m]⦄) :
    IsCutFree (generalizeByNewVar hp hΔ d) ↔ IsCutFree d := by simp [generalizeByNewVar]


-- @@ L106-106 verbatim
end Derivation
