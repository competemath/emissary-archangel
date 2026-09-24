module

public import Foundation.Propositional.Entailment.Cl
public import Foundation.Vorspiel.Multiset


-- @@ L6-13 verbatim
/-!
# Sequent calculus and variants

This file defines a characterization of Tait style calculus and Gentzen style calculus.

## Main Definitions
- `FFL.OneSidedLK`
-/


-- @@ L15-16 verbatim
@[expose]
public section


-- @@ L18-18 verbatim
namespace FFL


-- @@ L20-20 verbatim
/-! ## One-sided $\mathbf{LK}$ -/


-- @@ L22-28 verbatim
class OneSidedLK {F : Type*} [LogicalConnective F] [LogicalNeutral F]
    [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] (𝔇 : Multiset F → Type*) where
  identity (φ) : 𝔇 ⦃φ, ∼φ⦄
  contraction : 𝔇 Δ → Δ ⊆ Γ → 𝔇 Γ
  verum : 𝔇 ⦃⊤⦄
  and : 𝔇 (Γ + ⦃φ⦄) → 𝔇 (Γ + ⦃ψ⦄) → 𝔇 (Γ + ⦃φ ⋏ ψ⦄)
  or : 𝔇 (Γ + ⦃φ, ψ⦄) → 𝔇 (Γ + ⦃φ ⋎ ψ⦄)


-- @@ L30-34 verbatim
class OneSidedLK.Cut
    {F : Type*} [LogicalConnective F] [LogicalNeutral F]
    [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F]
    (𝔇 : Multiset F → Type*) extends OneSidedLK 𝔇 where
  cut : 𝔇 (Γ + ⦃φ⦄) → 𝔇 (Δ + ⦃∼φ⦄) → 𝔇 (Γ + Δ)


-- @@ L36-36 verbatim
namespace OneSidedLK


-- @@ L38-39 verbatim
variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]
  [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] {𝔇 : Multiset F → Type*}


-- @@ L41-41 verbatim
def cast (b : 𝔇 Γ) (h : Γ = Δ := by abel) : 𝔇 Δ := h ▸ b


-- @@ L43-43 verbatim
def contra [OneSidedLK 𝔇] (d : 𝔇 Γ) (h : Γ ⊆ Δ := by simp) : 𝔇 Δ := contraction d h


-- @@ L45-48 verbatim
def close [OneSidedLK 𝔇] (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝔇 Γ :=
  contraction (identity φ) (by
    intro ψ hψ
    rcases Multiset.mem_add.mp hψ with hψ | hψ <;> simp_all)


-- @@ L50-50 verbatim
def top [OneSidedLK 𝔇] (h : ⊤ ∈ Γ := by simp) : 𝔇 Γ := contraction verum (by simpa using h)


-- @@ L52-58 verbatim
def tensor [OneSidedLK 𝔇] {φ ψ : F} (dφ : 𝔇 (Γ + ⦃φ⦄)) (dψ : 𝔇 (Δ + ⦃ψ⦄)) :
    𝔇 (Γ + Δ + ⦃φ ⋏ ψ⦄) :=
  and
    (contraction dφ (by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all))
    (contraction dψ (by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all))

alias cut := OneSidedLK.Cut.cut


-- @@ L60-62 verbatim
def eCut [Cut 𝔇] (d₁ : 𝔇 (Γ + ⦃φ⦄)) (d₂ : 𝔇 (Δ + ⦃ψ⦄))
    (e : ∼φ = ψ := by simp) : 𝔇 (Γ + Δ) :=
  cut d₁ (cast d₂ (by simp [e]))


-- @@ L64-67 verbatim
/-- Eliminating falsum is the routine cut against the verum rule. -/
def removeBot [Cut 𝔇] (d : 𝔇 (Γ + ⦃⊥⦄)) : 𝔇 Γ :=
  have dt : 𝔇 ((0 : Multiset F) + ⦃∼⊥⦄) := cast verum (by simp)
  cast <| cut (φ := ⊥) (Γ := Γ) (Δ := 0) d dt


-- @@ L69-78 verbatim
/-- Modus ponens with independent side contexts. This is the routine cut derivation. -/
def modusPonens [Cut 𝔇] (di : 𝔇 (Γ + ⦃φ 🡒 ψ⦄)) (dp : 𝔇 (Δ + ⦃φ⦄)) :
    𝔇 (Γ + Δ + ⦃ψ⦄) :=
  have h₁ : 𝔇 ⦃∼(φ 🡒 ψ), ∼φ, ψ⦄ := cast
    (tensor (𝔇 := 𝔇) (Γ := ⦃∼φ⦄) (Δ := ⦃ψ⦄) (φ := φ) (ψ := ∼ψ)
      (cast (identity φ) (by abel)) (cast (identity (∼ψ)) (by simp; abel)))
    (by simp [LogicalConnective.DeMorgan.imply]; abel)
  have h₂ : 𝔇 (Γ + ⦃∼φ, ψ⦄) := cast <|
    cut (φ := φ 🡒 ψ) (Γ := Γ) (Δ := ⦃∼φ, ψ⦄) di (cast h₁)
  cast <| cut (φ := φ) (Γ := Δ) (Δ := Γ + ⦃ψ⦄) dp (cast h₂)


-- @@ L80-94 verbatim
def disj₂ {Γ : List F} {Δ : Multiset F} [OneSidedLK 𝔇] :
    𝔇 ((Γ : Multiset F) + Δ) → 𝔇 (Δ + ⦃⋁Γ⦄) := fun d ↦
  match Γ with
  | [] => contra d (by intro φ hφ; simp_all)
  | [φ] => cast d (by
    change φ ::ₘ Δ = Δ + ⦃φ⦄
    exact (Multiset.add_atom_eq_cons φ Δ).symm)
  | φ :: ψ :: Γ => by
    have dt : 𝔇 ((Δ + ⦃φ⦄) + ⦃⋁(ψ :: Γ)⦄) :=
      disj₂ (cast d (by
        change (φ ::ₘ (↑(ψ :: Γ) : Multiset F)) + Δ = (↑(ψ :: Γ) : Multiset F) + (Δ + ⦃φ⦄)
        rw [← Multiset.add_atom_eq_cons]
        abel))
    exact or (Γ := Δ) (φ := φ) (ψ := ⋁(ψ :: Γ)) (cast dt (by abel))
  termination_by _ => Γ.length


-- @@ L96-103 verbatim
def conj₂ [OneSidedLK 𝔇] {Γ : List F} {Δ : Multiset F}
    (d : (φ : F) → φ ∈ Γ → 𝔇 (Δ + ⦃φ⦄)) : 𝔇 (Δ + ⦃⋀Γ⦄) :=
  match Γ with
  |          [] => contra verum (by intro φ hφ; simp_all)
  |         [φ] => d φ (by simp)
  | φ :: ψ :: Γ =>
    have : 𝔇 (Δ + ⦃⋀(ψ :: Γ)⦄) := conj₂ (Γ := ψ :: Γ) (fun χ h ↦ d χ (by simp_all))
    and (Γ := Δ) (φ := φ) (ψ := ⋀(ψ :: Γ)) (d φ (by simp)) this


-- @@ L105-105 verbatim
namespace AxiomDerivation


-- @@ L107-107 verbatim
variable [OneSidedLK 𝔇]


-- @@ L109-110 verbatim
def introOr (d : 𝔇 ⦃φ, ψ⦄) : 𝔇 ⦃φ ⋎ ψ⦄ :=
  cast (or (Γ := 0) (φ := φ) (ψ := ψ) (cast d (by abel))) (by simp)


-- @@ L112-113 verbatim
def introDisj {Γ : List F} (d : 𝔇 (Γ : Multiset F)) : 𝔇 ⦃⋁Γ⦄ :=
  cast <| disj₂ (Γ := Γ) (Δ := 0) (cast d)


-- @@ L115-122 verbatim
/-- The rule expansion of the classical negation equivalence axiom. This is a routine syntactic derivation. -/
def negEquiv (φ : F) : 𝔇 ⦃(φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ)⦄ :=
  have d₁ : 𝔇 ⦃φ ⋎ ∼φ ⋎ ⊥⦄ := introDisj <| close φ (Γ := ⦃φ, ∼φ, ⊥⦄)
  have dp : 𝔇 ⦃∼φ, φ⦄ := close φ (Γ := ⦃∼φ, φ⦄)
  have dt : 𝔇 ⦃∼φ, ⊤⦄ := top (Γ := ⦃∼φ, ⊤⦄)
  have dc : 𝔇 ⦃∼φ, φ ⋏ ⊤⦄ := cast <| and (Γ := ⦃∼φ⦄) (φ := φ) (ψ := ⊤) (cast dp) (cast dt)
  cast <| and (Γ := 0) (φ := φ ⋎ ∼φ ⋎ ⊥) (ψ := φ ⋏ ⊤ ⋎ ∼φ)
    (cast d₁) (cast <| introOr (φ := φ ⋏ ⊤) (ψ := ∼φ) <| cast dc (by abel))


-- @@ L124-126 verbatim
/-- The rule expansion of the K axiom. This is a routine syntactic derivation. -/
def implyK (φ ψ : F) : 𝔇 ⦃∼φ ⋎ ∼ψ ⋎ φ⦄ :=
  introDisj <| close φ (Γ := ⦃∼φ, ∼ψ, φ⦄)


-- @@ L128-145 verbatim
/-- The rule expansion of the S axiom. This is a routine syntactic derivation. -/
def implyS (φ ψ χ : F) : 𝔇 ⦃φ ⋏ ψ ⋏ ∼χ ⋎ φ ⋏ ∼ψ ⋎ ∼φ ⋎ χ⦄ :=
  let A := φ ⋏ ψ ⋏ ∼χ
  let B := φ ⋏ ∼ψ
  let C := ∼φ
  let D := χ
  have dφ : 𝔇 (⦃B, C, D⦄ + ⦃φ⦄) := close φ (Γ := ⦃B, C, D⦄ + ⦃φ⦄)
    (by simp) (by simp [C])
  have dbp : 𝔇 (⦃C, D, ψ⦄ + ⦃φ⦄) := close φ (Γ := ⦃C, D, ψ⦄ + ⦃φ⦄)
    (by simp) (by simp [C])
  have dbn : 𝔇 (⦃C, D, ψ⦄ + ⦃∼ψ⦄) := close ψ (Γ := ⦃C, D, ψ⦄ + ⦃∼ψ⦄)
  have dψ : 𝔇 (⦃B, C, D⦄ + ⦃ψ⦄) := cast <|
    and (Γ := ⦃C, D, ψ⦄) (φ := φ) (ψ := ∼ψ) dbp dbn
  have dnχ : 𝔇 (⦃B, C, D⦄ + ⦃∼χ⦄) := close χ (Γ := ⦃B, C, D⦄ + ⦃∼χ⦄)
    (by simp [D]) (by simp)
  have dr : 𝔇 (⦃B, C, D⦄ + ⦃ψ ⋏ ∼χ⦄) := and (φ := ψ) (ψ := ∼χ) dψ dnχ
  have da : 𝔇 ⦃A, B, C, D⦄ := cast <| and (φ := φ) (ψ := ψ ⋏ ∼χ) dφ dr
  introDisj da


-- @@ L147-150 verbatim
/-- The rule expansion of the first conjunction axiom. This is a routine syntactic derivation. -/
def and₁ (φ ψ : F) : 𝔇 ⦃(∼φ ⋎ ∼ψ) ⋎ φ⦄ :=
  introOr <| cast <| or (Γ := ⦃φ⦄) (φ := ∼φ) (ψ := ∼ψ)
    (cast <| close φ (Γ := ⦃φ, ∼φ, ∼ψ⦄))


-- @@ L152-155 verbatim
/-- The rule expansion of the second conjunction axiom. This is a routine syntactic derivation. -/
def and₂ (φ ψ : F) : 𝔇 ⦃(∼φ ⋎ ∼ψ) ⋎ ψ⦄ :=
  introOr <| cast <| or (Γ := ⦃ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
    (cast <| close ψ (Γ := ⦃ψ, ∼φ, ∼ψ⦄))


-- @@ L157-163 verbatim
/-- The rule expansion of conjunction introduction. This is a routine syntactic derivation. -/
def and₃ (φ ψ : F) : 𝔇 ⦃∼φ ⋎ ∼ψ ⋎ φ ⋏ ψ⦄ :=
  have dp : 𝔇 ⦃∼φ, ∼ψ, φ⦄ := close φ (Γ := ⦃∼φ, ∼ψ, φ⦄)
  have dq : 𝔇 ⦃∼φ, ∼ψ, ψ⦄ := close ψ (Γ := ⦃∼φ, ∼ψ, ψ⦄)
  introDisj (Γ := [∼φ, ∼ψ, φ ⋏ ψ]) <| cast <|
    and (Γ := ⦃∼φ, ∼ψ⦄) (φ := φ) (ψ := ψ)
    (cast dp (by abel)) (cast dq (by abel))


-- @@ L165-167 verbatim
/-- The rule expansion of the first disjunction axiom. This is a routine syntactic derivation. -/
def or₁ (φ ψ : F) : 𝔇 ⦃∼φ ⋎ φ ⋎ ψ⦄ :=
  introDisj <| close φ (Γ := ⦃∼φ, φ, ψ⦄)


-- @@ L169-171 verbatim
/-- The rule expansion of the second disjunction axiom. This is a routine syntactic derivation. -/
def or₂ (φ ψ : F) : 𝔇 ⦃∼ψ ⋎ φ ⋎ ψ⦄ :=
  introDisj <| close ψ (Γ := ⦃∼ψ, φ, ψ⦄)


-- @@ L173-188 verbatim
/-- The rule expansion of disjunction elimination. This is a routine syntactic derivation. -/
def or₃ (φ ψ χ : F) : 𝔇 ⦃φ ⋏ ∼χ ⋎ ψ ⋏ ∼χ ⋎ ∼φ ⋏ ∼ψ ⋎ χ⦄ :=
  let A := φ ⋏ ∼χ
  let B := ψ ⋏ ∼χ
  let C := ∼φ ⋏ ∼ψ
  let D := χ
  have dap : 𝔇 (⦃B, D, ∼φ⦄ + ⦃φ⦄) := close φ (Γ := ⦃B, D, ∼φ⦄ + ⦃φ⦄)
  have dan : 𝔇 (⦃B, D, ∼φ⦄ + ⦃∼χ⦄) := close χ (Γ := ⦃B, D, ∼φ⦄ + ⦃∼χ⦄)
    (by simp [D]) (by simp)
  have dnp : 𝔇 (⦃A, B, D⦄ + ⦃∼φ⦄) := cast <| and (φ := φ) (ψ := ∼χ) dap dan
  have dbp : 𝔇 (⦃A, D, ∼ψ⦄ + ⦃ψ⦄) := close ψ (Γ := ⦃A, D, ∼ψ⦄ + ⦃ψ⦄)
  have dbn : 𝔇 (⦃A, D, ∼ψ⦄ + ⦃∼χ⦄) := close χ (Γ := ⦃A, D, ∼ψ⦄ + ⦃∼χ⦄)
    (by simp [D]) (by simp)
  have dnn : 𝔇 (⦃A, B, D⦄ + ⦃∼ψ⦄) := cast <| and (φ := ψ) (ψ := ∼χ) dbp dbn
  have dc : 𝔇 ⦃A, B, C, D⦄ := cast <| and (φ := ∼φ) (ψ := ∼ψ) dnp dnn
  introDisj dc


-- @@ L190-192 verbatim
/-- The rule expansion of double-negation elimination. This is a routine syntactic derivation. -/
def dne (φ : F) : 𝔇 ⦃∼φ ⋎ φ⦄ :=
  introOr <| close φ (Γ := ⦃∼φ, φ⦄)


-- @@ L194-194 verbatim
end AxiomDerivation


-- @@ L196-196 verbatim
open Entailment


-- @@ L198-226 verbatim
/-- A one-sided classical calculus induces classical entailment whenever singleton
derivations can be embedded as proofs. This is the routine translation of the
Hilbert axioms into one-sided sequent rules. -/
abbrev AxiomDerivation.cl {P : Type*} [Entailment P F] (𝓟 : P)
    [Entailment.ModusPonens 𝓟] [OneSidedLK 𝔇]
    (lift : ∀ {φ}, 𝔇 ⦃φ⦄ → 𝓟 ⊢! φ) : Entailment.Cl 𝓟 where
  negEquiv! {φ} := Entailment.cast
    (show 𝓟 ⊢! (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) from
      lift <| AxiomDerivation.negEquiv φ)
    (by simp [Axioms.NegEquiv, LogicalConnective.DeMorgan.imply, LogicalConnective.iff])
  verum! := lift verum
  implyK! {φ ψ} := Entailment.cast (lift <| AxiomDerivation.implyK φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  implyS! {φ ψ χ} := Entailment.cast (lift <| AxiomDerivation.implyS φ ψ χ)
    (by simp [LogicalConnective.DeMorgan.imply])
  and₁! {φ ψ} := Entailment.cast (lift <| AxiomDerivation.and₁ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  and₂! {φ ψ} := Entailment.cast (lift <| AxiomDerivation.and₂ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  and₃! {φ ψ} := Entailment.cast (lift <| AxiomDerivation.and₃ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  or₁! {φ ψ} := Entailment.cast (lift <| AxiomDerivation.or₁ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  or₂! {φ ψ} := Entailment.cast (lift <| AxiomDerivation.or₂ φ ψ)
    (by simp [LogicalConnective.DeMorgan.imply])
  or₃! {φ ψ χ} := Entailment.cast (lift <| AxiomDerivation.or₃ φ ψ χ)
    (by simp [LogicalConnective.DeMorgan.imply])
  dne! {φ} := Entailment.cast (lift <| AxiomDerivation.dne φ)
    (by simp [LogicalConnective.DeMorgan.imply])


-- @@ L228-230 verbatim
/-- An entailment relation which is determined solely by derivability. -/
class PrincipalEntailment (𝔇 : outParam (Multiset F → Type*)) {P : Type*} [Entailment P F] (𝓟 : P) where
  equiv {φ} : 𝓟 ⊢! φ ≃ 𝔇 ⦃φ⦄


-- @@ L232-232 verbatim
namespace PrincipalEntailment


-- @@ L234-234 verbatim
variable {P : Type*} [Entailment P F] {𝓟 : P} [PrincipalEntailment 𝔇 𝓟]


-- @@ L236-240 verbatim
omit [LogicalConnective F] [LogicalNeutral F]
  [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] in
lemma provable_iff :
    𝓟 ⊢ φ ↔ Nonempty (𝔇 ⦃φ⦄) := by
  simpa using! OneSidedLK.PrincipalEntailment.equiv.nonempty_congr


-- @@ L242-242 verbatim
variable [OneSidedLK.Cut 𝔇] (𝓟)


-- @@ L244-246 verbatim
instance : Entailment.ModusPonens 𝓟 where
  mdp! {φ ψ} b₁ b₂ :=
    equiv.symm <| cast <| modusPonens (Γ := 0) (Δ := 0) (equiv b₁) (equiv b₂)


-- @@ L248-248 verbatim
instance : Entailment.Cl 𝓟 := AxiomDerivation.cl 𝓟 PrincipalEntailment.equiv.symm


-- @@ L250-260 verbatim
variable {𝓟}

lemma derivable_iff_provable_disj {Γ : List F} : Nonempty (𝔇 (Γ : Multiset F)) ↔ 𝓟 ⊢ ⋁Γ := by
  constructor
  · rintro ⟨d⟩
    have : 𝔇 ((Γ : Multiset F) + 0) := cast d
    exact provable_iff.mpr ⟨disj₂ this⟩
  · rintro h
    have d₁ : 𝔇 ⦃⋁Γ⦄ := (provable_iff.mp h).some
    have d₂ : 𝔇 ((Γ : Multiset F) + ⦃⋀(∼Γ)⦄) := conj₂ fun φ h ↦ close φ (by simp) (by simp_all)
    exact ⟨cast (eCut (Γ := 0) (Δ := (Γ : Multiset F)) d₁ d₂)⟩


-- @@ L262-262 verbatim
end PrincipalEntailment


-- @@ L264-265 verbatim
abbrev Pullback (𝔇 : Multiset F → Type*) {G : Type*} [LogicalConnective G]
    [LogicalNeutral G] (f : G →ˡᶜ F) : Multiset G → Type _ := fun Γ ↦ 𝔇 (Γ.map f)


-- @@ L267-267 verbatim
namespace Pullback


-- @@ L269-270 verbatim
variable {G : Type*} [LogicalConnective G] [LogicalNeutral G]
  [TildeInvolutive G] [LogicalConnective.DeMorgan G] [LogicalNeutral.DeMorgan G] {f : G →ˡᶜ F}


-- @@ L272-274 verbatim
def cast (d : 𝔇 Δ) (h : Δ = Γ.map f := by simp) : Pullback 𝔇 f Γ := by
  unfold Pullback
  exact h ▸ d


-- @@ L276-276 verbatim
def uncast (d : Pullback 𝔇 f Γ) (h : Δ = Γ.map f := by simp) : 𝔇 Δ := h ▸ d


-- @@ L278-284 verbatim
instance oneSidedLK [OneSidedLK 𝔇] : OneSidedLK (Pullback 𝔇 f) where
  identity φ := cast <| identity (𝔇 := 𝔇) (f φ)
  contraction {Δ Γ} d h := cast (contraction d (Multiset.map_subset_map h) : 𝔇 (Γ.map f)) (by simp)
  verum := cast verum
  and {Γ φ ψ} d₁ d₂ := cast <| and (Γ := Γ.map f) (φ := f φ) (ψ := f ψ)
    (uncast d₁ (by simp)) (uncast d₂ (by simp))
  or {Γ φ ψ} d := cast <| or (Γ := Γ.map f) (φ := f φ) (ψ := f ψ) (uncast d (by simp))


-- @@ L286-290 verbatim
instance cut [Cut 𝔇] : Cut (Pullback 𝔇 f) where
  cut {Γ φ Δ} bp bn :=
    have bp : 𝔇 (Γ.map f + ⦃f φ⦄) := uncast bp
    have bn : 𝔇 (Δ.map f + ⦃∼f φ⦄) := uncast bn
    cast (Cut.cut (φ := f φ) bp bn)


-- @@ L292-294 verbatim
instance {P : Type*} [Entailment P F] (𝓟 : P) [PrincipalEntailment 𝔇 𝓟] :
    PrincipalEntailment (Pullback 𝔇 f) (Entailment.pullback 𝓟 f) where
  equiv {φ} := PrincipalEntailment.equiv (φ := f φ)


-- @@ L296-298 verbatim
omit [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F]
  [TildeInvolutive G] [LogicalConnective.DeMorgan G] [LogicalNeutral.DeMorgan G] in
@[simp] lemma nonempty_iff {Γ} : Nonempty (Pullback 𝔇 f Γ) ↔ Nonempty (𝔇 (Γ.map f)) := by simp [Pullback]


-- @@ L300-302 verbatim
omit [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F]
  [TildeInvolutive G] [LogicalConnective.DeMorgan G] [LogicalNeutral.DeMorgan G] in
@[simp] lemma isEmpty_iff {Γ} : IsEmpty (Pullback 𝔇 f Γ) ↔ IsEmpty (𝔇 (Γ.map f)) := by simp [Pullback]


-- @@ L304-304 verbatim
end Pullback


-- @@ L306-306 verbatim
end OneSidedLK


-- @@ L308-308 verbatim
end FFL


-- @@ L310-310 verbatim
end
