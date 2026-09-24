module

public import Foundation.Propositional.Formula.NNFormula
public import Foundation.Logic.Calculus


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
namespace FFL.Propositional


-- @@ L10-10 verbatim
abbrev Sequent (α : Type*) := Multiset (NNFormula α)


-- @@ L12-18 verbatim
inductive Derivation : Sequent α → Type _
| identity (a : α) : Derivation ⦃NNFormula.atom a, NNFormula.natom a⦄
| cut : Derivation (Γ + ⦃φ⦄) → Derivation (Δ + ⦃∼φ⦄) → Derivation (Γ + Δ)
| wk : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| verum : Derivation ⦃⊤⦄
| or : Derivation (Γ + ⦃φ, ψ⦄) → Derivation (Γ + ⦃φ ⋎ ψ⦄)
| and : Derivation (Γ + ⦃φ⦄) → Derivation (Γ + ⦃ψ⦄) → Derivation (Γ + ⦃φ ⋏ ψ⦄)


-- @@ L20-20 verbatim
prefix:45 "⊢ᴸᴷ⁰ " => Derivation


-- @@ L22-22 verbatim
namespace Derivation


-- @@ L24-24 verbatim
variable {T U : Theory α} {Δ Δ₁ Δ₂ Γ : Sequent α}


-- @@ L26-32 verbatim
def height {Δ : Sequent α} : ⊢ᴸᴷ⁰ Δ → ℕ
  |identity _ => 0
  | cut dp dn => max dp.height dn.height + 1
  |    wk d _ => d.height + 1
  |     verum => 0
  |      or d => d.height + 1
  | and dp dq => max (height dp) (height dq) + 1


-- @@ L34-34 verbatim
protected abbrev cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ := by abel) : ⊢ᴸᴷ⁰ Γ := e ▸ d


-- @@ L36-37 verbatim
@[simp] lemma height_cast (d : ⊢ᴸᴷ⁰ Δ) (e : Δ = Γ) : height (Derivation.cast d e) = height d := by
  rcases e with rfl; simp [Derivation.cast]


-- @@ L39-39 verbatim
def weakening (d : ⊢ᴸᴷ⁰ Δ) (h : Δ ⊆ Γ := by simp) : ⊢ᴸᴷ⁰ Γ := wk d h


-- @@ L41-41 verbatim
def top (h : ⊤ ∈ Δ := by simp) : ⊢ᴸᴷ⁰ Δ := verum.wk (by simp [h])


-- @@ L43-44 verbatim
def identity' (a : α) (hpos : .atom a ∈ Δ := by simp) (hneg : .natom a ∈ Δ := by simp) : ⊢ᴸᴷ⁰ Δ :=
  (identity a).wk (by intro φ hφ; rcases Multiset.mem_add.mp hφ with hφ | hφ <;> simp_all)


-- @@ L46-50 verbatim
def tensor {φ ψ} (dφ : ⊢ᴸᴷ⁰ Γ + ⦃φ⦄) (dψ : ⊢ᴸᴷ⁰ Δ + ⦃ψ⦄) :
    ⊢ᴸᴷ⁰ Γ + Δ + ⦃φ ⋏ ψ⦄ :=
  and
    (dφ.weakening (by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all))
    (dψ.weakening (by intro χ hχ; rcases Multiset.mem_add.mp hχ with hχ | hχ <;> simp_all))


-- @@ L52-63 verbatim
/-- Identity expansion; the standard structural induction on propositional formulas (folklore). -/
def eta : (φ : NNFormula α) → ⊢ᴸᴷ⁰ ⦃φ, ∼φ⦄
  | .atom a | .natom a => identity' a
  | ⊤ | ⊥ => top
  | φ ⋏ ψ =>
    (or (Γ := ⦃φ ⋏ ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
      (tensor (Γ := ⦃∼φ⦄) (Δ := ⦃∼ψ⦄) (φ := φ) (ψ := ψ)
        (eta φ).cast (eta ψ).cast).cast).cast (by simp [add_comm])
  | φ ⋎ ψ =>
    (or (Γ := ⦃∼φ ⋏ ∼ψ⦄) (φ := φ) (ψ := ψ)
      (tensor (Γ := ⦃φ⦄) (Δ := ⦃ψ⦄) (φ := ∼φ) (ψ := ∼ψ)
        (eta φ) (eta ψ)).cast).cast (by simp [add_comm])


-- @@ L65-66 verbatim
def close (φ : NNFormula α) (hp : φ ∈ Δ := by simp) (hn : ∼φ ∈ Δ := by simp) : ⊢ᴸᴷ⁰ Δ :=
  eta φ |>.weakening (by intro ψ hψ; rcases Multiset.mem_add.mp hψ with hψ | hψ <;> simp_all)


-- @@ L68-73 verbatim
instance : OneSidedLK (Derivation (α := α)) where
  verum := verum
  and d₁ d₂ := d₁.and d₂
  or d := d.or
  contraction d ss := d.wk ss
  identity φ := eta φ


-- @@ L75-76 verbatim
instance : OneSidedLK.Cut (Derivation (α := α)) where
  cut dp dn := cut dp dn


-- @@ L78-78 verbatim
end Derivation


-- @@ L80-80 verbatim
/-! ## Classical proof system -/


-- @@ L82-83 verbatim
inductive Proof.Symbol (α : Type*) : Type
  | symbol


-- @@ L85-85 verbatim
notation "𝐋𝐊⁰" => Proof.Symbol.symbol


-- @@ L87-87 verbatim
abbrev Proof (φ : NNFormula α) := ⊢ᴸᴷ⁰ ⦃φ⦄


-- @@ L89-90 verbatim
instance : Entailment (Proof.Symbol α) (NNFormula α) where
  Prf _ := Proof


-- @@ L92-94 verbatim
namespace Proof

lemma def_eq (φ : NNFormula α) : (𝐋𝐊⁰ ⊢! φ) = (⊢ᴸᴷ⁰ ⦃φ⦄) := rfl


-- @@ L96-97 verbatim
instance : OneSidedLK.PrincipalEntailment (Derivation (α := α)) (𝐋𝐊⁰ : Proof.Symbol α) where
  equiv := Equiv.refl _


-- @@ L99-99 verbatim
instance classical : Entailment.Cl (𝐋𝐊⁰ : Proof.Symbol α) := inferInstance


-- @@ L101-101 verbatim
end Proof


-- @@ L103-103 verbatim
abbrev NNFormula.IsTautology (φ : NNFormula α) : Prop := 𝐋𝐊⁰ ⊢ φ


-- @@ L105-105 verbatim
end FFL.Propositional


-- @@ L107-107 verbatim
end
