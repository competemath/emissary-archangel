/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.Entailment
public import LeanPool.Incompleteness.Foundation.Logic.Axioms
public import Mathlib.Algebra.Order.Ring.Nat


-- @@ L12-12 verbatim
/-! # Basic -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace Entailment


-- @@ L20-20 verbatim
variable {S F : Type*} [LogicalConnective F] [Entailment F S]

-- @@ L21-21 verbatim
variable {𝓢 : S} {φ ψ χ : F}



-- @@ L24-25 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def cast (e : φ = ψ) (b : Entailment.Prf 𝓢 φ) : Entailment.Prf 𝓢 ψ :=
  e ▸ b


-- @@ L26-28 expanded
omit [LogicalConnective F] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma cast! (e : φ = ψ) (b : Provable 𝓢 φ) : Provable 𝓢 ψ :=
  ⟨cast e b.some⟩


-- @@ L31-34 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class ModusPonens (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  mdp {φ ψ : F} : Entailment.Prf 𝓢 (Arrow.arrow φ ψ) → Entailment.Prf 𝓢 φ → Entailment.Prf 𝓢 ψ


-- @@ L36-36 verbatim
alias mdp := ModusPonens.mdp

-- @@ L37-38 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀" => mdp


-- @@ L40-42 expanded
lemma mdp! [ModusPonens 𝓢] : Provable 𝓢 (Arrow.arrow φ ψ) → Provable 𝓢 φ → Provable 𝓢 ψ := by
  rintro ⟨hpq⟩ ⟨hp⟩; exact ⟨mdp hpq hp⟩


-- @@ L43-44 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀" => mdp!


-- @@ L46-49 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomVerum (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  verum : Entailment.Prf 𝓢 Axioms.Verum


-- @@ L51-52 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def verum [HasAxiomVerum 𝓢] : Entailment.Prf 𝓢 ⊤ :=
  HasAxiomVerum.verum


-- @@ L53-53 expanded
@[simp]
lemma verum! [HasAxiomVerum 𝓢] : Provable 𝓢 ⊤ :=
  ⟨verum⟩


-- @@ L56-59 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomImply₁ (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  imply₁ (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.Imply₁ φ ψ)


-- @@ L61-62 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def imply₁ [HasAxiomImply₁ 𝓢] : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ φ)) :=
  HasAxiomImply₁.imply₁ _ _


-- @@ L63-63 expanded
@[simp]
lemma imply₁! [HasAxiomImply₁ 𝓢] : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ φ)) :=
  ⟨imply₁⟩


-- @@ L65-66 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def imply₁' [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (h : Entailment.Prf 𝓢 φ) :
    Entailment.Prf 𝓢 (Arrow.arrow ψ φ) :=
  mdp imply₁ h


-- @@ L67-67 expanded
lemma imply₁'! [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (d : Provable 𝓢 φ) :
    Provable 𝓢 (Arrow.arrow ψ φ) :=
  ⟨imply₁' d.some⟩


-- @@ L69-71 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[deprecated imply₁' (since := "2026-05-27")]
def dhyp [ModusPonens 𝓢] [HasAxiomImply₁ 𝓢] (ψ : F) (b : Entailment.Prf 𝓢 φ) :
    Entailment.Prf 𝓢 (Arrow.arrow ψ φ) :=
  imply₁' b


-- @@ L74-77 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomImply₂ (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  imply₂ (φ ψ χ : F) : Entailment.Prf 𝓢 (Axioms.Imply₂ φ ψ χ)


-- @@ L79-81 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def imply₂ [HasAxiomImply₂ 𝓢] :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ))
        (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ))) :=
  HasAxiomImply₂.imply₂ _ _ _


-- @@ L82-83 expanded
@[simp]
lemma imply₂! [HasAxiomImply₂ 𝓢] :
    Provable 𝓢
      (Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ))
        (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ))) :=
  ⟨imply₂⟩


-- @@ L85-88 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def imply₂' [ModusPonens 𝓢] [HasAxiomImply₂ 𝓢]
    (d₁ : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ)))
    (d₂ : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) (d₃ : Entailment.Prf 𝓢 φ) : Entailment.Prf 𝓢 χ :=
  mdp (mdp (mdp imply₂ d₁) d₂) d₃


-- @@ L89-92 expanded
lemma imply₂'! [ModusPonens 𝓢] [HasAxiomImply₂ 𝓢]
    (d₁ : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ))) (d₂ : Provable 𝓢 (Arrow.arrow φ ψ))
    (d₃ : Provable 𝓢 φ) : Provable 𝓢 χ :=
  ⟨imply₂' d₁.some d₂.some d₃.some⟩


-- @@ L95-100 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomAndElim (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  and₁ (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.AndElim₁ φ ψ)
  /-- Imported declaration from the Incompleteness formalization. -/
  and₂ (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.AndElim₂ φ ψ)


-- @@ L102-103 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def and₁ [HasAxiomAndElim 𝓢] : Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) φ) :=
  HasAxiomAndElim.and₁ _ _


-- @@ L104-104 expanded
@[simp]
lemma and₁! [HasAxiomAndElim 𝓢] : Provable 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) φ) :=
  ⟨and₁⟩


-- @@ L106-107 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def and₁' [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : Entailment.Prf 𝓢 (Wedge.wedge φ ψ)) :
    Entailment.Prf 𝓢 φ :=
  mdp and₁ d


-- @@ L108-108 verbatim
alias andLeft := and₁'


-- @@ L110-110 expanded
lemma and₁'! [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : Provable 𝓢 (Wedge.wedge φ ψ)) :
    Provable 𝓢 φ :=
  ⟨and₁' d.some⟩


-- @@ L111-111 verbatim
alias and_left! := and₁'!


-- @@ L113-114 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def and₂ [HasAxiomAndElim 𝓢] : Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) ψ) :=
  HasAxiomAndElim.and₂ _ _


-- @@ L115-115 expanded
@[simp]
lemma and₂! [HasAxiomAndElim 𝓢] : Provable 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) ψ) :=
  ⟨and₂⟩


-- @@ L117-118 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def and₂' [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : Entailment.Prf 𝓢 (Wedge.wedge φ ψ)) :
    Entailment.Prf 𝓢 ψ :=
  mdp and₂ d


-- @@ L119-119 verbatim
alias andRight := and₂'


-- @@ L121-121 expanded
lemma and₂'! [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : Provable 𝓢 (Wedge.wedge φ ψ)) :
    Provable 𝓢 ψ :=
  ⟨and₂' d.some⟩


-- @@ L122-122 verbatim
alias and_right! := and₂'!



-- @@ L125-128 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomAndInst (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  and₃ (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.AndInst φ ψ)


-- @@ L130-131 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def and₃ [HasAxiomAndInst 𝓢] : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Wedge.wedge φ ψ))) :=
  HasAxiomAndInst.and₃ _ _


-- @@ L132-132 expanded
@[simp]
lemma and₃! [HasAxiomAndInst 𝓢] : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Wedge.wedge φ ψ))) :=
  ⟨and₃⟩


-- @@ L134-136 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def and₃' [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : Entailment.Prf 𝓢 φ) (d₂ : Entailment.Prf 𝓢 ψ) :
    Entailment.Prf 𝓢 (Wedge.wedge φ ψ) :=
  mdp (mdp and₃ d₁) d₂


-- @@ L137-137 verbatim
alias andIntro := and₃'


-- @@ L139-140 expanded
lemma and₃'! [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : Provable 𝓢 φ) (d₂ : Provable 𝓢 ψ) :
    Provable 𝓢 (Wedge.wedge φ ψ) :=
  ⟨and₃' d₁.some d₂.some⟩


-- @@ L141-141 verbatim
alias and_intro! := and₃'!



-- @@ L144-149 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomOrInst (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  or₁ (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.OrInst₁ φ ψ)
  /-- Imported declaration from the Incompleteness formalization. -/
  or₂ (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.OrInst₂ φ ψ)


-- @@ L151-152 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def or₁ [HasAxiomOrInst 𝓢] : Entailment.Prf 𝓢 (Arrow.arrow φ (Vee.vee φ ψ)) :=
  HasAxiomOrInst.or₁ _ _


-- @@ L153-153 expanded
@[simp]
lemma or₁! [HasAxiomOrInst 𝓢] : Provable 𝓢 (Arrow.arrow φ (Vee.vee φ ψ)) :=
  ⟨or₁⟩


-- @@ L155-156 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def or₁' [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : Entailment.Prf 𝓢 φ) :
    Entailment.Prf 𝓢 (Vee.vee φ ψ) :=
  mdp or₁ d


-- @@ L157-157 expanded
lemma or₁'! [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : Provable 𝓢 φ) : Provable 𝓢 (Vee.vee φ ψ) :=
  ⟨or₁' d.some⟩


-- @@ L159-160 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def or₂ [HasAxiomOrInst 𝓢] : Entailment.Prf 𝓢 (Arrow.arrow ψ (Vee.vee φ ψ)) :=
  HasAxiomOrInst.or₂ _ _


-- @@ L161-161 expanded
@[simp]
lemma or₂! [HasAxiomOrInst 𝓢] : Provable 𝓢 (Arrow.arrow ψ (Vee.vee φ ψ)) :=
  ⟨or₂⟩


-- @@ L163-164 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def or₂' [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : Entailment.Prf 𝓢 ψ) :
    Entailment.Prf 𝓢 (Vee.vee φ ψ) :=
  mdp or₂ d


-- @@ L165-165 expanded
lemma or₂'! [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : Provable 𝓢 ψ) : Provable 𝓢 (Vee.vee φ ψ) :=
  ⟨or₂' d.some⟩


-- @@ L168-171 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomOrElim (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  or₃ (φ ψ χ : F) : Entailment.Prf 𝓢 (Axioms.OrElim φ ψ χ)


-- @@ L173-175 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def or₃ [HasAxiomOrElim 𝓢] :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow (Vee.vee φ ψ) χ))) :=
  HasAxiomOrElim.or₃ _ _ _


-- @@ L176-176 expanded
@[simp]
lemma or₃! [HasAxiomOrElim 𝓢] :
    Provable 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow (Vee.vee φ ψ) χ))) :=
  ⟨or₃⟩


-- @@ L178-181 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def or₃'' [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : Entailment.Prf 𝓢 (Arrow.arrow φ χ))
    (d₂ : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) : Entailment.Prf 𝓢 (Arrow.arrow (Vee.vee φ ψ) χ) :=
  mdp (mdp or₃ d₁) d₂


-- @@ L182-184 expanded
lemma or₃''! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : Provable 𝓢 (Arrow.arrow φ χ))
    (d₂ : Provable 𝓢 (Arrow.arrow ψ χ)) : Provable 𝓢 (Arrow.arrow (Vee.vee φ ψ) χ) :=
  ⟨or₃'' d₁.some d₂.some⟩


-- @@ L186-189 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def or₃''' [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : Entailment.Prf 𝓢 (Arrow.arrow φ χ))
    (d₂ : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) (d₃ : Entailment.Prf 𝓢 (Vee.vee φ ψ)) :
    Entailment.Prf 𝓢 χ :=
  mdp (mdp (mdp or₃ d₁) d₂) d₃


-- @@ L190-190 verbatim
alias orCases := or₃'''


-- @@ L192-194 expanded
lemma or₃'''! [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : Provable 𝓢 (Arrow.arrow φ χ))
    (d₂ : Provable 𝓢 (Arrow.arrow ψ χ)) (d₃ : Provable 𝓢 (Vee.vee φ ψ)) : Provable 𝓢 χ :=
  ⟨or₃''' d₁.some d₂.some d₃.some⟩


-- @@ L195-195 verbatim
alias or_cases! := or₃'''!



-- @@ L198-201 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomEFQ (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  efq (φ : F) : Entailment.Prf 𝓢 (Axioms.EFQ φ)


-- @@ L203-204 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def efq [HasAxiomEFQ 𝓢] : Entailment.Prf 𝓢 (Arrow.arrow ⊥ φ) :=
  HasAxiomEFQ.efq _


-- @@ L205-205 expanded
@[simp]
lemma efq! [HasAxiomEFQ 𝓢] : Provable 𝓢 (Arrow.arrow ⊥ φ) :=
  ⟨efq⟩


-- @@ L207-208 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def efq' [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (b : Entailment.Prf 𝓢 ⊥) : Entailment.Prf 𝓢 φ :=
  mdp efq b


-- @@ L209-209 expanded
lemma efq'! [ModusPonens 𝓢] [HasAxiomEFQ 𝓢] (h : Provable 𝓢 ⊥) : Provable 𝓢 φ :=
  ⟨efq' h.some⟩


-- @@ L212-215 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomLEM (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  lem (φ : F) : Entailment.Prf 𝓢 (Axioms.LEM φ)


-- @@ L217-218 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def lem [HasAxiomLEM 𝓢] : Entailment.Prf 𝓢 (Vee.vee φ (Tilde.tilde φ)) :=
  HasAxiomLEM.lem φ


-- @@ L219-219 expanded
@[simp]
lemma lem! [HasAxiomLEM 𝓢] : Provable 𝓢 (Vee.vee φ (Tilde.tilde φ)) :=
  ⟨lem⟩


-- @@ L222-225 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDNE (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  dne (φ : F) : Entailment.Prf 𝓢 (Axioms.DNE φ)


-- @@ L227-228 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dne [HasAxiomDNE 𝓢] : Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) φ) :=
  HasAxiomDNE.dne _


-- @@ L229-229 expanded
@[simp]
lemma dne! [HasAxiomDNE 𝓢] : Provable 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) φ) :=
  ⟨dne⟩


-- @@ L231-232 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dne' [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : Entailment.Prf 𝓢 (Tilde.tilde (Tilde.tilde φ))) :
    Entailment.Prf 𝓢 φ :=
  mdp dne b


-- @@ L233-233 expanded
lemma dne'! [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : Provable 𝓢 (Tilde.tilde (Tilde.tilde φ))) :
    Provable 𝓢 φ :=
  ⟨dne' h.some⟩


-- @@ L236-239 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomWeakLEM (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  wlem (φ : F) : Entailment.Prf 𝓢 (Axioms.WeakLEM φ)


-- @@ L241-242 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def wlem [HasAxiomWeakLEM 𝓢] :
    Entailment.Prf 𝓢 (Vee.vee (Tilde.tilde φ) (Tilde.tilde (Tilde.tilde φ))) :=
  HasAxiomWeakLEM.wlem φ


-- @@ L243-243 expanded
@[simp]
lemma wlem! [HasAxiomWeakLEM 𝓢] :
    Provable 𝓢 (Vee.vee (Tilde.tilde φ) (Tilde.tilde (Tilde.tilde φ))) :=
  ⟨wlem⟩


-- @@ L246-249 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDummett (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  dummett (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.Dummett φ ψ)


-- @@ L251-252 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dummett [HasAxiomDummett 𝓢] : Entailment.Prf 𝓢 (Vee.vee (Arrow.arrow φ ψ) (Arrow.arrow ψ φ)) :=
  HasAxiomDummett.dummett φ ψ


-- @@ L253-253 expanded
@[simp]
lemma dummett! [HasAxiomDummett 𝓢] : Provable 𝓢 (Axioms.Dummett φ ψ) :=
  ⟨dummett⟩


-- @@ L256-259 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomPeirce (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  peirce (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.Peirce φ ψ)


-- @@ L261-262 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def peirce [HasAxiomPeirce 𝓢] :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow (Arrow.arrow φ ψ) φ) φ) :=
  HasAxiomPeirce.peirce _ _


-- @@ L263-263 expanded
@[simp]
lemma peirce! [HasAxiomPeirce 𝓢] : Provable 𝓢 (Arrow.arrow (Arrow.arrow (Arrow.arrow φ ψ) φ) φ) :=
  ⟨peirce⟩


-- @@ L266-272 expanded
/-- Negation `∼φ` is equivalent to `φ ==> ⊥` on **system**.

This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ ==> ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  negEquiv (φ : F) : Entailment.Prf 𝓢 (Axioms.NegEquiv φ)


-- @@ L274-275 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def negEquiv [NegationEquiv 𝓢] :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Tilde.tilde φ) (Arrow.arrow φ ⊥)) :=
  NegationEquiv.negEquiv _


-- @@ L276-276 expanded
@[simp]
lemma negEquiv! [NegationEquiv 𝓢] :
    Provable 𝓢 (LogicalConnective.iff (Tilde.tilde φ) (Arrow.arrow φ ⊥)) :=
  ⟨negEquiv⟩


-- @@ L278-281 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomElimContra (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  elimContra (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.ElimContra φ ψ)


-- @@ L283-285 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def elimContra [HasAxiomElimContra 𝓢] :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ)) (Arrow.arrow φ ψ)) :=
  HasAxiomElimContra.elimContra _ _


-- @@ L286-286 expanded
@[simp]
lemma elimContra! [HasAxiomElimContra 𝓢] :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ)) (Arrow.arrow φ ψ)) :=
  ⟨elimContra⟩


-- @@ L288-295 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Minimal (𝓢 : S) extends
              ModusPonens 𝓢,
              NegationEquiv 𝓢,
              HasAxiomVerum 𝓢,
              HasAxiomImply₁ 𝓢, HasAxiomImply₂ 𝓢,
              HasAxiomAndElim 𝓢, HasAxiomAndInst 𝓢,
              HasAxiomOrInst 𝓢, HasAxiomOrElim 𝓢


-- @@ L297-298 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Intuitionistic (𝓢 : S) extends Entailment.Minimal 𝓢, HasAxiomEFQ 𝓢


-- @@ L300-301 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Classical (𝓢 : S) extends Entailment.Minimal 𝓢, HasAxiomDNE 𝓢



-- @@ L304-304 verbatim
section «lp_section_1»


-- @@ L306-306 verbatim
variable [ModusPonens 𝓢]


-- @@ L308-311 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.negEquiv'.mp [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    Entailment.Prf 𝓢 (Tilde.tilde φ) → Entailment.Prf 𝓢 (Arrow.arrow φ ⊥) := fun h =>
  mdp (and₁' negEquiv) h


-- @@ L312-315 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.negEquiv'.mpr [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    Entailment.Prf 𝓢 (Arrow.arrow φ ⊥) → Entailment.Prf 𝓢 (Tilde.tilde φ) := fun h =>
  mdp (and₂' negEquiv) h


-- @@ L316-317 expanded
lemma negEquiv'! [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    Provable 𝓢 (Tilde.tilde φ) ↔ Provable 𝓢 (Arrow.arrow φ ⊥) :=
  ⟨fun ⟨h⟩ => ⟨negEquiv'.mp h⟩, fun ⟨h⟩ => ⟨negEquiv'.mpr h⟩⟩


-- @@ L319-321 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffIntro [HasAxiomAndInst 𝓢] (b₁ : Entailment.Prf 𝓢 (Arrow.arrow φ ψ))
    (b₂ : Entailment.Prf 𝓢 (Arrow.arrow ψ φ)) : Entailment.Prf 𝓢 (LogicalConnective.iff φ ψ) :=
  andIntro b₁ b₂


-- @@ L322-324 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma iff_intro! [HasAxiomAndInst 𝓢] (h₁ : Provable 𝓢 (Arrow.arrow φ ψ))
    (h₂ : Provable 𝓢 (Arrow.arrow ψ φ)) : Provable 𝓢 (LogicalConnective.iff φ ψ) :=
  ⟨andIntro h₁.some h₂.some⟩


-- @@ L326-327 expanded
lemma and_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] :
    Provable 𝓢 (Wedge.wedge φ ψ) ↔ Provable 𝓢 φ ∧ Provable 𝓢 ψ :=
  ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩


-- @@ L329-331 expanded
lemma iff_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] :
    Provable 𝓢 (LogicalConnective.iff φ ψ) ↔
      Provable 𝓢 (Arrow.arrow φ ψ) ∧ Provable 𝓢 (Arrow.arrow ψ φ) :=
  ⟨fun h ↦ ⟨and_left! h, and_right! h⟩, fun h ↦ and_intro! h.1 h.2⟩


-- @@ L333-335 expanded
lemma provable_iff_of_iff [HasAxiomAndElim 𝓢] (h : Provable 𝓢 (LogicalConnective.iff φ ψ)) :
    Provable 𝓢 φ ↔ Provable 𝓢 ψ :=
  ⟨fun hp ↦ mdp (and_left! h) hp, fun hq ↦ mdp (and_right! h) hq⟩


-- @@ L337-339 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impId [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) : Entailment.Prf 𝓢 (Arrow.arrow φ φ) :=
  mdp (mdp (imply₂ (φ := φ) (ψ := (Arrow.arrow φ φ)) (χ := φ)) imply₁) imply₁


-- @@ L340-341 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[simp]
lemma imp_id! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] : Provable 𝓢 (Arrow.arrow φ φ) :=
  ⟨impId φ⟩


-- @@ L343-345 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffId [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ : F) :
    Entailment.Prf 𝓢 (LogicalConnective.iff φ φ) :=
  and₃' (impId φ) (impId φ)


-- @@ L346-348 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[simp]
lemma iff_id! [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] :
    Provable 𝓢 (LogicalConnective.iff φ φ) :=
  ⟨iffId φ⟩


-- @@ L350-354 verbatim
instance [NegAbbrev F] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [HasAxiomAndInst 𝓢] :
    Entailment.NegationEquiv 𝓢 where
  negEquiv := by
    intro φ
    simpa only [Axioms.NegEquiv, NegAbbrev.neg] using iffId _



-- @@ L357-359 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def notbot [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] :
    Entailment.Prf 𝓢 (Tilde.tilde ⊥) :=
  negEquiv'.mpr (impId ⊥)


-- @@ L360-362 expanded
@[simp]
lemma notbot! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] [NegationEquiv 𝓢] [HasAxiomAndElim 𝓢] :
    Provable 𝓢 (Tilde.tilde ⊥) :=
  ⟨notbot⟩


-- @@ L364-366 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdp₁ [HasAxiomImply₂ 𝓢] (bqr : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ)))
    (bq : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) : Entailment.Prf 𝓢 (Arrow.arrow φ χ) :=
  mdp (mdp imply₂ bqr) bq


-- @@ L367-368 expanded
lemma mdp₁! [HasAxiomImply₂ 𝓢] (hqr : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ)))
    (hq : Provable 𝓢 (Arrow.arrow φ ψ)) : Provable 𝓢 (Arrow.arrow φ χ) :=
  ⟨mdp₁ hqr.some hq.some⟩


-- @@ L370-371 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₁" => mdp₁

-- @@ L372-373 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₁" => mdp₁!


-- @@ L375-378 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdp₂ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (bqr : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ s))))
    (bq : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ))) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ s)) :=
  mdp₁ (mdp₁ (imply₁' (imply₂)) bqr) bq


-- @@ L379-381 expanded
lemma mdp₂! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (hqr : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ s))))
    (hq : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ))) :
    Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ s)) :=
  ⟨mdp₂ hqr.some hq.some⟩


-- @@ L383-384 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₂" => mdp₂

-- @@ L385-386 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₂" => mdp₂!


-- @@ L388-391 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdp₃ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (bqr : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ (Arrow.arrow s t)))))
    (bq : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ s)))) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ t))) :=
  mdp₂ (mdp₂ (imply₁' <| imply₁' <| imply₂) bqr) bq


-- @@ L392-394 expanded
lemma mdp₃! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (hqr : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ (Arrow.arrow s t)))))
    (hq : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ s)))) :
    Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ t))) :=
  ⟨mdp₃ hqr.some hq.some⟩


-- @@ L396-397 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₃" => mdp₃

-- @@ L398-399 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₃" => mdp₃!


-- @@ L401-404 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdp₄ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (bqr :
      Entailment.Prf 𝓢
        (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ (Arrow.arrow s (Arrow.arrow t u))))))
    (bq : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ (Arrow.arrow s t))))) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ (Arrow.arrow s u)))) :=
  mdp₃ (mdp₃ (imply₁' <| imply₁' <| imply₁' <| imply₂) bqr) bq


-- @@ L405-408 expanded
lemma mdp₄! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (hqr :
      Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ (Arrow.arrow s (Arrow.arrow t u))))))
    (hq : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ (Arrow.arrow s t))))) :
    Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ (Arrow.arrow s u)))) :=
  ⟨mdp₄ hqr.some hq.some⟩


-- @@ L409-410 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₄" => mdp₄

-- @@ L411-412 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:90 "⨀₄" => mdp₄!


-- @@ L414-417 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impTrans'' [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (bpq : Entailment.Prf 𝓢 (Arrow.arrow φ ψ))
    (bqr : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) : Entailment.Prf 𝓢 (Arrow.arrow φ χ) :=
  mdp (mdp imply₂ (imply₁' bqr)) bpq


-- @@ L418-420 expanded
lemma imp_trans''! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (hpq : Provable 𝓢 (Arrow.arrow φ ψ))
    (hqr : Provable 𝓢 (Arrow.arrow ψ χ)) : Provable 𝓢 (Arrow.arrow φ χ) :=
  ⟨impTrans'' hpq.some hqr.some⟩


-- @@ L422-425 expanded
lemma unprovable_imp_trans''! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (hpq : Provable 𝓢 (Arrow.arrow φ ψ)) :
    Unprovable 𝓢 (Arrow.arrow φ χ) → Unprovable 𝓢 (Arrow.arrow ψ χ) :=
  by
  intro hp hq
  exact hp (imp_trans''! hpq hq)


-- @@ L427-431 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffTrans'' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (h₁ : Entailment.Prf 𝓢 (LogicalConnective.iff φ ψ))
    (h₂ : Entailment.Prf 𝓢 (LogicalConnective.iff ψ χ)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff φ χ) :=
  iffIntro (impTrans'' (and₁' h₁) (and₁' h₂)) (impTrans'' (and₂' h₂) (and₂' h₁))


-- @@ L432-435 expanded
lemma iff_trans''! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (h₁ : Provable 𝓢 (LogicalConnective.iff φ ψ)) (h₂ : Provable 𝓢 (LogicalConnective.iff ψ χ)) :
    Provable 𝓢 (LogicalConnective.iff φ χ) :=
  ⟨iffTrans'' h₁.some h₂.some⟩


-- @@ L437-442 expanded
lemma unprovable_iff! [HasAxiomAndElim 𝓢] (H : Provable 𝓢 (LogicalConnective.iff φ ψ)) :
    Unprovable 𝓢 φ ↔ Unprovable 𝓢 ψ := by
  constructor; · intro hp hq; have := mdp (and₂'! H) hq; contradiction;
  · intro hq hp; have := mdp (and₁'! H) hp; contradiction;


-- @@ L444-446 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def imply₁₁ [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ φ))) :=
  impTrans'' imply₁ imply₁


-- @@ L447-449 expanded
@[simp]
lemma imply₁₁! [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (φ ψ χ : F) :
    Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ φ))) :=
  ⟨imply₁₁ φ ψ χ⟩


-- @@ L451-454 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyAnd [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (bq : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) (br : Entailment.Prf 𝓢 (Arrow.arrow φ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Wedge.wedge ψ χ)) :=
  mdp₁ (mdp₁ (imply₁' and₃) bq) br


-- @@ L455-458 expanded
lemma imply_and! [HasAxiomAndInst 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (hq : Provable 𝓢 (Arrow.arrow φ ψ)) (hr : Provable 𝓢 (Arrow.arrow φ χ)) :
    Provable 𝓢 (Arrow.arrow φ (Wedge.wedge ψ χ)) :=
  ⟨implyAnd hq.some hr.some⟩


-- @@ L461-464 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andComm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (φ ψ : F) : Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) (Wedge.wedge ψ φ)) :=
  implyAnd and₂ and₁


-- @@ L465-467 expanded
lemma and_comm! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) (Wedge.wedge ψ φ)) :=
  ⟨andComm φ ψ⟩


-- @@ L469-472 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andComm' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (h : Entailment.Prf 𝓢 (Wedge.wedge φ ψ)) : Entailment.Prf 𝓢 (Wedge.wedge ψ φ) :=
  mdp (andComm _ _) h


-- @@ L473-476 expanded
lemma and_comm'! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (h : Provable 𝓢 (Wedge.wedge φ ψ)) : Provable 𝓢 (Wedge.wedge ψ φ) :=
  ⟨andComm' h.some⟩


-- @@ L479-482 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffComm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (φ ψ : F) :
    Entailment.Prf 𝓢 (Arrow.arrow (LogicalConnective.iff φ ψ) (LogicalConnective.iff ψ φ)) :=
  andComm _ _


-- @@ L483-485 expanded
lemma iff_comm! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] :
    Provable 𝓢 (Arrow.arrow (LogicalConnective.iff φ ψ) (LogicalConnective.iff ψ φ)) :=
  ⟨iffComm φ ψ⟩


-- @@ L487-490 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffComm' [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (h : Entailment.Prf 𝓢 (LogicalConnective.iff φ ψ)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff ψ φ) :=
  mdp (iffComm _ _) h


-- @@ L491-494 expanded
lemma iff_comm'! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢]
    (h : Provable 𝓢 (LogicalConnective.iff φ ψ)) : Provable 𝓢 (LogicalConnective.iff ψ φ) :=
  ⟨iffComm' h.some⟩


-- @@ L497-505 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andImplyIffImplyImply [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢]
    [HasAxiomImply₂ 𝓢] (φ ψ χ : F) :
    Entailment.Prf 𝓢
      (LogicalConnective.iff (Arrow.arrow (Wedge.wedge φ ψ) χ) (Arrow.arrow φ (Arrow.arrow ψ χ))) :=
  by
  let b₁ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (Wedge.wedge φ ψ) χ) (Arrow.arrow φ (Arrow.arrow ψ χ))) :=
    mdp₃ (imply₁₁ (Arrow.arrow (Wedge.wedge φ ψ) χ) φ ψ)
      (imply₁' (ψ := Arrow.arrow (Wedge.wedge φ ψ) χ) and₃)
  let b₂ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ)) (Arrow.arrow (Wedge.wedge φ ψ) χ)) :=
    mdp₂ (mdp₂ imply₁ (imply₁' (ψ := Arrow.arrow φ (Arrow.arrow ψ χ)) and₁))
      (imply₁' (ψ := Arrow.arrow φ (Arrow.arrow ψ χ)) and₂);
  exact iffIntro b₁ b₂


-- @@ L506-509 expanded
lemma and_imply_iff_imply_imply! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢]
    [HasAxiomImply₂ 𝓢] :
    Provable 𝓢
      (LogicalConnective.iff (Arrow.arrow (Wedge.wedge φ ψ) χ) (Arrow.arrow φ (Arrow.arrow ψ χ))) :=
  ⟨andImplyIffImplyImply φ ψ χ⟩


-- @@ L511-515 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.andImplyIffImplyImply'.mp [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢]
    [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ)) :=
  mdp (and₁' <| andImplyIffImplyImply φ ψ χ) d


-- @@ L516-520 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.andImplyIffImplyImply'.mpr [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢]
    [HasAxiomImply₁ 𝓢] [HasAxiomImply₂ 𝓢] (d : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ))) :
    Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) χ) :=
  mdp (and₂' <| andImplyIffImplyImply φ ψ χ) d


-- @@ L522-525 expanded
lemma and_imply_iff_imply_imply'! [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImply₁ 𝓢]
    [HasAxiomImply₂ 𝓢] :
    (Provable 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) χ)) ↔
      (Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ))) :=
  ⟨fun ⟨h⟩ => ⟨andImplyIffImplyImply'.mp h⟩, fun ⟨h⟩ => ⟨andImplyIffImplyImply'.mpr h⟩⟩


-- @@ L527-528 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyLeftVerum [HasAxiomVerum 𝓢] [HasAxiomImply₁ 𝓢] : Entailment.Prf 𝓢 (Arrow.arrow φ ⊤) :=
  imply₁' verum


-- @@ L529-530 expanded
@[simp]
lemma implyLeftVerum! [HasAxiomImply₁ 𝓢] [HasAxiomVerum 𝓢] : Provable 𝓢 (Arrow.arrow φ ⊤) :=
  ⟨implyLeftVerum⟩


-- @@ L534-535 expanded
instance [(𝓢 : S) → ModusPonens 𝓢] [(𝓢 : S) → HasAxiomEFQ 𝓢] : DeductiveExplosion S :=
  ⟨fun b _ ↦ mdp efq b⟩


-- @@ L538-538 verbatim
end «lp_section_1»


-- @@ L540-540 verbatim
section «lp_section_2»


-- @@ L542-542 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L544-550 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def conj₂Nth :
    (Γ : List F) →
      (n : ℕ) → (hn : n < Γ.length) → Entailment.Prf 𝓢 (Arrow.arrow (List.conj₂ Γ) Γ[n])
  | [], _, hn => by simp at hn
  | [ψ], 0, _ => impId ψ
  | φ :: ψ :: Γ, 0, _ => and₁
  | φ :: ψ :: Γ, n + 1, hn =>
    impTrans'' (and₂ (φ := φ)) (conj₂Nth (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))


-- @@ L552-553 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma conj₂_nth! (Γ : List F) (n : ℕ) (hn : n < Γ.length) :
    Provable 𝓢 (Arrow.arrow (List.conj₂ Γ) Γ[n]) :=
  ⟨conj₂Nth Γ n hn⟩


-- @@ L555-555 verbatim
variable [DecidableEq F]

-- @@ L556-556 verbatim
variable {Γ Δ : List F}


-- @@ L558-567 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def generalConj {Γ : List F} {φ : F} (h : φ ∈ Γ) : Entailment.Prf 𝓢 (Arrow.arrow Γ.conj φ) :=
  match Γ with
  | [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ then cast (by simp [e]) (and₁ (φ := φ) (ψ := Γ.conj))
    else
      have : φ ∈ Γ := by simpa [e] using h
      impTrans'' and₂ (generalConj this)


-- @@ L568-571 expanded
omit [DecidableEq F] in
lemma generalConj! (h : φ ∈ Γ) : Provable 𝓢 (Arrow.arrow Γ.conj φ) := by
  classical exact ⟨generalConj h⟩


-- @@ L573-577 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def conjIntro (Γ : List F) (b : (φ : F) → φ ∈ Γ → Entailment.Prf 𝓢 φ) : Entailment.Prf 𝓢 Γ.conj :=
  match Γ with
  | [] => verum
  | ψ :: Γ => andIntro (b ψ (by simp)) (conjIntro Γ (fun ψ hq ↦ b ψ (by simp [hq])))


-- @@ L579-583 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyConj (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow φ Γ.conj) :=
  match Γ with
  | [] => imply₁' verum
  | ψ :: Γ => implyAnd (b ψ (by simp)) (implyConj φ Γ (fun ψ hq ↦ b ψ (by simp [hq])))


-- @@ L585-587 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def conjImplyConj (h : Δ ⊆ Γ) : Entailment.Prf 𝓢 (Arrow.arrow Γ.conj Δ.conj) :=
  implyConj _ _ (fun _ hq ↦ generalConj (h hq))


-- @@ L589-593 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def generalConj' {Γ : List F} {φ : F} (h : φ ∈ Γ) :
    Entailment.Prf 𝓢 (Arrow.arrow (List.conj₂ Γ) φ) :=
  have : Γ.idxOf φ < Γ.length := List.idxOf_lt_length_iff.mpr h
  have : Γ[Γ.idxOf φ] = φ := List.getElem_idxOf this
  cast (by rw [this]) <| conj₂Nth Γ (Γ.idxOf φ) (by assumption)


-- @@ L594-597 expanded
omit [DecidableEq F] in
lemma generate_conj'! (h : φ ∈ Γ) : Provable 𝓢 (Arrow.arrow (List.conj₂ Γ) φ) := by
  classical exact ⟨generalConj' h⟩


-- @@ L599-606 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def conjIntro' (Γ : List F) (b : (φ : F) → φ ∈ Γ → Entailment.Prf 𝓢 φ) :
    Entailment.Prf 𝓢 (List.conj₂ Γ) :=
  match Γ with
  | [] => verum
  | [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.conj₂_cons_nonempty];
    exact andIntro (b ψ (by simp)) (conjIntro' _ (by aesop))


-- @@ L607-609 expanded
omit [DecidableEq F] in
lemma conj_intro'! (b : (φ : F) → φ ∈ Γ → Provable 𝓢 φ) : Provable 𝓢 (List.conj₂ Γ) :=
  ⟨conjIntro' Γ (fun φ hp => (b φ hp).some)⟩


-- @@ L611-618 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyConj' (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (List.conj₂ Γ)) :=
  match Γ with
  | [] => imply₁' verum
  | [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.conj₂_cons_nonempty];
    apply implyAnd (b ψ (by simp)) (implyConj' φ _ (fun ψ hq ↦ b ψ (by simp [hq])));


-- @@ L619-621 expanded
omit [DecidableEq F] in
lemma imply_conj'! (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → Provable 𝓢 (Arrow.arrow φ ψ)) :
    Provable 𝓢 (Arrow.arrow φ (List.conj₂ Γ)) :=
  ⟨implyConj' φ Γ (fun ψ hq => (b ψ hq).some)⟩


-- @@ L623-625 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def conjImplyConj' {Γ Δ : List F} (h : Δ ⊆ Γ) :
    Entailment.Prf 𝓢 (Arrow.arrow (List.conj₂ Γ) (List.conj₂ Δ)) :=
  implyConj' _ _ (fun _ hq ↦ generalConj' (h hq))


-- @@ L627-627 verbatim
end «lp_section_2»



-- @@ L630-630 verbatim
section «lp_section_3»


-- @@ L632-632 verbatim
variable {G T : Type*} [Entailment G T] [LogicalConnective G] {𝓣 : T}


-- @@ L634-651 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def _root_.LO.Entailment.Minimal.ofEquiv (𝓢 : S) [Entailment.Minimal 𝓢] (𝓣 : T) (f : Hom G F)
    (e : (φ : G) → Entailment.Prf 𝓢 (f φ) ≃ Entailment.Prf 𝓣 φ) : Entailment.Minimal 𝓣
    where
  mdp
    {φ ψ dpq
      dp} :=
    (e ψ)
      (let d : Entailment.Prf 𝓢 (Arrow.arrow (f φ) (f ψ)) := by
        simpa using (e (Arrow.arrow φ ψ)).symm dpq
      mdp d ((e φ).symm dp))
  negEquiv φ := e _ (by simpa using negEquiv)
  verum := e _ (by simpa using verum)
  imply₁ φ ψ := e _ (by simpa using imply₁)
  imply₂ φ ψ χ := e _ (by simpa using imply₂)
  and₁ φ ψ := e _ (by simpa using and₁)
  and₂ φ ψ := e _ (by simpa using and₂)
  and₃ φ ψ := e _ (by simpa using and₃)
  or₁ φ ψ := e _ (by simpa using or₁)
  or₂ φ ψ := e _ (by simpa using or₂)
  or₃ φ ψ χ := e _ (by simpa using or₃)


-- @@ L653-671 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def _root_.LO.Entailment.Classical.ofEquiv (𝓢 : S) [Entailment.Classical 𝓢] (𝓣 : T) (f : Hom G F)
    (e : (φ : G) → Entailment.Prf 𝓢 (f φ) ≃ Entailment.Prf 𝓣 φ) : Entailment.Classical 𝓣
    where
  mdp
    {φ ψ dpq
      dp} :=
    (e ψ)
      (let d : Entailment.Prf 𝓢 (Arrow.arrow (f φ) (f ψ)) := by
        simpa using (e (Arrow.arrow φ ψ)).symm dpq
      mdp d ((e φ).symm dp))
  negEquiv φ := e _ (by simpa using negEquiv)
  verum := e _ (by simpa using verum)
  imply₁ φ ψ := e _ (by simpa using imply₁)
  imply₂ φ ψ χ := e _ (by simpa using imply₂)
  and₁ φ ψ := e _ (by simpa using and₁)
  and₂ φ ψ := e _ (by simpa using and₂)
  and₃ φ ψ := e _ (by simpa using and₃)
  or₁ φ ψ := e _ (by simpa using or₁)
  or₂ φ ψ := e _ (by simpa using or₂)
  or₃ φ ψ χ := e _ (by simpa using or₃)
  dne φ := e _ (by simpa using dne)


-- @@ L673-673 verbatim
end «lp_section_3»


-- @@ L675-675 verbatim
end Entailment

-- @@ L676-676 verbatim
end LO
