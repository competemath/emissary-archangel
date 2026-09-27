/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Basic


-- @@ L10-10 verbatim
/-! # Lukasiewicz -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO


-- @@ L17-17 verbatim
section «lp_section_1»


-- @@ L19-24 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class LukasiewiczAbbrev (F : Type*) [LogicalConnective F] where
  top : ⊤ = Tilde.tilde (⊥ : F)
  neg {φ : F} : Tilde.tilde φ = Arrow.arrow φ ⊥
  or {φ ψ : F} : Vee.vee φ ψ = Arrow.arrow (Tilde.tilde φ) ψ
  and {φ ψ : F} : Wedge.wedge φ ψ = Tilde.tilde (Arrow.arrow φ (Tilde.tilde ψ))


-- @@ L26-26 verbatim
instance [LogicalConnective F] [LukasiewiczAbbrev F] : NegAbbrev F := ⟨LukasiewiczAbbrev.neg⟩


-- @@ L28-28 verbatim
end «lp_section_1»



-- @@ L31-31 verbatim
namespace Entailment


-- @@ L33-37 verbatim
attribute [local simp]
  LukasiewiczAbbrev.top
  LukasiewiczAbbrev.neg
  LukasiewiczAbbrev.or
  LukasiewiczAbbrev.and


-- @@ L39-39 verbatim
variable {S F : Type*} [LogicalConnective F] [LukasiewiczAbbrev F] [Entailment F S]


-- @@ L41-41 verbatim
variable (𝓢 : S)


-- @@ L43-48 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Lukasiewicz [LukasiewiczAbbrev F]
  extends ModusPonens 𝓢,
          HasAxiomImply₁ 𝓢,
          HasAxiomImply₂ 𝓢,
          HasAxiomElimContra 𝓢


-- @@ L50-50 verbatim
namespace Lukasiewicz


-- @@ L52-52 verbatim
variable {𝓢 : S} {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ s t : F}


-- @@ L54-54 verbatim
variable [Entailment.Lukasiewicz 𝓢]


-- @@ L56-57 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def verum : Entailment.Prf 𝓢 ⊤ := by simp only [LukasiewiczAbbrev.top, LukasiewiczAbbrev.neg];
  exact impId ⊥;


-- @@ L58-58 verbatim
instance : HasAxiomVerum 𝓢 := ⟨Lukasiewicz.verum⟩


-- @@ L60-68 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dne : Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) φ) := by
  have d₁ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Tilde.tilde φ))
        (Arrow.arrow
          (Arrow.arrow (Tilde.tilde (Tilde.tilde (Tilde.tilde (Tilde.tilde φ))))
            (Tilde.tilde (Tilde.tilde φ)))
          (Arrow.arrow (Tilde.tilde φ) (Tilde.tilde (Tilde.tilde (Tilde.tilde φ)))))) :=
    imply₁' <| elimContra;
  have d₂ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Tilde.tilde φ))
        (Arrow.arrow (Tilde.tilde (Tilde.tilde (Tilde.tilde (Tilde.tilde φ))))
          (Tilde.tilde (Tilde.tilde φ)))) :=
    imply₁;
  have d₃ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Tilde.tilde φ))
        (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) (Tilde.tilde (Tilde.tilde (Tilde.tilde φ))))
          (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) φ))) :=
    imply₁' <| elimContra;
  have d₄ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Tilde.tilde φ))
        (Arrow.arrow (Tilde.tilde φ) (Tilde.tilde (Tilde.tilde (Tilde.tilde φ))))) :=
    mdp₁ d₁ d₂;
  have d₅ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) φ)) :=
    mdp₁ d₃ d₄;
  have d₆ :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde φ))) :=
    impId _;
  exact mdp₁ d₅ d₆;


-- @@ L69-69 verbatim
instance : HasAxiomDNE 𝓢 := ⟨fun φ => Lukasiewicz.dne (φ := φ)⟩


-- @@ L71-75 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dni : Entailment.Prf 𝓢 (Arrow.arrow φ (Tilde.tilde (Tilde.tilde φ))) := by
  have d₁ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (Tilde.tilde (Tilde.tilde (Tilde.tilde φ))) (Tilde.tilde φ))
        (Arrow.arrow φ (Tilde.tilde (Tilde.tilde φ)))) :=
    elimContra;
  have d₂ :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde (Tilde.tilde φ))) (Tilde.tilde φ)) :=
    dne (φ := Tilde.tilde φ);
  exact mdp d₁ d₂;


-- @@ L77-81 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def explode (h₁ : Entailment.Prf 𝓢 φ) (h₂ : Entailment.Prf 𝓢 (Tilde.tilde φ)) :
    Entailment.Prf 𝓢 ψ := by have d₁ := imply₁ (𝓢 := 𝓢) (φ := Tilde.tilde φ) (ψ := Tilde.tilde ψ);
  have := mdp d₁ h₂; exact mdp (mdp elimContra this) h₁;


-- @@ L83-88 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def explodeHyp (h₁ : Entailment.Prf 𝓢 (Arrow.arrow φ ψ))
    (h₂ : Entailment.Prf 𝓢 (Arrow.arrow φ (Tilde.tilde ψ))) : Entailment.Prf 𝓢 (Arrow.arrow φ χ) :=
  by
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow φ (Arrow.arrow (Tilde.tilde ψ) (Arrow.arrow (Tilde.tilde χ) (Tilde.tilde ψ)))) :=
    imply₁' imply₁ (ψ := φ)
  have : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow (Tilde.tilde χ) (Tilde.tilde ψ))) :=
    mdp₁ this h₂;
  have : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ)) :=
    mdp₁ (imply₁' elimContra (ψ := φ)) this;
  exact mdp₁ this h₁;


-- @@ L90-95 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def explodeHyp₂ (h₁ : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ)))
    (h₂ : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Tilde.tilde χ)))) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ s)) :=
  by
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow φ
        (Arrow.arrow ψ
          (Arrow.arrow (Tilde.tilde χ) (Arrow.arrow (Tilde.tilde s) (Tilde.tilde χ))))) :=
    imply₁' (imply₁' imply₁ (ψ := ψ)) (ψ := φ)
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow (Tilde.tilde (s)) (Tilde.tilde χ)))) :=
    mdp₂ this h₂;
  have : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Arrow.arrow χ s))) :=
    mdp₂ (imply₁' (imply₁' elimContra (ψ := ψ)) (ψ := φ)) this;
  exact mdp₂ this h₁;


-- @@ L97-102 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def efq : Entailment.Prf 𝓢 (Arrow.arrow ⊥ φ) := by
  have := explodeHyp (𝓢 := 𝓢) (φ := ⊥) (ψ := ⊤) (χ := φ);
  exact
    this (by simp only [LukasiewiczAbbrev.top, LukasiewiczAbbrev.neg]; exact imply₁)
      (by simp only [LukasiewiczAbbrev.top, LukasiewiczAbbrev.neg]; exact imply₁);


-- @@ L103-103 verbatim
instance : HasAxiomEFQ 𝓢 := ⟨fun φ => Lukasiewicz.efq (φ := φ)⟩


-- @@ L105-109 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impSwap (h : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ))) :
    Entailment.Prf 𝓢 (Arrow.arrow ψ (Arrow.arrow φ χ)) :=
  by
  refine mdp₂ (χ := ψ) ?_ ?_; · exact imply₁' h;
  · exact imply₁;


-- @@ L111-112 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdpIn₁ : Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ ψ)) :=
  impId _


-- @@ L114-115 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdpIn₂ : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow (Arrow.arrow φ ψ) ψ)) :=
  impSwap mdpIn₁


-- @@ L117-118 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdp₂In₁ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ))
        (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ))) :=
  imply₂


-- @@ L120-121 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdp₂In₂ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ ψ)
        (Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ)) (Arrow.arrow φ χ))) :=
  impSwap mdp₂In₁


-- @@ L123-125 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impTrans'₁ (bpq : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow φ χ)) :=
  impSwap (impTrans'' bpq mdpIn₂)


-- @@ L127-128 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impTrans'₂ (bqr : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ)) :=
  mdp imply₂ (imply₁' bqr)


-- @@ L130-132 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impTrans₂ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ))) :=
  impTrans'' (impSwap (imply₁' (impId (Arrow.arrow ψ χ)))) mdp₂In₁


-- @@ L134-135 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impTrans₁ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow φ χ))) :=
  impSwap impTrans₂


-- @@ L137-138 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dhypBoth (h : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ)) :=
  mdp imply₂ (imply₁' <| h)


-- @@ L140-143 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def explode₂₁ : Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde φ) (Arrow.arrow φ ψ)) := by
  simp only [LukasiewiczAbbrev.neg]; exact dhypBoth efq;


-- @@ L145-146 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def explode₁₂ : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow (Tilde.tilde φ) ψ)) :=
  impSwap explode₂₁


-- @@ L148-149 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contraIntro :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ))) :=
  by simpa using impTrans₁;


-- @@ L151-152 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contraIntro' :
    Entailment.Prf 𝓢 (Arrow.arrow φ ψ) →
      Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ)) :=
  fun h => mdp contraIntro h


-- @@ L154-159 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andElim₁ : Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) φ) :=
  by
  simp only [LukasiewiczAbbrev.and];
  have : Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde φ) (Arrow.arrow φ (Tilde.tilde ψ))) :=
    explodeHyp₂ explode₂₁ imply₁;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Arrow.arrow φ (Tilde.tilde ψ))) (Tilde.tilde (Tilde.tilde φ))) :=
    contraIntro' explode₂₁
  exact impTrans'' this dne;


-- @@ L161-166 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andElim₂ : Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) ψ) := by
  simp only [LukasiewiczAbbrev.and];
  have : Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde ψ) (Arrow.arrow φ (Tilde.tilde ψ))) :=
    imply₁ (φ := Tilde.tilde ψ) (ψ := φ);
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Arrow.arrow φ (Tilde.tilde ψ))) (Tilde.tilde (Tilde.tilde ψ))) :=
    contraIntro' this;
  exact impTrans'' this dne;


-- @@ L167-169 verbatim
instance : HasAxiomAndElim 𝓢 :=
  ⟨fun φ ψ => Lukasiewicz.andElim₁ (φ := φ) (ψ := ψ),
    fun φ ψ => Lukasiewicz.andElim₂ (φ := φ) (ψ := ψ)⟩


-- @@ L171-173 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andImplyLeft :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow φ₁ ψ) (Arrow.arrow (Wedge.wedge φ₁ φ₂) ψ)) :=
  mdp₂ (impSwap <| imply₁' (impId _)) (imply₁' andElim₁)


-- @@ L174-175 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andImplyLeft' (h : Entailment.Prf 𝓢 (Arrow.arrow φ₁ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ₁ φ₂) ψ) :=
  mdp andImplyLeft h


-- @@ L177-179 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andImplyRight :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow φ₂ ψ) (Arrow.arrow (Wedge.wedge φ₁ φ₂) ψ)) :=
  mdp₂ (impSwap <| imply₁' (impId _)) (imply₁' andElim₂)


-- @@ L180-181 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andImplyRight' (h : Entailment.Prf 𝓢 (Arrow.arrow φ₂ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ₁ φ₂) ψ) :=
  mdp andImplyRight h


-- @@ L183-189 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andInst'' (hp : Entailment.Prf 𝓢 φ) (hq : Entailment.Prf 𝓢 ψ) :
    Entailment.Prf 𝓢 (Wedge.wedge φ ψ) :=
  by
  simp only [LukasiewiczAbbrev.and];
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ (Tilde.tilde ψ)) (Arrow.arrow φ (Tilde.tilde ψ))) :=
    impId _
  have : Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow φ (Tilde.tilde ψ)) (Tilde.tilde ψ)) :=
    mdp₁ this (imply₁' hp);
  have : Entailment.Prf 𝓢 (Arrow.arrow ψ (Tilde.tilde (Arrow.arrow φ (Tilde.tilde ψ)))) :=
    impTrans'' dni <| contraIntro' this;
  exact mdp this hq;


-- @@ L191-198 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andInst : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ (Wedge.wedge φ ψ))) := by


-- @@ L200-200 verbatim
instance : HasAxiomAndInst 𝓢 := ⟨fun φ ψ => Lukasiewicz.andInst (φ := φ) (ψ := ψ)⟩



-- @@ L203-206 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orInst₁ : Entailment.Prf 𝓢 (Arrow.arrow φ (Vee.vee φ ψ)) := by simp only [LukasiewiczAbbrev.or];
  exact explode₁₂;


-- @@ L208-211 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orInst₂ : Entailment.Prf 𝓢 (Arrow.arrow ψ (Vee.vee φ ψ)) := by
  simp only [LukasiewiczAbbrev.or, LukasiewiczAbbrev.neg]; exact imply₁;


-- @@ L213-217 verbatim
instance : HasAxiomOrInst 𝓢 :=
  ⟨fun φ ψ => Lukasiewicz.orInst₁ (φ := φ) (ψ := ψ),
    fun φ ψ => Lukasiewicz.orInst₂ (φ := φ) (ψ := ψ)⟩

-- or_imply

-- @@ L218-239 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orElim :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow (Vee.vee φ ψ) χ))) :=
  by
  simp only [LukasiewiczAbbrev.or];
  have d₁ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ)
          (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) ψ)
            (Arrow.arrow (Arrow.arrow φ χ) (Arrow.arrow (Tilde.tilde χ) (Tilde.tilde φ)))))) :=
    (imply₁' (ψ := Arrow.arrow φ χ) <|
      imply₁' (ψ := Arrow.arrow ψ χ) <|
        imply₁' (ψ := Arrow.arrow (Tilde.tilde φ) ψ) <| contraIntro (φ := φ) (ψ := χ));
  have d₂ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ)
          (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) ψ)
            (Arrow.arrow (Tilde.tilde χ) (Tilde.tilde φ))))) :=
    mdp₃ d₁ (imply₁₁ (Arrow.arrow φ χ) (Arrow.arrow ψ χ) (Arrow.arrow (Tilde.tilde φ) ψ));
  have d₃ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ)
          (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) ψ) (Arrow.arrow (Tilde.tilde χ) ψ)))) :=
    mdp₄
      (imply₁' (ψ := Arrow.arrow φ χ) <|
        imply₁' (ψ := Arrow.arrow ψ χ) <|
          imply₁ (φ := Arrow.arrow (Tilde.tilde φ) ψ) (ψ := Tilde.tilde χ))
      d₂;
  have d₄ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ)
          (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) ψ) (Arrow.arrow (Tilde.tilde χ) χ)))) :=
    mdp₄
      (imply₁' (ψ := Arrow.arrow φ χ) <|
        imply₁₁ (φ := Arrow.arrow ψ χ) (ψ := Arrow.arrow (Tilde.tilde φ) ψ) (χ := Tilde.tilde χ))
      d₃;
  have d₅ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ)
          (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) ψ)
            (Arrow.arrow (Tilde.tilde χ) (Arrow.arrow χ ⊥))))) :=
    by
    simpa using
      imply₁' (ψ := Arrow.arrow φ χ) <|
        imply₁' (ψ := Arrow.arrow ψ χ) <|
          imply₁' (ψ := Arrow.arrow (Tilde.tilde φ) ψ) <| impId (φ := Tilde.tilde χ);
  have d₆ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ)
          (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) ψ) (Tilde.tilde (Tilde.tilde χ))))) :=
    by
  have d₇ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ χ)
        (Arrow.arrow (Arrow.arrow ψ χ)
          (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) ψ)
            (Arrow.arrow (Tilde.tilde (Tilde.tilde χ)) χ)))) :=
    imply₁' (ψ := Arrow.arrow φ χ) <|
      imply₁' (ψ := Arrow.arrow ψ χ) <|
        imply₁' (ψ := Arrow.arrow (Tilde.tilde φ) ψ) <| dne (φ := χ);
  exact mdp₃ d₇ d₆;


-- @@ L241-241 verbatim
instance : HasAxiomOrElim 𝓢 := ⟨fun φ ψ χ => Lukasiewicz.orElim (φ := φ) (ψ := ψ) (χ := χ)⟩


-- @@ L243-243 verbatim
instance : Entailment.Classical 𝓢 where


-- @@ L245-245 verbatim
end Lukasiewicz


-- @@ L247-247 verbatim
end Entailment


-- @@ L249-249 verbatim
end LO
