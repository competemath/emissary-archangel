/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.LogicSymbol
import Mathlib.Tactic.Bound.Init


-- @@ L11-11 verbatim
/-! # Axioms -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Axioms


-- @@ L19-19 verbatim
section «lp_section_1»


-- @@ L21-21 verbatim
variable {F : Type*} [LogicalConnective F]

-- @@ L22-22 verbatim
variable (φ ψ χ : F)


-- @@ L24-25 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Verum : F := ⊤

-- @@ L26-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Verum.set : Set F := { Axioms.Verum }


-- @@ L29-30 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Imply₁ :=
  Arrow.arrow φ (Arrow.arrow ψ φ)


-- @@ L31-32 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Imply₁.set : Set F := { Axioms.Imply₁ φ ψ | (φ) (ψ) }


-- @@ L34-35 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Imply₂ :=
  Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ)) (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ))


-- @@ L36-37 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Imply₂.set : Set F := { Axioms.Imply₂ φ ψ χ | (φ) (ψ) (χ) }


-- @@ L39-40 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev ElimContra :=
  Arrow.arrow (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ)) (Arrow.arrow φ ψ)


-- @@ L41-42 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.ElimContra.set : Set F := { Axioms.ElimContra φ ψ | (φ) (ψ) }


-- @@ L44-45 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev AndElim₁ :=
  Arrow.arrow (Wedge.wedge φ ψ) φ


-- @@ L46-47 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.AndElim₁.set : Set F := { Axioms.AndElim₁ φ ψ | (φ) (ψ) }


-- @@ L49-50 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev AndElim₂ :=
  Arrow.arrow (Wedge.wedge φ ψ) ψ


-- @@ L51-52 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.AndElim₂.set : Set F := { Axioms.AndElim₂ φ ψ | (φ) (ψ) }


-- @@ L54-55 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev AndInst :=
  Arrow.arrow φ (Arrow.arrow ψ (Wedge.wedge φ ψ))


-- @@ L56-57 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.AndInst.set : Set F := { Axioms.AndInst φ ψ | (φ) (ψ) }


-- @@ L59-60 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev OrInst₁ :=
  Arrow.arrow φ (Vee.vee φ ψ)


-- @@ L61-62 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.OrInst₁.set : Set F := { Axioms.OrInst₁ φ ψ | (φ) (ψ) }


-- @@ L64-65 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev OrInst₂ :=
  Arrow.arrow ψ (Vee.vee φ ψ)


-- @@ L66-67 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.OrInst₂.set : Set F := { Axioms.OrInst₂ φ ψ | (φ) (ψ) }


-- @@ L69-70 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev OrElim :=
  Arrow.arrow (Arrow.arrow φ χ) (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow (Vee.vee φ ψ) χ))


-- @@ L71-72 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.OrElim.set : Set F := { Axioms.OrElim φ ψ χ | (φ) (ψ) (χ) }


-- @@ L74-75 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev NegEquiv :=
  LogicalConnective.iff (Tilde.tilde φ) (Arrow.arrow φ ⊥)


-- @@ L76-77 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.NegEquiv.set : Set F := { Axioms.NegEquiv φ | (φ) }


-- @@ L79-80 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev EFQ :=
  Arrow.arrow ⊥ φ


-- @@ L81-82 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.EFQ.set : Set F := { Axioms.EFQ φ | (φ) }

-- @@ L83-84 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "EFQAx" => EFQ.set


-- @@ L86-87 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev LEM :=
  Vee.vee φ (Tilde.tilde φ)


-- @@ L88-89 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.LEM.set : Set F := { Axioms.LEM φ | (φ) }

-- @@ L90-91 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "LEMAx" => LEM.set


-- @@ L93-94 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev WeakLEM :=
  Vee.vee (Tilde.tilde φ) (Tilde.tilde (Tilde.tilde φ))


-- @@ L95-96 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.WeakLEM.set : Set F := { Axioms.WeakLEM φ | (φ) }

-- @@ L97-98 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "WLEMAx" => WeakLEM.set


-- @@ L100-101 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Dummett :=
  Vee.vee (Arrow.arrow φ ψ) (Arrow.arrow ψ φ)


-- @@ L102-103 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Dummett.set : Set F := { Axioms.Dummett φ ψ | (φ) (ψ) }

-- @@ L104-105 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "DummettAx" => Dummett.set


-- @@ L107-108 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev DNE :=
  Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) φ


-- @@ L109-110 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.DNE.set : Set F := { Axioms.DNE φ | (φ) }

-- @@ L111-112 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "DNEAx" => DNE.set


-- @@ L114-115 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Peirce :=
  Arrow.arrow (Arrow.arrow (Arrow.arrow φ ψ) φ) φ


-- @@ L116-117 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Peirce.set : Set F := { Axioms.Peirce φ ψ | (φ) (ψ) }

-- @@ L118-119 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "PeirceAx" => Peirce.set


-- @@ L121-121 verbatim
end «lp_section_1»


-- @@ L123-123 verbatim
end Axioms

-- @@ L124-124 verbatim
end LO
