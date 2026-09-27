/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.LogicSymbol
public import LeanPool.Incompleteness.Foundation.Modal.Geachean
import Mathlib.Tactic.Bound.Init


-- @@ L12-12 verbatim
/-! # Axioms -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace Axioms


-- @@ L20-20 verbatim
variable {F : Type*} [BasicModalLogicalConnective F]

-- @@ L21-21 verbatim
variable (φ ψ χ : F)



-- @@ L24-24 verbatim
section «lp_section_1»


-- @@ L26-27 expanded
/-- `◇` is duality of `□`. -/
protected abbrev DiaDuality :=
  LogicalConnective.iff (Dia.dia φ) (Tilde.tilde (Box.box (Tilde.tilde φ)))


-- @@ L28-29 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.DiaDuality.set : Set F := { Axioms.DiaDuality φ | (φ) }


-- @@ L31-32 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K :=
  Arrow.arrow (Box.box (Arrow.arrow φ ψ)) (Arrow.arrow (Box.box φ) (Box.box ψ))


-- @@ L33-34 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.K.set : Set F := { Axioms.K φ ψ | (φ) (ψ) }

-- @@ L35-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "KAx" => K.set


-- @@ L38-39 expanded
/-- Axiom for reflexive -/
protected abbrev T :=
  Arrow.arrow (Box.box φ) φ


-- @@ L40-41 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.T.set : Set F := { Axioms.T φ | (φ) }

-- @@ L42-43 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "TAx" => T.set


-- @@ L45-46 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev DiaTc :=
  Arrow.arrow φ (Dia.dia φ)


-- @@ L48-49 expanded
/-- Axiom for symmetric -/
protected abbrev B :=
  Arrow.arrow φ (Box.box (Dia.dia φ))


-- @@ L50-51 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.B.set : Set F := { Axioms.B φ | (φ) }

-- @@ L52-53 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "BAx" => B.set


-- @@ L55-56 expanded
/-- `□`-only version of axiom `BAx`. -/
protected abbrev B₂ :=
  Arrow.arrow (Box.box φ) (Box.box (Tilde.tilde (Box.box (Tilde.tilde φ))))


-- @@ L57-58 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.B₂.set : Set F := { Axioms.B₂ φ | (φ) }

-- @@ L59-60 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "BBoxAx" => B₂.set


-- @@ L62-63 expanded
/-- Axiom for serial -/
protected abbrev D :=
  Arrow.arrow (Box.box φ) (Dia.dia φ)


-- @@ L64-65 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.D.set : Set F := { Axioms.D φ | (φ) }

-- @@ L66-67 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "DAx" => D.set



-- @@ L70-71 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev P : F :=
  Tilde.tilde (Box.box ⊥)


-- @@ L72-73 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.P.set : Set F := { Axioms.P | }

-- @@ L74-75 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "PAx" => P.set

-- @@ L76-76 expanded
@[simp 1100]
lemma _root_.LO.Axioms.P.set.def : P.set = {(Tilde.tilde (Box.box ⊥) : F)} := by ext; simp;


-- @@ L78-79 expanded
/-- Axiom for transivity -/
protected abbrev Four :=
  Arrow.arrow (Box.box φ) (Box.box (Box.box φ))


-- @@ L80-81 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Four.set : Set F := { Axioms.Four φ | (φ) }

-- @@ L82-83 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "𝟰" => Four.set


-- @@ L85-86 expanded
/-- Axiom for euclidean -/
protected abbrev Five :=
  Arrow.arrow (Dia.dia φ) (Box.box (Dia.dia φ))


-- @@ L87-88 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Five.set : Set F := { Axioms.Five φ | (φ) }

-- @@ L89-90 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "𝟱" => Five.set


-- @@ L92-93 expanded
/-- `□`-only version of axiom `𝟱`. -/
protected abbrev Five₂ :=
  Arrow.arrow (Tilde.tilde (Box.box φ)) (Box.box (Tilde.tilde (Box.box (Tilde.tilde φ))))


-- @@ L94-95 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Five₂.set : Set F := { Axioms.Five₂ φ | (φ) }

-- @@ L96-97 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "𝟱(□)" => Five₂.set


-- @@ L99-100 expanded
/-- Axiom for confluency -/
protected abbrev Dot2 :=
  Arrow.arrow (Dia.dia (Box.box φ)) (Box.box (Dia.dia φ))


-- @@ L101-102 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Dot2.set : Set F := { Axioms.Dot2 φ | (φ) }

-- @@ L103-104 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max ".𝟮" => Dot2.set


-- @@ L106-107 expanded
/-- Axiom for density -/
protected abbrev C4 :=
  Arrow.arrow (Box.box (Box.box φ)) (Box.box φ)


-- @@ L108-109 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.C4.set : Set F := { Axioms.C4 φ | (φ) }

-- @@ L110-111 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "C4Ax" => C4.set


-- @@ L113-114 expanded
/-- Axiom for functionality -/
protected abbrev CD :=
  Arrow.arrow (Dia.dia φ) (Box.box φ)


-- @@ L115-116 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.CD.set : Set F := { Axioms.CD φ | (φ) }

-- @@ L117-118 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "CDAx" => CD.set


-- @@ L120-121 expanded
/-- Axiom for coreflexivity -/
protected abbrev Tc :=
  Arrow.arrow φ (Box.box φ)


-- @@ L122-123 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Tc.set : Set F := { Axioms.Tc φ | (φ) }

-- @@ L124-125 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "TcAx" => Tc.set


-- @@ L127-128 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev DiaT :=
  Arrow.arrow (Dia.dia φ) φ


-- @@ L130-131 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Ver :=
  Box.box φ


-- @@ L132-133 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Ver.set : Set F := { Axioms.Ver φ | (φ) }

-- @@ L134-135 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "VerAx" => Ver.set


-- @@ L137-138 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Dot3 :=
  Vee.vee (Box.box (Arrow.arrow (Box.box φ) ψ)) (Box.box (Arrow.arrow (Box.box ψ) φ))


-- @@ L139-140 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Dot3.set : Set F := { Axioms.Dot3 φ ψ | (φ) (ψ) }

-- @@ L141-142 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max ".𝟯" => Dot3.set


-- @@ L144-145 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Grz :=
  Arrow.arrow (Box.box (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ))) φ)) φ


-- @@ L146-147 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Grz.set : Set F := { Axioms.Grz φ | (φ) }

-- @@ L148-149 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "GrzAx" => Grz.set


-- @@ L151-152 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev M :=
  (Arrow.arrow (Box.box (Dia.dia φ)) (Dia.dia (Box.box φ)))


-- @@ L153-154 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.M.set : Set F := { Axioms.M φ | (φ) }

-- @@ L155-156 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "MAx" => M.set


-- @@ L158-159 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev L :=
  Arrow.arrow (Box.box (Arrow.arrow (Box.box φ) φ)) (Box.box φ)


-- @@ L160-161 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.L.set : Set F := { Axioms.L φ | (φ) }

-- @@ L162-163 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "LAx" => L.set


-- @@ L165-166 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev H :=
  Arrow.arrow (Box.box (LogicalConnective.iff (Box.box φ) φ)) (Box.box φ)


-- @@ L167-168 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.H.set : Set F := { Axioms.H φ | (φ) }

-- @@ L169-170 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "HAx" => H.set


-- @@ L172-172 verbatim
end «lp_section_1»


-- @@ L174-175 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Geach (t : Geachean.Taple) (φ : F) :=
  Arrow.arrow (multidia t.i (multibox t.m φ)) (multibox t.j (multidia t.n φ))


-- @@ L176-177 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Axioms.Geach.set (t : Geachean.Taple) : Set F := { Axioms.Geach t φ | (φ) }

-- @@ L178-179 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max "GeachAx(" t ")" => Geach.set t


-- @@ L181-181 verbatim
end Axioms

-- @@ L182-182 verbatim
end LO
