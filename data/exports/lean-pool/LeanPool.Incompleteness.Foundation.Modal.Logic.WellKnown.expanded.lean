/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.K4
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.K45
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.K5
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KB
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KB4
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KB5
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KD
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KD4
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KD45
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KD5
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KDB
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KT
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KTB
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S4
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S4Dot2
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S4Dot3
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.S5
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Triv
public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.S5Grz
public import LeanPool.Incompleteness.Foundation.Modal.Logic.Basic
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomGrz
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomL
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomVer
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Completeness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Soundness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Unnecessitation
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Grz.Soundness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Ver


-- @@ L38-38 verbatim
/-! # WellKnown -/


-- @@ L40-40 verbatim
@[expose] public section



-- @@ L43-43 verbatim
namespace LO

-- @@ L44-44 verbatim
namespace Modal


-- @@ L46-46 verbatim
namespace Logic


-- @@ L48-49 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K4 : Logic := Hilbert.K4.logic

-- @@ L50-52 verbatim
lemma _root_.LO.Modal.Logic.K4.eq_TransitiveKripkeFrameClass_Logic :
    Logic.K4 = Kripke.TransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L55-56 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K45 : Logic := Hilbert.K45.logic

-- @@ L57-59 verbatim
lemma _root_.LO.Modal.Logic.K45.eq_TransitiveEuclideanKripkeFrameClass_Logic :
    Logic.K45 = Kripke.TransitiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L62-63 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K5 : Logic := Hilbert.K5.logic

-- @@ L64-66 verbatim
lemma _root_.LO.Modal.Logic.K5.eq_EuclideanKripkeFrameClass_Logic :
    Logic.K5 = Kripke.EuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L69-70 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB : Logic := Hilbert.KB.logic

-- @@ L71-73 verbatim
lemma _root_.LO.Modal.Logic.KB.eq_SymmetricKripkeFrameClass_Logic :
    Logic.KB = Kripke.SymmetricFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L76-77 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB4 : Logic := Hilbert.KB4.logic

-- @@ L78-80 verbatim
lemma _root_.LO.Modal.Logic.KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic :
    Logic.KB4 = Kripke.SymmetricTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L83-84 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KB5 : Logic := Hilbert.KB5.logic

-- @@ L85-87 verbatim
lemma _root_.LO.Modal.Logic.KB5.eq_ReflexiveEuclideanKripkeFrameClass_Logic :
    Logic.KB5 = Kripke.SymmetricEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L90-91 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD : Logic := Hilbert.KD.logic

-- @@ L92-94 verbatim
lemma _root_.LO.Modal.Logic.KD.eq_SerialKripkeFrameClass_Logic :
    Logic.KD = Kripke.SerialFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L97-98 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD4 : Logic := Hilbert.KD4.logic

-- @@ L99-101 verbatim
lemma _root_.LO.Modal.Logic.KD4.eq_SerialTransitiveKripkeFrameClass_Logic :
    Logic.KD4 = Kripke.SerialTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L104-105 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD45 : Logic := Hilbert.KD45.logic

-- @@ L106-108 verbatim
lemma _root_.LO.Modal.Logic.KD45.eq_SerialTransitiveEuclideanKripkeFrameClass_Logic :
    Logic.KD45 = Kripke.SerialTransitiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L111-112 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KD5 : Logic := Hilbert.KD5.logic

-- @@ L113-115 verbatim
lemma _root_.LO.Modal.Logic.KD5.eq_SerialEuclideanKripkeFrameClass_Logic :
    Logic.KD5 = Kripke.SerialEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L118-119 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KDB : Logic := Hilbert.KDB.logic

-- @@ L120-122 verbatim
lemma _root_.LO.Modal.Logic.KDB.eq_SerialSymmetricKripkeFrameClass_Logic :
    Logic.KDB = Kripke.SerialSymmetricFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L125-126 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KT : Logic := Hilbert.KT.logic

-- @@ L127-129 verbatim
lemma _root_.LO.Modal.Logic.KT.eq_ReflexiveKripkeFrameClass_Logic :
    Logic.KT = Kripke.ReflexiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L132-133 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KTB : Logic := Hilbert.KTB.logic

-- @@ L134-136 verbatim
lemma _root_.LO.Modal.Logic.KTB.eq_ReflexiveSymmetricKripkeFrameClass_Logic :
    Logic.KTB = Kripke.ReflexiveSymmetricFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L139-140 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4 : Logic := Hilbert.S4.logic

-- @@ L141-143 verbatim
lemma _root_.LO.Modal.Logic.S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic :
    Logic.S4 = Kripke.ReflexiveTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L146-147 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4Dot2 : Logic := Hilbert.S4Dot2.logic

-- @@ L148-150 verbatim
lemma _root_.LO.Modal.Logic.S4Dot2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic :
    Logic.S4Dot2 = Kripke.ReflexiveTransitiveConfluentFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L153-154 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S4Dot3 : Logic := Hilbert.S4Dot3.logic

-- @@ L155-157 verbatim
lemma _root_.LO.Modal.Logic.S4Dot3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic :
    Logic.S4Dot3 = Kripke.ReflexiveTransitiveConnectedFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


-- @@ L159-160 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S5 : Logic := Hilbert.S5.logic

-- @@ L161-163 verbatim
lemma _root_.LO.Modal.Logic.S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic :
    Logic.S5 = Kripke.ReflexiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic

-- @@ L164-166 verbatim
lemma _root_.LO.Modal.Logic.S5.eq_UniversalKripkeFrameClass_Logic :
    Logic.S5 = Kripke.UniversalFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


-- @@ L168-169 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S5Grz : Logic := Hilbert.S5Grz.logic



-- @@ L172-173 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev GL : Logic := Hilbert.GL.logic

-- @@ L174-176 verbatim
lemma _root_.LO.Modal.Logic.GL.eq_TransitiveIrreflexiveFiniteKripkeFrameClass_Logic :
    Logic.GL = Kripke.TransitiveIrreflexiveFiniteFrameClass.logic
  := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic

-- @@ L177-177 verbatim
instance : (Logic.GL).Unnecessitation := inferInstance



-- @@ L180-181 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KH : Logic := Hilbert.KH.logic



-- @@ L184-185 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Grz : Logic := Hilbert.Grz.logic

-- @@ L186-188 verbatim
lemma _root_.LO.Modal.Logic.Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic :
    Logic.Grz = Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass.logic
  := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic



-- @@ L191-192 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Triv : Logic := Hilbert.Triv.logic

-- @@ L193-195 verbatim
lemma _root_.LO.Modal.Logic.Triv.eq_EqualityKripkeFrameClass_Logic :
    Logic.Triv = Kripke.EqualityFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



-- @@ L198-199 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Ver : Logic := Hilbert.Ver.logic

-- @@ L200-200 verbatim
instance : (Logic.Ver).Normal := Hilbert.normal

-- @@ L201-203 verbatim
lemma _root_.LO.Modal.Logic.Ver.eq_IsolatedFrameClass_Logic :
    Logic.Ver = Kripke.IsolatedFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


-- @@ L205-205 verbatim
end Logic


-- @@ L207-207 verbatim
end Modal

-- @@ L208-208 verbatim
end LO
