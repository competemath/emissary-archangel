/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.IntProp.Kripke.Basic
import LeanPool.Incompleteness.Foundation.IntProp.Kripke.Hilbert.Soundness


-- @@ L12-12 verbatim
/-! # Basic -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace IntProp


-- @@ L20-20 verbatim
open Kripke

-- @@ L21-21 verbatim
open Formula.Kripke



-- @@ L24-25 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.IntProp.Kripke.EuclideanFrameClass : FrameClass := { F | Euclidean F }


-- @@ L27-46 expanded
instance _root_.LO.IntProp.Kripke.EuclideanFrameClass.definedByLEM :
    Kripke.EuclideanFrameClass.DefinedByFormula (Axioms.LEM (.atom 0)) :=
  ⟨by
    rintro F; constructor;
    · rintro hEucl _ ⟨_, rfl⟩; exact ValidOnFrame.lem <| symm_of_refl_eucl F.rel_refl.refl hEucl
    · rintro h x y z Rxy Rxz;
      let V : Kripke.Valuation F :=
        ⟨fun {v a} => Frame.Rel' z v, by intro w v Rwv a Rzw; exact F.rel_trans' Rzw Rwv; ⟩;
      suffices Satisfies ⟨F, V⟩ y (.atom 0) by simpa [Satisfies] using this;
      apply V.hereditary Rxy; have hlem : Realize F (Axioms.LEM (.atom 0)) := h _ rfl;
      have hx := (ValidOnFrame.models_iff.mp hlem) V x;
      simp only [Semantics.Realize, Satisfies, imp_false, or_iff_not_imp_right, not_forall, not_not,
        forall_exists_index, V] at hx;
      exact hx z Rxz (F.rel_refl.refl z)⟩


-- @@ L48-51 verbatim
instance : Kripke.EuclideanFrameClass.IsNonempty := ⟨by
  use pointFrame;
  simp [Euclidean];
⟩



-- @@ L54-54 verbatim
open Kripke


-- @@ L56-56 verbatim
namespace Hilbert

-- @@ L57-57 verbatim
namespace Cl

-- @@ L58-58 verbatim
namespace Kripke


-- @@ L60-61 verbatim
instance : EuclideanFrameClass.DefinedBy (Hilbert.Cl.axioms) :=
  FrameClass.definedBy_with_axiomEFQ inferInstance


-- @@ L63-63 verbatim
instance sound : Sound Hilbert.Cl EuclideanFrameClass := inferInstance


-- @@ L65-66 verbatim
instance consistent : Entailment.Consistent Hilbert.Cl :=
  Kripke.Hilbert.consistent_of_FrameClass EuclideanFrameClass


-- @@ L68-68 verbatim
end Kripke

-- @@ L69-69 verbatim
end Cl

-- @@ L70-70 verbatim
end Hilbert



-- @@ L73-73 verbatim
end IntProp

-- @@ L74-74 verbatim
end LO
