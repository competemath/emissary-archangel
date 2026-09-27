/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.K
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Completeness
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Filteration
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness


-- @@ L14-14 verbatim
/-! # K -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace LO

-- @@ L20-20 verbatim
namespace Modal


-- @@ L22-22 verbatim
open Kripke


-- @@ L24-24 verbatim
namespace Hilbert

-- @@ L25-25 verbatim
namespace K


-- @@ L27-27 verbatim
instance _root_.LO.Modal.Hilbert.K.Kripke.sound : Sound (Hilbert.K) AllFrameClass := inferInstance


-- @@ L29-29 verbatim
instance : Entailment.Consistent (Hilbert.K) := Hilbert.consistent_of_FrameClass AllFrameClass


-- @@ L31-31 verbatim
instance : Kripke.Canonical (Hilbert.K) (AllFrameClass) := ⟨by trivial⟩


-- @@ L33-35 verbatim
instance _root_.LO.Modal.Hilbert.K.Kripke.completeAll :
    Complete (Hilbert.K) (AllFrameClass) :=
  inferInstance


-- @@ L37-53 verbatim
instance _root_.LO.Modal.Hilbert.K.Kripke.completeAllFinite :
    Complete (Hilbert.K) (AllFiniteFrameClass) :=
  ⟨by
  intro φ hp;
  apply Kripke.completeAll.complete;
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFilterationModel M ↑φ.subformulas;
  apply filteration FM (coarsestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulas) by
      use ⟨FM.toFrame⟩;
      simp [];
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Val
⟩


-- @@ L55-55 verbatim
end K

-- @@ L56-56 verbatim
end Hilbert


-- @@ L58-58 verbatim
end Modal

-- @@ L59-59 verbatim
end LO
