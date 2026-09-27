/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.KT4B
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Preservation


-- @@ L12-12 verbatim
/-! # S5 -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace Modal


-- @@ L20-20 verbatim
open Kripke

-- @@ L21-21 verbatim
open Geachean


-- @@ L23-26 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveEuclideanFrameClass :
    FrameClass :=
  { F | Std.Refl F ∧ Euclidean F }


-- @@ L28-28 verbatim
namespace Hilbert

-- @@ L29-29 verbatim
namespace S5


-- @@ L31-36 verbatim
instance _root_.LO.Modal.Hilbert.S5.Kripke.sound :
    Sound (Hilbert.S5) (Kripke.ReflexiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩})
  · exact eq_Geach
  · unfold ReflexiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.euclidean_def];


-- @@ L38-40 verbatim
instance _root_.LO.Modal.Hilbert.S5.Kripke.consistent : Entailment.Consistent (Hilbert.S5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;


-- @@ L42-47 verbatim
instance _root_.LO.Modal.Hilbert.S5.Kripke.complete :
    Complete (Hilbert.S5) (Kripke.ReflexiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold ReflexiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.euclidean_def];


-- @@ L49-49 verbatim
end S5

-- @@ L50-50 verbatim
end Hilbert



-- @@ L53-53 verbatim
namespace Kripke


-- @@ L55-56 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev UniversalFrameClass : FrameClass := { F | Universal F }


-- @@ L58-67 expanded
lemma iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass :
    Realize UniversalFrameClass φ ↔ Realize ReflexiveEuclideanFrameClass φ :=
  by
  constructor;
  · intro h F hF V r; let M : Model := ⟨F, V⟩;
    apply
      Model.PointGenerated.modal_equivalent_at_root (M := ⟨F, V⟩)
          (by exact ⟨trans_of_refl_eucl hF.1.refl hF.2⟩) r |>.mp;
    apply
      @h (Frame.PointGenerated F r).toFrame (Frame.PointGenerated.rel_universal hF.1 hF.2)
        (Frame.PointGenerated M r).Val;
  · rintro h F F_univ; exact @h F (⟨⟨refl_of_universal F_univ⟩, eucl_of_universal F_univ⟩);


-- @@ L69-69 verbatim
end Kripke



-- @@ L72-72 verbatim
namespace Hilbert

-- @@ L73-73 verbatim
namespace S5


-- @@ L75-81 verbatim
instance _root_.LO.Modal.Hilbert.S5.Kripke.soundUniversal :
    Sound (Hilbert.S5) (Kripke.UniversalFrameClass) :=
  ⟨by
  intro φ hF;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mpr;
  exact Kripke.sound.sound hF;
⟩


-- @@ L83-90 verbatim
instance _root_.LO.Modal.Hilbert.S5.Kripke.completeUniversal :
    Complete (Hilbert.S5) (Kripke.UniversalFrameClass) :=
  ⟨by
  intro φ hF;
  apply Kripke.complete.complete;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mp;
  exact hF;
⟩


-- @@ L92-92 verbatim
end S5

-- @@ L93-93 verbatim
end Hilbert



-- @@ L96-99 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveEuclideanFiniteFrameClass :
    FiniteFrameClass :=
  { F | Std.Refl F.Rel ∧ Euclidean F.Rel }


-- @@ L101-101 verbatim
namespace Kripke


-- @@ L103-114 verbatim
lemma eq_ReflexiveTransitiveSymmetricFiniteFrameClass_ReflexiveEuclideanFiniteFrameClass :
    ReflexiveTransitiveSymmetricFiniteFrameClass = ReflexiveEuclideanFiniteFrameClass := by
  ext F;
  constructor;
  · rintro ⟨hRefl, hTrans, hSymm⟩;
    constructor;
    · assumption;
    · exact eucl_of_symm_trans hSymm hTrans.trans;
  · rintro ⟨hRefl, hEucl⟩;
    refine ⟨hRefl, ?_, ?_⟩;
    · exact ⟨trans_of_refl_eucl hRefl.refl hEucl⟩;
    · exact symm_of_refl_eucl hRefl.refl hEucl;


-- @@ L116-116 verbatim
end Kripke


-- @@ L118-118 verbatim
end Modal

-- @@ L119-119 verbatim
end LO
