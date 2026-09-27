/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic


-- @@ L10-10 verbatim
/-! # Closure -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Modal


-- @@ L18-18 verbatim
namespace Kripke


-- @@ L20-20 verbatim
variable {F : Frame} {x y z : F.World}


-- @@ L22-22 verbatim
open Relation



-- @@ L25-25 verbatim
section «lp_section_1»


-- @@ L27-29 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.RelReflTransGen : _root_.Rel F.World F.World :=
  ReflTransGen (Frame.Rel' · ·)


-- @@ L30-31 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺^* " => Frame.RelReflTransGen


-- @@ L33-33 verbatim
namespace Frame

-- @@ L34-34 verbatim
namespace RelReflTransGen


-- @@ L36-36 expanded
@[simp]
lemma single (hxy : Frame.Rel' x y) : Frame.RelReflTransGen x y :=
  ReflTransGen.single hxy


-- @@ L38-38 verbatim
@[simp] lemma reflexive : Std.Refl F.RelReflTransGen := ⟨fun _ => ReflTransGen.refl⟩


-- @@ L40-40 expanded
@[simp]
lemma refl {x : F.World} : Frame.RelReflTransGen x x :=
  reflexive.refl x


-- @@ L42-43 verbatim
@[simp] lemma transitive : IsTrans F.World F.RelReflTransGen :=
  ⟨fun _ _ _ hxy hyz => ReflTransGen.trans hxy hyz⟩


-- @@ L45-47 verbatim
@[simp] lemma symmetric : IsSymmetric F.Rel → IsSymmetric F.RelReflTransGen := fun h => by
  let : Std.Symm F.Rel := ⟨fun _ _ => @h _ _⟩
  exact fun _ _ hxy => Std.Symm.symm (r := F.RelReflTransGen) _ _ hxy


-- @@ L49-49 verbatim
end RelReflTransGen

-- @@ L50-50 verbatim
end Frame



-- @@ L53-56 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.TransitiveReflexiveClosure (F : Frame) : Frame
    where
  World := F.World
  Rel := (Frame.RelReflTransGen · ·)


-- @@ L57-58 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^*" => Frame.TransitiveReflexiveClosure


-- @@ L60-60 verbatim
namespace Frame

-- @@ L61-61 verbatim
namespace TransitiveReflexiveClosure


-- @@ L63-63 expanded
lemma single (hxy : Frame.Rel' x y) : (Frame.TransitiveReflexiveClosure F).Rel x y :=
  ReflTransGen.single hxy


-- @@ L65-65 expanded
lemma rel_reflexive : Std.Refl ((Frame.TransitiveReflexiveClosure F).Rel) :=
  ⟨fun _ => ReflTransGen.refl⟩


-- @@ L67-67 expanded
lemma rel_transitive :
    IsTrans (Frame.TransitiveReflexiveClosure F) ((Frame.TransitiveReflexiveClosure F).Rel) :=
  ⟨fun _ _ _ hxy hyz => ReflTransGen.trans hxy hyz⟩


-- @@ L69-70 expanded
lemma rel_symmetric : IsSymmetric F.Rel → IsSymmetric (Frame.TransitiveReflexiveClosure F) :=
  fun h => by simp_all


-- @@ L72-72 verbatim
end TransitiveReflexiveClosure

-- @@ L73-73 verbatim
end Frame


-- @@ L75-75 verbatim
end «lp_section_1»



-- @@ L78-78 verbatim
section «lp_section_2»


-- @@ L80-82 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.RelTransGen {F : Frame} : _root_.Rel F.World F.World :=
  TransGen (Frame.Rel' · ·)


-- @@ L83-84 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺^+ " => Frame.RelTransGen


-- @@ L86-86 verbatim
namespace Frame

-- @@ L87-87 verbatim
namespace RelTransGen


-- @@ L89-89 expanded
@[simp]
lemma single (hxy : Frame.Rel' x y) : Frame.RelTransGen x y :=
  TransGen.single hxy


-- @@ L91-92 verbatim
@[simp]
lemma transitive : IsTrans F.World F.RelTransGen := ⟨fun _ _ _ => TransGen.trans⟩


-- @@ L94-99 verbatim
@[simp]
lemma symmetric (hSymm : IsSymmetric F.Rel) : IsSymmetric F.RelTransGen := by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single <| hSymm h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single <| hSymm hyz) ih


-- @@ L101-101 verbatim
end RelTransGen

-- @@ L102-102 verbatim
end Frame



-- @@ L105-108 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.TransitiveClosure (F : Frame) : Frame
    where
  World := F.World
  Rel := (Frame.RelTransGen · ·)


-- @@ L109-110 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^+" => Frame.TransitiveClosure


-- @@ L112-112 verbatim
namespace Frame

-- @@ L113-113 verbatim
namespace TransitiveClosure


-- @@ L115-115 expanded
lemma single (hxy : Frame.Rel' x y) : (Frame.TransitiveClosure F).Rel x y :=
  TransGen.single hxy


-- @@ L117-117 expanded
lemma rel_transitive : IsTrans (Frame.TransitiveClosure F) ((Frame.TransitiveClosure F).Rel) :=
  ⟨fun _ _ _ => TransGen.trans⟩


-- @@ L119-119 expanded
lemma rel_symmetric (hSymm : IsSymmetric F.Rel) : IsSymmetric (Frame.TransitiveClosure F) := by
  simp_all


-- @@ L121-121 verbatim
end TransitiveClosure

-- @@ L122-122 verbatim
end Frame


-- @@ L124-124 verbatim
end «lp_section_2»



-- @@ L127-127 verbatim
section «lp_section_3»


-- @@ L129-131 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Kripke.Frame.RelReflGen : _root_.Rel F.World F.World :=
  ReflGen (Frame.Rel' · ·)


-- @@ L132-133 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:45 " ≺^= " => Frame.RelReflGen


-- @@ L135-138 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.ReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^= ·)

-- @@ L139-140 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^=" => Frame.ReflexiveClosure


-- @@ L142-142 verbatim
end «lp_section_3»



-- @@ L145-145 verbatim
section «lp_section_4»


-- @@ L147-149 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Kripke.Frame.RelIrreflGen : _root_.Rel F.World F.World :=
  IrreflGen (Frame.Rel' · ·)


-- @@ L150-151 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:45 " ≺^≠ " => Frame.RelIrreflGen


-- @@ L153-153 verbatim
namespace Frame

-- @@ L154-154 verbatim
namespace RelIrreflGen


-- @@ L156-156 verbatim
@[simp] lemma rel_irreflexive : Std.Irrefl F.RelIrreflGen := by exact ⟨fun x h => h.1 rfl⟩


-- @@ L158-158 verbatim
end RelIrreflGen

-- @@ L159-159 verbatim
end Frame



-- @@ L162-165 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.IrreflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^≠ ·)

-- @@ L166-167 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:95 "^≠" => Frame.IrreflexiveClosure


-- @@ L169-169 verbatim
namespace Frame

-- @@ L170-170 verbatim
namespace IrreflexiveClosure


-- @@ L172-172 expanded
lemma rel_irreflexive : Std.Irrefl ((Frame.IrreflexiveClosure F).Rel) := by
  exact ⟨fun x h => h.1 rfl⟩


-- @@ L174-174 verbatim
end IrreflexiveClosure

-- @@ L175-175 verbatim
end Frame


-- @@ L177-177 verbatim
end «lp_section_4»



-- @@ L180-180 verbatim
end Kripke


-- @@ L182-182 verbatim
end Modal

-- @@ L183-183 verbatim
end LO
