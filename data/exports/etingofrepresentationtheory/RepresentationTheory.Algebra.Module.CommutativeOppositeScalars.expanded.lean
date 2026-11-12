/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.Opposite
import RepresentationTheory.Alignment.Attribute


-- @@ L11-11 verbatim
/-! # Modules over commutative rings and their opposites -/


-- @@ L13-13 verbatim
namespace RepresentationTheory.Algebra.Module.CommutativeOppositeScalars


-- @@ L15-15 verbatim
variable (A M : Type*) [CommRing A] [AddCommGroup M]


-- @@ L17-19 verbatim
/-- A ring homomorphism from the opposite of a commutative ring back to the ring. -/
def fromMulOppositeRingHom : Aᵐᵒᵖ →+* A :=
  (RingHom.id A).fromOpposite fun x y => mul_comm x y


-- @@ L21-23 verbatim
/-- A ring homomorphism from a commutative ring to its opposite ring. -/
def toMulOppositeRingHom : A →+* Aᵐᵒᵖ :=
  (RingHom.id A).toOpposite fun x y => mul_comm x y


-- @@ L25-28 verbatim
/-- A module over the opposite of a commutative ring obtained from a module over the ring. -/
@[source_ref "Chapter2/Remark2.3.2" (role := supporting)]
abbrev moduleOverMulOpposite [Module A M] : Module Aᵐᵒᵖ M :=
  Module.compHom M (fromMulOppositeRingHom A)


-- @@ L30-34 verbatim
/-- The induced opposite-ring scalar action agrees with the given scalar action. -/
@[source_ref "Chapter2/Remark2.3.2" (role := supporting)]
theorem op_smul_eq_smul [Module A M] (a : A) (m : M) :
    letI := moduleOverMulOpposite A M
    (MulOpposite.op a) • m = a • m := rfl


-- @@ L36-39 verbatim
/-- A module over a commutative ring obtained from a module over its opposite ring. -/
@[source_ref "Chapter2/Remark2.3.2" (role := supporting)]
abbrev moduleOfMulOpposite [Module Aᵐᵒᵖ M] : Module A M :=
  Module.compHom M (toMulOppositeRingHom A)


-- @@ L41-45 verbatim
/-- The induced scalar action agrees with the given action of the corresponding opposite-ring element. -/
@[source_ref "Chapter2/Remark2.3.2" (role := primary)]
theorem smul_eq_op_smul [Module Aᵐᵒᵖ M] (a : A) (m : M) :
    letI := moduleOfMulOpposite A M
    a • m = (MulOpposite.op a) • m := rfl


-- @@ L47-47 verbatim
end RepresentationTheory.Algebra.Module.CommutativeOppositeScalars
