/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
module

public import Mathlib.Algebra.Field.ZMod
public import LeanPool.ConnesRigidity.Core
import Mathlib.Data.Finsupp.Encodable


-- @@ L14-16 verbatim
/-!
# The special-linear carrier in Zhou's construction
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace Connes

-- @@ L21-21 verbatim
namespace SpecialLinear


-- @@ L23-24 verbatim
/-- Characteristic-two scalar field. Paper: §§2, 4. -/
abbrev F := ZMod 2

-- @@ L25-26 verbatim
/-- Polynomial coefficient ring. Paper: §2. -/
abbrev R := Polynomial F

-- @@ L27-28 verbatim
/-- Special-linear group carrier. Paper: §§2, 4. -/
abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) R


-- @@ L30-33 verbatim
/-- Countability of the polynomial ring. Paper: §4. -/
noncomputable instance : Countable R := by
  exact Countable.of_equiv (ℕ →₀ F)
    (AddMonoidAlgebra.coeffEquiv.symm.trans (Polynomial.toFinsuppIso F).toEquiv.symm)


-- @@ L35-38 verbatim
/-- Countability of the matrix carrier. Paper: §4. -/
noncomputable instance : Countable (Matrix (Fin 3) (Fin 3) R) := by
  change Countable (Fin 3 → Fin 3 → R)
  infer_instance


-- @@ L40-43 verbatim
/-- Countability of the special-linear carrier. Paper: §4. -/
noncomputable instance : Countable SL3 := by
  change Countable {A : Matrix (Fin 3) (Fin 3) R // A.det = 1}
  infer_instance


-- @@ L45-49 verbatim
/-- Countable discrete acting-group carrier. Paper: §§4, 5. -/
noncomputable def sl3Group : CountableDiscreteGroup where
  Carrier := SL3
  group := inferInstance
  countable := by infer_instance


-- @@ L51-51 verbatim
end SpecialLinear

-- @@ L52-52 verbatim
end Connes
