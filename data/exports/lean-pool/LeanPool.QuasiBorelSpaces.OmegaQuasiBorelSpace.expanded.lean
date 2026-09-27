/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.Chain
import LeanPool.QuasiBorelSpaces.Basic


-- @@ L11-15 verbatim
/-!
# LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace`.
-/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
open OmegaCompletePartialOrder

-- @@ L21-21 verbatim
open QuasiBorelSpace


-- @@ L23-38 verbatim
/-!
# Omega quasi-Borel spaces

This file defines omega quasi-borel spaces (ωQBS), which combine `QuasiBorelSpace` and
`OmegaCompletePartialOrder` structures with a compatibility axiom stating that pointwise
ω-suprema of ω-chains of morphisms are morphisms (Definition 3.5 in [VakarKS19]).

We prove that products and coproducts preserve the ωQBS structure (Lemma 3.9).

See [VakarKS19].

## Definitions

* `OmegaQuasiBorelSpace`: A type with both an `OmegaCompletePartialOrder` and a
  `QuasiBorelSpace`, satisfying the compatibility axiom.
-/


-- @@ L40-50 verbatim
/--
An ωQBS (Omega quasi-borel space) is a type equipped with both a
`QuasiBorelSpace` and an `OmegaCompletePartialOrder`, satisfying the
compatibility axiom: variables are closed under pointwise ω-suprema of ω-chains.
-/
class OmegaQuasiBorelSpace (A : Type*) extends OmegaCompletePartialOrder A, QuasiBorelSpace A where
  /--
  Compatibility axiom (Definition 3.5 in [VakarKS19]):
  variables are closed under pointwise ω-suprema of ω-chains.
  -/
  isHom_ωSup : IsHom (OmegaCompletePartialOrder.ωSup : Chain A → A)


-- @@ L52-52 verbatim
namespace OmegaQuasiBorelSpace


-- @@ L54-54 verbatim
variable {A B C : Type*}


-- @@ L56-56 verbatim
attribute [simp, local fun_prop] isHom_ωSup


-- @@ L58-67 verbatim
/--
Pointwise supremum of a chain of QBS morphisms is a QBS morphism
(also known as the "Compatibility Axiom" for the exponential to be an ωQBS)
-/
@[fun_prop]
lemma isHom_ωSup'
    {_ : QuasiBorelSpace A} {_ : OmegaQuasiBorelSpace B}
    (f : A → Chain B) (hc : IsHom f) :
    IsHom (fun x ↦ ωSup (f x)) := by
  fun_prop


-- @@ L69-72 verbatim
instance
    [QuasiBorelSpace A] [OmegaCompletePartialOrder A] [Subsingleton A]
    : OmegaQuasiBorelSpace A where
  isHom_ωSup := by simp only [isHom_to_subsingleton]


-- @@ L74-74 verbatim
end OmegaQuasiBorelSpace
