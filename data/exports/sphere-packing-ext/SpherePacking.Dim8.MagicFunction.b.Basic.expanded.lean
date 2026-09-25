/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module
public import SpherePacking.Dim8.MagicFunction.b.Psi
public import SpherePacking.MagicFunction.IntegralParametrisations


-- @@ L10-23 verbatim
/-!
# Defining integrals for `b`

This file defines the six contour integrals `J₁'`-`J₆'` used to build the magic function `b`.
The prime indicates the radial profile as a function of the real parameter `x = ‖v‖^2`; the
unprimed versions `J₁`-`J₆` are the induced functions on `EuclideanSpace ℝ (Fin 8)`.

## Main definitions
* `MagicFunction.b.RealIntegrals.J₁'` ... `J₆'`, `MagicFunction.b.RealIntegrals.b'`
* `MagicFunction.b.RadialFunctions.J₁` ... `J₆`, `MagicFunction.b.RadialFunctions.b`

## Main statement
* `MagicFunction.b.RadialFunctions.b_eq`
-/


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
local notation "V" => EuclideanSpace ℝ (Fin 8)


-- @@ L29-29 verbatim
open Set Complex Real MagicFunction.Parametrisations


-- @@ L31-31 verbatim
namespace MagicFunction.b.RealIntegrals


-- @@ L33-40 verbatim
/--
The first auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₁' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, I -- CV factor.
  * ψT' (z₁' t)
  * cexp (π * I * x * (z₁' t))


-- @@ L42-49 verbatim
/--
The second auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₂' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1,
  ψT' (z₂' t)
  * cexp (π * I * x * (z₂' t))


-- @@ L51-58 verbatim
/--
The third auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₃' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, I -- CV factor.
  * ψT' (z₃' t)
  * cexp (π * I * x * (z₃' t))


-- @@ L60-67 verbatim
/--
The fourth auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₄' (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, -1 -- CV factor.
  * ψT' (z₄' t)
  * cexp (π * I * x * (z₄' t))


-- @@ L69-76 verbatim
/--
The fifth auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₅' (x : ℝ) : ℂ := -2 * ∫ t in (0 : ℝ)..1, I -- CV factor.
  * ψI' (z₅' t)
  * cexp (π * I * x * (z₅' t))


-- @@ L78-85 verbatim
/--
The sixth auxiliary contour integral defining the radial profile of `b`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def J₆' (x : ℝ) : ℂ := -2 * ∫ t in Ici (1 : ℝ), I -- CV factor.
  * ψS' (z₆' t)
  * cexp (π * I * x * (z₆' t))


-- @@ L87-92 verbatim
/--
The radial profile defining the magic function `b` as a function of `x = ‖v‖^2`.

The prime indicates that this is a function of the real parameter `x = ‖v‖^2`.
-/
@[expose] public def b' (x : ℝ) := J₁' x + J₂' x + J₃' x + J₄' x + J₅' x + J₆' x


-- @@ L94-94 verbatim
end MagicFunction.b.RealIntegrals

-- @@ L95-95 verbatim
open MagicFunction.b.RealIntegrals


-- @@ L97-97 verbatim
namespace MagicFunction.b.RadialFunctions


-- @@ L99-100 verbatim
/-- The function on `V` induced from the radial profile `J₁'` by `x = ‖v‖^2`. -/
@[expose] public def J₁ (x : V) : ℂ := J₁' (‖x‖ ^ 2)


-- @@ L102-103 verbatim
/-- The function on `V` induced from the radial profile `J₂'` by `x = ‖v‖^2`. -/
@[expose] public def J₂ (x : V) : ℂ := J₂' (‖x‖ ^ 2)


-- @@ L105-106 verbatim
/-- The function on `V` induced from the radial profile `J₃'` by `x = ‖v‖^2`. -/
@[expose] public def J₃ (x : V) : ℂ := J₃' (‖x‖ ^ 2)


-- @@ L108-109 verbatim
/-- The function on `V` induced from the radial profile `J₄'` by `x = ‖v‖^2`. -/
@[expose] public def J₄ (x : V) : ℂ := J₄' (‖x‖ ^ 2)


-- @@ L111-112 verbatim
/-- The function on `V` induced from the radial profile `J₅'` by `x = ‖v‖^2`. -/
@[expose] public def J₅ (x : V) : ℂ := J₅' (‖x‖ ^ 2)


-- @@ L114-115 verbatim
/-- The function on `V` induced from the radial profile `J₆'` by `x = ‖v‖^2`. -/
@[expose] public def J₆ (x : V) : ℂ := J₆' (‖x‖ ^ 2)


-- @@ L117-118 verbatim
/-- The magic function `b` on `V`, obtained from the radial profile `b'` by `x = ‖v‖^2`. -/
@[expose] public def b (x : V) : ℂ := b' (‖x‖ ^ 2)


-- @@ L120-120 verbatim
section Eq


-- @@ L122-123 verbatim
/-- Expand `b` as the sum of the six defining integrals. -/
public lemma b_eq (x : V) : b x = J₁ x + J₂ x + J₃ x + J₄ x + J₅ x + J₆ x := rfl


-- @@ L125-125 verbatim
end Eq


-- @@ L127-127 verbatim
end MagicFunction.b.RadialFunctions


-- @@ L129-129 verbatim
end
