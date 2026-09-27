/-
Copyright (c) 2026 PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PrimeNumberTheoremAnd contributors
-/

module

public import Mathlib.Algebra.Notation.Support


-- @@ L11-18 verbatim
/-!
Ported for Lean Pool from PrimeNumberTheoremAnd commit
0c7abf7be7765dc5ffd21afc1c37b018199ec3c9, via wewantmoore commit
d59bd80ea93fabb9faf769e790ab47692645e022 (both Apache-2.0).
The port adds the MooreBound namespace and updates Mathlib APIs and proof style.
Wiener and Consequences retain the PNT and prime-interval dependency closure;
unrelated later developments and LeanArchitect annotations are omitted.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace MooreBound


-- @@ L24-24 verbatim
namespace Function


-- @@ L26-26 verbatim
open _root_.Function


-- @@ L28-28 verbatim
variable {α : Type*} [Zero α]


-- @@ L30-31 verbatim
theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp


-- @@ L33-34 verbatim
theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id


-- @@ L36-36 verbatim
end Function


-- @@ L38-38 verbatim
end MooreBound
