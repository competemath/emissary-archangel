/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Permanent.Attach
import Mathlib.Data.Fin.VecNotation


-- @@ L9-21 verbatim
/-!
# Valiant's XOR gadget

The four-node weighted graph of [Valiant 1979][valiant1979complexity] that
couples two edges of a graph so that, in every cycle cover, exactly one of
them is used: attached in place of the edges `u → v` and `u' → v'`, the gadget
has no cover of its own, no cover entering through one edge and leaving
through the other, and no cover using both edges, while the covers using
exactly one edge weigh `4` (`DescriptiveComplexity.pdel_attachValiant`). The
first edge enters at node `0` and leaves from node `3`; the second enters at
node `3` and leaves from node `0`. The six local values are computed by
`decide`.
-/


-- @@ L23-23 verbatim
namespace DescriptiveComplexity


-- @@ L25-25 verbatim
open Finset


-- @@ L27-29 verbatim
/-- **Valiant's XOR gadget.** -/
def xorGadget : Fin 4 → Fin 4 → ℤ :=
  ![![0, 1, -1, -1], ![1, -1, 1, 1], ![0, 1, 1, 2], ![0, 1, 3, 0]]


-- @@ L31-31 verbatim
theorem xorGadget_internal : pdel xorGadget ∅ ∅ = 0 := by decide


-- @@ L33-33 verbatim
theorem xorGadget_first : pdel xorGadget {3} {0} = 4 := by decide


-- @@ L35-35 verbatim
theorem xorGadget_second : pdel xorGadget {0} {3} = 4 := by decide


-- @@ L37-37 verbatim
theorem xorGadget_cross₁ : pdel xorGadget {3} {3} = 0 := by decide


-- @@ L39-39 verbatim
theorem xorGadget_cross₂ : pdel xorGadget {0} {0} = 0 := by decide


-- @@ L41-41 verbatim
theorem xorGadget_both : pdel xorGadget {3, 0} {0, 3} = 0 := by decide


-- @@ L43-43 verbatim
section Attach


-- @@ L45-45 verbatim
variable {V : Type} [Fintype V] [DecidableEq V] (M₀ : V → V → ℤ) (u u' v v' : V)


-- @@ L47-50 verbatim
/-- **Valiant's gadget attached in place of the edges `u → v` and
`u' → v'`.** -/
abbrev attachValiant : V ⊕ Fin 4 → V ⊕ Fin 4 → ℤ :=
  attachXor M₀ xorGadget u u' v v' 0 3 3 0


-- @@ L52-63 verbatim
/-- **The expansion of Valiant's gadget**: four times the covers using exactly
one of the two edges. -/
theorem pdel_attachValiant (A B : Finset V) (huu' : u ≠ u') (hvv' : v ≠ v') (hv : v ∉ B)
    (hv' : v' ∉ B) :
    pdel (attachValiant M₀ u u' v v') (A.map Function.Embedding.inl)
      (B.map Function.Embedding.inl) =
      4 * ((if u ∈ A then 0 else pdel M₀ (insert u A) (insert v B)) +
        (if u' ∈ A then 0 else pdel M₀ (insert u' A) (insert v' B))) := by
  rw [attachValiant, pdel_attachXor (by decide) A B (by decide) huu' hvv' hv hv',
    xorGadget_internal, xorGadget_first, xorGadget_second, xorGadget_cross₁, xorGadget_cross₂,
    xorGadget_both]
  ring


-- @@ L65-65 verbatim
end Attach


-- @@ L67-67 verbatim
end DescriptiveComplexity
