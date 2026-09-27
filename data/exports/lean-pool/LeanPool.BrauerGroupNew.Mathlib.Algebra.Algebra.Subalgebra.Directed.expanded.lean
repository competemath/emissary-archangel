/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Subalgebra.Directed


-- @@ L11-16 verbatim
/-!
# LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Directed

Imported Lean Pool material for
`LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Directed`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace Subalgebra

-- @@ L21-22 verbatim
variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {K : ι → Subalgebra R A}
  {s : Set ι}


-- @@ L24-28 verbatim
lemma coe_biSup_of_directedOn (hs : s.Nonempty) (dir : DirectedOn (K · ≤ K ·) s) :
    ↑(⨆ i ∈ s, K i) = ⨆ i ∈ s, (K i : Set A) := by
  have := hs.to_subtype
  rw [← iSup_subtype'', ← iSup_subtype'', coe_iSup_of_directed, Set.iSup_eq_iUnion]
  rwa [← Function.comp_def, directed_comp, ← directedOn_iff_directed]


-- @@ L30-30 verbatim
end Subalgebra
