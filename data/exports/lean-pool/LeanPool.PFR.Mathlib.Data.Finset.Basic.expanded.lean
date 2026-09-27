/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Attr


-- @@ L12-14 verbatim
/-!
# Elementary lemmas about finite sets
-/


-- @@ L16-16 verbatim
namespace Finset

-- @@ L17-17 verbatim
variable {α : Type*} {s : Finset α}


-- @@ L19-21 verbatim
@[simp]
public
lemma ne_empty_iff_nonempty : s ≠ ∅ ↔ s.Nonempty := nonempty_iff_ne_empty.symm


-- @@ L23-23 verbatim
end Finset
