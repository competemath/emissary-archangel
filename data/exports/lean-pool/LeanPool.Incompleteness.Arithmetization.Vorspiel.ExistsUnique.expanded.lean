/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Aesop.BuiltinRules
public import Mathlib.Basic.ExistsUnique
import Mathlib.Data.Finset.Attr
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.SetLike


-- @@ L18-18 verbatim
/-! # ExistsUnique -/


-- @@ L20-20 verbatim
@[expose] public section



-- @@ L23-23 verbatim
namespace Classical

-- @@ L24-24 verbatim
variable {α : Sort*} {p : α → Prop} {r : α → α → Prop}


-- @@ L26-30 verbatim
lemma exitsUnique_extend (h : ∀ x, p x → ∃! y, r x y) (default : α) (x : α) :
    ∃! y, (p x → r x y) ∧ (¬p x → y = default) := by
  by_cases hx : p x
  · simpa [hx] using h _ hx
  · simp [hx]


-- @@ L32-34 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def «extendedChoose!» (h : ∀ x, p x → ∃! y, r x y)
    (default : α) (x : α) : α := choose (exitsUnique_extend h default x).exists


-- @@ L36-38 verbatim
lemma «extendedchoose!_spec» (h : ∀ x, p x → ∃! y, r x y) (default : α) (hx : p x) :
    r x (extendedChoose! h default x) :=
  choose_spec (exitsUnique_extend h default x).exists |>.1 hx


-- @@ L40-42 verbatim
lemma «extendedchoose!_spec_not» (h : ∀ x, p x → ∃! y, r x y) (default : α) (hx : ¬p x) :
    extendedChoose! h default x = default :=
  choose_spec (exitsUnique_extend h default x).exists |>.2 hx


-- @@ L44-46 verbatim
lemma «extendedChoose!_uniq» (h : ∀ x, p x → ∃! y, r x y) (default : α) (hpx : p x) (hrx : r x y) :
    y = extendedChoose! h default x :=
  (h x hpx).unique hrx (extendedchoose!_spec h default hpx)


-- @@ L48-50 verbatim
lemma «extendedChoose!_eq_iff» (h : ∀ x, p x → ∃! y, r x y) (default : α) (hpx : p x) :
    y = extendedChoose! h default x ↔ r x y :=
  ⟨by rintro rfl; exact extendedchoose!_spec h default hpx, extendedChoose!_uniq h default hpx⟩


-- @@ L52-52 verbatim
end Classical
