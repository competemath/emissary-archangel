import OAI.Combinatorics.TwoWayAutomata.Source
import OAI.Combinatorics.Automata.Model


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace TwoWayComplementation.CompanionBridge


-- @@ L8-8 verbatim
open OneWayLiveness

-- @@ L9-9 verbatim
open scoped SetRel


-- @@ L11-16 verbatim
/-- Exact currying/uncurrying equivalence of the two full relation alphabets. -/
def relationEquiv (H : Type*) : BRel H ≃ SetRel H H where
  toFun R := {xy | R.holds xy.1 xy.2}
  invFun R := ⟨fun x y => (x, y) ∈ R⟩
  left_inv _R := rfl
  right_inv _R := rfl


-- @@ L18-27 verbatim
/-- Both products compose in path order, including the identity for the empty word. -/
theorem relationProduct_map {H : Type*} (w : List (BRel H)) :
    relationProduct (w.map (relationEquiv H)) = relationEquiv H w.prod := by
  induction w with
  | nil => rfl
  | cons R w ih =>
    change relationEquiv H R ○ relationProduct (w.map (relationEquiv H)) =
      relationEquiv H (R * w.prod)
    rw [ih]
    rfl


-- @@ L29-33 verbatim
theorem sourceLanguage_map_iff {H : Type*} (w : List (BRel H)) :
    w.map (relationEquiv H) ∈ sourceLanguage H ↔ BRel.live w := by
  change (relationProduct (w.map (relationEquiv H))).Nonempty ↔ _
  rw [relationProduct_map]
  exact ⟨fun ⟨⟨x, y⟩, h⟩ => ⟨x, y, h⟩, fun ⟨x, y, h⟩ => ⟨(x, y), h⟩⟩


-- @@ L35-35 verbatim
end TwoWayComplementation.CompanionBridge


-- @@ L37-37 verbatim
end OAI
