import Seymour.Matroid.Regularity


-- @@ L3-7 verbatim
/-!
# Matroid Duality

Here we study the duals of matroids given by their standard representation.
-/


-- @@ L9-9 verbatim
open scoped Matrix


-- @@ L11-11 verbatim
variable {α R : Type*} [DecidableEq α]


-- @@ L13-20 verbatim
/-- The dual of standard representation (transpose the matrix and flip its signs). -/
def StandardRepr.dual [DivisionRing R] (S : StandardRepr α R) : StandardRepr α R where
  X := S.Y
  Y := S.X
  hXY := S.hXY.symm
  B := - S.Bᵀ -- the sign is chosen following Oxley (it does not change the resulting matroid)
  decmemX := S.decmemY
  decmemY := S.decmemX


-- @@ L22-22 verbatim
postfix:max "✶" => StandardRepr.dual


-- @@ L24-26 expanded
/-- The dual of dual is the original standard representation. -/
lemma StandardRepr.dual_dual [DivisionRing R] (S : StandardRepr α R) : (S✶)✶ = S := by
  simp [StandardRepr.dual]


-- @@ L28-29 expanded
lemma StandardRepr.dual_indices_union_eq [DivisionRing R] (S : StandardRepr α R) :
    S✶.X ∪ S✶.Y = S.X ∪ S.Y :=
  Set.union_comm S.Y S.X


-- @@ L31-33 expanded
@[simp]
lemma StandardRepr.dual_ground [DivisionRing R] (S : StandardRepr α R) :
    S✶.toMatroid.E = S.toMatroid.E :=
  S.dual_indices_union_eq

