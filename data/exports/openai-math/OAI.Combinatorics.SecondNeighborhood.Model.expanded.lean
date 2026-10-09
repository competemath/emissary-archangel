import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Union


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SeymourSecondNeighborhood


-- @@ L8-8 verbatim
variable {V : Type*}


-- @@ L10-12 verbatim
structure IsOriented (r : V → V → Prop) : Prop where
  loopless : ∀ v, ¬ r v v
  asymmetric : ∀ {u v}, r u v → ¬ r v u


-- @@ L14-14 verbatim
variable [Fintype V] [DecidableEq V]


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-20 verbatim
def firstNeighbors (r : V → V → Prop) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (r v)


-- @@ L22-25 verbatim
def secondNeighbors (r : V → V → Prop) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w =>
    w ≠ v ∧ ¬ r v w ∧ ∃ u, r v u ∧ r u w)


-- @@ L27-28 verbatim
def GoodVertex (r : V → V → Prop) (v : V) : Prop :=
  (firstNeighbors r v).card ≤ (secondNeighbors r v).card


-- @@ L30-30 verbatim
end


-- @@ L32-32 verbatim
end SeymourSecondNeighborhood


-- @@ L34-34 verbatim
end OAI
