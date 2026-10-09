import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
universe u


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
namespace MetricEntropyDuality


-- @@ L14-14 verbatim
open Filter Topology

-- @@ L15-15 verbatim
open scoped BigOperators Pointwise


-- @@ L17-17 verbatim
abbrev RealSpace (ι : Type u) := ι → ℝ


-- @@ L19-20 verbatim
def pairing {ι : Type u} [Fintype ι] (x y : RealSpace ι) : ℝ :=
  ∑ i, x i * y i


-- @@ L22-23 verbatim
def cube (ι : Type u) : Set (RealSpace ι) :=
  {x | ∀ i, |x i| ≤ 1}


-- @@ L25-26 verbatim
def polar {ι : Type u} [Fintype ι] (K : Set (RealSpace ι)) : Set (RealSpace ι) :=
  {y | ∀ x ∈ K, pairing x y ≤ 1}


-- @@ L28-30 verbatim
def Covers {ι : Type u} {M : ℕ} (A B : Set (RealSpace ι))
    (centers : Fin M → RealSpace ι) : Prop :=
  ∀ x ∈ A, ∃ j, x - centers j ∈ B


-- @@ L32-33 verbatim
def Coverable {ι : Type u} (A B : Set (RealSpace ι)) : Prop :=
  ∃ M : ℕ, ∃ centers : Fin M → RealSpace ι, Covers A B centers


-- @@ L35-36 verbatim
def coveringNumber {ι : Type u} (A B : Set (RealSpace ι)) : ℕ :=
  sInf {M : ℕ | ∃ centers : Fin M → RealSpace ι, Covers A B centers}


-- @@ L38-43 verbatim
structure IsSymmetricConvexBody {ι : Type u} [Fintype ι]
    (K : Set (RealSpace ι)) : Prop where
  isCompact : IsCompact K
  convex : Convex ℝ K
  symmetric : ∀ x, x ∈ K ↔ -x ∈ K
  interior_nonempty : (interior K).Nonempty


-- @@ L45-45 verbatim
end MetricEntropyDuality


-- @@ L47-47 verbatim
end


-- @@ L49-49 verbatim
end OAI
