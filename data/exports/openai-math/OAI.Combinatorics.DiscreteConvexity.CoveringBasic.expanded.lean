import OAI.Combinatorics.DiscreteConvexity.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-15 verbatim
/-!
# Finite objects in the elementary covering argument

Sampling is indexed by ordered pairs of edges, including diagonal pairs.
Different pairs remain different indices even if their unions coincide.
Residual generators are indexed by injective ordered tuples.
-/


-- @@ L17-17 verbatim
namespace TalagrandDiscreteConvexity.Covering


-- @@ L19-19 verbatim
variable {V : Type*} [DecidableEq V]


-- @@ L21-23 verbatim
/-- An ordered tuple of distinct members of a finite edge family. -/
def EdgeTuple (H : Family V) (t : ℕ) :=
  {f : Fin t → ↥H // Function.Injective f}


-- @@ L25-28 verbatim
noncomputable instance edgeTupleFintype (H : Family V) (t : ℕ) :
    Fintype (EdgeTuple H t) := by
  classical
  exact Subtype.fintype _


-- @@ L30-31 verbatim
/-- All independent ordered-pair sampling indices. -/
abbrev PairIndex (H : Family V) := ↥H × ↥H


-- @@ L33-34 verbatim
/-- A sampling outcome specifies precisely the pairs selected. -/
abbrev Sample (H : Family V) := Finset (PairIndex H)


-- @@ L36-37 verbatim
def tupleUnion {H : Family V} {t : ℕ} (f : EdgeTuple H t) : Finset V :=
  Finset.univ.biUnion (fun i => (f.val i).val)


-- @@ L39-42 verbatim
noncomputable def tuplePairs {H : Family V} {t : ℕ}
    (f : EdgeTuple H t) : Finset (PairIndex H) := by
  classical
  exact Finset.univ.image (fun ij : Fin t × Fin t => (f.val ij.1, f.val ij.2))


-- @@ L44-47 verbatim
@[simp] theorem mem_tupleUnion {H : Family V} {t : ℕ}
    {f : EdgeTuple H t} {v : V} :
    v ∈ tupleUnion f ↔ ∃ i, v ∈ (f.val i).val := by
  simp [tupleUnion]


-- @@ L49-53 verbatim
@[simp] theorem mem_tuplePairs {H : Family V} {t : ℕ}
    {f : EdgeTuple H t} {p : PairIndex H} :
    p ∈ tuplePairs f ↔ ∃ i j, (f.val i, f.val j) = p := by
  classical
  simp [tuplePairs, Prod.exists]


-- @@ L55-59 verbatim
/-- The weighted number of edges containing a prescribed vertex set. -/
noncomputable def weightedDegree (H : Family V) (rho : ℝ) (r : ℕ)
    (I : Finset V) : ℝ := by
  classical
  exact ((H.filter (fun e => I ⊆ e)).card : ℝ) * rho ^ (r - I.card)


-- @@ L61-64 verbatim
/-- Edges avoiding all prescribed initial generators. -/
noncomputable def regularFamily (H C0 : Family V) : Family V := by
  classical
  exact H.filter (fun e => ∀ I ∈ C0, ¬ I ⊆ e)


-- @@ L66-69 verbatim
@[simp] theorem mem_regularFamily {H C0 : Family V} {e : Finset V} :
    e ∈ regularFamily H C0 ↔ e ∈ H ∧ ∀ I ∈ C0, ¬ I ⊆ e := by
  classical
  simp [regularFamily]


-- @@ L71-73 verbatim
theorem regularFamily_subset (H C0 : Family V) : regularFamily H C0 ⊆ H := by
  intro e he
  exact (mem_regularFamily.mp he).1


-- @@ L75-75 verbatim
section FiniteGround


-- @@ L77-77 verbatim
variable [Fintype V]


-- @@ L79-83 verbatim
/-- The high weighted-degree sets used as the initial generators. -/
noncomputable def initialFamily (H : Family V) (rho : ℝ) (r : ℕ)
    (T : ℝ) : Family V := by
  classical
  exact Finset.univ.filter (fun I => I.card ≤ r ∧ T < weightedDegree H rho r I)


-- @@ L85-87 verbatim
/-- The regular edges for the actual high-degree initial family. -/
noncomputable def regularEdges (H : Family V) (rho : ℝ) (r : ℕ)
    (T : ℝ) : Family V := regularFamily H (initialFamily H rho r T)


-- @@ L89-92 verbatim
/-- Sets containing at least `m` distinct edges of the original family. -/
noncomputable def denseFamily (H : Family V) (m : ℕ) : Family V := by
  classical
  exact Finset.univ.filter (fun S => m ≤ (H.filter (fun e => e ⊆ S)).card)


-- @@ L94-98 verbatim
@[simp] theorem mem_initialFamily {H : Family V} {rho T : ℝ}
    {r : ℕ} {I : Finset V} :
    I ∈ initialFamily H rho r T ↔ I.card ≤ r ∧ T < weightedDegree H rho r I := by
  classical
  simp [initialFamily]


-- @@ L100-104 verbatim
@[simp] theorem mem_regularEdges {H : Family V} {rho T : ℝ}
    {r : ℕ} {e : Finset V} :
    e ∈ regularEdges H rho r T ↔
      e ∈ H ∧ ∀ I ∈ initialFamily H rho r T, ¬ I ⊆ e := by
  exact mem_regularFamily


-- @@ L106-109 verbatim
@[simp] theorem mem_denseFamily {H : Family V} {m : ℕ} {S : Finset V} :
    S ∈ denseFamily H m ↔ m ≤ (H.filter (fun e => e ⊆ S)).card := by
  classical
  simp [denseFamily]


-- @@ L111-112 verbatim
theorem regularEdges_subset (H : Family V) (rho : ℝ) (r : ℕ) (T : ℝ) :
    regularEdges H rho r T ⊆ H := regularFamily_subset _ _


-- @@ L114-114 verbatim
end FiniteGround


-- @@ L116-116 verbatim
end TalagrandDiscreteConvexity.Covering


-- @@ L118-118 verbatim
end OAI
