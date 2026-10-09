import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-10 verbatim
/-!
The final claim constructs the spaces and states all eleven original results.
`Analysis.RecursivePotentials.Challenge.main_iff_original` verifies statement preservation.
-/


-- @@ L12-12 verbatim
universe uIndex uSpace uOther uDomain uTarget uFiber


-- @@ L14-14 verbatim
open scoped BigOperators


-- @@ L16-16 verbatim
namespace RecursivePotentials


-- @@ L18-18 verbatim
def leastPair (x a b : ℝ) : ℝ × ℝ := (max a (x + b), max b (-x + a))


-- @@ L20-26 verbatim
structure FiniteRootedTree (ι : Type uIndex) where
  root : ι
  parent : ι → ι
  depth : ι → ℕ
  parent_root : parent root = root
  depth_root : depth root = 0
  parent_depth : ∀ i, i ≠ root → depth (parent i) < depth i


-- @@ L28-28 verbatim
namespace FiniteRootedTree


-- @@ L30-30 verbatim
section


-- @@ L32-33 verbatim
variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)


-- @@ L35-36 verbatim
def children (s : ι) : Finset ι :=
  Finset.univ.filter fun c => c ≠ T.root ∧ T.parent c = s


-- @@ L38-38 verbatim
def maxDepth : ℕ := Finset.univ.sup T.depth


-- @@ L40-51 verbatim
noncomputable def fields (v : ι → ℝ) (s : ι) : ℝ × ℝ :=
  leastPair (v s)
    (Real.sqrt (∑ c : {c // c ∈ T.children s}, (fields v c.1).1 ^ 2))
    (Real.sqrt (∑ c : {c // c ∈ T.children s}, (fields v c.1).2 ^ 2))
termination_by T.maxDepth - T.depth s
decreasing_by
  all_goals
    have hc := (Finset.mem_filter.mp c.2).2
    have hd := T.parent_depth c.1 hc.1
    rw [hc.2] at hd
    have hm : T.depth c.1 ≤ T.maxDepth := Finset.le_sup (Finset.mem_univ c.1)
    omega


-- @@ L53-53 verbatim
def Initial (H : Finset ι) : Prop := T.root ∈ H ∧ ∀ s ∈ H, T.parent s ∈ H


-- @@ L55-55 verbatim
end


-- @@ L57-57 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)


-- @@ L59-62 verbatim
def ancestors (s : ι) : Finset ι :=
  if _hs : s = T.root then {s} else insert s (ancestors (T.parent s))
termination_by T.depth s
decreasing_by exact T.parent_depth s _hs


-- @@ L64-65 verbatim
def ancestorClosure (S : Finset ι) : Finset ι :=
  insert T.root (S.biUnion T.ancestors)


-- @@ L67-73 verbatim
def restrict (H : Finset ι) (hH : T.Initial H) : FiniteRootedTree H where
  root := ⟨T.root, hH.1⟩
  parent s := ⟨T.parent s, hH.2 s.1 s.2⟩
  depth s := T.depth s
  parent_root := Subtype.ext T.parent_root
  depth_root := T.depth_root
  parent_depth s hs := T.parent_depth s (fun h => hs (Subtype.ext h))


-- @@ L75-77 verbatim
noncomputable def extend (H : Finset ι) (f : H → ℝ) : ι →₀ ℝ :=
  Finsupp.onFinset H (fun s => if hs : s ∈ H then f ⟨s, hs⟩ else 0)
    (fun s hs => by by_contra hh; simp [hh] at hs)


-- @@ L79-79 verbatim
def head (v : ι →₀ ℝ) : Finset ι := T.ancestorClosure v.support


-- @@ L81-81 verbatim
def projectHead (_T : FiniteRootedTree ι) (H : Finset ι) (v : ι →₀ ℝ) : ι →₀ ℝ := v.filter (· ∈ H)


-- @@ L83-83 verbatim
end FiniteRootedTree


-- @@ L85-88 verbatim
structure CofiniteSubspace (E : Type uSpace) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  space : Submodule ℝ E
  closed : IsClosed (space : Set E)
  finiteQuotient : Module.Finite ℝ (E ⧸ space)


-- @@ L90-90 verbatim
section Moduli


-- @@ L92-92 verbatim
variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L94-94 verbatim
noncomputable def averagedGain (x : E) (t : ℝ) (y : E) : ℝ := (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1


-- @@ L96-97 verbatim
noncomputable def averagedInner (x : E) (t : ℝ) (F : CofiniteSubspace E) : ℝ :=
  sInf {r : ℝ | ∃ y ∈ F.space, 1 ≤ ‖y‖ ∧ r = averagedGain x t y}


-- @@ L99-101 verbatim
noncomputable def averagedModulus (E : Type uSpace) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = sSup (Set.range (averagedInner x t))}


-- @@ L103-103 verbatim
end Moduli


-- @@ L105-114 verbatim
def sequenceTree : FiniteRootedTree (List ℕ) where
  root := []
  parent := List.dropLast
  depth := List.length
  parent_root := rfl
  depth_root := rfl
  parent_depth s hs := by
    rw [List.length_dropLast]
    have h := List.length_pos_iff_ne_nil.mpr hs
    omega


-- @@ L116-116 verbatim
abbrev ComponentNode (h : ℕ+) := {s : List ℕ // s.length ≤ h.val}


-- @@ L118-118 verbatim
abbrev JoinedNode := Option (Σ h : ℕ+, ComponentNode h)


-- @@ L120-143 verbatim
def joinedTree : FiniteRootedTree JoinedNode where
  root := none
  parent
    | none => none
    | some ⟨h, s⟩ => if s.1 = [] then none else
        some ⟨h, ⟨s.1.dropLast, by rw [List.length_dropLast]; have := s.2; omega⟩⟩
  depth
    | none => 0
    | some ⟨_, s⟩ => s.1.length + 1
  parent_root := rfl
  depth_root := rfl
  parent_depth s hs := by
    cases s with
    | none => exact (hs rfl).elim
    | some s =>
      obtain ⟨h, s⟩ := s
      dsimp
      by_cases he : s.1 = []
      · simp [he]
      · rw [ite_eq_right he]
        dsimp
        rw [List.length_dropLast]
        have hpos := List.length_pos_iff_ne_nil.mpr he
        omega


-- @@ L145-145 verbatim
open Filter Topology


-- @@ L147-148 verbatim
def WeaklyNull {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ → E) : Prop :=
  ∀ f : E →L[ℝ] ℝ, Tendsto (fun k => f (d k)) atTop (𝓝 0)


-- @@ L150-157 verbatim
structure EquivalentNorm (E : Type uSpace) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  N : Seminorm ℝ E
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  lower_bound : ∀ x, lower * ‖x‖ ≤ N x
  upper_bound : ∀ x, N x ≤ upper * ‖x‖


-- @@ L159-159 verbatim
namespace EquivalentNorm


-- @@ L161-161 verbatim
variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)


-- @@ L163-164 verbatim
noncomputable def inner (x : E) (t : ℝ) (F : CofiniteSubspace E) : ℝ :=
  sInf {r : ℝ | ∃ y ∈ F.space, A.N y = 1 ∧ r = A.N (x + t • y) - 1}


-- @@ L166-167 verbatim
noncomputable def modulus (t : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x : E, A.N x = 1 ∧ r = sSup (Set.range (A.inner x t))}


-- @@ L169-169 verbatim
def AUC : Prop := ∀ t : ℝ, 0 < t → 0 < A.modulus t


-- @@ L171-171 verbatim
end EquivalentNorm


-- @@ L173-173 verbatim
open Filter Topology


-- @@ L175-175 verbatim
open scoped ENNReal


-- @@ L177-177 verbatim
section


-- @@ L179-180 verbatim
def IsReflexive (E : Type uSpace) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)


-- @@ L182-182 verbatim
namespace SquareSum


-- @@ L184-185 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]


-- @@ L187-187 verbatim
abbrev Space : Type _ := ↥(lp E 2)


-- @@ L189-189 verbatim
end SquareSum


-- @@ L191-191 verbatim
end


-- @@ L193-193 verbatim
open UniformSpace


-- @@ L195-195 verbatim
section


-- @@ L197-218 verbatim
def completionEquivOfDense {E : Type uSpace} {F : Type uOther} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E →L[ℝ] F)
    (K : NNReal) (hK : ∀ x, ‖x‖ ≤ K * ‖f x‖) (hdense : DenseRange f) : Completion E ≃L[ℝ] F := by
  let g := f.fromCompletion
  have hbound : ∀ x : Completion E, ‖x‖ ≤ K * ‖g x‖ := by
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_le continuous_norm (continuous_const.mul (g.continuous.norm))
    | ih x => simpa only [g, ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe] using hK x
  have hanti := g.antilipschitz_of_bound hbound
  have hclosed := hanti.isClosed_range g.uniformContinuous
  have hsurj : Function.Surjective g := by
    intro y
    have hh : y ∈ closure (Set.range f) := hdense y
    have hsub : Set.range f ⊆ Set.range g := by
      rintro _ ⟨x, rfl⟩
      exact ⟨(x : Completion E), ContinuousLinearMap.fromCompletion_apply_coe f x⟩
    have hm := closure_mono hsub hh
    rw [hclosed.closure_eq] at hm
    exact hm
  exact ContinuousLinearEquiv.ofBijective g (LinearMap.ker_eq_bot.mpr hanti.injective)
    (LinearMap.range_eq_top.mpr hsurj)


-- @@ L220-220 verbatim
end


-- @@ L222-232 verbatim
def componentTree (h : ℕ+) : FiniteRootedTree (ComponentNode h) where
  root := ⟨[], by simp⟩
  parent s := ⟨s.1.dropLast, by rw [List.length_dropLast]; have := s.2; omega⟩
  depth s := s.1.length
  parent_root := Subtype.ext rfl
  depth_root := rfl
  parent_depth s hs := by
    rw [List.length_dropLast]
    have hne : s.1 ≠ [] := fun h => hs (Subtype.ext h)
    have hp := List.length_pos_iff_ne_nil.mpr hne
    omega


-- @@ L234-234 verbatim
section


-- @@ L236-241 verbatim
def logarithmicGamma (M β : ℝ) : ℝ :=
  let h := β ^ 2 / (2 * M ^ 2)
  let c := β * Real.sqrt h / 8
  let H := 1 + Real.log (M / c)
  let K := 4 * (2 + Real.sqrt 6) * H / h
  β * h / 8 * Real.exp (-K)


-- @@ L243-243 verbatim
end


-- @@ L245-245 verbatim
open Filter


-- @@ L247-247 verbatim
open scoped Topology


-- @@ L249-251 verbatim
structure ChildExponent where
  val : ℝ
  one_le : 1 ≤ val


-- @@ L253-253 verbatim
namespace ChildExponent


-- @@ L255-255 verbatim
variable (p : ChildExponent)


-- @@ L257-258 verbatim
def agg {ι : Type uIndex} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ i ∈ s, |f i| ^ p.val) ^ (1 / p.val)


-- @@ L260-260 verbatim
end ChildExponent


-- @@ L262-262 verbatim
namespace FiniteRootedTree


-- @@ L264-265 verbatim
variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)


-- @@ L267-278 verbatim
def pfields (v : ι → ℝ) (s : ι) : ℝ × ℝ :=
  leastPair (v s)
    (p.agg Finset.univ (fun c : {c // c ∈ T.children s} => (pfields v c.1).1))
    (p.agg Finset.univ (fun c : {c // c ∈ T.children s} => (pfields v c.1).2))
termination_by T.maxDepth - T.depth s
decreasing_by
  all_goals
    have hc := (Finset.mem_filter.mp c.2).2
    have hd := T.parent_depth c.1 hc.1
    rw [hc.2] at hd
    have hm : T.depth c.1 ≤ T.maxDepth := Finset.le_sup (Finset.mem_univ c.1)
    omega


-- @@ L280-280 verbatim
end FiniteRootedTree


-- @@ L282-282 verbatim
namespace VariableExponent


-- @@ L284-284 verbatim
def heightExponent (h : ℕ+) : ℝ := 1 + 1 / (h.val : ℝ)


-- @@ L286-286 verbatim
def cubicConstant : ℝ := (6 * Real.exp 1)⁻¹ ^ 3


-- @@ L288-288 verbatim
def sixthConstant : ℝ := 2 * Real.exp (-(Real.exp 1 - 1)) * (4 : ℝ)⁻¹ ^ 6


-- @@ L290-290 verbatim
end VariableExponent


-- @@ L292-292 verbatim
open Filter Topology TopologicalSpace


-- @@ L294-294 verbatim
open scoped ENNReal


-- @@ L296-296 verbatim
end RecursivePotentials


-- @@ L298-298 verbatim
namespace ComparatorModel


-- @@ L300-300 verbatim
open scoped BigOperators


-- @@ L302-302 verbatim
namespace RecursivePotentials


-- @@ L304-304 verbatim
noncomputable abbrev leastPair := @_root_.OAI.RecursivePotentials.leastPair


-- @@ L306-306 verbatim
noncomputable abbrev FiniteRootedTree := @_root_.OAI.RecursivePotentials.FiniteRootedTree


-- @@ L308-308 verbatim
namespace FiniteRootedTree


-- @@ L310-310 verbatim
section


-- @@ L312-313 verbatim
variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)


-- @@ L315-315 verbatim
noncomputable abbrev Initial (T : FiniteRootedTree ι) := _root_.OAI.RecursivePotentials.FiniteRootedTree.Initial T


-- @@ L317-317 verbatim
end


-- @@ L319-319 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)


-- @@ L321-321 verbatim
noncomputable abbrev restrict (T : FiniteRootedTree ι) := _root_.OAI.RecursivePotentials.FiniteRootedTree.restrict T


-- @@ L323-323 verbatim
noncomputable abbrev extend (H : Finset ι) := _root_.OAI.RecursivePotentials.FiniteRootedTree.extend H


-- @@ L325-325 verbatim
noncomputable abbrev head (T : FiniteRootedTree ι) := _root_.OAI.RecursivePotentials.FiniteRootedTree.head T


-- @@ L327-329 verbatim
class Heads : Prop where
  initial : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) (v : ι →₀ ℝ),
    T.Initial (T.head v)


-- @@ L331-331 verbatim
variable [ComparatorModel.RecursivePotentials.FiniteRootedTree.Heads]


-- @@ L333-335 verbatim
noncomputable def P (v : ι →₀ ℝ) : ι →₀ ℝ :=
  extend (T.head v) (fun s => ((T.restrict (T.head v) (FiniteRootedTree.Heads.initial T v)).fields
    (fun s => v s.1) s).1)


-- @@ L337-339 verbatim
noncomputable def Q (v : ι →₀ ℝ) : ι →₀ ℝ :=
  extend (T.head v) (fun s => ((T.restrict (T.head v) (FiniteRootedTree.Heads.initial T v)).fields
    (fun s => v s.1) s).2)


-- @@ L341-341 verbatim
noncomputable def normSum (v : ι →₀ ℝ) : ℝ := T.P v T.root + T.Q v T.root


-- @@ L343-343 verbatim
noncomputable abbrev projectHead (T : FiniteRootedTree ι) := _root_.OAI.RecursivePotentials.FiniteRootedTree.projectHead T


-- @@ L345-345 verbatim
end FiniteRootedTree


-- @@ L347-347 verbatim
variable [ComparatorModel.RecursivePotentials.FiniteRootedTree.Heads]


-- @@ L349-349 verbatim
def TreeVector {ι : Type uIndex} (_T : FiniteRootedTree ι) := ι →₀ ℝ


-- @@ L351-351 verbatim
namespace TreeVector


-- @@ L353-353 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)


-- @@ L355-355 verbatim
instance : AddCommGroup (TreeVector T) := inferInstanceAs (AddCommGroup (ι →₀ ℝ))


-- @@ L357-357 verbatim
instance : Module ℝ (TreeVector T) := inferInstanceAs (Module ℝ (ι →₀ ℝ))


-- @@ L359-359 verbatim
instance : CoeFun (TreeVector T) (fun _ => ι → ℝ) := ⟨fun v => (show ι →₀ ℝ from v)⟩


-- @@ L361-361 verbatim
noncomputable instance : Norm (TreeVector T) := ⟨fun v => T.normSum v⟩


-- @@ L363-369 verbatim
class Construction : Prop where
  core : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι),
    NormedSpace.Core ℝ (TreeVector T)
  coordinate_bound : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (v : ι →₀ ℝ) (s : ι), |v s| ≤ T.normSum v
  projection_bound : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (H : Finset ι), T.Initial H → ∀ v, T.normSum (T.projectHead H v) ≤ T.normSum v


-- @@ L371-371 verbatim
variable [ComparatorModel.RecursivePotentials.TreeVector.Construction]


-- @@ L373-374 verbatim
noncomputable instance : NormedAddCommGroup (TreeVector T) :=
  NormedAddCommGroup.ofCore (TreeVector.Construction.core T)


-- @@ L376-376 verbatim
noncomputable instance : NormedSpace ℝ (TreeVector T) := NormedSpace.ofCore (TreeVector.Construction.core T)


-- @@ L378-381 verbatim
def coordinateLinear (s : ι) : TreeVector T →ₗ[ℝ] ℝ where
  toFun v := v s
  map_add' _v _w := rfl
  map_smul' _a _v := rfl


-- @@ L383-387 verbatim
noncomputable def coordinate (s : ι) : TreeVector T →L[ℝ] ℝ :=
  (coordinateLinear T s).mkContinuous 1 (fun v => by
    change ‖v s‖ ≤ 1 * T.normSum v
    rw [Real.norm_eq_abs, one_mul]
    exact TreeVector.Construction.coordinate_bound T v s)


-- @@ L389-402 verbatim
def projectionLinear (H : Finset ι) : TreeVector T →ₗ[ℝ] TreeVector T where
  toFun := T.projectHead H
  map_add' v w := by
    change ι →₀ ℝ at v w
    apply Finsupp.ext
    intro s
    change T.projectHead H (v + w) s = (T.projectHead H v + T.projectHead H w) s
    by_cases hs : s ∈ H <;> simp [FiniteRootedTree.projectHead, _root_.OAI.RecursivePotentials.FiniteRootedTree.projectHead, hs]
  map_smul' a v := by
    change ι →₀ ℝ at v
    apply Finsupp.ext
    intro s
    change T.projectHead H (a • v) s = (a • T.projectHead H v) s
    by_cases hs : s ∈ H <;> simp [FiniteRootedTree.projectHead, _root_.OAI.RecursivePotentials.FiniteRootedTree.projectHead, hs]


-- @@ L404-409 verbatim
noncomputable def projection (H : Finset ι) (hH : T.Initial H) :
    TreeVector T →L[ℝ] TreeVector T :=
  (projectionLinear T H).mkContinuous 1 (fun v => by
    change T.normSum (T.projectHead H v) ≤ 1 * T.normSum v
    rw [one_mul]
    exact TreeVector.Construction.projection_bound T H hH v)


-- @@ L411-411 verbatim
end TreeVector


-- @@ L413-413 verbatim
variable [ComparatorModel.RecursivePotentials.TreeVector.Construction]


-- @@ L415-416 verbatim
abbrev TreeSpace {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) :=
  UniformSpace.Completion (TreeVector T)


-- @@ L418-418 verbatim
namespace TreeSpace


-- @@ L420-420 verbatim
open UniformSpace


-- @@ L422-422 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)


-- @@ L424-424 verbatim
def coordinate (s : ι) : TreeSpace T →L[ℝ] ℝ := (TreeVector.coordinate T s).fromCompletion


-- @@ L426-427 verbatim
def P (s : ι) : TreeSpace T → ℝ :=
  Completion.extension (fun v : TreeVector T => T.P v s)


-- @@ L429-430 verbatim
def Q (s : ι) : TreeSpace T → ℝ :=
  Completion.extension (fun v : TreeVector T => T.Q v s)


-- @@ L432-433 verbatim
def projection (H : Finset ι) (hH : T.Initial H) : TreeSpace T →L[ℝ] TreeSpace T :=
  (TreeVector.projection T H hH).completion


-- @@ L435-436 verbatim
def tail (H : Finset ι) (hH : T.Initial H) : Submodule ℝ (TreeSpace T) :=
  (projection T H hH).ker


-- @@ L438-438 verbatim
end TreeSpace


-- @@ L440-440 verbatim
section Moduli


-- @@ L442-442 verbatim
variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L444-444 verbatim
noncomputable abbrev averagedModulus := @_root_.OAI.RecursivePotentials.averagedModulus


-- @@ L446-446 verbatim
end Moduli


-- @@ L448-448 verbatim
noncomputable abbrev sequenceTree := @_root_.OAI.RecursivePotentials.sequenceTree


-- @@ L450-450 verbatim
noncomputable abbrev ComponentNode := @_root_.OAI.RecursivePotentials.ComponentNode


-- @@ L452-452 verbatim
noncomputable abbrev JoinedNode := @_root_.OAI.RecursivePotentials.JoinedNode


-- @@ L454-454 verbatim
noncomputable abbrev joinedTree := @_root_.OAI.RecursivePotentials.joinedTree


-- @@ L456-456 verbatim
abbrev XSigma := TreeSpace sequenceTree


-- @@ L458-458 verbatim
abbrev XJoined := TreeSpace joinedTree


-- @@ L460-461 verbatim
def ZeroTreeVector {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) : Type _ :=
  ↥((TreeVector.coordinate T T.root).ker)


-- @@ L463-463 verbatim
namespace ZeroTreeVector


-- @@ L465-465 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)


-- @@ L467-468 verbatim
instance : AddCommGroup (ZeroTreeVector T) :=
  inferInstanceAs (AddCommGroup (TreeVector.coordinate T T.root).ker)


-- @@ L470-471 verbatim
instance : Module ℝ (ZeroTreeVector T) :=
  inferInstanceAs (Module ℝ (TreeVector.coordinate T T.root).ker)


-- @@ L473-474 verbatim
def toTree : ZeroTreeVector T →ₗ[ℝ] TreeVector T :=
  (TreeVector.coordinate T T.root).ker.subtype


-- @@ L476-476 verbatim
instance : Norm (ZeroTreeVector T) := ⟨fun v => T.P (toTree T v) T.root⟩


-- @@ L478-482 verbatim
class Construction : Prop where
  core : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι),
    NormedSpace.Core ℝ (ZeroTreeVector T)
  half : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (v : ZeroTreeVector T), ‖v‖ = ‖toTree T v‖ / 2


-- @@ L484-484 verbatim
variable [ComparatorModel.RecursivePotentials.ZeroTreeVector.Construction]


-- @@ L486-486 verbatim
instance : NormedAddCommGroup (ZeroTreeVector T) := NormedAddCommGroup.ofCore (ZeroTreeVector.Construction.core T)


-- @@ L488-488 verbatim
instance : NormedSpace ℝ (ZeroTreeVector T) := NormedSpace.ofCore (ZeroTreeVector.Construction.core T)


-- @@ L490-491 verbatim
def inclusion : ZeroTreeVector T →L[ℝ] TreeVector T :=
  (toTree T).mkContinuous 2 (fun v => by rw [ZeroTreeVector.Construction.half]; exact le_of_eq (by ring))


-- @@ L493-500 verbatim
def projectionLinear (H : Finset ι) (hH : T.Initial H) : ZeroTreeVector T →ₗ[ℝ] ZeroTreeVector T :=
  (((TreeVector.projection T H hH).toLinearMap).comp (toTree T)).codRestrict
    (TreeVector.coordinate T T.root).ker (fun v => by
      change TreeVector.coordinate T T.root (TreeVector.projection T H hH (toTree T v)) = 0
      change T.projectHead H (toTree T v) T.root = 0
      change (if T.root ∈ H then toTree T v T.root else 0) = 0
      rw [ite_eq_left hH.1]
      exact v.2)


-- @@ L502-506 verbatim
def projection (H : Finset ι) (hH : T.Initial H) : ZeroTreeVector T →L[ℝ] ZeroTreeVector T :=
  (projectionLinear T H hH).mkContinuous 1 (fun v => by
    rw [one_mul, ZeroTreeVector.Construction.half, ZeroTreeVector.Construction.half]
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
      (TreeVector.Construction.projection_bound T H hH (toTree T v)))


-- @@ L508-508 verbatim
end ZeroTreeVector


-- @@ L510-510 verbatim
variable [ComparatorModel.RecursivePotentials.ZeroTreeVector.Construction]


-- @@ L512-513 verbatim
abbrev ZeroTreeSpace {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) :=
  UniformSpace.Completion (ZeroTreeVector T)


-- @@ L515-515 verbatim
namespace ZeroTreeSpace


-- @@ L517-517 verbatim
open UniformSpace


-- @@ L519-519 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)


-- @@ L521-521 verbatim
def inclusion : ZeroTreeSpace T →L[ℝ] TreeSpace T := (ZeroTreeVector.inclusion T).completion


-- @@ L523-524 verbatim
def projection (H : Finset ι) (hH : T.Initial H) : ZeroTreeSpace T →L[ℝ] ZeroTreeSpace T :=
  (ZeroTreeVector.projection T H hH).completion


-- @@ L526-527 verbatim
def tail (H : Finset ι) (hH : T.Initial H) : Submodule ℝ (ZeroTreeSpace T) :=
  (projection T H hH).ker


-- @@ L529-529 verbatim
end ZeroTreeSpace


-- @@ L531-531 verbatim
abbrev XZero := ZeroTreeSpace joinedTree


-- @@ L533-533 verbatim
namespace ZeroTreeSpace


-- @@ L535-535 verbatim
open UniformSpace


-- @@ L537-537 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)


-- @@ L539-540 verbatim
def coordinate (s : ι) : ZeroTreeSpace T →L[ℝ] ℝ :=
  (TreeSpace.coordinate T s).comp (inclusion T)


-- @@ L542-542 verbatim
def P (s : ι) (x : ZeroTreeSpace T) : ℝ := TreeSpace.P T s (inclusion T x)


-- @@ L544-544 verbatim
def Q (s : ι) (x : ZeroTreeSpace T) : ℝ := TreeSpace.Q T s (inclusion T x)


-- @@ L546-546 verbatim
end ZeroTreeSpace


-- @@ L548-548 verbatim
open Filter Topology


-- @@ L550-550 verbatim
noncomputable abbrev WeaklyNull := @_root_.OAI.RecursivePotentials.WeaklyNull


-- @@ L552-552 verbatim
noncomputable abbrev EquivalentNorm := @_root_.OAI.RecursivePotentials.EquivalentNorm


-- @@ L554-554 verbatim
namespace EquivalentNorm


-- @@ L556-556 verbatim
variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)


-- @@ L558-558 verbatim
noncomputable abbrev modulus (A : EquivalentNorm E) := _root_.OAI.RecursivePotentials.EquivalentNorm.modulus A


-- @@ L560-560 verbatim
noncomputable abbrev AUC (A : EquivalentNorm E) := _root_.OAI.RecursivePotentials.EquivalentNorm.AUC A


-- @@ L562-562 verbatim
end EquivalentNorm


-- @@ L564-564 verbatim
open Filter Topology


-- @@ L566-566 verbatim
open scoped ENNReal


-- @@ L568-568 verbatim
section


-- @@ L570-570 verbatim
noncomputable abbrev IsReflexive := @_root_.OAI.RecursivePotentials.IsReflexive


-- @@ L572-572 verbatim
namespace SquareSum


-- @@ L574-575 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]


-- @@ L577-577 verbatim
noncomputable abbrev Space := @_root_.OAI.RecursivePotentials.SquareSum.Space


-- @@ L579-579 verbatim
end SquareSum


-- @@ L581-581 verbatim
end


-- @@ L583-583 verbatim
open UniformSpace


-- @@ L585-585 verbatim
section


-- @@ L587-587 verbatim
noncomputable abbrev completionEquivOfDense := @_root_.OAI.RecursivePotentials.completionEquivOfDense


-- @@ L589-589 verbatim
end


-- @@ L591-591 verbatim
noncomputable abbrev componentTree := @_root_.OAI.RecursivePotentials.componentTree


-- @@ L593-593 verbatim
section


-- @@ L595-595 verbatim
noncomputable abbrev logarithmicGamma := @_root_.OAI.RecursivePotentials.logarithmicGamma


-- @@ L597-597 verbatim
end


-- @@ L599-599 verbatim
open Filter


-- @@ L601-601 verbatim
open scoped Topology


-- @@ L603-608 verbatim
def XJoined_separated_familiesStatement : Prop := ∀ {ε : ℝ} (_ : 0 < ε),
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      (ε ≤ 2 → η = min (1/2) (logarithmicGamma 2 (ε/16))) ∧
      ∀ (x : XJoined) (z : ℕ → XJoined),
        (∀ n, ‖x+z n‖ ≤ 1) → (∀ n, ‖x-z n‖ ≤ 1) →
        (∀ i j, i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖ ≤ 1-η


-- @@ L610-610 verbatim
noncomputable abbrev ChildExponent := @_root_.OAI.RecursivePotentials.ChildExponent


-- @@ L612-612 verbatim
namespace VariableExponent


-- @@ L614-614 verbatim
noncomputable abbrev heightExponent := @_root_.OAI.RecursivePotentials.VariableExponent.heightExponent


-- @@ L616-616 verbatim
noncomputable abbrev cubicConstant := @_root_.OAI.RecursivePotentials.VariableExponent.cubicConstant


-- @@ L618-618 verbatim
noncomputable abbrev sixthConstant := @_root_.OAI.RecursivePotentials.VariableExponent.sixthConstant


-- @@ L620-620 verbatim
end VariableExponent


-- @@ L622-622 verbatim
namespace VariableTree


-- @@ L624-624 verbatim
open FiniteRootedTree


-- @@ L626-627 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)


-- @@ L629-631 verbatim
noncomputable def P (v : ι →₀ ℝ) : ι →₀ ℝ :=
  extend (T.head v) (fun s => ((T.restrict (T.head v) (FiniteRootedTree.Heads.initial T v)).pfields e
    (fun s => v s.1) s).1)


-- @@ L633-635 verbatim
noncomputable def Q (v : ι →₀ ℝ) : ι →₀ ℝ :=
  extend (T.head v) (fun s => ((T.restrict (T.head v) (FiniteRootedTree.Heads.initial T v)).pfields e
    (fun s => v s.1) s).2)


-- @@ L637-637 verbatim
noncomputable def normSum (v : ι →₀ ℝ) : ℝ := P T e v T.root + Q T e v T.root


-- @@ L639-639 verbatim
end VariableTree


-- @@ L641-641 verbatim
def AggregationVector {ι : Type uIndex} (_T : FiniteRootedTree ι) (_e : ChildExponent) := ι →₀ ℝ


-- @@ L643-643 verbatim
namespace AggregationVector


-- @@ L645-646 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)


-- @@ L648-648 verbatim
instance : AddCommGroup (AggregationVector T e) := inferInstanceAs (AddCommGroup (ι →₀ ℝ))


-- @@ L650-650 verbatim
instance : Module ℝ (AggregationVector T e) := inferInstanceAs (Module ℝ (ι →₀ ℝ))


-- @@ L652-652 verbatim
instance : CoeFun (AggregationVector T e) (fun _ => ι → ℝ) := ⟨fun v => (show ι →₀ ℝ from v)⟩


-- @@ L654-654 verbatim
noncomputable instance : Norm (AggregationVector T e) := ⟨fun v => VariableTree.normSum T e v⟩


-- @@ L656-660 verbatim
class Construction : Prop where
  core : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) (e : ChildExponent),
    NormedSpace.Core ℝ (AggregationVector T e)
  coordinate_bound : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent) (v : ι →₀ ℝ) (s : ι), |v s| ≤ VariableTree.normSum T e v


-- @@ L662-662 verbatim
variable [ComparatorModel.RecursivePotentials.AggregationVector.Construction]


-- @@ L664-665 verbatim
noncomputable instance : NormedAddCommGroup (AggregationVector T e) :=
  NormedAddCommGroup.ofCore (AggregationVector.Construction.core T e)


-- @@ L667-667 verbatim
noncomputable instance : NormedSpace ℝ (AggregationVector T e) := NormedSpace.ofCore (AggregationVector.Construction.core T e)


-- @@ L669-672 verbatim
def coordinateLinear (s : ι) : AggregationVector T e →ₗ[ℝ] ℝ where
  toFun v := v s
  map_add' _v _w := rfl
  map_smul' _a _v := rfl


-- @@ L674-678 verbatim
noncomputable def coordinate (s : ι) : AggregationVector T e →L[ℝ] ℝ :=
  (coordinateLinear T e s).mkContinuous 1 (fun v => by
    change ‖v s‖ ≤ 1 * VariableTree.normSum T e v
    rw [Real.norm_eq_abs, one_mul]
    exact AggregationVector.Construction.coordinate_bound T e v s)


-- @@ L680-680 verbatim
end AggregationVector


-- @@ L682-682 verbatim
variable [ComparatorModel.RecursivePotentials.AggregationVector.Construction]


-- @@ L684-686 verbatim
abbrev AggregationSpace {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent) :=
  UniformSpace.Completion (AggregationVector T e)


-- @@ L688-688 verbatim
namespace AggregationSpace


-- @@ L690-690 verbatim
open UniformSpace


-- @@ L692-693 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)


-- @@ L695-696 verbatim
def coordinate (s : ι) :
    AggregationSpace T e →L[ℝ] ℝ := (AggregationVector.coordinate T e s).fromCompletion


-- @@ L698-699 verbatim
def P (s : ι) : AggregationSpace T e → ℝ :=
  Completion.extension (fun v : AggregationVector T e => VariableTree.P T e v s)


-- @@ L701-702 verbatim
def Q (s : ι) : AggregationSpace T e → ℝ :=
  Completion.extension (fun v : AggregationVector T e => VariableTree.Q T e v s)


-- @@ L704-704 verbatim
end AggregationSpace


-- @@ L706-706 verbatim
namespace AggregationVector


-- @@ L708-709 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)


-- @@ L711-711 verbatim
def basisVector (s : ι) : AggregationVector T e := Finsupp.single s 1


-- @@ L713-713 verbatim
end AggregationVector


-- @@ L715-715 verbatim
open Filter Topology TopologicalSpace


-- @@ L717-717 verbatim
open scoped ENNReal


-- @@ L719-719 verbatim
namespace ChildExponent


-- @@ L721-722 verbatim
instance (e : ChildExponent) : Fact (1 ≤ ENNReal.ofReal e.val) :=
  ⟨by simpa using ENNReal.ofReal_le_ofReal e.one_le⟩


-- @@ L724-724 verbatim
end ChildExponent


-- @@ L726-726 verbatim
namespace AggregationVector


-- @@ L728-728 verbatim
open scoped ENNReal


-- @@ L730-731 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)


-- @@ L733-733 verbatim
abbrev CoordinateLp (ι : Type uIndex) (e : ChildExponent) := ↥(lp (fun _ : ι => ℝ) (ENNReal.ofReal e.val))


-- @@ L735-736 verbatim
def toLpLinear : AggregationVector T e →ₗ[ℝ] CoordinateLp ι e :=
  Finsupp.lsum ℝ (fun s => lp.lsingle (𝕜 := ℝ) (E := fun _ : ι => ℝ) (ENNReal.ofReal e.val) s)


-- @@ L738-746 verbatim
class LpConstruction : Prop where
  bounds : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent), 1 < e.val →
    (∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1) →
    ∀ h : ℕ, (∀ s, T.depth s ≤ h) → ∀ v : AggregationVector T e,
    ‖v‖ ≤ (2*(h+1:ℝ)^(1-1/e.val))*‖toLpLinear T e v‖ ∧
      ‖toLpLinear T e v‖ ≤ (h+1:ℝ)^(1/e.val)*‖v‖
  dense : ∀ {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent), DenseRange (toLpLinear T e)


-- @@ L748-748 verbatim
variable [ComparatorModel.RecursivePotentials.AggregationVector.LpConstruction]


-- @@ L750-754 verbatim
def toLp (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : AggregationVector T e →L[ℝ] CoordinateLp ι e :=
  (toLpLinear T e).mkContinuous ((h+1:ℝ)^(1/e.val))
    (fun v => (LpConstruction.bounds T e hp hstep h hh v).2)


-- @@ L756-756 verbatim
end AggregationVector


-- @@ L758-758 verbatim
namespace AggregationSpace


-- @@ L760-760 verbatim
open AggregationVector


-- @@ L762-763 verbatim
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)


-- @@ L765-765 verbatim
variable [ComparatorModel.RecursivePotentials.AggregationVector.LpConstruction]


-- @@ L767-773 verbatim
def lpEquiv (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : AggregationSpace T e ≃L[ℝ] CoordinateLp ι e :=
  completionEquivOfDense (AggregationVector.toLp T e hp hstep h hh)
    ⟨2*(h+1:ℝ)^(1-1/e.val),by positivity⟩
    (fun v => (AggregationVector.LpConstruction.bounds T e hp hstep h hh v).1)
    (AggregationVector.LpConstruction.dense T e)


-- @@ L775-775 verbatim
end AggregationSpace


-- @@ L777-777 verbatim
namespace Variable


-- @@ L779-779 verbatim
section


-- @@ L781-781 verbatim
open UniformSpace VariableExponent Filter Topology TopologicalSpace


-- @@ L783-783 verbatim
variable [ComparatorModel.RecursivePotentials.AggregationVector.LpConstruction]


-- @@ L785-788 verbatim
def exponent (h : ℕ+) : ChildExponent := ⟨heightExponent h,(by
  dsimp [heightExponent]
  have hh : (0 : ℝ) < h.val := by exact_mod_cast h.pos
  exact le_add_of_nonneg_right (le_of_lt (one_div_pos.mpr hh)))⟩


-- @@ L790-790 verbatim
abbrev Component (h : ℕ+) := AggregationSpace (componentTree h) (exponent h)


-- @@ L792-792 verbatim
abbrev Xv := SquareSum.Space Component


-- @@ L794-794 verbatim
abbrev Node := Σ h : ℕ+, ComponentNode h


-- @@ L796-807 verbatim
def componentEquiv (h : ℕ+) :
    Component h ≃L[ℝ] AggregationVector.CoordinateLp (ComponentNode h) (exponent h) :=
  AggregationSpace.lpEquiv (componentTree h) (exponent h) (by
      dsimp [exponent, heightExponent]
      have hh : (0 : ℝ) < h.val := by exact_mod_cast h.pos
      exact lt_add_of_pos_right _ (one_div_pos.mpr hh))
    (by
      intro c hc
      change c.1.length = c.1.dropLast.length + 1
      rw [List.length_dropLast]
      have hp := List.length_pos_iff_ne_nil.mpr (show c.1 ≠ [] from fun he => hc (Subtype.ext he))
      omega) h.val (fun c => c.2)


-- @@ L809-810 verbatim
def componentCoordinate (h : ℕ+) (s : ComponentNode h) : Component h →L[ℝ] ℝ :=
  AggregationSpace.coordinate (componentTree h) (exponent h) s


-- @@ L812-813 verbatim
def coordinate (s : Node) : Xv →L[ℝ] ℝ :=
  (componentCoordinate s.1 s.2).comp (lp.evalCLM ℝ Component 2 s.1)


-- @@ L815-816 verbatim
def basis (s : Node) : Xv := lp.single 2 s.1
  ((AggregationVector.basisVector (componentTree s.1) (exponent s.1) s.2 : AggregationVector (componentTree s.1) (exponent s.1)) : Component s.1)


-- @@ L818-818 verbatim
def FiniteTotalSupport (x : Xv) : Prop := ∃ S : Finset Node, ∀ s ∉ S, coordinate s x = 0


-- @@ L820-820 verbatim
def projection (S : Finset Node) : Xv →L[ℝ] Xv := ∑ s ∈ S, (coordinate s).smulRight (basis s)


-- @@ L822-825 verbatim
def AdmissibleHeads (x y : Xv) (A : ∀ h, Finset (ComponentNode h)) : Prop :=
  ∀ h, x h ≠ 0 → (componentTree h).Initial (A h) ∧
    (∀ s ∉ A h, componentCoordinate h s (x h) = 0) ∧
    (∀ s ∈ A h, componentCoordinate h s (y h) = 0)


-- @@ L827-829 verbatim
def cubic_stabilityStatement : Prop := ∀ (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (_ : AdmissibleHeads x y A) {R : ℝ} (_ : 0 < R) (_ : ‖x+y‖ ≤ R) (_ : ‖x-y‖ ≤ R),
    ‖x‖^2+cubicConstant/(2*Real.sqrt 2*R)*‖y‖^3 ≤ R^2


-- @@ L831-833 verbatim
def sixth_stabilityStatement : Prop := ∀ (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (_ : AdmissibleHeads x y A),
    sixthConstant*‖y‖^6/(‖x+y‖^2+‖x-y‖^2)^2 ≤ ‖x+y‖^2+‖x-y‖^2-2*‖x‖^2


-- @@ L835-835 verbatim
def weakTailConstant : ℝ := cubicConstant/(2*Real.sqrt 2)


-- @@ L837-837 verbatim
def theta (ε : ℝ) : ℝ := Real.sqrt (1-weakTailConstant*ε^3)


-- @@ L839-842 verbatim
def weak_tailStatement : Prop := ∀ (x : Xv) {ε : ℝ} (_ : 0 < ε) (_hε1 : ε ≤ 1)
    (y : ℕ → Xv) (_ : WeaklyNull y) (_ : ∀ j, ε ≤ ‖y j‖)
    (_ : ∀ j, ‖x+y j‖ ≤ 1) (_ : ∀ j, ‖x-y j‖ ≤ 1),
    ‖x‖ ≤ theta ε ∧ theta ε < 1


-- @@ L844-844 verbatim
end


-- @@ L846-846 verbatim
open UniformSpace VariableExponent Filter Topology


-- @@ L848-848 verbatim
variable [ComparatorModel.RecursivePotentials.AggregationVector.LpConstruction]


-- @@ L850-851 verbatim
def one_sided_modulus_zeroStatement : Prop := ∀ (A : EquivalentNorm Xv),
    A.modulus (A.lower/A.upper) = 0


-- @@ L853-854 verbatim
def no_equivalent_AUCStatement : Prop := ∀ (A : EquivalentNorm Xv),
    ¬A.AUC


-- @@ L856-856 verbatim
end Variable


-- @@ L858-858 verbatim
variable [ComparatorModel.RecursivePotentials.AggregationVector.LpConstruction]


-- @@ L860-879 verbatim
structure RootSumCompletionStatement {ι : Type uIndex} [DecidableEq ι]
    (T : FiniteRootedTree ι) : Prop where
  complete : CompleteSpace (TreeSpace T)
  infinite_dimensional : ¬Module.Finite ℝ (TreeSpace T)
  coordinate_continuous : ∀ s, Continuous (TreeSpace.coordinate T s)
  coordinate_extends : ∀ s (v : TreeVector T), TreeSpace.coordinate T s (v : TreeSpace T) = v s
  fields_continuous : ∀ s, Continuous (TreeSpace.P T s) ∧ Continuous (TreeSpace.Q T s)
  fields_extend : ∀ s (v : TreeVector T),
    TreeSpace.P T s (v : TreeSpace T) = T.P v s ∧ TreeSpace.Q T s (v : TreeSpace T) = T.Q v s
  root_formula : ∀ x : TreeSpace T, ‖x‖ = TreeSpace.P T T.root x + TreeSpace.Q T T.root x
  projections : ∀ (H : Finset ι) (hH : T.Initial H),
    (∀ x : TreeSpace T, ‖TreeSpace.projection T H hH x‖ ≤ ‖x‖) ∧
    (∀ x : TreeSpace T, TreeSpace.projection T H hH (TreeSpace.projection T H hH x) = TreeSpace.projection T H hH x) ∧
    (∀ (s : ι) (x : TreeSpace T), TreeSpace.coordinate T s (TreeSpace.projection T H hH x) =
      if s ∈ H then TreeSpace.coordinate T s x else 0) ∧
    FiniteDimensional ℝ (TreeSpace.projection T H hH).range ∧
    IsClosed (TreeSpace.tail T H hH : Set (TreeSpace T)) ∧
    Module.Finite ℝ (TreeSpace T ⧸ TreeSpace.tail T H hH) ∧
    ∀ x ∈ TreeSpace.tail T H hH, ∀ ε : ℝ, 0 < ε →
      ∃ v : TreeVector T, TreeVector.projection T H hH v = 0 ∧ ‖(v : TreeSpace T)-x‖ < ε


-- @@ L881-903 verbatim
structure ZeroRootCompletionStatement {ι : Type uIndex} [DecidableEq ι]
    (T : FiniteRootedTree ι) : Prop where
  complete : CompleteSpace (ZeroTreeSpace T)
  infinite_dimensional : ¬Module.Finite ℝ (ZeroTreeSpace T)
  coordinate_continuous : ∀ s, Continuous (ZeroTreeSpace.coordinate T s)
  coordinate_extends : ∀ s (v : ZeroTreeVector T),
    ZeroTreeSpace.coordinate T s (v : ZeroTreeSpace T) = ZeroTreeVector.toTree T v s
  fields_continuous : ∀ s, Continuous (ZeroTreeSpace.P T s) ∧ Continuous (ZeroTreeSpace.Q T s)
  fields_extend : ∀ s (v : ZeroTreeVector T),
    ZeroTreeSpace.P T s (v : ZeroTreeSpace T) = T.P (ZeroTreeVector.toTree T v) s ∧
    ZeroTreeSpace.Q T s (v : ZeroTreeSpace T) = T.Q (ZeroTreeVector.toTree T v) s
  root_fixed : ∀ x : ZeroTreeSpace T, ZeroTreeSpace.coordinate T T.root x = 0
  root_formula : ∀ x : ZeroTreeSpace T, ‖x‖ = ZeroTreeSpace.P T T.root x ∧ ‖x‖ = ZeroTreeSpace.Q T T.root x
  projections : ∀ (H : Finset ι) (hH : T.Initial H),
    (∀ x : ZeroTreeSpace T, ‖ZeroTreeSpace.projection T H hH x‖ ≤ ‖x‖) ∧
    (∀ x : ZeroTreeSpace T, ZeroTreeSpace.projection T H hH (ZeroTreeSpace.projection T H hH x) = ZeroTreeSpace.projection T H hH x) ∧
    (∀ (s : ι) (x : ZeroTreeSpace T), ZeroTreeSpace.coordinate T s (ZeroTreeSpace.projection T H hH x) =
      if s ∈ H then ZeroTreeSpace.coordinate T s x else 0) ∧
    FiniteDimensional ℝ (ZeroTreeSpace.projection T H hH).range ∧
    IsClosed (ZeroTreeSpace.tail T H hH : Set (ZeroTreeSpace T)) ∧
    Module.Finite ℝ (ZeroTreeSpace T ⧸ ZeroTreeSpace.tail T H hH) ∧
    ∀ x ∈ ZeroTreeSpace.tail T H hH, ∀ ε : ℝ, 0 < ε →
      ∃ v : ZeroTreeVector T, ZeroTreeVector.projection T H hH v = 0 ∧ ‖(v : ZeroTreeSpace T)-x‖ < ε


-- @@ L905-907 verbatim
def rec_completionStatement : Prop := RootSumCompletionStatement sequenceTree ∧
    ZeroRootCompletionStatement joinedTree ∧ RootSumCompletionStatement joinedTree ∧
    IsReflexive XZero ∧ IsReflexive XJoined


-- @@ L909-916 verbatim
def rec_mainStatement : Prop := (∀ t : ℝ, 0 < t → t < 1 → t^3/128 ≤ averagedModulus XSigma t ∧ t^3/128 ≤ averagedModulus XJoined t) ∧
    (∀ (H : Finset JoinedNode), joinedTree.Initial H → ∀ x : XZero,
      (∀ s ∉ H, ZeroTreeSpace.coordinate joinedTree s x = 0) → ∀ z : XZero,
      (∀ s ∈ H, ZeroTreeSpace.coordinate joinedTree s z = 0) → z ≠ 0 →
      (‖x+z‖+‖x-z‖)/2 ≥ ‖x‖+‖z‖^3/(8*(2*‖x‖+‖z‖)^2)) ∧
    (∀ A : EquivalentNorm XSigma, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XZero, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XJoined, ¬A.AUC)


-- @@ L918-919 verbatim
def stop_all_radiiStatement : Prop := ∀ {t : ℝ} (_ : 0 < t),
    0 < averagedModulus XSigma t


-- @@ L921-921 verbatim
namespace Variable


-- @@ L923-923 verbatim
open VariableExponent


-- @@ L925-927 verbatim
def nu (h : ℕ+) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)) : ℝ :=
  AggregationSpace.P (componentTree h) (exponent h) (componentTree h).root ((componentEquiv h).symm v) +
  AggregationSpace.Q (componentTree h) (exponent h) (componentTree h).root ((componentEquiv h).symm v)


-- @@ L929-935 verbatim
structure SourceNormStatement (h : ℕ+) : Prop where
  nonneg : ∀ v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h), 0 ≤ nu h v
  definite : ∀ v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h), nu h v = 0 ↔ v = 0
  triangle : ∀ v w : AggregationVector.CoordinateLp (ComponentNode h) (exponent h),
    nu h (v+w) ≤ nu h v + nu h w
  homogeneous : ∀ (a : ℝ) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)),
    nu h (a • v) = |a| * nu h v


-- @@ L937-946 verbatim
def spaceStatement : Prop := (∀ h : ℕ+, CompleteSpace (Component h) ∧ IsReflexive (Component h) ∧
      SeparableSpace (Component h →L[ℝ] ℝ) ∧ SourceNormStatement h ∧
      ∀ v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h),
        (h.val+1:ℝ)^(-1/heightExponent h)*‖v‖ ≤ nu h v ∧
        nu h v ≤ 2*(h.val+1:ℝ)^(1-1/heightExponent h)*‖v‖) ∧
    CompleteSpace Xv ∧ IsReflexive Xv ∧ SeparableSpace (Xv →L[ℝ] ℝ) ∧
    Dense {x : Xv | FiniteTotalSupport x} ∧
    ∀ S : Finset Node, Continuous (projection S) ∧ FiniteDimensional ℝ (projection S).range ∧
      (∀ x : Xv, projection S (projection S x) = projection S x) ∧
      ∀ (s : Node) (x : Xv), coordinate s (projection S x) = if s ∈ S then coordinate s x else 0


-- @@ L948-950 verbatim
def aggregateChildren (h : ℕ+) (s : ComponentNode h) (f : ComponentNode h → ℝ) : ℝ :=
  (∑' c, if c ≠ (componentTree h).root ∧ (componentTree h).parent c = s then
    f c ^ heightExponent h else 0) ^ (1/heightExponent h)


-- @@ L952-955 verbatim
def lpPotentials (h : ℕ+) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h))
    (s : ComponentNode h) : ℝ × ℝ :=
  (AggregationSpace.P (componentTree h) (exponent h) s ((componentEquiv h).symm v),
    AggregationSpace.Q (componentTree h) (exponent h) s ((componentEquiv h).symm v))


-- @@ L957-963 verbatim
def lp_model_exactStatement : Prop := ∀ (h : ℕ+)
    (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h))
    (f : ComponentNode h → ℝ × ℝ)
    (_ : ∀ s, f s = leastPair (v s)
      (aggregateChildren h s (fun c => (f c).1))
      (aggregateChildren h s (fun c => (f c).2))),
    f = lpPotentials h v ∧ nu h v = (f (componentTree h).root).1+(f (componentTree h).root).2


-- @@ L965-965 verbatim
end Variable


-- @@ L967-967 verbatim
end RecursivePotentials


-- @@ L969-969 verbatim
end ComparatorModel


-- @@ L971-971 verbatim
namespace ComparatorModel.RecursivePotentials


-- @@ L973-989 verbatim
def MainClaim : Prop :=
  ∃ h0 : FiniteRootedTree.Heads.{0}, letI := h0;
  ∃ h1 : TreeVector.Construction.{0}, letI := h1;
  ∃ h2 : ZeroTreeVector.Construction.{0}, letI := h2;
  ∃ h3 : AggregationVector.Construction.{0}, letI := h3;
  ∃ h4 : AggregationVector.LpConstruction.{0}, letI := h4;
  rec_mainStatement ∧
  rec_completionStatement ∧
  stop_all_radiiStatement ∧
  XJoined_separated_familiesStatement ∧
  Variable.spaceStatement ∧
  Variable.lp_model_exactStatement ∧
  Variable.one_sided_modulus_zeroStatement ∧
  Variable.no_equivalent_AUCStatement ∧
  Variable.sixth_stabilityStatement ∧
  Variable.cubic_stabilityStatement ∧
  Variable.weak_tailStatement


-- @@ L991-991 verbatim
end ComparatorModel.RecursivePotentials


-- @@ L993-993 verbatim
end


-- @@ L995-995 verbatim
end OAI
