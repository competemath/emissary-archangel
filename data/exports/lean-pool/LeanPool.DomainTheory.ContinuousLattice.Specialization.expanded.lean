/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Order.ScottTopology


-- @@ L11-21 verbatim
/-!
# Specialization order and Scott topology (Scott 1972, §2 opening)

Scott's §2 begins with the specialization order on a `T₀`-space and the induced
(Scott)
topology on a complete lattice. Proposition 2.1 (monotone nets and least upper
bounds) is
split into its two directions; the convergence-to-below direction is the
mathematically
heavier half and is recorded as `proposition_2_1_of_le`.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace Domain.ContinuousLattice


-- @@ L27-27 verbatim
open Topology Set


-- @@ L29-29 verbatim
universe u


-- @@ L31-31 verbatim
variable {X D : Type*} [TopologicalSpace X] [CompleteLattice D]


-- @@ L33-33 verbatim
/-! ### Specialization order -/


-- @@ L35-38 verbatim
/-- **Scott 1972, §2.** The *specialization order*: `x ⊑ y` when `x ∈ U` open
implies `y ∈ U`. -/
def SpecializationLe (x y : X) : Prop :=
  ∀ U, IsOpen U → x ∈ U → y ∈ U


-- @@ L40-43 verbatim
instance specializationPreorder : Preorder X where
  le := SpecializationLe
  le_refl x := fun _ _ hx => hx
  le_trans x y z hxy hyz U hU hxU := hyz U hU (hxy U hU hxU)


-- @@ L45-49 verbatim
theorem specializationLe_antisymm [T0Space X] {x y : X}
    (hxy : SpecializationLe x y) (hyx : SpecializationLe y x) : x = y :=
  Inseparable.eq (inseparable_iff_specializes_and.2
    ⟨specializes_iff_forall_open.2 fun s hs hy => hyx s hs hy,
     specializes_iff_forall_open.2 fun s hs hx => hxy s hs hx⟩)


-- @@ L51-51 verbatim
/-! ### Scott topology from `ScottOpen` -/


-- @@ L53-56 verbatim
/-- Scott's induced topology on a complete lattice, realized as mathlib's Scott
topology. -/
@[reducible] noncomputable def scottTopologicalSpace : TopologicalSpace D :=
  Topology.scott D univ


-- @@ L58-67 verbatim
theorem ScottOpen_iff_dirSupInacc {U : Set D} : ScottOpen U ↔ IsUpperSet U ∧ DirSupInacc U := by
  constructor
  · intro ⟨hU, hU'⟩
    refine ⟨hU, fun d hd₁ hd₂ a ha hmem => ?_⟩
    rw [← IsLUB.sSup_eq ha] at hmem
    simp_all
  · intro ⟨hU, hU'⟩
    refine ⟨hU, fun d hd₁ hd₂ hmem => ?_⟩
    obtain ⟨s, hs, hsU⟩ := hU' hd₁ hd₂ (isLUB_sSup d) hmem
    exact ⟨s, hs, hsU⟩


-- @@ L69-73 verbatim
theorem isOpen_iff_scottOpen {U : Set D} : @IsOpen D scottTopologicalSpace U ↔ ScottOpen U := by
  have inst : @IsScott D univ _ (Topology.scott D univ) :=
    @IsScott.mk D univ _ (Topology.scott D univ) rfl
  rw [ScottOpen_iff_dirSupInacc, ← dirSupInaccOn_univ (s := U)]
  exact @IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn D univ _ (Topology.scott D univ) U inst


-- @@ L75-78 verbatim
/-- Scott-open sets in our sense agree with mathlib's Scott topology (alias). -/
theorem isOpen_scott_iff_scottOpen {U : Set D} :
    @IsOpen D (Topology.scott D univ) U ↔ ScottOpen U :=
  isOpen_iff_scottOpen


-- @@ L80-80 verbatim
/-! ### Monotone nets and Proposition 2.1 -/


-- @@ L82-82 verbatim
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]


-- @@ L84-86 verbatim
/-- A net indexed by a directed preorder that is monotone in the specialization order. -/
def IsMonotoneNet (x : ι → D) : Prop :=
  Monotone x


-- @@ L88-90 verbatim
/-- Scott convergence of a monotone net to a point. -/
def ScottConvergesTo (x : ι → D) (y : D) : Prop :=
  ∀ U, ScottOpen U → y ∈ U → ∃ i, ∀ j ≥ i, x j ∈ U


-- @@ L92-92 verbatim
variable {x : ι → D} {L y : D}


-- @@ L94-109 verbatim
/-- **Scott 1972, Proposition 2.1 (backward).** If `y ≤ L` and `L` is  the lub of
a monotone
net, then the net converges to `y` in the Scott topology. -/
theorem proposition_2_1_of_le [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L)
    (hyL : y ≤ L) : ScottConvergesTo x y := by
  intro U hU hyU
  have hdir : DirectedOn (· ≤ ·) (range x) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := IsDirected.directed (r := (· ≤ ·)) i j
    exact ⟨x k, ⟨k, rfl⟩, hx hik, hx hjk⟩
  have hLU : sSup (range x) ∈ U := by
    rw [IsLUB.sSup_eq hL]
    exact hU.1 hyL hyU
  obtain ⟨s, hsS, hsU⟩ := hU.2 (Set.range_nonempty x) hdir hLU
  obtain ⟨i₀, rfl⟩ := hsS
  refine ⟨i₀, fun j hj => hU.1 (hx hj) hsU⟩


-- @@ L111-121 verbatim
/-- The complement of a principal lower set `Iic L` is Scott-open: it is an upper
set, and it
is inaccessible by directed suprema because if every member of a directed `S` lies
below `L`
then so does `⊔S`. -/
theorem scottOpen_not_le (L : D) : ScottOpen {z : D | ¬ z ≤ L} := by
  refine ⟨fun a b hab ha hb => ha (le_trans hab hb), fun S hSne hSdir hmem => ?_⟩
  by_contra hcon
  refine hmem (sSup_le fun s hs => ?_)
  by_contra hsL
  exact hcon ⟨s, hs, hsL⟩


-- @@ L123-131 verbatim
omit [IsDirected ι (· ≤ ·)] in
/-- **Scott 1972, Proposition 2.1 (forward).** If a monotone net converges to `y`
in the Scott
topology and `L` is its least upper bound, then `y ≤ L`. -/
theorem proposition_2_1_le_of_converges (hL : IsLUB (range x) L)
    (hconv : ScottConvergesTo x y) : y ≤ L := by
  by_contra hyL
  obtain ⟨i, hi⟩ := hconv {z : D | ¬ z ≤ L} (scottOpen_not_le L) hyL
  exact hi i le_rfl (hL.1 ⟨i, rfl⟩)


-- @@ L133-138 verbatim
/-- **Scott 1972, Proposition 2.1.** A monotone net with least upper bound `L`
converges to
`y` in the Scott topology iff `y ⊑ L = ⊔ {xᵢ}`. -/
theorem proposition_2_1 [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L) :
    ScottConvergesTo x y ↔ y ≤ L :=
  ⟨fun hconv => proposition_2_1_le_of_converges hL hconv, proposition_2_1_of_le hx hL⟩


-- @@ L140-140 verbatim
end Domain.ContinuousLattice
