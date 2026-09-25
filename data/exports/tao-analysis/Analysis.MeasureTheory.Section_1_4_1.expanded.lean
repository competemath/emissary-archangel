import Mathlib.Order.BooleanAlgebra.Defs

import Analysis.MeasureTheory.Section_1_3_5


-- @@ L5-10 verbatim
/-!
# Introduction to Measure Theory, Section 1.4.1: Boolean algebras

A companion to (the introduction to) Section 1.4.1 of the book "An introduction to Measure Theory".

-/


-- @@ L12-17 verbatim
/-- Definition 1.4.1 -/
class ConcreteBooleanAlgebra (X:Type*) where
  measurable : Set X → Prop
  empty_mem : measurable (∅ : Set X)
  compl_mem : ∀ E, measurable E → measurable Eᶜ
  union_mem : ∀ E F, measurable E → measurable F → measurable (E ∪ F)


-- @@ L19-20 verbatim
instance ConcreteBooleanAlgebra.instLE (X:Type*) : LE (ConcreteBooleanAlgebra X) :=
  ⟨fun B1 B2 => ∀ E, B1.measurable E → B2.measurable E⟩


-- @@ L22-27 verbatim
instance ConcreteBooleanAlgebra.instPartialOrder (X:Type*) : PartialOrder (ConcreteBooleanAlgebra X) :=
  {
    le_refl := sorry
    le_trans := sorry
    le_antisymm := sorry
  }


-- @@ L29-30 verbatim
def ConcreteBooleanAlgebra.measurableSets {X:Type*} (B: ConcreteBooleanAlgebra X) : Set (Set X) :=
  { E | B.measurable E }


-- @@ L32-42 verbatim
/-- Example 1.4.3 (the largest algebra) -/
instance ConcreteBooleanAlgebra.instOrderTop {X:Type*} : OrderTop (ConcreteBooleanAlgebra X) :=
  {
    top := {
      measurable := fun _ => True
      empty_mem := trivial
      compl_mem := fun _ _ => trivial
      union_mem := fun _ _ _ _ => trivial
    }
    le_top := sorry
  }


-- @@ L44-54 verbatim
/-- Example 1.4.3 (the smallest algebra) -/
instance ConcreteBooleanAlgebra.instOrderBot {X:Type*} : OrderBot (ConcreteBooleanAlgebra X) :=
  {
    bot := {
      measurable := fun E => E = ∅ ∨ E = Set.univ
      empty_mem := by grind
      compl_mem := fun E hE => by grind
      union_mem := fun E F hE hF => by grind
    }
    bot_le := sorry
  }


-- @@ L56-63 verbatim
/-- Exercise 1.4.1 (Elementary algebra) -/
def EuclideanSpace'.elementary_boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => IsElementary E ∨ IsElementary Eᶜ
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }


-- @@ L65-72 verbatim
/-- Example 1.4.4 (Jordan algebra) -/
def JordanMeasurable.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => JordanMeasurable E ∨ JordanMeasurable Eᶜ
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }


-- @@ L74-76 verbatim
def JordanMeasurable.gt_elementary_boolean_algebra (d:ℕ) :
  JordanMeasurable.boolean_algebra d ≥ EuclideanSpace'.elementary_boolean_algebra d :=
  by sorry


-- @@ L78-85 verbatim
/-- Example 1.4.5 (Lebesgue algebra) -/
def LebesgueMeasurable.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => LebesgueMeasurable E
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }


-- @@ L87-89 verbatim
def LebesgueMeasurable.gt_jordan_boolean_algebra (d:ℕ) :
  LebesgueMeasurable.boolean_algebra d ≥ JordanMeasurable.boolean_algebra d :=
  by sorry


-- @@ L91-98 verbatim
/-- Example 1.4.6 (Null algebra) -/
def IsNull.boolean_algebra (d:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  {
    measurable := fun E => IsNull E ∨ IsNull Eᶜ
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }


-- @@ L100-102 verbatim
def IsNull.lt_lebesgue_boolean_algebra (d:ℕ) :
  IsNull.boolean_algebra d ≤ LebesgueMeasurable.boolean_algebra d :=
  by sorry


-- @@ L104-111 verbatim
/-- Exercise 1.4.2 (Restriction) -/
def ConcreteBooleanAlgebra.restrict {X:Type*} (B: ConcreteBooleanAlgebra X) (A:Set X) : ConcreteBooleanAlgebra A :=
  {
    measurable := fun E => ∃ E' : Set X, B.measurable E' ∧ E = Subtype.val ⁻¹' E'
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }


-- @@ L113-115 verbatim
def ConcreteBooleanAlgebra.restrict_iff {X:Type*} {B: ConcreteBooleanAlgebra X} {A:Set X} (h: B.measurable A) (E: Set A) :
  (B.restrict A).measurable E ↔ B.measurable (Subtype.val '' E) :=
  by sorry


-- @@ L117-136 verbatim
/-- Remark 1.4.2: {name}`ConcreteBooleanAlgebra`s are {name}`BooleanAlgebra`s -/
def ConcreteBooleanAlgebra.toBooleanAlgebra {X:Type*} (B: ConcreteBooleanAlgebra X) : BooleanAlgebra (B.measurableSets) :=
{
   sup := sorry
   le_sup_left := sorry
   le_sup_right := sorry
   sup_le := sorry
   inf := sorry
   inf_le_left := sorry
   inf_le_right := sorry
   le_inf := sorry
   le_sup_inf := sorry
   compl := sorry
   top := sorry
   bot := sorry
   inf_compl_le_bot := sorry
   top_le_sup_compl := sorry
   le_top := sorry
   bot_le := sorry
}


-- @@ L138-138 verbatim
def IsPartition {I X:Type*} (parts: I → Set X) : Prop := (Set.PairwiseDisjoint Set.univ parts) ∧ (⋃ i, parts i = Set.univ)


-- @@ L140-147 verbatim
/-- Example 1.4.7 (Atomic algebra) -/
def IsPartition.to_ConcreteBooleanAlgebra {I X: Type*} {atoms: I → Set X} (h_part: IsPartition atoms) : ConcreteBooleanAlgebra X :=
  {
    measurable := fun E => ∃ J: Set I, E = ⋃ i ∈ J, atoms i
    empty_mem := by sorry
    compl_mem := by sorry
    union_mem := by sorry
  }


-- @@ L149-149 verbatim
def IsPartition.discrete (X:Type*) : IsPartition (fun x:X ↦ {x}) := by sorry


-- @@ L151-151 verbatim
def ConcreteBooleanAlgebra.top_atomic (X:Type*) : (IsPartition.discrete X).to_ConcreteBooleanAlgebra = ⊤ := by sorry


-- @@ L153-153 verbatim
def IsPartition.trivial (X:Type*) : IsPartition (fun (x:Unit) ↦ (Set.univ: Set X)) := by sorry


-- @@ L155-155 verbatim
def ConcreteBooleanAlgebra.bot_atomic (X:Type*) : (IsPartition.trivial X).to_ConcreteBooleanAlgebra = ⊥ := by sorry


-- @@ L157-159 verbatim
def IsPartition.finer_than {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (_: IsPartition parts_I) (_: IsPartition parts_J) : Prop :=
  ∀ i:I, ∃ j:J, parts_I i ⊆ parts_J j


-- @@ L161-165 verbatim
def IsPartition.mono {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (hI: IsPartition parts_I) (hJ: IsPartition parts_J)
  (h_finer: hI.finer_than hJ) :
  hI.to_ConcreteBooleanAlgebra ≥ hJ.to_ConcreteBooleanAlgebra :=
  by sorry


-- @@ L167-168 verbatim
def IsPartition.remove_empty {I X:Type*} {parts: I → Set X} (h_part: IsPartition parts) : IsPartition (fun (i:{i:I // parts i ≠ ∅}) ↦ parts i.val) :=
  by sorry


-- @@ L170-173 verbatim
def IsPartition.remove_empty_to_ConcreteBooleanAlgebra {I X:Type*} {parts: I → Set X} (h_part: IsPartition parts) :
  h_part.to_ConcreteBooleanAlgebra =
  h_part.remove_empty.to_ConcreteBooleanAlgebra :=
  by sorry


-- @@ L175-176 verbatim
/-- A variant of {name}`DyadicCube` with {name}`BoundedInterval.Ico` intervals -/
noncomputable def DyadicCube' {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : Box d := { side := fun i ↦ BoundedInterval.Ico (a i/2^n) ((a i + 1)/2^n) }


-- @@ L178-180 verbatim
/-- Example 1.4.8 -/
def DyadicCube'.partition (d n:ℕ) : IsPartition (fun (a: Fin d → ℤ) ↦ (DyadicCube' n a).toSet) :=
  by sorry


-- @@ L182-183 verbatim
def DyadicCube'.boolean_algebra (d n:ℕ) : ConcreteBooleanAlgebra (EuclideanSpace' d) :=
  (DyadicCube'.partition d n).to_ConcreteBooleanAlgebra


-- @@ L185-186 verbatim
def DyadicCube'.boolean_algebra_mono (d:ℕ) {m n:ℕ} (h: m ≤ n) :
  DyadicCube'.boolean_algebra d m ≤ DyadicCube'.boolean_algebra d n := by sorry


-- @@ L188-188 verbatim
def IsPartition.relabels {I J X:Type*} {parts_I: I → Set X} (_: IsPartition parts_I) {parts_J : J → Set X} (_: IsPartition parts_J) : Prop := ∃ e : I ≃ J, ∀ i:I, parts_I i = parts_J (e i)


-- @@ L190-192 verbatim
/-- Exercise 1.4.3 (Non-empty atoms of an atomic algebra determined up to relabeling) -/
def IsPartition.boolean_algebra_eq_iff {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (hI: IsPartition parts_I) (hJ: IsPartition parts_J) : hI.to_ConcreteBooleanAlgebra = hJ.to_ConcreteBooleanAlgebra ↔ hI.remove_empty.relabels hJ.remove_empty := by sorry


-- @@ L194-194 verbatim
def IsPartition.no_empty {I X:Type*} {parts: I → Set X} (_: IsPartition parts) : Prop := ∀ i:I, parts i ≠ ∅


-- @@ L196-197 verbatim
def IsPartition.boolean_algebra_eq_iff' {I J X:Type*} {parts_I: I → Set X} {parts_J: J → Set X}
  (hI: IsPartition parts_I) (hJ: IsPartition parts_J) (hIn: hI.no_empty) (hJn: hJ.no_empty) : hI.to_ConcreteBooleanAlgebra = hJ.to_ConcreteBooleanAlgebra ↔ hI.relabels hJ := by sorry


-- @@ L199-200 verbatim
def ConcreteBooleanAlgebra.isAtomic {X:Type*} (B: ConcreteBooleanAlgebra X) : Prop :=
  ∃ (I:Type*) (parts: I → Set X) (hI:IsPartition parts), B = hI.to_ConcreteBooleanAlgebra


-- @@ L202-204 verbatim
/-- Exercise 1.4.4 (Finite boolean algebras are atomic) -/
def ConcreteBooleanAlgebra.atomic_of_finite {X:Type*} (B: ConcreteBooleanAlgebra X) (h_fin: (B.measurableSets).Finite) : B.isAtomic :=
  by sorry


-- @@ L206-206 verbatim
def ConcreteBooleanAlgebra.card_of_finite {X:Type*} (B: ConcreteBooleanAlgebra X) (h_fin: (B.measurableSets).Finite) : ∃ n:ℕ, (B.measurableSets).ncard = 2^n := by sorry


-- @@ L208-210 verbatim
/-- Exercise 1.4.5 (elementary algebra not atomic) -/
def EuclideanSpace'.elementary_boolean_algebra_not_atomic (d:ℕ) (hd: d ≥ 1) : ¬ (EuclideanSpace'.elementary_boolean_algebra d).isAtomic :=
  by sorry


-- @@ L212-214 verbatim
/-- Exercise 1.4.5 (Jordan algebra not atomic) -/
def JordanMeasurable.boolean_algebra_not_atomic (d:ℕ) (hd: d ≥ 1) : ¬ (JordanMeasurable.boolean_algebra d).isAtomic :=
  by sorry


-- @@ L216-218 verbatim
/-- Exercise 1.4.5 (Lebesgue algebra not atomic) -/
def LebesgueMeasurable.boolean_algebra_not_atomic (d:ℕ) (hd: d ≥ 1) : ¬ (LebesgueMeasurable.boolean_algebra d).isAtomic :=
  by sorry


-- @@ L220-222 verbatim
/-- Exercise 1.4.5 (Null algebra not atomic) -/
def IsNull.boolean_algebra_not_atomic (d:ℕ) (hd: d ≥ 1) : ¬ (IsNull.boolean_algebra d).isAtomic :=
  by sorry


-- @@ L224-234 verbatim
/-- Exercise 1.4.6 (Intersection of algebras) -/
instance ConcreteBooleanAlgebra.instInfSet {X:Type*} : InfSet (ConcreteBooleanAlgebra X) :=
  {
      sInf S :=
        {
          measurable := fun E => ∀ B ∈ S, B.measurable E
          empty_mem := by sorry
          compl_mem := by sorry
          union_mem := by sorry
        }
  }


-- @@ L236-237 verbatim
def ConcreteBooleanAlgebra.generated_by {X:Type*} (F: Set (Set X)) : ConcreteBooleanAlgebra X :=
  sInf { B | ∀ E ∈ F, B.measurable E }


-- @@ L239-243 verbatim
/-- Definition 1.4.10 (Generation of algebras) -/
instance ConcreteBooleanAlgebra.instSupSet {X:Type*} : SupSet (ConcreteBooleanAlgebra X) :=
  {
      sSup S := ConcreteBooleanAlgebra.generated_by (⋃ B ∈ S, B.measurableSets)
  }


-- @@ L245-259 verbatim
instance ConcreteBooleanAlgebra.instCompleteLattice {X:Type*} : CompleteLattice (ConcreteBooleanAlgebra X) :=
  {
    sup := sorry
    le_sup_left := sorry
    le_sup_right := sorry
    sup_le := sorry
    inf := sorry
    inf_le_left := sorry
    inf_le_right := sorry
    le_inf := sorry
    le_top := sorry
    bot_le := sorry
    isLUB_sSup := sorry
    isGLB_sInf := sorry
  }


-- @@ L261-262 verbatim
/-- Example 1.4.11 -/
instance ConcreteBooleanAlgebra.eq_generated_by_iff {X:Type*} (F: Set (Set X)) : (∃ (B : ConcreteBooleanAlgebra X), B.measurableSets = F) ↔ (ConcreteBooleanAlgebra.generated_by F).measurableSets = F := by sorry


-- @@ L264-266 verbatim
/-- Exercise 1.4.7 (Generation by boxes) -/
instance EuclideanSpace'.elementary_boolean_algebra_generated_by_boxes (d:ℕ) : EuclideanSpace'.elementary_boolean_algebra d =
  ConcreteBooleanAlgebra.generated_by (Box.toSet '' Set.univ) := by sorry


-- @@ L268-271 verbatim
/-- Exercise 1.4.9 (Recursive definition of generated Boolean algebra). -/
def ConcreteBooleanAlgebra.generated_by_eq {X:Type*} (F: Set (Set X)) :
  (ConcreteBooleanAlgebra.generated_by F).measurableSets =
  ⋃ n, Nat.rec (motive := fun _ ↦ Set (Set X)) F (fun n G ↦ { E: Set X | (∃ S: Finset G, E = ⋃ (H:S), H) ∨ (∃ S: Finset G, E = (⋃ (H:S), H)ᶜ) }) n := by sorry

  
