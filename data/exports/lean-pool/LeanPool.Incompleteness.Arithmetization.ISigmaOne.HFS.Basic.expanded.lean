/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Bit
import LeanPool.Incompleteness.Arithmetization.Definability.Init


-- @@ L11-15 verbatim
/-!

# Hereditary Finite Set Theory in $\mathsf{I} \Sigma_1$

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L21-21 verbatim
namespace LO

-- @@ L22-22 verbatim
namespace Arith


-- @@ L24-24 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L26-26 expanded
variable {V : Type*} [ORingStruc V] [ModelsTheory V (iSigma 1)]


-- @@ L28-28 verbatim
@[simp] lemma susbset_insert (x a : V) : a ⊆ insert x a := by intro z hz; simp [hz]


-- @@ L30-30 verbatim
@[simp] lemma bitRemove_susbset (x a : V) : bitRemove x a ⊆ a := by intro z; simp


-- @@ L32-32 expanded
lemma lt_of_mem_dom {x y m : V} (h : pair x y ∈ m) : x < m :=
  lt_of_le_of_lt (by simp) (lt_of_mem h)


-- @@ L34-34 expanded
lemma lt_of_mem_rng {x y m : V} (h : pair x y ∈ m) : y < m :=
  lt_of_le_of_lt (by simp) (lt_of_mem h)


-- @@ L36-40 verbatim
lemma insert_subset_insert_of_subset {a b : V} (x : V) (h : a ⊆ b) : insert x a ⊆ insert x b := by
  intro z hz
  rcases mem_bitInsert_iff.mp hz with (rfl | hz)
  · simp
  · simp [h hz]


-- @@ L42-42 verbatim
section «lp_section_1»


-- @@ L44-51 verbatim
@[simp] lemma under_subset_under_of_le {i j : V} : under i ⊆ under j ↔ i ≤ j :=
  ⟨by intro h; by_contra hij
      have : j < i := by simpa using hij
      simpa using h (mem_under_iff.mpr this),
   by intro hij x
      simp only [mem_under_iff]
      intro hx
      exact lt_of_lt_of_le hx hij⟩


-- @@ L53-53 verbatim
end «lp_section_1»


-- @@ L55-55 verbatim
section «lp_section_2»


-- @@ L57-62 expanded
lemma sUnion_exists_unique (s : V) : ∃! u : V, ∀ x, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) :=
  by
  have : BoldfacePred Sg1 fun x ↦ ∃ t ∈ s, x ∈ t := by
    aesop  (config := { terminal := true })  (rule_sets := [Definability])
  exact
    finite_comprehension₁! this
      ⟨s, fun i ↦ by rintro ⟨t, ht, hi⟩; exact lt_trans (lt_of_mem hi) (lt_of_mem ht)⟩


-- @@ L64-65 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def sUnion (s : V) : V := Classical.choose! (sUnion_exists_unique s)


-- @@ L67-68 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "⋃ʰᶠ " => sUnion


-- @@ L70-71 expanded
@[simp]
lemma mem_sUnion_iff {a b : V} : a ∈ sUnion b ↔ ∃ c ∈ b, a ∈ c :=
  Classical.choose!_spec (sUnion_exists_unique b) a


-- @@ L73-73 expanded
@[simp]
lemma sUnion_empty : (sUnion ∅ : V) = ∅ :=
  mem_ext (by simp)


-- @@ L75-79 expanded
lemma sUnion_lt_of_pos {a : V} (ha : 0 < a) : sUnion a < a :=
  lt_of_lt_log ha
    (by
      simp only [mem_sUnion_iff, forall_exists_index, and_imp]
      intro i x hx hi
      exact lt_of_lt_of_le (lt_of_mem hi) (le_log_of_mem hx))


-- @@ L81-84 expanded
@[simp]
lemma sUnion_le (a : V) : sUnion a ≤ a :=
  by
  rcases zero_le a with (rfl | pos)
  · simp [← emptyset_def]
  · exact le_of_lt (sUnion_lt_of_pos pos)


-- @@ L86-95 expanded
lemma sUnion_graph {u s : V} : u = sUnion s ↔ ∀ x < u + s, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) :=
  ⟨by rintro rfl; simp, by
    intro h; apply mem_ext
    intro x; simp only [mem_sUnion_iff]
    constructor
    · intro hx
      exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · rintro ⟨c, hc, hx⟩
      exact
        h x (lt_of_lt_of_le (lt_trans (lt_of_mem hx) (lt_of_mem hc)) (by simp)) |>.mpr ⟨c, hc, hx⟩⟩


-- @@ L97-99 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.sUnionDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.ballLT (Semiterm.Operator.Add.add.operator ![#0, #1])
      (LogicalConnective.iff (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1])
        (bexIn (#2) (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0]))))
    (by simp)


-- @@ L101-102 expanded
lemma sUnion_defined : DefinedFunction₁ Sg0 ((sUnion ·) : V → V) sUnionDef := by intro v;
  simp [sUnionDef, sUnion_graph]


-- @@ L104-105 expanded
@[simp]
lemma sUnion_defined_iff (v) : Semiformula.Evalbm V v sUnionDef.val ↔ v 0 = sUnion (v 1) :=
  sUnion_defined.df.iff v


-- @@ L107-107 expanded
instance sUnion_definable : BoldfaceFunction₁ Sg0 ((sUnion ·) : V → V) :=
  sUnion_defined.to_definable


-- @@ L109-111 expanded
instance sUnion_definable' (ℌ : HierarchySymbol) : BoldfaceFunction₁ ℌ ((sUnion ·) : V → V) :=
  sUnion_definable.of_zero


-- @@ L113-113 verbatim
end «lp_section_2»


-- @@ L115-115 verbatim
section «lp_section_3»


-- @@ L117-118 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def union (a b : V) : V :=
  sUnion { a, b }


-- @@ L120-121 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instUnionV : Union V := ⟨union⟩


-- @@ L123-123 verbatim
@[simp] lemma mem_cup_iff {a b c : V} : a ∈ b ∪ c ↔ a ∈ b ∨ a ∈ c := by simp [Union.union, union]


-- @@ L125-133 verbatim
private lemma union_graph {u s t : V} : u = s ∪ t ↔ ∀ x < u + s + t, (x ∈ u ↔ x ∈ s ∨ x ∈ t) :=
  ⟨by rintro rfl; simp, by
    intro h; apply mem_ext
    intro x; simp only [mem_cup_iff]
    constructor
    · intro hx; exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp [add_assoc])) |>.mp hx
    · rintro (hx | hx)
      · exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp )) |>.mpr (Or.inl hx)
      · exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp )) |>.mpr (Or.inr hx)⟩


-- @@ L135-137 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.unionDef : Sg0.Semisentence 3 :=
  .mkSigma
    (ball
      (Semiformula.Operator.operator Operator.LT.lt
        ![#0,
          Semiterm.Operator.Add.add.operator ![Semiterm.Operator.Add.add.operator ![#1, #2], #3]])
      (LogicalConnective.iff (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1])
        (Vee.vee (Semiformula.Operator.operator Operator.Mem.mem ![#0, #2])
          (Semiformula.Operator.operator Operator.Mem.mem ![#0, #3]))))
    (by simp)


-- @@ L139-140 expanded
lemma union_defined : DefinedFunction₂ Sg0 ((· ∪ ·) : V → V → V) unionDef := by intro v;
  simp [unionDef, union_graph]


-- @@ L142-143 verbatim
@[simp] lemma union_defined_iff (v) :
    Semiformula.Evalbm V v unionDef.val ↔ v 0 = v 1 ∪ v 2 := union_defined.df.iff v


-- @@ L145-145 expanded
instance union_definable : BoldfaceFunction₂ Sg0 ((· ∪ ·) : V → V → V) :=
  union_defined.to_definable


-- @@ L147-149 expanded
instance union_definable' (ℌ : HierarchySymbol) : BoldfaceFunction₂ ℌ ((· ∪ ·) : V → V → V) :=
  union_definable.of_zero


-- @@ L151-151 verbatim
lemma insert_eq_union_singleton (a s : V) : insert a s = {a} ∪ s := mem_ext (fun x ↦ by simp)


-- @@ L153-165 verbatim
@[simp] lemma union_polybound (a b : V) : a ∪ b ≤ 2 * (a + b) := le_iff_lt_succ.mpr
  <| lt_of_lt_log (by simp) (by
    simp only [mem_cup_iff]; rintro i (hi | hi)
    · calc
        i ≤ log (a + b) := le_trans (le_log_of_mem hi) (log_monotone (by simp))
        _ < log (2 * (a + b)) := by
          simp [log_two_mul_of_pos (show 0 < a + b from by simp [pos_of_nonempty hi])]
        _ ≤ log (2 * (a + b) + 1) := log_monotone (by simp)
    · calc
        i ≤ log (a + b) := le_trans (le_log_of_mem hi) (log_monotone (by simp))
        _ < log (2 * (a + b)) := by
          simp [log_two_mul_of_pos (show 0 < a + b from by simp [pos_of_nonempty hi])]
        _ ≤ log (2 * (a + b) + 1) := log_monotone (by simp))


-- @@ L167-167 expanded
instance : Bounded₂ ((· ∪ ·) : V → V → V) :=
  ⟨Semiterm.Operator.Mul.mul.operator
      ![Semiterm.numeral 2, Semiterm.Operator.Add.add.operator ![#0, #1]],
    fun _ ↦ by simp⟩


-- @@ L169-169 verbatim
lemma union_comm (a b : V) : a ∪ b = b ∪ a := mem_ext (by simp [or_comm])


-- @@ L171-171 verbatim
@[simp] lemma union_succ_union_left (a b : V) : a ⊆ a ∪ b := by intro x hx; simp [hx]


-- @@ L173-173 verbatim
@[simp] lemma union_succ_union_right (a b : V) : b ⊆ a ∪ b := by intro x hx; simp [hx]


-- @@ L175-175 verbatim
@[simp] lemma union_succ_union_union_left (a b c : V) : a ⊆ a ∪ b ∪ c := by intro x hx; simp [hx]


-- @@ L177-177 verbatim
@[simp] lemma union_succ_union_union_right (a b c : V) : b ⊆ a ∪ b ∪ c := by intro x hx; simp [hx]


-- @@ L179-179 verbatim
@[simp] lemma union_empty_eq_right (a : V) : a ∪ ∅ = a := mem_ext <| by simp


-- @@ L181-181 verbatim
@[simp] lemma union_empty_eq_left (a : V) : ∅ ∪ a = a := mem_ext <| by simp


-- @@ L183-183 verbatim
end «lp_section_3»


-- @@ L185-185 verbatim
section «lp_section_4»


-- @@ L187-194 expanded
lemma sInter_exists_unique (s : V) : ∃! u : V, ∀ x, (x ∈ u ↔ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t) :=
  by
  have : BoldfacePred Sg1 fun x ↦ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t := by
    aesop  (config := { terminal := true })  (rule_sets := [Definability])
  exact
    finite_comprehension₁! this
      ⟨s, fun i ↦ by
        rintro ⟨hs, h⟩
        have : log s ∈ s := log_mem_of_pos <| pos_iff_ne_zero.mpr hs
        exact _root_.trans (lt_of_mem <| h (log s) this) (lt_of_mem this)⟩


-- @@ L196-197 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def sInter (s : V) : V := Classical.choose! (sInter_exists_unique s)


-- @@ L199-200 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "⋂ʰᶠ " => sInter


-- @@ L202-203 expanded
lemma mem_sInter_iff {x s : V} : x ∈ sInter s ↔ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t :=
  Classical.choose!_spec (sInter_exists_unique s) x


-- @@ L205-205 expanded
@[simp]
lemma mem_sInter_iff_empty : sInter (∅ : V) = ∅ :=
  mem_ext (by simp [mem_sInter_iff])


-- @@ L207-209 expanded
lemma mem_sInter_iff_of_pos {x s : V} (h : s ≠ ∅) : x ∈ sInter s ↔ ∀ t ∈ s, x ∈ t := by
  simp [mem_sInter_iff, h]


-- @@ L211-211 verbatim
end «lp_section_4»


-- @@ L213-213 verbatim
section «lp_section_5»


-- @@ L215-216 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def inter (a b : V) : V :=
  sInter { a, b }


-- @@ L218-219 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped instance instInterV : Inter V := ⟨inter⟩


-- @@ L221-222 verbatim
@[simp] lemma mem_inter_iff {a b c : V} : a ∈ b ∩ c ↔ a ∈ b ∧ a ∈ c := by
  simp [Inter.inter, inter, mem_sInter_iff_of_pos (s := {b, c}) (nonempty_iff.mpr ⟨b, by simp⟩)]


-- @@ L224-224 verbatim
lemma inter_comm (a b : V) : a ∩ b = b ∩ a := mem_ext (by simp [and_comm])


-- @@ L226-230 verbatim
lemma inter_eq_self_of_subset {a b : V} (h : a ⊆ b) :
  a ∩ b = a := mem_ext (by
    simp only [mem_inter_iff, and_iff_left_iff_imp]
    intro i hi
    exact h hi)


-- @@ L232-232 verbatim
end «lp_section_5»


-- @@ L234-234 verbatim
section «lp_section_6»


-- @@ L236-242 expanded
lemma product_exists_unique (a b : V) : ∃! u : V, ∀ x, (x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = pair y z) :=
  by
  have : BoldfacePred Sg1 fun x ↦ ∃ y ∈ a, ∃ z ∈ b, x = pair y z := by
    aesop  (config := { terminal := true })  (rule_sets := [Definability])
  exact
    finite_comprehension₁! this
      ⟨pair (log a) (log b) + 1, fun i ↦
        by
        rintro ⟨y, hy, z, hz, rfl⟩
        exact lt_succ_iff_le.mpr (pair_le_pair (le_log_of_mem hy) (le_log_of_mem hz))⟩


-- @@ L244-245 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def product (a b : V) : V := Classical.choose! (product_exists_unique a b)


-- @@ L247-248 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:60 " ×ʰᶠ " => product


-- @@ L250-251 expanded
lemma mem_product_iff {x a b : V} : x ∈ product a b ↔ ∃ y ∈ a, ∃ z ∈ b, x = pair y z :=
  Classical.choose!_spec (product_exists_unique a b) x


-- @@ L253-257 expanded
lemma mem_product_iff' {x a b : V} : x ∈ product a b ↔ pi₁ x ∈ a ∧ pi₂ x ∈ b :=
  by
  rw [mem_product_iff]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩; simp [*]
  · rintro ⟨h₁, h₂⟩; exact ⟨pi₁ x, h₁, pi₂ x, h₂, by simp⟩


-- @@ L259-261 expanded
@[simp]
lemma pair_mem_product_iff {x y a b : V} : pair x y ∈ product a b ↔ x ∈ a ∧ y ∈ b := by
  simp [mem_product_iff']


-- @@ L263-264 expanded
lemma pair_mem_product {x y a b : V} (hx : x ∈ a) (hy : y ∈ b) : pair x y ∈ product a b := by
  simpa only [pair_mem_product_iff] using ⟨hx, hy⟩


-- @@ L266-275 expanded
private lemma product_graph {u a b : V} :
    u = product a b ↔ ∀ x < u + (a + b + 1) ^ 2, (x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = pair y z) :=
  ⟨by rintro rfl x _; simp [mem_product_iff], by
    intro h
    apply mem_ext; intro x; simp only [mem_product_iff]
    constructor
    · intro hx; exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact
        h (pair y z)
            (lt_of_lt_of_le (pair_lt_pair (lt_of_mem hy) (lt_of_mem hz))
              (le_trans (pair_polybound a b) <| by simp)) |>.mpr
          ⟨y, hy, z, hz, rfl⟩⟩


-- @@ L277-279 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.productDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.ballLT
      (Semiterm.Operator.Add.add.operator
        ![#0,
          (Semiterm.Operator.npow _ 2).operator
            ![Semiterm.Operator.Add.add.operator
                ![Semiterm.Operator.Add.add.operator ![#1, #2], Semiterm.numeral 1]]])
      (LogicalConnective.iff (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1])
        (bexIn (#2)
          (bexIn (#4)
            (LO.FirstOrder.Rewriting.substitute pairDef
              (vecCons (#2) (vecCons (#1) (vecCons #0 ![]))))))))
    (by simp)


-- @@ L281-282 expanded
lemma product_defined : DefinedFunction₂ Sg0 ((product · ·) : V → V → V) productDef := by intro v;
  simp [productDef, product_graph]


-- @@ L284-285 expanded
@[simp]
lemma product_defined_iff (v) : Semiformula.Evalbm V v productDef.val ↔ v 0 = product (v 1) (v 2) :=
  product_defined.df.iff v


-- @@ L287-287 expanded
instance product_definable : BoldfaceFunction₂ Sg0 ((product · ·) : V → V → V) :=
  product_defined.to_definable


-- @@ L289-291 expanded
instance product_definable' (ℌ : HierarchySymbol) :
    BoldfaceFunction₂ ℌ ((product · ·) : V → V → V) :=
  product_definable.of_zero


-- @@ L293-293 verbatim
end «lp_section_6»


-- @@ L295-295 verbatim
section «lp_section_7»


-- @@ L297-306 expanded
lemma domain_exists_unique (s : V) : ∃! d : V, ∀ x, x ∈ d ↔ ∃ y, pair x y ∈ s :=
  by
  have : BoldfacePred Sg1 fun x ↦ ∃ y, pair x y ∈ s :=
    HierarchySymbol.BoldfacePred.of_iff (Q := fun x ↦ ∃ y < s, pair x y ∈ s)
      (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
      (fun x ↦
        ⟨by rintro ⟨y, hy⟩; exact ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), hy⟩, by
          rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩)
  exact
    finite_comprehension₁! this
      (⟨s, fun x ↦ by rintro ⟨y, hy⟩; exact lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy)⟩)


-- @@ L308-309 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def domain (s : V) : V := Classical.choose! (domain_exists_unique s)


-- @@ L311-312 expanded
lemma mem_domain_iff {x s : V} : x ∈ domain s ↔ ∃ y, pair x y ∈ s :=
  Classical.choose!_spec (domain_exists_unique s) x


-- @@ L314-332 expanded
private lemma domain_graph {u s : V} :
    u = domain s ↔ ∀ x < u + s, (x ∈ u ↔ ∃ y < s, ∃ z ∈ s, z = pair x y) :=
  ⟨by
    rintro rfl x _; simp only [mem_domain_iff]
    exact
      ⟨by
        rintro ⟨y, hy⟩
        exact ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), pair x y, hy, rfl⟩,
        by
        rintro ⟨y, _, z, hz, hz_eq⟩
        rcases hz_eq
        exact ⟨y, hz⟩⟩,
    by
    intro h; apply mem_ext; intro x; simp only [mem_domain_iff]
    constructor
    · intro hx
      rcases h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx with ⟨y, _, z, hy, hz_eq⟩
      rcases hz_eq
      exact ⟨y, hy⟩
    · rintro ⟨y, hy⟩
      exact
        h x (lt_of_lt_of_le (lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy)) (by simp)) |>.mpr
          ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), _, hy, rfl⟩⟩


-- @@ L334-336 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.domainDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.ballLT (Semiterm.Operator.Add.add.operator ![#0, #1])
      (LogicalConnective.iff (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1])
        (Semiformula.bexLT (#2)
          (bexIn (#3)
            (LO.FirstOrder.Rewriting.substitute pairDef
              (vecCons (#0) (vecCons (#2) (vecCons #1 ![]))))))))
    (by simp)


-- @@ L338-339 expanded
lemma domain_defined : DefinedFunction₁ Sg0 (domain : V → V) domainDef := by intro v;
  simp [domainDef, domain_graph]


-- @@ L341-342 verbatim
@[simp] lemma domain_defined_iff (v) :
    Semiformula.Evalbm V v domainDef.val ↔ v 0 = domain (v 1) := domain_defined.df.iff v


-- @@ L344-344 expanded
instance domain_definable : BoldfaceFunction₁ Sg0 (domain : V → V) :=
  domain_defined.to_definable


-- @@ L346-348 expanded
instance domain_definable' (ℌ : HierarchySymbol) : BoldfaceFunction₁ ℌ (domain : V → V) :=
  domain_definable.of_zero


-- @@ L350-350 verbatim
@[simp] lemma domain_empty : domain (∅ : V) = ∅ := mem_ext (by simp [mem_domain_iff])


-- @@ L352-360 verbatim
@[simp] lemma domain_union (a b : V) : domain (a ∪ b) = domain a ∪ domain b := mem_ext (by
  simp only [mem_domain_iff, mem_cup_iff]
  intro x; constructor
  · rintro ⟨y, (hy | hy)⟩
    · left; exact ⟨y, hy⟩
    · right; exact ⟨y, hy⟩
  · rintro (⟨y, hy⟩ | ⟨y, hy⟩)
    · exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr hy⟩)


-- @@ L362-364 expanded
@[simp]
lemma domain_singleton (x y : V) : (domain {pair x y} : V) = { x } :=
  mem_ext (by simp [mem_domain_iff])


-- @@ L366-368 expanded
@[simp]
lemma domain_insert (x y s : V) : domain (insert (pair x y) s) = insert x (domain s) := by
  simp [insert_eq_union_singleton]


-- @@ L370-374 verbatim
@[simp] lemma domain_bound (s : V) : domain s ≤ 2 * s := le_iff_lt_succ.mpr
  <| lt_of_lt_log (by simp) (by
    simp only [mem_domain_iff]; rintro i ⟨x, hix⟩
    exact lt_of_le_of_lt (le_trans (le_pair_left i x) (le_log_of_mem hix))
      (by simp [log_two_mul_add_one_of_pos (pos_of_nonempty hix)]))


-- @@ L376-376 expanded
instance : Bounded₁ (domain : V → V) :=
  ⟨Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #0], fun _ ↦ by simp⟩


-- @@ L378-379 expanded
lemma mem_domain_of_pair_mem {x y s : V} (h : pair x y ∈ s) : x ∈ domain s :=
  mem_domain_iff.mpr ⟨y, h⟩


-- @@ L381-384 verbatim
lemma domain_subset_domain_of_subset {s t : V} (h : s ⊆ t) : domain s ⊆ domain t := by
  intro x hx
  rcases mem_domain_iff.mp hx with ⟨y, hy⟩
  exact mem_domain_iff.mpr ⟨y, h hy⟩


-- @@ L386-389 expanded
@[simp]
lemma domain_eq_empty_iff_eq_empty {s : V} : domain s = ∅ ↔ s = ∅ :=
  ⟨by
    simp only [isempty_iff, mem_domain_iff]
    intro h x hx
    exact h (pi₁ x) ⟨pi₂ x, by simpa using hx⟩, by rintro rfl; simp⟩


-- @@ L392-392 verbatim
end «lp_section_7»


-- @@ L394-394 verbatim
/-! ### Range -/


-- @@ L396-396 verbatim
section «lp_section_8»


-- @@ L398-407 expanded
lemma range_exists_unique (s : V) : ∃! r : V, ∀ y, y ∈ r ↔ ∃ x, pair x y ∈ s :=
  by
  have : BoldfacePred Sg1 fun y ↦ ∃ x, pair x y ∈ s :=
    HierarchySymbol.BoldfacePred.of_iff (Q := fun y ↦ ∃ x < s, pair x y ∈ s)
      (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
      (fun y ↦
        ⟨by rintro ⟨x, hy⟩; exact ⟨x, lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy), hy⟩, by
          rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩)
  exact
    finite_comprehension₁! this
      (⟨s, fun y ↦ by rintro ⟨x, hx⟩; exact lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hx)⟩)


-- @@ L410-411 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def range (s : V) : V := Classical.choose! (range_exists_unique s)


-- @@ L413-414 expanded
lemma mem_range_iff {y s : V} : y ∈ range s ↔ ∃ x, pair x y ∈ s :=
  Classical.choose!_spec (range_exists_unique s) y


-- @@ L416-434 expanded
private lemma range_graph {s' s : V} :
    s' = range s ↔ ∀ y < s' + s, (y ∈ s' ↔ ∃ x < s, ∃ z ∈ s, z = pair x y) :=
  ⟨by
    rintro rfl y _; simp only [mem_range_iff]
    exact
      ⟨by
        rintro ⟨x, hx⟩
        exact ⟨x, lt_of_mem_dom hx, pair x y, hx, rfl⟩,
        by
        rintro ⟨x, _, z, hz, hz_eq⟩
        rcases hz_eq
        exact ⟨x, hz⟩⟩,
    by
    intro h; apply mem_ext; intro y; simp only [mem_range_iff]
    constructor
    · intro hy
      rcases h y (lt_of_lt_of_le (lt_of_mem hy) (by simp)) |>.mp hy with ⟨x, _, z, hx, hz_eq⟩
      rcases hz_eq
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      exact
        h y (lt_of_lt_of_le (lt_of_mem_rng hx) (by simp)) |>.mpr ⟨x, lt_of_mem_dom hx, _, hx, rfl⟩⟩


-- @@ L436-438 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.rangeDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.ballLT (Semiterm.Operator.Add.add.operator ![#0, #1])
      (LogicalConnective.iff (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1])
        (Semiformula.bexLT (#2)
          (bexIn (#3)
            (LO.FirstOrder.Rewriting.substitute pairDef
              (vecCons (#0) (vecCons (#1) (vecCons #2 ![]))))))))
    (by simp)


-- @@ L440-441 expanded
lemma range_defined : DefinedFunction₁ Sg0 (range : V → V) rangeDef := by intro v;
  simp [rangeDef, range_graph]


-- @@ L443-444 verbatim
@[simp] lemma range_defined_iff (v) :
    Semiformula.Evalbm V v rangeDef.val ↔ v 0 = range (v 1) := range_defined.df.iff v


-- @@ L446-446 expanded
instance range_definable : BoldfaceFunction₁ Sg0 (range : V → V) :=
  range_defined.to_definable


-- @@ L448-450 expanded
instance range_definable' (ℌ : HierarchySymbol) : BoldfaceFunction₁ ℌ (range : V → V) :=
  range_definable.of_zero


-- @@ L452-452 verbatim
@[simp] lemma range_empty : range (∅ : V) = ∅ := mem_ext (by simp [mem_range_iff])


-- @@ L454-454 verbatim
end «lp_section_8»


-- @@ L456-456 verbatim
/-! ### Disjoint -/


-- @@ L458-458 verbatim
section «lp_section_9»


-- @@ L460-461 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Disjoint (s t : V) : Prop := s ∩ t = ∅


-- @@ L463-465 verbatim
lemma _root_.LO.Arith.Disjoint.iff {s t : V} :
    Disjoint s t ↔ ∀ x, x ∉ s ∨ x ∉ t := by
  simp [Disjoint, isempty_iff, imp_iff_not_or]


-- @@ L467-469 verbatim
lemma _root_.LO.Arith.Disjoint.not_of_mem {s t x : V} (hs : x ∈ s) (ht : x ∈ t) :
    ¬Disjoint s t := by
  simpa only [Disjoint.iff, not_forall, not_or, not_not] using ⟨x, hs, ht⟩


-- @@ L471-473 verbatim
lemma _root_.LO.Arith.Disjoint.symm {s t : V} (h : Disjoint s t) :
    Disjoint t s := by
  simpa [Disjoint, inter_comm t s] using h


-- @@ L475-477 verbatim
@[simp] lemma _root_.LO.Arith.Disjoint.singleton_iff {a : V} : Disjoint ({a} :
    V) s ↔ a ∉ s := by
  simp [Disjoint, isempty_iff]


-- @@ L479-479 verbatim
end «lp_section_9»


-- @@ L481-481 verbatim
/-! ### Mapping -/


-- @@ L483-483 verbatim
section «lp_section_10»


-- @@ L485-486 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def IsMapping (m : V) : Prop :=
  ∀ x ∈ domain m, ∃! y, pair x y ∈ m


-- @@ L488-488 verbatim
section «lp_section_11»


-- @@ L490-498 expanded
private lemma isMapping_iff {m : V} :
    IsMapping m ↔
      ∃ d ≤ 2 * m,
        d = domain m ∧ ∀ x ∈ d, ∃ y < m, pair x y ∈ m ∧ ∀ y' < m, pair x y' ∈ m → y' = y :=
  ⟨by
    intro hm
    exact
      ⟨domain m, by simp, rfl, fun x hx ↦
        by
        rcases hm x hx with ⟨y, hy, uniq⟩
        exact ⟨y, lt_of_mem_rng hy, hy, fun y' _ h' ↦ uniq y' h'⟩⟩,
    by
    rintro ⟨_, _, rfl, h⟩ x hx
    rcases h x hx with ⟨y, _, hxy, h⟩
    exact ExistsUnique.intro y hxy (fun y' hxy' ↦ h y' (lt_of_mem_rng hxy') hxy')⟩


-- @@ L500-503 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.isMappingDef : Sg0.Semisentence 1 :=
  .mkSigma
    (Semiformula.bexLTSucc (Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #0])
      (Wedge.wedge (LO.FirstOrder.Rewriting.substitute domainDef (vecCons (#0) (vecCons #1 ![])))
        (ballIn (#0)
          (Semiformula.bexLT (#2)
            (Wedge.wedge (memRelOpr.operator ![#3, #1, #0])
              (Semiformula.ballLT (#3)
                (Arrow.arrow (memRelOpr.operator ![#4, #2, #0])
                  (Semiformula.Operator.operator Operator.Eq.eq ![#0, #1]))))))))
    (by simp)


-- @@ L505-506 expanded
lemma isMapping_defined : DefinedPred Sg0 (IsMapping : V → Prop) isMappingDef := by intro v;
  simp [isMappingDef, isMapping_iff]


-- @@ L508-509 verbatim
@[simp] lemma isMapping_defined_iff (v) :
    Semiformula.Evalbm V v isMappingDef.val ↔ IsMapping (v 0) := isMapping_defined.df.iff v


-- @@ L511-513 expanded
instance isMapping_definable : BoldfacePred Sg0 (IsMapping : V → Prop) :=
  isMapping_defined.to_definable


-- @@ L515-517 expanded
instance isMapping_definable' (ℌ) : BoldfacePred ℌ (IsMapping : V → Prop) :=
  isMapping_definable.of_zero


-- @@ L519-519 verbatim
end «lp_section_11»


-- @@ L521-524 expanded
lemma _root_.LO.Arith.IsMapping.get_exists_uniq {m : V} (h : IsMapping m) {x : V}
    (hx : x ∈ domain m) : ∃! y, pair x y ∈ m :=
  h x hx


-- @@ L526-528 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.IsMapping.get {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m) : V :=
  Classical.choose! (IsMapping.get_exists_uniq h hx)


-- @@ L530-532 expanded
@[simp]
lemma _root_.LO.Arith.IsMapping.get_mem {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m) :
    pair x (h.get hx) ∈ m :=
  Classical.choose!_spec (IsMapping.get_exists_uniq h hx)


-- @@ L534-537 expanded
lemma _root_.LO.Arith.IsMapping.get_uniq {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m)
    (hy : pair x y ∈ m) : y = h.get hx :=
  (h x hx).unique hy (by simp)


-- @@ L539-539 verbatim
@[simp] lemma _root_.LO.Arith.IsMapping.empty : IsMapping (∅ : V) := by intro x; simp


-- @@ L541-555 verbatim
lemma _root_.LO.Arith.IsMapping.union_of_disjoint_domain {m₁ m₂ : V}
    (h₁ : IsMapping m₁) (h₂ : IsMapping m₂)
    (disjoint : Disjoint (domain m₁) (domain m₂)) : IsMapping (m₁ ∪ m₂) := by
  intro x
  simp only [domain_union, mem_cup_iff]; rintro (hx | hx)
  · exact ExistsUnique.intro (h₁.get hx) (by simp) (by
      intro y
      rintro (hy | hy)
      · exact h₁.get_uniq hx hy
      · by_contra; exact Disjoint.not_of_mem hx (mem_domain_of_pair_mem hy) disjoint)
  · exact ExistsUnique.intro (h₂.get hx) (by simp) (by
      intro y
      rintro (hy | hy)
      · by_contra; exact Disjoint.not_of_mem hx (mem_domain_of_pair_mem hy) disjoint.symm
      · exact h₂.get_uniq hx hy)


-- @@ L557-559 expanded
@[simp]
lemma _root_.LO.Arith.IsMapping.singleton (x y : V) : IsMapping ({pair x y} : V) :=
  by
  intro x
  simp_all


-- @@ L561-564 expanded
lemma _root_.LO.Arith.IsMapping.insert {x y m : V} (h : IsMapping m) (disjoint : x ∉ domain m) :
    IsMapping (insert (pair x y) m) :=
  by
  rw [insert_eq_union_singleton]
  exact IsMapping.union_of_disjoint_domain (by simp) h (by simpa)


-- @@ L566-571 expanded
lemma _root_.LO.Arith.IsMapping.of_subset {m m' : V} (h : IsMapping m) (ss : m' ⊆ m) :
    IsMapping m' := fun x hx ↦
  by
  rcases mem_domain_iff.mp hx with ⟨y, hy⟩
  have : ∃! y, pair x y ∈ m := h x (domain_subset_domain_of_subset ss hx)
  exact ExistsUnique.intro y hy (fun y' hy' ↦ this.unique (ss hy') (ss hy))


-- @@ L573-576 expanded
lemma _root_.LO.Arith.IsMapping.uniq {m x y₁ y₂ : V} (h : IsMapping m) :
    pair x y₁ ∈ m → pair x y₂ ∈ m → y₁ = y₂ := fun h₁ h₂ ↦
  h x (mem_domain_iff.mpr ⟨y₁, h₁⟩) |>.unique h₁ h₂


-- @@ L579-579 verbatim
end «lp_section_10»


-- @@ L581-581 verbatim
/-! ### Restriction of mapping -/


-- @@ L583-583 verbatim
section «lp_section_12»


-- @@ L585-589 expanded
lemma restr_exists_unique (f s : V) : ∃! g : V, ∀ x, (x ∈ g ↔ x ∈ f ∧ pi₁ x ∈ s) :=
  by
  have : BoldfacePred Sg1 fun x ↦ x ∈ f ∧ pi₁ x ∈ s := by
    aesop  (config := { terminal := true })  (rule_sets := [Definability])
  exact finite_comprehension₁! this ⟨f, fun i ↦ by rintro ⟨hi, _⟩; exact lt_of_mem hi⟩


-- @@ L591-592 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def restr (f s : V) : V := Classical.choose! (restr_exists_unique f s)


-- @@ L594-595 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped infix:80 " ↾ " => restr


-- @@ L597-598 expanded
lemma mem_restr_iff {x f s : V} : x ∈ f ↾ s ↔ x ∈ f ∧ pi₁ x ∈ s :=
  Classical.choose!_spec (restr_exists_unique f s) x


-- @@ L600-602 expanded
@[simp]
lemma pair_mem_restr_iff {x y f s : V} : pair x y ∈ f ↾ s ↔ pair x y ∈ f ∧ x ∈ s := by
  simp [mem_restr_iff]


-- @@ L604-604 verbatim
@[simp] lemma restr_empty (f : V) : f ↾ ∅ = ∅ := mem_ext (by simp [mem_restr_iff])


-- @@ L606-606 verbatim
@[simp] lemma restr_subset_self (f s : V) : f ↾ s ⊆ f := fun _ hx ↦ (mem_restr_iff.mp hx).1


-- @@ L608-608 verbatim
@[simp] lemma restr_le_self (f s : V) : f ↾ s ≤ f := le_of_subset (by simp)


-- @@ L610-611 verbatim
lemma _root_.LO.Arith.IsMapping.restr {m : V} (h : IsMapping m) (s : V) : IsMapping (m ↾ s) :=
  h.of_subset (by simp)


-- @@ L613-614 verbatim
lemma domain_restr (f s : V) : domain (f ↾ s) = domain f ∩ s :=
  mem_ext (by simp [mem_domain_iff, pair_mem_restr_iff, exists_and_right, mem_inter_iff])


-- @@ L616-617 verbatim
lemma domain_restr_of_subset_domain {f s : V} (h : s ⊆ domain f) : domain (f ↾ s) = s := by
  simp [domain_restr, inter_comm, inter_eq_self_of_subset h]


-- @@ L619-619 verbatim
end «lp_section_12»


-- @@ L621-628 expanded
theorem insert_induction {P : V → Prop} (hP : BoldfacePred Γ-[1] P) (hempty : P ∅)
    (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s :=
  order_induction_hh Γ 1 hP <| by
    intro s IH
    rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    · exact hempty
    ·
      simpa [insert_remove hx] using
        hinsert x (bitRemove x s) (by simp) (IH _ (bitRemove_lt_of_mem hx))


-- @@ L630-633 expanded
@[elab_as_elim]
lemma insert_induction_sigmaOne {P : V → Prop} (hP : BoldfacePred Sg1 P) (hempty : P ∅)
    (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s :=
  insert_induction hP hempty hinsert


-- @@ L635-638 expanded
@[elab_as_elim]
lemma insert_induction_piOne {P : V → Prop} (hP : BoldfacePred Pg1 P) (hempty : P ∅)
    (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s :=
  insert_induction hP hempty hinsert


-- @@ L640-669 expanded
theorem sigmaOne_skolem {R : V → V → Prop} (hP : BoldfaceRel Sg1 R) {s : V}
    (H : ∀ x ∈ s, ∃ y, R x y) : ∃ f, IsMapping f ∧ domain f = s ∧ ∀ x y, pair x y ∈ f → R x y :=
  by
  have : ∀ u, u ⊆ s → ∃ f, IsMapping f ∧ domain f = u ∧ ∀ x y, pair x y ∈ f → R x y :=
    by
    intro u hu
    induction u using insert_induction_sigmaOne
    · have :
        BoldfacePred Sg1 fun u ↦
          u ⊆ s → ∃ f, IsMapping f ∧ domain f = u ∧ ∀ x < f, ∀ y < f, pair x y ∈ f → R x y :=
        by aesop  (config := { terminal := true })  (rule_sets := [Definability])
      exact
        this.of_iff <| by intro x;
          apply
            imp_congr_right <| fun _ ↦
              exists_congr <| fun f ↦
                and_congr_right <| fun _ ↦
                  and_congr_right <| fun _ ↦
                    ⟨fun h x _ y _ hxy ↦ h x y hxy, fun h x y hxy ↦
                      h x (lt_of_mem_dom hxy) y (lt_of_mem_rng hxy) hxy⟩
    case hempty => exact ⟨∅, by simp⟩
    case hinsert a u ha
      ih =>
      have : ∃ f, IsMapping f ∧ domain f = u ∧ ∀ x y, pair x y ∈ f → R x y :=
        ih (subset_trans (susbset_insert a u) hu)
      rcases this with ⟨f, mf, rfl, hf⟩
      have : ∃ b, R a b := H a (hu (by simp))
      rcases this with ⟨b, hb⟩
      let f' := insert (pair a b) f
      exact
        ⟨f', mf.insert (by simpa using ha), by simp [f'],
          by
          intro x y hxy
          rcases (show x = a ∧ y = b ∨ pair x y ∈ f by simpa [f'] using hxy) with (⟨rfl, rfl⟩ | h)
          · exact hb
          · exact hf x y h⟩
  exact this s (by rfl)


-- @@ L671-689 expanded
theorem sigma₁_replacement {f : V → V} (hf : BoldfaceFunction₁ Sg1 f) (s : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x ∈ s, y = f x :=
  by
  have : ∀ x ∈ s, ∃ y, y = f x := by intro x _; exact ⟨f x, rfl⟩
  have : ∃ F, IsMapping F ∧ domain F = s ∧ ∀ (x y : V), pair x y ∈ F → y = f x :=
    sigmaOne_skolem (by aesop  (config := { terminal := true })  (rule_sets := [Definability])) this
  rcases this with ⟨F, _, rfl, hF⟩
  refine ExistsUnique.intro (range F) ?_ ?_
  · intro y
    simp only [mem_range_iff]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, mem_domain_iff.mpr ⟨y, hx⟩, hF _ _ hx⟩
    · simp only [mem_domain_iff, forall_exists_index, and_imp]
      rintro x y hxy rfl; exact ⟨x, by rcases hF _ _ hxy; exact hxy⟩
  · intro s' hs'
    apply mem_ext; intro y
    simp only [hs', mem_domain_iff, mem_range_iff]
    constructor
    · rintro ⟨x, ⟨y, hxy⟩, rfl⟩; exact ⟨x, by rcases hF _ _ hxy; exact hxy⟩
    · rintro ⟨x, hxy⟩; exact ⟨x, ⟨y, hxy⟩, hF _ _ hxy⟩


-- @@ L691-699 expanded
theorem sigma₁_replacement₂ {f : V → V → V} (hf : BoldfaceFunction₂ Sg1 f) (s₁ s₂ : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x₁ ∈ s₁, ∃ x₂ ∈ s₂, y = f x₁ x₂ :=
  by
  have : BoldfaceFunction₁ Sg1 (fun x ↦ f (pi₁ x) (pi₂ x)) := by
    aesop  (config := { terminal := true })  (rule_sets := [Definability])
  exact
    (existsUnique_congr
          (by
            intro t; apply forall_congr'; intro y; apply iff_congr (by rfl)
            simp only [mem_product_iff']; constructor
            · rintro ⟨x, ⟨h₁, h₂⟩, rfl⟩; exact ⟨pi₁ x, h₁, pi₂ x, h₂, by rfl⟩
            · rintro ⟨x₁, h₁, x₂, h₂, rfl⟩; exact ⟨pair x₁ x₂, by simp [h₁, h₂]⟩)).mp
      (sigma₁_replacement this (product s₁ s₂))


-- @@ L701-701 verbatim
section «lp_section_13»


-- @@ L703-704 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def fstIdx (p : V) : V :=
  pi₁ (p - 1)


-- @@ L706-707 verbatim
@[simp] lemma fstIdx_le_self (p : V) : fstIdx p ≤ p :=
  le_trans (by simp [fstIdx]) (show p - 1 ≤ p by simp)


-- @@ L709-711 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.fstIdxDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute subDef
          (vecCons (#0) (vecCons (#2) (vecCons (Semiterm.numeral 1) ![]))))
        (LO.FirstOrder.Rewriting.substitute pi₁Def (vecCons (#1) (vecCons #0 ![])))))
    (by simp)


-- @@ L713-714 expanded
lemma fstIdx_defined : DefinedFunction₁ Sg0 (fstIdx : V → V) fstIdxDef := by intro v;
  simp [fstIdxDef, fstIdx]


-- @@ L716-717 verbatim
@[simp] lemma eval_fstIdxDef (v) :
    Semiformula.Evalbm V v fstIdxDef.val ↔ v 0 = fstIdx (v 1) := fstIdx_defined.df.iff v


-- @@ L719-719 expanded
instance fstIdx_definable : BoldfaceFunction₁ Sg0 (fstIdx : V → V) :=
  fstIdx_defined.to_definable


-- @@ L721-721 expanded
instance fstIdx_definable' (Γ) : BoldfaceFunction₁ Γ (fstIdx : V → V) :=
  fstIdx_definable.of_zero


-- @@ L723-723 verbatim
end «lp_section_13»


-- @@ L725-725 verbatim
section «lp_section_14»


-- @@ L727-728 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def sndIdx (p : V) : V :=
  pi₂ (p - 1)


-- @@ L730-731 verbatim
@[simp] lemma sndIdx_le_self (p : V) : sndIdx p ≤ p :=
  le_trans (by simp [sndIdx]) (show p - 1 ≤ p by simp)


-- @@ L733-735 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.sndIdxDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Semiformula.bexLTSucc (#1)
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute subDef
          (vecCons (#0) (vecCons (#2) (vecCons (Semiterm.numeral 1) ![]))))
        (LO.FirstOrder.Rewriting.substitute pi₂Def (vecCons (#1) (vecCons #0 ![])))))
    (by simp)


-- @@ L737-738 expanded
lemma sndIdx_defined : DefinedFunction₁ Sg0 (sndIdx : V → V) sndIdxDef := by intro v;
  simp [sndIdxDef, sndIdx]


-- @@ L740-741 verbatim
@[simp] lemma eval_sndIdxDef (v) :
    Semiformula.Evalbm V v sndIdxDef.val ↔ v 0 = sndIdx (v 1) := sndIdx_defined.df.iff v


-- @@ L743-743 expanded
instance sndIdx_definable : BoldfaceFunction₁ Sg0 (sndIdx : V → V) :=
  sndIdx_defined.to_definable


-- @@ L745-745 expanded
instance sndIdx_definable' (Γ) : BoldfaceFunction₁ Γ (sndIdx : V → V) :=
  sndIdx_definable.of_zero


-- @@ L747-747 verbatim
end «lp_section_14»


-- @@ L749-749 verbatim
end Arith

-- @@ L750-750 verbatim
end LO


-- @@ L752-752 verbatim
end «lp_nc_section_1»
