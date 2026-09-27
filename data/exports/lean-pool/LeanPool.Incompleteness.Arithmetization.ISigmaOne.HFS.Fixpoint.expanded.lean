/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaOne.HFS.PRF
import LeanPool.Incompleteness.Arithmetization.Definability.Init


-- @@ L11-15 verbatim
/-!

# Fixpoint Construction

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
namespace Fixpoint


-- @@ L30-33 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Blueprint (k : ℕ) where
  /-- Imported declaration from the Incompleteness formalization. -/
  core : Dlt1.Semisentence (k + 2)


-- @@ L35-35 verbatim
namespace Blueprint


-- @@ L37-37 verbatim
variable {k} (φ : Blueprint k)


-- @@ L39-39 verbatim
instance : Coe (Blueprint k) (Dlt1.Semisentence (k + 2)) := ⟨Blueprint.core⟩


-- @@ L41-44 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def succDef : Sg1.Semisentence (k + 3) :=
  .mkSigma
    (Semiformula.ballLT
      (Semiterm.Operator.Add.add.operator
        ![#0, Semiterm.Operator.Add.add.operator ![#2, Semiterm.numeral 1]])
      (Wedge.wedge
        (Arrow.arrow (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1])
          (Wedge.wedge (Semiformula.Operator.operator Operator.LE.le ![#0, #3])
            (LO.FirstOrder.Rewriting.substitute φ.core.sigma
              (vecCons (#0) (vecCons #2 fun x ↦ #(finSuccItr x 4))))))
        (Arrow.arrow
          (Wedge.wedge (Semiformula.Operator.operator Operator.LE.le ![#0, #3])
            (LO.FirstOrder.Rewriting.substitute φ.core.pi
              (vecCons (#0) (vecCons #2 fun x ↦ #(finSuccItr x 4)))))
          (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1]))))
    (by simp)


-- @@ L46-49 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def prBlueprint : PR.Blueprint k
    where
  zero :=
    .mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0]) (by simp)
  succ := φ.succDef


-- @@ L51-52 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def limSeqDef : Sg1.Semisentence (k + 2) := (φ.prBlueprint).resultDef


-- @@ L54-56 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def fixpointDef : Sg1.Semisentence (k + 1) :=
  .mkSigma
    (ExQuantifier.ex
      (ExQuantifier.ex
        (Wedge.wedge
          (LO.FirstOrder.Rewriting.substitute φ.limSeqDef
            (vecCons (#0) (vecCons #1 fun x ↦ #(finSuccItr x 3))))
          (Semiformula.Operator.operator Operator.Mem.mem ![#2, #0]))))
    (by simp)


-- @@ L58-61 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def fixpointDefΔ₁ : Dlt1.Semisentence (k + 1) :=
  .mkDelta
    (.mkSigma
      (ExQuantifier.ex
        (Wedge.wedge
          (LO.FirstOrder.Rewriting.substitute φ.limSeqDef
            (vecCons (#0)
              (vecCons (Semiterm.Operator.Add.add.operator ![#1, Semiterm.numeral 1]) fun x ↦
                #(finSuccItr x 2))))
          (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))
      (by simp))
    (.mkPi
      (UnivQuantifier.univ
        (Arrow.arrow
          (LO.FirstOrder.Rewriting.substitute φ.limSeqDef
            (vecCons (#0)
              (vecCons (Semiterm.Operator.Add.add.operator ![#1, Semiterm.numeral 1]) fun x ↦
                #(finSuccItr x 2))))
          (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0])))
      (by simp))


-- @@ L63-63 verbatim
end Blueprint


-- @@ L65-65 verbatim
variable (V)


-- @@ L67-72 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Construction {k : ℕ} (φ : Blueprint k) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Φ : (Fin k → V) → Set V → V → Prop
  defined : Dlt1.Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.core
  monotone {C C' : Set V} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x


-- @@ L74-77 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Arith.Fixpoint.Construction.Finite {k : ℕ} {φ : Blueprint k} (c :
    Construction V φ) where
  finite {C : Set V} {v x} : c.Φ v C x → ∃ m, c.Φ v {y ∈ C | y < m} x


-- @@ L79-82 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Arith.Fixpoint.Construction.StrongFinite {k : ℕ} {φ : Blueprint k} (c :
    Construction V φ) where
  strong_finite {C : Set V} {v x} : c.Φ v C x → c.Φ v {y ∈ C | y < x} x


-- @@ L84-85 verbatim
instance {k : ℕ} {φ : Blueprint k} (c : Construction V φ) [c.StrongFinite] : c.Finite where
  finite {_ _ x} := fun h ↦ ⟨x, Construction.StrongFinite.strong_finite h⟩


-- @@ L87-87 verbatim
variable {V}


-- @@ L89-89 verbatim
namespace Construction


-- @@ L91-91 verbatim
variable {k : ℕ} {φ : Blueprint k} (c : Construction V φ) (v : Fin k → V)


-- @@ L93-95 verbatim
lemma eval_formula (v : Fin k.succ.succ → V) :
    Semiformula.Evalbm V v φ.core.val ↔ c.Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0) :=
      c.defined.df.iff v


-- @@ L97-104 expanded
lemma succ_existsUnique (s ih : V) : ∃! u : V, ∀ x, (x ∈ u ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x) :=
  by
  have : BoldfacePred Sg1 fun x ↦ x ≤ s ∧ c.Φ v {z | z ∈ ih} x := by
    apply
      HierarchySymbol.Boldface.and
        (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
        ⟨φ.core.sigma.rew <| Rew.embSubsts (vecCons (#0) (vecCons &ih fun i ↦ &(v i))), by intro x;
          simp [HierarchySymbol.Semiformula.val_sigma, c.eval_formula]⟩
  exact finite_comprehension₁! this ⟨s + 1, fun i ↦ by rintro ⟨hi, _⟩; exact lt_succ_iff_le.mpr hi⟩


-- @@ L106-107 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def succ (s ih : V) : V := Classical.choose! (c.succ_existsUnique v s ih)


-- @@ L109-109 verbatim
variable {v}


-- @@ L111-113 verbatim
lemma mem_succ_iff {v s ih} :
    x ∈ c.succ v s ih ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x :=
      Classical.choose!_spec (c.succ_existsUnique v s ih) x


-- @@ L115-123 verbatim
private lemma succ_graph {u v s ih} :
    u = c.succ v s ih ↔ ∀ x < u + (s + 1), x ∈ u ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x :=
  ⟨by rintro rfl x _; simp [mem_succ_iff], by
    intro h; apply mem_ext
    intro x; constructor
    · intro hx; exact c.mem_succ_iff.mpr <| h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · intro hx
      exact h x (lt_of_lt_of_le (lt_succ_iff_le.mpr (c.mem_succ_iff.mp hx).1)
        (by simp)) |>.mpr (c.mem_succ_iff.mp hx)⟩


-- @@ L125-142 verbatim
lemma succ_defined : Sg1.DefinedFunction (fun v :
    Fin (k + 2) → V ↦ c.succ (v ·.succ.succ) (v 1) (v 0)) φ.succDef := by
  intro v
  simp only [Fin.succ_one_eq_two, Fin.succ_zero_eq_one, succ_graph, Blueprint.succDef,
    Nat.succ_eq_add_one, HierarchySymbol.Semiformula.val_sigma,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_ballLT, Semiterm.val_operator₂,
    Semiterm.val_bvar, Semiterm.val_const, Structure.numeral_eq_numeral, ORingStruc.one_eq_one,
    Structure.Add.add, LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_imply,
    Semiformula.eval_operator₂, Matrix.vecCons_zero, Matrix.cons_val_one, Structure.Mem.mem,
    Matrix.cons_app_three, Structure.LE.le, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.cons_app_two, Matrix.vecCons_succ, c.eval_formula, LogicalConnective.Prop.and_eq,
    LogicalConnective.Prop.arrow_eq, c.defined.proper.iff', forall_and_index]
  constructor
  · simp_all
  · intro h x hx
    constructor
    · exact (h x hx).1
    · simp_all


-- @@ L144-146 verbatim
lemma eval_succDef (v) :
    Semiformula.Evalbm V v φ.succDef.val ↔ v 0 = c.succ (v ·.succ.succ.succ) (v 2) (v 1) :=
      c.succ_defined.df.iff v


-- @@ L148-153 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def prConstruction : PR.Construction V φ.prBlueprint where
  zero := fun _ ↦ ∅
  succ := c.succ
  zero_defined := by intro v; simp [Blueprint.prBlueprint, emptyset_def]
  succ_defined := by intro v; simp [Blueprint.prBlueprint, c.eval_succDef]


-- @@ L155-155 verbatim
variable (v)


-- @@ L157-158 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def limSeq (s : V) : V := c.prConstruction.result v s


-- @@ L160-160 verbatim
variable {v}


-- @@ L162-162 verbatim
@[simp] lemma limSeq_zero : c.limSeq v 0 = ∅ := by simp [limSeq, prConstruction]


-- @@ L164-165 verbatim
lemma limSeq_succ (s : V) :
    c.limSeq v (s + 1) = c.succ v s (c.limSeq v s) := by simp [limSeq, prConstruction]


-- @@ L167-168 verbatim
lemma termSet_defined : Sg1.DefinedFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) φ.limSeqDef :=
  fun v ↦ by simp [c.prConstruction.result_defined_iff, Blueprint.limSeqDef]; rfl


-- @@ L170-172 verbatim
lemma eval_limSeqDef (v) :
    Semiformula.Evalbm V v φ.limSeqDef.val ↔ v 0 = c.limSeq (v ·.succ.succ) (v 1) :=
      c.termSet_defined.df.iff v


-- @@ L174-175 verbatim
instance limSeq_definable :
  Sg1.BoldfaceFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) := c.termSet_defined.to_definable


-- @@ L177-179 expanded
@[aesop 10 (rule_sets := [Definability]) safe]
instance limSeq_definable' (Γ) : Γ-[m + 1].BoldfaceFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) :=
  c.limSeq_definable.of_sigmaOne


-- @@ L181-183 verbatim
lemma mem_limSeq_succ_iff {x s : V} :
    x ∈ c.limSeq v (s + 1) ↔ x ≤ s ∧ c.Φ v {z | z ∈ c.limSeq v s} x := by
      simp [limSeq_succ, mem_succ_iff]


-- @@ L185-201 expanded
lemma limSeq_cumulative {s s' : V} : s ≤ s' → c.limSeq v s ⊆ c.limSeq v s' :=
  by
  induction s' using induction_sigma1 generalizing s
  · apply
      HierarchySymbol.Boldface.ball_le
        (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
    apply HierarchySymbol.Boldface.comp₂
    ·
      exact
        ⟨φ.limSeqDef.rew <| Rew.embSubsts (vecCons (#0) (vecCons #1 fun i ↦ &(v i))), by intro v;
          simp [c.eval_limSeqDef]⟩
    ·
      exact
        ⟨φ.limSeqDef.rew <| Rew.embSubsts (vecCons (#0) (vecCons #2 fun i ↦ &(v i))), by intro v;
          simp [c.eval_limSeqDef]⟩
  case zero => simp only [nonpos_iff_eq_zero, limSeq_zero]; rintro rfl; simp
  case succ s' ih =>
    intro hs u hu
    rcases zero_or_succ s with (rfl | ⟨s, rfl⟩)
    · simp at hu
    have hs : s ≤ s' := by simpa using hs
    rcases c.mem_limSeq_succ_iff.mp hu with ⟨hu, Hu⟩
    exact c.mem_limSeq_succ_iff.mpr ⟨_root_.le_trans hu hs, c.monotone (fun z hz ↦ ih hs hz) Hu⟩


-- @@ L203-228 expanded
lemma mem_limSeq_self [c.StrongFinite] {u s : V} : u ∈ c.limSeq v s → u ∈ c.limSeq v (u + 1) :=
  by
  induction u using order_induction_pi1 generalizing s
  · apply HierarchySymbol.Boldface.all
    apply HierarchySymbol.Boldface.imp
    ·
      apply
        HierarchySymbol.Boldface.comp₂
          ⟨φ.limSeqDef.rew <| Rew.embSubsts (vecCons (#0) (vecCons #1 fun i ↦ &(v i))), by intro v;
            simp [c.eval_limSeqDef]⟩
          (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
    ·
      apply
        HierarchySymbol.Boldface.comp₂
          ⟨φ.limSeqDef.rew <|
              Rew.embSubsts
                (vecCons (#0)
                  (vecCons (Semiterm.Operator.Add.add.operator ![#2, Semiterm.numeral 1]) fun i ↦
                    &(v i))),
            by intro v; simp [c.eval_limSeqDef]⟩
          (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
  case ind u ih =>
    rcases zero_or_succ s with (rfl | ⟨s, rfl⟩)
    · simp
    intro hu
    rcases c.mem_limSeq_succ_iff.mp hu with ⟨_, Hu⟩
    have : c.Φ v {z | z ∈ c.limSeq v s ∧ z < u} u := StrongFinite.strong_finite Hu
    have : c.Φ v {z | z ∈ c.limSeq v u} u :=
      c.monotone
        (by
          simp only [Set.ofPred_subset_ofPred, and_imp]
          intro z hz hzu
          exact c.limSeq_cumulative (succ_le_iff_lt.mpr hzu) (ih z hzu hz))
        this
    exact c.mem_limSeq_succ_iff.mpr ⟨by rfl, this⟩


-- @@ L230-230 verbatim
variable (v)


-- @@ L232-233 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def fixedPoint (x : V) : Prop := ∃ s, x ∈ c.limSeq v s


-- @@ L235-235 verbatim
variable {v}


-- @@ L237-238 verbatim
lemma fixpoint_iff [c.StrongFinite] {x : V} : c.fixedPoint v x ↔ x ∈ c.limSeq v (x + 1) :=
  ⟨by rintro ⟨s, hs⟩; exact c.mem_limSeq_self hs, fun h ↦ ⟨x + 1, h⟩⟩


-- @@ L240-245 verbatim
lemma fixpoint_iff_succ {x : V} : c.fixedPoint v x ↔ ∃ u, x ∈ c.limSeq v (u + 1) :=
  ⟨by
    rintro ⟨u, h⟩
    rcases zero_or_succ u with (rfl | ⟨u, rfl⟩)
    · simp at h
    · exact ⟨u, h⟩, by rintro ⟨u, h⟩; exact ⟨u + 1, h⟩⟩


-- @@ L247-271 expanded
lemma finite_upperbound (m : V) : ∃ s, ∀ z < m, c.fixedPoint v z → z ∈ c.limSeq v s :=
  by
  have : ∃ F : V, ∀ x, x ∈ F ↔ x < m ∧ c.fixedPoint v x :=
    by
    have : BoldfacePred Sg1 fun x ↦ x < m ∧ c.fixedPoint v x :=
      HierarchySymbol.Boldface.and
        (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
        (HierarchySymbol.Boldface.ex
          (HierarchySymbol.Boldface.comp₂
            ⟨φ.limSeqDef.rew <| Rew.embSubsts (vecCons (#0) (vecCons #1 fun i ↦ &(v i))), by
              intro v; simp [c.eval_limSeqDef]⟩
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))))
    exact finite_comprehension₁! this ⟨m, fun i hi ↦ hi.1⟩ |>.exists
  rcases this with ⟨F, hF⟩
  have : ∀ x ∈ F, ∃ u, x ∈ c.limSeq v u := by intro x hx; exact hF x |>.mp hx |>.2
  have : ∃ f, IsMapping f ∧ domain f = F ∧ ∀ (x y : V), pair x y ∈ f → x ∈ c.limSeq v y :=
    sigmaOne_skolem
      (by
        apply
          HierarchySymbol.Boldface.comp₂
            ⟨φ.limSeqDef.rew <| Rew.embSubsts (vecCons (#0) (vecCons #2 fun i ↦ &(v i))), by
              intro v; simp [c.eval_limSeqDef]⟩
            (by aesop  (config := { terminal := true })  (rule_sets := [Definability])))
      this
  rcases this with ⟨f, mf, rfl, hf⟩
  exact
    ⟨f, by
      intro z hzm hz
      have : ∃ u, pair z u ∈ f := mf.get_exists_uniq ((hF z).mpr ⟨hzm, hz⟩) |>.exists
      rcases this with ⟨u, hu⟩
      have : z ∈ c.limSeq v u := hf z u hu
      exact c.limSeq_cumulative (le_of_lt <| lt_of_mem_rng hu) this⟩


-- @@ L273-289 verbatim
theorem case [c.Finite] : c.fixedPoint v x ↔ c.Φ v {z | c.fixedPoint v z} x :=
  ⟨by intro h
      rcases c.fixpoint_iff_succ.mp h with ⟨u, hu⟩
      have : c.Φ v {z | z ∈ c.limSeq v u} x := (c.mem_limSeq_succ_iff.mp hu).2
      exact c.monotone (fun z hx ↦ by exact ⟨u, hx⟩) this,
   by intro hx
      rcases Finite.finite hx with ⟨m, hm⟩
      simp only [Set.mem_ofPred_eq] at hm
      have : ∃ s, ∀ z < m, c.fixedPoint v z → z ∈ c.limSeq v s := c.finite_upperbound m
      rcases this with ⟨s, hs⟩
      have : c.Φ v {z | z ∈ c.limSeq v s} x :=
        c.monotone (by
          simp_all)
          hm
      exact ⟨max s x + 1,
        c.mem_limSeq_succ_iff.mpr <| ⟨by simp,
          c.monotone (fun z hz ↦ c.limSeq_cumulative (by simp) hz) this⟩⟩⟩


-- @@ L291-291 verbatim
section «lp_section_1»


-- @@ L293-294 verbatim
lemma fixpoint_defined : Sg1.Defined (fun v ↦ c.fixedPoint (v ·.succ) (v 0)) φ.fixpointDef := by
  intro v; simp [Blueprint.fixpointDef, c.eval_limSeqDef]; rfl


-- @@ L296-298 verbatim
lemma eval_fixpointDef (v) :
    Semiformula.Evalbm V v φ.fixpointDef.val ↔ c.fixedPoint (v ·.succ) (v 0) :=
      c.fixpoint_defined.df.iff v


-- @@ L300-303 verbatim
lemma fixpoint_definedΔ₁ [c.StrongFinite] :
    Dlt1.Defined (fun v ↦ c.fixedPoint (v ·.succ) (v 0)) φ.fixpointDefΔ₁ :=
  ⟨by intro v; simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef],
   by intro v; simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef, fixpoint_iff]⟩


-- @@ L305-307 verbatim
lemma eval_fixpointDefΔ₁ [c.StrongFinite] (v) :
    Semiformula.Evalbm V v φ.fixpointDefΔ₁.val ↔ c.fixedPoint (v ·.succ) (v 0) :=
      c.fixpoint_definedΔ₁.df.iff v


-- @@ L309-309 verbatim
end «lp_section_1»


-- @@ L311-326 expanded
theorem induction [c.StrongFinite] {P : V → Prop} (hP : BoldfacePred Γ-[1] P)
    (H : ∀ C : Set V, (∀ x ∈ C, c.fixedPoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.fixedPoint v x → P x :=
  by
  apply order_induction_hh (Γ := Γ) (m := 1) (P := fun x ↦ c.fixedPoint v x → P x)
  ·
    apply
      HierarchySymbol.Boldface.imp
        (HierarchySymbol.BoldfacePred.comp
          (by
            apply HierarchySymbol.Boldface.of_deltaOne
            exact
              ⟨φ.fixpointDefΔ₁.rew <| Rew.embSubsts <| vecCons #0 fun x ↦ &(v x),
                c.fixpoint_definedΔ₁.proper.rew' _, by intro v; simp [c.eval_fixpointDefΔ₁]⟩)
          (by aesop  (config := { terminal := true })  (rule_sets := [Definability])))
        (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
  intro x ih hx
  have : c.Φ v {y | c.fixedPoint v y ∧ y < x} x := StrongFinite.strong_finite (c.case.mp hx)
  exact H {y | c.fixedPoint v y ∧ y < x} (by intro y ⟨hy, hyx⟩; exact ⟨hy, ih y hyx hy⟩) x this


-- @@ L328-328 verbatim
end Construction


-- @@ L330-330 verbatim
end Fixpoint


-- @@ L332-332 verbatim
end Arith

-- @@ L333-333 verbatim
end LO


-- @@ L335-335 verbatim
end «lp_nc_section_1»
