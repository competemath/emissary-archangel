module

public import Foundation.FirstOrder.Arithmetic.HFS.PRF


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-10 verbatim
/-!

# Fixpoint Construction

-/


-- @@ L12-12 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L14-14 expanded
variable {V : Type*} [ORingStructure V] [ModelsSet (Language.str V oRing) (ISigma 1)]


-- @@ L16-22 verbatim
namespace Fixpoint

-- `Fixpoint` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Arithmetic.Fixpoint.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end Fixpoint`).

-- @@ L23-23 verbatim
set_option linter.dupNamespace false


-- @@ L25-26 expanded
structure Blueprint (k : ℕ) where
  core : HierarchySymbol.deltaOne.Semisentence (k + 2)


-- @@ L28-28 verbatim
namespace Blueprint


-- @@ L30-30 verbatim
variable {k} (φ : Blueprint k)


-- @@ L32-32 expanded
instance : Coe (Blueprint k) (HierarchySymbol.deltaOne.Semisentence (k + 2)) :=
  ⟨Blueprint.core⟩


-- @@ L34-35 expanded
def succDef : HierarchySymbol.sigmaOne.Semisentence (k + 3) :=
  .mkSigma
    (Semiformula.ballLT
      (Semiterm.Operator.Add.add.operator
        ![#0, Semiterm.Operator.Add.add.operator ![#2, Semiterm.numeral 1]])
      (@HWedge.hWedge _ _ _ Wedge.instHWedge
        (@HArrow.hArrow _ _ _ Arrow.instHArrow
          (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1])
          (@HWedge.hWedge _ _ _ Wedge.instHWedge
            (Semiformula.Operator.operator Operator.LE.le ![#0, #3])
            (FFL.FirstOrder.Rewriting.subst φ.core.sigma
              (vecCons (#0) (vecCons #2 fun x ↦ #(finSuccItr x 4))))))
        (@HArrow.hArrow _ _ _ Arrow.instHArrow
          (@HWedge.hWedge _ _ _ Wedge.instHWedge
            (Semiformula.Operator.operator Operator.LE.le ![#0, #3])
            (FFL.FirstOrder.Rewriting.subst φ.core.pi
              (vecCons (#0) (vecCons #2 fun x ↦ #(finSuccItr x 4)))))
          (Semiformula.Operator.operator Operator.Mem.mem ![#0, #1]))))


-- @@ L37-39 expanded
def prBlueprint : PR.Blueprint k
    where
  zero := .mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])
  succ := φ.succDef


-- @@ L41-41 expanded
def limSeqDef : HierarchySymbol.sigmaOne.Semisentence (k + 2) :=
  (φ.prBlueprint).resultDef


-- @@ L43-44 expanded
def fixpointDef : HierarchySymbol.sigmaOne.Semisentence (k + 1) :=
  .mkSigma
    (ExsQuantifier.exs
      (ExsQuantifier.exs
        (@HWedge.hWedge _ _ _ Wedge.instHWedge
          (FFL.FirstOrder.Rewriting.subst φ.limSeqDef
            (vecCons (#0) (vecCons #1 fun x ↦ #(finSuccItr x 3))))
          (Semiformula.Operator.operator Operator.Mem.mem ![#2, #0]))))


-- @@ L46-48 expanded
def fixpointDefΔ₁ : HierarchySymbol.deltaOne.Semisentence (k + 1) :=
  .mkDelta
    (.mkSigma
      (ExsQuantifier.exs
        (@HWedge.hWedge _ _ _ Wedge.instHWedge
          (FFL.FirstOrder.Rewriting.subst φ.limSeqDef
            (vecCons (#0)
              (vecCons (Semiterm.Operator.Add.add.operator ![#1, Semiterm.numeral 1]) fun x ↦
                #(finSuccItr x 2))))
          (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0]))))
    (.mkPi
      (UnivQuantifier.all
        (@HArrow.hArrow _ _ _ Arrow.instHArrow
          (FFL.FirstOrder.Rewriting.subst φ.limSeqDef
            (vecCons (#0)
              (vecCons (Semiterm.Operator.Add.add.operator ![#1, Semiterm.numeral 1]) fun x ↦
                #(finSuccItr x 2))))
          (Semiformula.Operator.operator Operator.Mem.mem ![#1, #0]))))


-- @@ L50-50 verbatim
end Blueprint


-- @@ L52-52 verbatim
variable (V)


-- @@ L54-57 expanded
structure Construction {k : ℕ} (φ : Blueprint k) where
  Φ : (Fin k → V) → Set V → V → Prop
  defined : HierarchySymbol.deltaOne.Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.core
  monotone {C C' : Set V} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x


-- @@ L59-60 verbatim
class Construction.Finite {k : ℕ} {φ : Blueprint k} (c : Construction V φ) where
  finite {C : Set V} {v x} : c.Φ v C x → ∃ m, c.Φ v {y ∈ C | y < m} x


-- @@ L62-63 verbatim
class Construction.StrongFinite {k : ℕ} {φ : Blueprint k} (c : Construction V φ) where
  strong_finite {C : Set V} {v x} : c.Φ v C x → c.Φ v {y ∈ C | y < x} x


-- @@ L65-66 verbatim
instance {k : ℕ} {φ : Blueprint k} (c : Construction V φ) [c.StrongFinite] : c.Finite where
  finite {_ _ x} := fun h ↦ ⟨x, Construction.StrongFinite.strong_finite h⟩


-- @@ L68-68 verbatim
variable {V}


-- @@ L70-70 verbatim
namespace Construction


-- @@ L72-72 verbatim
variable {k : ℕ} {φ : Blueprint k} (c : Construction V φ) (v : Fin k → V)


-- @@ L74-75 verbatim
lemma eval_formula (v : Fin k.succ.succ → V) :
    φ.core.val.Evalb v ↔ c.Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0) := c.defined.iff


-- @@ L77-84 expanded
lemma succ_existsUnique (s ih : V) : ∃! u : V, ∀ x, (x ∈ u ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x) :=
  by
  have : DefinablePred HierarchySymbol.sigmaOne fun x ↦ x ≤ s ∧ c.Φ v {z | z ∈ ih} x := by
    apply
      HierarchySymbol.Definable.and
        (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
        ⟨φ.core.sigma.rew <| Rew.embSubsts (vecCons (#0) (vecCons &ih fun i ↦ &(v i))), by intro x;
          simp [HierarchySymbol.Semiformula.val_sigma, c.eval_formula]⟩
  exact finite_comprehension₁! this ⟨s + 1, fun i ↦ by rintro ⟨hi, _⟩; exact lt_succ_iff_le.mpr hi⟩


-- @@ L86-86 verbatim
noncomputable def succ (s ih : V) : V := Classical.choose! (c.succ_existsUnique v s ih)


-- @@ L88-88 verbatim
variable {v}


-- @@ L90-91 verbatim
lemma mem_succ_iff {v s ih} :
    x ∈ c.succ v s ih ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x := Classical.choose!_spec (c.succ_existsUnique v s ih) x


-- @@ L93-101 verbatim
private lemma succ_graph {u v s ih} :
    u = c.succ v s ih ↔ ∀ x < u + (s + 1), x ∈ u ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x :=
  ⟨by rintro rfl x _; simp [mem_succ_iff], by
    intro h; apply mem_ext
    intro x; constructor
    · intro hx; exact c.mem_succ_iff.mpr <| h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · intro hx
      exact h x (lt_of_lt_of_le (lt_succ_iff_le.mpr (c.mem_succ_iff.mp hx).1)
        (by simp)) |>.mpr (c.mem_succ_iff.mp hx)⟩


-- @@ L103-106 expanded
lemma succ_defined :
    HierarchySymbol.sigmaOne.DefinedFunction
      (fun v : Fin (k + 2) → V ↦ c.succ (v ·.succ.succ) (v 1) (v 0)) φ.succDef :=
  .mk fun v ↦
    by
    simp [Blueprint.succDef, succ_graph, HierarchySymbol.Semiformula.val_sigma, c.eval_formula,
      c.defined.proper.iff', -and_imp, BinderNotation.finSuccItr]
    grind


-- @@ L108-109 verbatim
lemma eval_succDef (v : Fin (k + 3) → V) :
    φ.succDef.val.Evalb v ↔ v 0 = c.succ (v ·.succ.succ.succ) (v 2) (v 1) := c.succ_defined.iff


-- @@ L111-115 verbatim
noncomputable def prConstruction : PR.Construction V φ.prBlueprint where
  zero := fun _ ↦ ∅
  succ := c.succ
  zero_defined := .mk fun v ↦ by simp [Blueprint.prBlueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by simp [Blueprint.prBlueprint, c.eval_succDef]


-- @@ L117-117 verbatim
variable (v)


-- @@ L119-119 verbatim
noncomputable def limSeq (s : V) : V := c.prConstruction.result v s


-- @@ L121-121 verbatim
variable {v}


-- @@ L123-123 verbatim
@[simp] lemma limSeq_zero : c.limSeq v 0 = ∅ := by simp [limSeq, prConstruction]


-- @@ L125-125 verbatim
lemma limSeq_succ (s : V) : c.limSeq v (s + 1) = c.succ v s (c.limSeq v s) := by simp [limSeq, prConstruction]


-- @@ L127-128 expanded
lemma termSet_defined :
    HierarchySymbol.sigmaOne.DefinedFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) φ.limSeqDef :=
  .mk fun v ↦ by simp [c.prConstruction.result_defined_iff, Blueprint.limSeqDef]; rfl


-- @@ L130-131 verbatim
@[simp] lemma eval_limSeqDef (v : Fin (k + 2) → V) :
    φ.limSeqDef.val.Evalb v ↔ v 0 = c.limSeq (v ·.succ.succ) (v 1) := c.termSet_defined.iff


-- @@ L133-134 expanded
instance limSeq_definable :
    HierarchySymbol.sigmaOne.DefinableFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) :=
  c.termSet_defined.to_definable


-- @@ L136-136 expanded
@[simp, aesop 10 (rule_sets := [Definability]) safe]
instance limSeq_definable' (Γ) : Γ-[m + 1].DefinableFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) :=
  c.limSeq_definable.of_sigmaOne


-- @@ L138-139 verbatim
lemma mem_limSeq_succ_iff {x s : V} :
    x ∈ c.limSeq v (s + 1) ↔ x ≤ s ∧ c.Φ v {z | z ∈ c.limSeq v s} x := by simp [limSeq_succ, mem_succ_iff]


-- @@ L141-155 expanded
lemma limSeq_cumulative {s s' : V} : s ≤ s' → c.limSeq v s ⊆ c.limSeq v s' :=
  by
  induction s' using ISigma1.sigma1_succ_induction generalizing s
  · apply
      HierarchySymbol.Definable.ball_le
        (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
    apply HierarchySymbol.Definable.comp₂
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


-- @@ L157-180 expanded
lemma mem_limSeq_self [c.StrongFinite] {u s : V} : u ∈ c.limSeq v s → u ∈ c.limSeq v (u + 1) :=
  by
  induction u using ISigma1.pi1_order_induction generalizing s
  · apply HierarchySymbol.Definable.all
    apply HierarchySymbol.Definable.imp
    ·
      apply
        HierarchySymbol.Definable.comp₂
          ⟨φ.limSeqDef.rew <| Rew.embSubsts (vecCons (#0) (vecCons #1 fun i ↦ &(v i))), by intro v;
            simp [c.eval_limSeqDef]⟩
          (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
    ·
      apply
        HierarchySymbol.Definable.comp₂
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


-- @@ L182-182 verbatim
variable (v)


-- @@ L184-184 verbatim
def Fixpoint (x : V) : Prop := ∃ s, x ∈ c.limSeq v s


-- @@ L186-186 verbatim
variable {v}


-- @@ L188-189 verbatim
lemma fixpoint_iff [c.StrongFinite] {x : V} : c.Fixpoint v x ↔ x ∈ c.limSeq v (x + 1) :=
  ⟨by rintro ⟨s, hs⟩; exact c.mem_limSeq_self hs, fun h ↦ ⟨x + 1, h⟩⟩


-- @@ L191-196 verbatim
lemma fixpoint_iff_succ {x : V} : c.Fixpoint v x ↔ ∃ u, x ∈ c.limSeq v (u + 1) :=
  ⟨by
    rintro ⟨u, h⟩
    rcases zero_or_succ u with (rfl | ⟨u, rfl⟩)
    · simp at h
    · exact ⟨u, h⟩, by rintro ⟨u, h⟩; exact ⟨u + 1, h⟩⟩


-- @@ L198-220 expanded
lemma finite_upperbound (m : V) : ∃ s, ∀ z < m, c.Fixpoint v z → z ∈ c.limSeq v s :=
  by
  have : ∃ F : V, ∀ x, x ∈ F ↔ x < m ∧ c.Fixpoint v x :=
    by
    have : DefinablePred HierarchySymbol.sigmaOne fun x ↦ x < m ∧ c.Fixpoint v x :=
      HierarchySymbol.Definable.and
        (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
        (HierarchySymbol.Definable.exs
          (HierarchySymbol.Definable.comp₂
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
          HierarchySymbol.Definable.comp₂
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


-- @@ L222-237 verbatim
theorem case [c.Finite] : c.Fixpoint v x ↔ c.Φ v {z | c.Fixpoint v z} x :=
  ⟨by intro h
      rcases c.fixpoint_iff_succ.mp h with ⟨u, hu⟩
      have : c.Φ v {z | z ∈ c.limSeq v u} x := (c.mem_limSeq_succ_iff.mp hu).2
      exact c.monotone (fun z hx ↦ by exact ⟨u, hx⟩) this,
   by intro hx
      rcases Finite.finite hx with ⟨m, hm⟩
      have : ∃ s, ∀ z < m, c.Fixpoint v z → z ∈ c.limSeq v s := c.finite_upperbound m
      rcases this with ⟨s, hs⟩
      have : c.Φ v {z | z ∈ c.limSeq v s} x :=
        c.monotone (by
          simp only [Set.ofPred_subset_ofPred, and_imp]
          intro z hz hzm; exact hs z hzm hz)
          hm
      exact ⟨max s x + 1,
        c.mem_limSeq_succ_iff.mpr <| ⟨by simp, c.monotone (fun z hz ↦ c.limSeq_cumulative (by simp) hz) this⟩⟩⟩


-- @@ L239-239 verbatim
section


-- @@ L241-242 expanded
lemma fixpoint_defined :
    HierarchySymbol.sigmaOne.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDef :=
  .mk fun v ↦ by simp [Blueprint.fixpointDef, c.eval_limSeqDef]; rfl


-- @@ L244-245 verbatim
@[simp] lemma eval_fixpointDef (v : Fin (k + 1) → V) :
    φ.fixpointDef.val.Evalb v ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_defined.iff


-- @@ L247-249 expanded
lemma fixpoint_definedΔ₁ [c.StrongFinite] :
    HierarchySymbol.deltaOne.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDefΔ₁ :=
  ⟨by intro v; simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef], by intro v;
    simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef, fixpoint_iff]⟩


-- @@ L251-252 verbatim
@[simp] lemma eval_fixpointDefΔ₁ [c.StrongFinite] (v : Fin (k + 1) → V) :
    φ.fixpointDefΔ₁.val.Evalb v ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_definedΔ₁.iff


-- @@ L254-254 verbatim
end


-- @@ L256-270 expanded
theorem induction [c.StrongFinite] {P : V → Prop} (hP : DefinablePred Γ-[1] P)
    (H : ∀ C : Set V, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.Fixpoint v x → P x :=
  by
  apply
    InductionOnHierarchy.order_induction_sigma (Γ := Γ) (m := 1) (P := fun x ↦ c.Fixpoint v x → P x)
  ·
    apply
      HierarchySymbol.Definable.imp
        (HierarchySymbol.DefinablePred.comp
          (by
            apply HierarchySymbol.Definable.of_deltaOne
            exact
              ⟨φ.fixpointDefΔ₁.rew <| Rew.embSubsts <| vecCons #0 fun x ↦ &(v x),
                c.fixpoint_definedΔ₁.proper.rew' _, by intro v; simp [c.eval_fixpointDefΔ₁]⟩)
          (by aesop  (config := { terminal := true })  (rule_sets := [Definability])))
        (by aesop  (config := { terminal := true })  (rule_sets := [Definability]))
  intro x ih hx
  have : c.Φ v {y | c.Fixpoint v y ∧ y < x} x := StrongFinite.strong_finite (c.case.mp hx)
  exact H {y | c.Fixpoint v y ∧ y < x} (by intro y ⟨hy, hyx⟩; exact ⟨hy, ih y hyx hy⟩) x this


-- @@ L272-272 verbatim
end Construction


-- @@ L274-274 verbatim
attribute [irreducible] Blueprint.fixpointDef


-- @@ L276-276 verbatim
end Fixpoint


-- @@ L278-278 verbatim
end FFL.FirstOrder.Arithmetic
