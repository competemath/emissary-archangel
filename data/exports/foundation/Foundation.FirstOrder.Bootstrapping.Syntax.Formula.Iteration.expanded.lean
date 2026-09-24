module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Functions


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-6 verbatim
namespace FFL.FirstOrder.Semiformula


-- @@ L8-8 verbatim
variable {L : Language} {ξ : Type*} {n : ℕ}


-- @@ L10-12 expanded
def replicate (p : Semiformula L ξ n) : ℕ → Semiformula L ξ n
  | 0 => p
  | k + 1 => binop% HWedge.hWedge p (p.replicate k)


-- @@ L14-14 verbatim
lemma replicate_zero (p : Semiformula L ξ n) : p.replicate 0 = p := by simp [replicate]


-- @@ L16-16 expanded
lemma replicate_succ (p : Semiformula L ξ n) (k : ℕ) :
    p.replicate (k + 1) = binop% HWedge.hWedge p (p.replicate k) := by simp [replicate]


-- @@ L18-18 verbatim
def weight (k : ℕ) : Semiformula L ξ n := (List.replicate k ⊤).conj


-- @@ L20-20 verbatim
end FFL.FirstOrder.Semiformula


-- @@ L22-22 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L24-24 expanded
variable {V : Type*} [ORingStructure V] [ModelsSet (Language.str V oRing) (ISigma 1)]


-- @@ L26-26 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L28-28 verbatim
namespace QQConj


-- @@ L30-32 expanded
def blueprint : VecRec.Blueprint 0
    where
  nil := .mkSigma (FFL.FirstOrder.Rewriting.subst qqVerumDef (vecCons #0 ![]))
  adjoin :=
    .mkSigma
      (FFL.FirstOrder.Rewriting.subst qqAndDef (vecCons (#0) (vecCons (#1) (vecCons #3 ![]))))


-- @@ L34-38 verbatim
noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := ^⊤
  adjoin _ p _ ih := p ^⋏ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L40-40 verbatim
end QQConj


-- @@ L42-42 verbatim
section qqConj


-- @@ L44-44 verbatim
open QQConj


-- @@ L46-46 verbatim
noncomputable def qqConj (ps : V) : V := construction.result ![] ps


-- @@ L48-48 expanded
def qqConjGraph : HierarchySymbol.sigmaOne.Semisentence 2 :=
  blueprint.resultDef


-- @@ L50-50 verbatim
scoped notation:65 "^⋀ " ps:66 => qqConj ps


-- @@ L52-52 verbatim
@[simp] lemma qqConj_nil : ^⋀ (0 : V) = ^⊤ := by simp [qqConj, construction]


-- @@ L54-54 verbatim
@[simp] lemma qqConj_cons (p ps : V) : ^⋀ (p ∷ ps) = p ^⋏ (^⋀ ps) := by simp [qqConj, construction]


-- @@ L56-56 verbatim
section


-- @@ L58-58 expanded
instance qqConj.defined : DefinedFunction₁ (V := V) HierarchySymbol.sigmaOne qqConj qqConjGraph :=
  construction.result_defined


-- @@ L60-60 expanded
instance qqConj.definable : DefinableFunction₁ HierarchySymbol.sigmaOne (qqConj : V → V) :=
  qqConj.defined.to_definable


-- @@ L62-62 expanded
instance qqConj.definable' : DefinableFunction₁ Γ-[m + 1] (qqConj : V → V) :=
  .of_sigmaOne qqConj.definable


-- @@ L64-64 verbatim
end


-- @@ L66-82 expanded
@[simp]
lemma qqConj_semiformula {n ps : V} :
    IsSemiformula L n (^⋀ ps) ↔ (∀ i < len ps, IsSemiformula L n ps.[i]) :=
  by
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case adjoin p ps
    ih =>
    simp only [qqConj_cons, IsSemiformula.and, ih, len_adjoin]
    constructor
    · rintro ⟨hp, hps⟩ i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simpa using hp
      · simpa using hps i (by simpa using hi)
    · intro h
      exact ⟨by simpa using h 0 (by simp), fun i hi ↦ by simpa using h (i + 1) (by simpa using hi)⟩


-- @@ L84-90 expanded
@[simp]
lemma len_le_conj (ps : V) : len ps ≤ ^⋀ ps :=
  by
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp [qqVerum]
  case adjoin p ps ih =>
    simp only [len_adjoin, qqConj_cons, succ_le_iff_lt]
    exact lt_of_le_of_lt ih (by simp)


-- @@ L92-92 verbatim
end qqConj


-- @@ L94-94 verbatim
namespace QQDisj


-- @@ L96-98 expanded
def blueprint : VecRec.Blueprint 0
    where
  nil := .mkSigma (FFL.FirstOrder.Rewriting.subst qqFalsumDef (vecCons #0 ![]))
  adjoin :=
    .mkSigma (FFL.FirstOrder.Rewriting.subst qqOrDef (vecCons (#0) (vecCons (#1) (vecCons #3 ![]))))


-- @@ L100-104 verbatim
noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := ^⊥
  adjoin _ p _ ih := p ^⋎ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L106-106 verbatim
end QQDisj


-- @@ L108-108 verbatim
section qqDisj


-- @@ L110-110 verbatim
open QQDisj


-- @@ L112-112 verbatim
noncomputable def qqDisj (ps : V) : V := construction.result ![] ps


-- @@ L114-114 expanded
def qqDisjGraph : HierarchySymbol.sigmaOne.Semisentence 2 :=
  blueprint.resultDef


-- @@ L116-116 verbatim
scoped notation:65 "^⋁ " ps:66 => qqDisj ps


-- @@ L118-118 verbatim
@[simp] lemma qqDisj_nil : ^⋁ (0 : V) = ^⊥ := by simp [qqDisj, construction]


-- @@ L120-120 verbatim
@[simp] lemma qqDisj_cons (p ps : V) : ^⋁ (p ∷ ps) = p ^⋎ (^⋁ ps) := by simp [qqDisj, construction]


-- @@ L122-122 verbatim
section


-- @@ L124-124 expanded
instance qqDisj.defined : DefinedFunction₁ (V := V) HierarchySymbol.sigmaOne qqDisj qqDisjGraph :=
  construction.result_defined


-- @@ L126-126 expanded
instance qqDisj.definable : DefinableFunction₁ (V := V) HierarchySymbol.sigmaOne qqDisj :=
  qqDisj.defined.to_definable


-- @@ L128-128 expanded
instance qqDisj.definable' : DefinableFunction₁ (V := V) Γ-[m + 1] qqDisj :=
  .of_sigmaOne qqDisj.definable


-- @@ L130-130 verbatim
end


-- @@ L132-148 expanded
@[simp]
lemma qqDisj_semiformula {ps : V} :
    IsSemiformula L n (^⋁ ps) ↔ (∀ i < len ps, IsSemiformula L n ps.[i]) :=
  by
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case nil => simp
  case adjoin p ps ih =>
    simp only [qqDisj_cons, IsSemiformula.or, ih, len_adjoin]
    constructor
    · rintro ⟨hp, hps⟩ i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simpa using hp
      · simpa using hps i (by simpa using hi)
    · intro h
      exact ⟨by simpa using h 0 (by simp), fun i hi ↦ by simpa using h (i + 1) (by simpa using hi)⟩


-- @@ L150-150 verbatim
end qqDisj


-- @@ L152-158 verbatim
namespace Arithmetic

-- `Arithmetic` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Bootstrapping.Arithmetic.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end Arithmetic`).

-- @@ L159-159 verbatim
set_option linter.dupNamespace false


-- @@ L161-167 verbatim
/-! ### Disjunction of sequential substution

`disjSeqSubst w p k = subst (k ∷ w) p ^⋎ ⋯ ^⋎ subst (0 ∷ w) p ^⋎ ⊥`

 -/

-- TOFO: remove

-- @@ L168-168 verbatim
section disjSeqSubst


-- @@ L170-170 verbatim
namespace DisjSeqSubst


-- @@ L172-175 expanded
noncomputable def blueprint : PR.Blueprint 2
    where
  zero := .mkSigma (FFL.FirstOrder.Rewriting.subst qqFalsumDef (vecCons #0 ![]))
  succ :=
    .mkSigma
      (ExsQuantifier.exs
        (@HWedge.hWedge _ _ _ Wedge.instHWedge
          (FFL.FirstOrder.Rewriting.subst numeralGraph (vecCons (#0) (vecCons #3 ![])))
          (ExsQuantifier.exs
            (@HWedge.hWedge _ _ _ Wedge.instHWedge
              (FFL.FirstOrder.Rewriting.subst adjoinDef
                (vecCons (#0) (vecCons (#1) (vecCons #5 ![]))))
              (ExsQuantifier.exs
                (@HWedge.hWedge _ _ _ Wedge.instHWedge
                  (FFL.FirstOrder.Rewriting.subst (substsGraph oRing)
                    (vecCons (#0) (vecCons (#1) (vecCons #7 ![]))))
                  (FFL.FirstOrder.Rewriting.subst qqOrDef
                    (vecCons (#3) (vecCons (#0) (vecCons #4 ![]))))))))))


-- @@ L177-181 expanded
noncomputable def construction : PR.Construction V blueprint
    where
  zero _ := ^⊥
  succ param k ih := (subst oRing (numeral k ∷ param 0) (param 1)) ^⋎ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L183-183 verbatim
end DisjSeqSubst


-- @@ L185-185 verbatim
open DisjSeqSubst


-- @@ L187-187 verbatim
noncomputable def disjSeqSubst (w p k : V) : V := construction.result ![w, p] k


-- @@ L189-189 verbatim
@[simp] lemma disjSeqSubst_zero (w p : V) : disjSeqSubst w p 0 = ^⊥ := by simp [disjSeqSubst, construction]


-- @@ L191-192 expanded
@[simp]
lemma disjSeqSubst_succ (w p k : V) :
    disjSeqSubst w p (k + 1) = subst oRing (numeral k ∷ w) p ^⋎ disjSeqSubst w p k := by
  simp [disjSeqSubst, construction]


-- @@ L194-194 expanded
noncomputable def disjSeqSubstGraph : HierarchySymbol.sigmaOne.Semisentence 4 :=
  blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])


-- @@ L196-196 verbatim
section


-- @@ L198-199 expanded
instance disjSeqSubst.defined :
    DefinedFunction₃ (V := V) HierarchySymbol.sigmaOne disjSeqSubst disjSeqSubstGraph :=
  .mk fun v ↦ by simp [construction.result_defined_iff, disjSeqSubstGraph, disjSeqSubst]


-- @@ L201-201 expanded
instance disjSeqSubst.definable :
    DefinableFunction₃ (V := V) HierarchySymbol.sigmaOne disjSeqSubst :=
  disjSeqSubst.defined.to_definable


-- @@ L203-203 expanded
instance disjSeqSubst.definable' : DefinableFunction₃ (V := V) Γ-[m + 1] disjSeqSubst :=
  .of_sigmaOne disjSeqSubst.definable


-- @@ L205-205 verbatim
end


-- @@ L207-213 expanded
lemma _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.IsSemiformula.disjSeqSubst {n m w p : V}
    (hw : IsSemitermVec oRing n m w) (hp : IsSemiformula oRing (n + 1) p) (k : V) :
    IsSemiformula oRing m (disjSeqSubst w p k) :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k ih => simpa [ih] using hp.subst <| hw.adjoin (numeral_semiterm m k)


-- @@ L215-229 expanded
lemma substs_conj_disjSeqSubst {n m l v w p : V} (hp : IsSemiformula oRing (n + 1) p)
    (hw : IsSemitermVec oRing n m w) (hv : IsSemitermVec oRing m l v) (k : V) :
    subst oRing v (disjSeqSubst w p k) = disjSeqSubst (termSubstVec oRing n v w) p k :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k
    ih =>
    have hkw : IsSemitermVec oRing (n + 1) m (numeral k ∷ w) := hw.adjoin (numeral_semiterm m k)
    have ha : IsSemiformula oRing m (disjSeqSubst w p k) := hp.disjSeqSubst hw k
    rw [disjSeqSubst_succ, substs_or (hp.subst hkw).isUFormula ha.isUFormula,
      substs_substs hp hv hkw, termSubstVec_cons (by simp) hw.isUTerm, numeral_substs hv]
    simp [ih]


-- @@ L231-231 verbatim
end disjSeqSubst


-- @@ L233-233 verbatim
section substItr


-- @@ L235-235 verbatim
namespace SubstItr


-- @@ L237-240 expanded
noncomputable def blueprint : PR.Blueprint 2
    where
  zero := .mkSigma (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])
  succ :=
    .mkSigma
      (ExsQuantifier.exs
        (@HWedge.hWedge _ _ _ Wedge.instHWedge
          (FFL.FirstOrder.Rewriting.subst numeralGraph (vecCons (#0) (vecCons #3 ![])))
          (ExsQuantifier.exs
            (@HWedge.hWedge _ _ _ Wedge.instHWedge
              (FFL.FirstOrder.Rewriting.subst adjoinDef
                (vecCons (#0) (vecCons (#1) (vecCons #5 ![]))))
              (ExsQuantifier.exs
                (@HWedge.hWedge _ _ _ Wedge.instHWedge
                  (FFL.FirstOrder.Rewriting.subst (substsGraph oRing)
                    (vecCons (#0) (vecCons (#1) (vecCons #7 ![]))))
                  (FFL.FirstOrder.Rewriting.subst adjoinDef
                    (vecCons (#3) (vecCons (#0) (vecCons #4 ![]))))))))))


-- @@ L242-246 expanded
noncomputable def construction : PR.Construction V blueprint
    where
  zero _ := 0
  succ param k ih := (subst oRing (numeral k ∷ param 0) (param 1)) ∷ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L248-248 verbatim
end SubstItr


-- @@ L250-250 verbatim
open SubstItr


-- @@ L252-252 verbatim
noncomputable def substItr (w p k : V) : V := construction.result ![w, p] k


-- @@ L254-254 verbatim
@[simp] lemma substItr_zero (w p : V) : substItr w p 0 = 0 := by simp [substItr, construction]


-- @@ L256-256 expanded
@[simp]
lemma substItr_succ (w p k : V) :
    substItr w p (k + 1) = subst oRing (numeral k ∷ w) p ∷ substItr w p k := by
  simp [substItr, construction]


-- @@ L258-258 verbatim
section


-- @@ L260-260 expanded
noncomputable def substItrGraph : HierarchySymbol.sigmaOne.Semisentence 4 :=
  blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])


-- @@ L262-263 expanded
instance substItr.defined :
    DefinedFunction₃ (V := V) HierarchySymbol.sigmaOne substItr substItrGraph :=
  .mk fun v ↦ by simp [construction.result_defined_iff, substItrGraph, substItr]


-- @@ L265-265 expanded
instance substItr.definable :
    DefinableFunction₃ HierarchySymbol.sigmaOne (substItr : V → V → V → V) :=
  substItr.defined.to_definable


-- @@ L267-267 expanded
instance substItr.definable' : DefinableFunction₃ Γ-[m + 1] (substItr : V → V → V → V) :=
  .of_sigmaOne substItr.definable


-- @@ L269-269 verbatim
end


-- @@ L271-275 expanded
@[simp]
lemma len_substItr (w p k : V) : len (substItr w p k) = k :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k ih => simp [ih]


-- @@ L277-286 expanded
@[simp]
lemma substItr_nth (w p k : V) {i} (hi : i < k) :
    (substItr w p k).[i] = subst oRing (numeral (k - (i + 1)) ∷ w) p :=
  by
  induction k using ISigma1.sigma1_succ_induction generalizing i
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp at hi
  case succ k ih =>
    simp only [substItr_succ]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using hi)]


-- @@ L288-294 expanded
lemma _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.IsSemiformula.substItrConj {m n w p : V}
    (hp : IsSemiformula oRing (n + 1) p) (hw : IsSemitermVec oRing n m w) (k : V) :
    IsSemiformula oRing m (^⋀ substItr w p k) :=
  by
  simp only [qqConj_semiformula, len_substItr]
  intro i hi
  simp only [hi, substItr_nth]
  apply hp.subst (by simp [hw])


-- @@ L296-302 expanded
lemma _root_.FFL.FirstOrder.Arithmetic.Bootstrapping.IsSemiformula.substItrDisj {m n w p : V}
    (hp : IsSemiformula oRing (n + 1) p) (hw : IsSemitermVec oRing n m w) (k : V) :
    IsSemiformula oRing m (^⋁ substItr w p k) :=
  by
  simp only [qqDisj_semiformula, len_substItr]
  intro i hi
  simp only [hi, substItr_nth]
  apply hp.subst (by simp [hw])


-- @@ L304-314 expanded
lemma neg_conj_substItr {n w p k : V} (hp : IsSemiformula oRing (n + 1) p)
    (hw : IsSemitermVec oRing n m w) :
    neg oRing (^⋀ (substItr w p k)) = ^⋁ (substItr w (neg oRing p) k) :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k ih =>
    simp only [substItr_succ, qqConj_cons, qqDisj_cons]
    rw [neg_and (L := oRing), ← substs_neg hp (m := m), ih]
    · simp [hw]
    · exact IsSemiformula.isUFormula <| hp.subst (by simpa [hw])
    · exact IsSemiformula.isUFormula <| hp.substItrConj hw k


-- @@ L316-326 expanded
lemma neg_disj_substItr {n w p k : V} (hp : IsSemiformula oRing (n + 1) p)
    (hw : IsSemitermVec oRing n m w) :
    neg oRing (^⋁ (substItr w p k)) = ^⋀ (substItr w (neg oRing p) k) :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k ih =>
    simp only [substItr_succ, qqDisj_cons, qqConj_cons]
    rw [neg_or (L := oRing), ← substs_neg hp (m := m), ih]
    · simp [hw]
    · apply IsSemiformula.isUFormula <| hp.subst (by simpa [hw])
    · apply IsSemiformula.isUFormula <| hp.substItrDisj hw k


-- @@ L328-340 expanded
lemma shift_conj_substItr {n w p k : V} (hp : IsSemiformula oRing (n + 1) p)
    (hw : IsSemitermVec oRing n m w) :
    shift oRing (^⋀ (substItr w p k)) = ^⋀ (substItr (termShiftVec oRing n w) (shift oRing p) k) :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k ih =>
    simp only [substItr_succ, qqConj_cons]
    rw [shift_and (L := oRing), shift_substs hp (m := m), ih, termShiftVec_cons (L := oRing),
      numeral_shift]
    · simp
    · exact hw.isUTerm
    · exact hw.adjoin (numeral_semiterm m k)
    · exact IsSemiformula.isUFormula <| hp.subst (by simpa [hw])
    · exact IsSemiformula.isUFormula <| hp.substItrConj hw k


-- @@ L342-354 expanded
lemma shift_disj_substItr {n w p k : V} (hp : IsSemiformula oRing (n + 1) p)
    (hw : IsSemitermVec oRing n m w) :
    shift oRing (^⋁ (substItr w p k)) = ^⋁ (substItr (termShiftVec oRing n w) (shift oRing p) k) :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k ih =>
    simp only [substItr_succ, qqDisj_cons]
    rw [shift_or (L := oRing), shift_substs hp (m := m), ih, termShiftVec_cons (L := oRing),
      numeral_shift]
    · simp
    · exact hw.isUTerm
    · exact hw.adjoin (numeral_semiterm m k)
    · exact IsSemiformula.isUFormula <| hp.subst (by simpa [hw])
    · exact IsSemiformula.isUFormula <| hp.substItrDisj hw k


-- @@ L356-371 expanded
lemma substs_conj_substItr {n m l w p k : V} (hp : IsSemiformula oRing (n + 1) p)
    (hw : IsSemitermVec oRing n m w) (hv : IsSemitermVec oRing m l v) :
    subst oRing v (^⋀ (substItr w p k)) = ^⋀ (substItr (termSubstVec oRing n v w) p k) :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k
    ih =>
    have hkw : IsSemitermVec oRing (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : IsSemiformula oRing m (^⋀ substItr w p k) :=
      by
      simp only [qqConj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.subst (hw.adjoin (by simp))
    simp only [substItr_succ, qqConj_cons]
    rw [substs_and (hp.subst hkw).isUFormula ha.isUFormula, substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm, numeral_substs hv]
    simp [ih]


-- @@ L373-388 expanded
lemma substs_disj_substItr {n m l w p k : V} (hp : IsSemiformula oRing (n + 1) p)
    (hw : IsSemitermVec oRing n m w) (hv : IsSemitermVec oRing m l v) :
    subst oRing v (^⋁ (substItr w p k)) = ^⋁ (substItr (termSubstVec oRing n v w) p k) :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp
  case succ k
    ih =>
    have hkw : IsSemitermVec oRing (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : IsSemiformula oRing m (^⋁ substItr w p k) :=
      by
      simp only [qqDisj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.subst (hw.adjoin (by simp))
    simp only [substItr_succ, qqDisj_cons]
    rw [substs_or (hp.subst hkw).isUFormula ha.isUFormula, substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm, numeral_substs hv]
    simp [ih]


-- @@ L390-390 verbatim
end substItr


-- @@ L392-392 verbatim
end Arithmetic


-- @@ L394-394 verbatim
section verums


-- @@ L396-396 verbatim
noncomputable def qqVerums (k : V) : V := ^⋀ repeatVec ^⊤ k


-- @@ L398-399 expanded
def qqVerumsGraph : HierarchySymbol.sigmaOne.Semisentence 2 :=
  .mkSigma
    (ExsQuantifier.exs
      (@HWedge.hWedge _ _ _ Wedge.instHWedge
        (FFL.FirstOrder.Rewriting.subst qqVerumDef (vecCons #0 ![]))
        (ExsQuantifier.exs
          (@HWedge.hWedge _ _ _ Wedge.instHWedge
            (FFL.FirstOrder.Rewriting.subst repeatVecDef
              (vecCons (#0) (vecCons (#1) (vecCons #3 ![]))))
            (FFL.FirstOrder.Rewriting.subst qqConjGraph (vecCons (#2) (vecCons #0 ![])))))))


-- @@ L401-402 verbatim
@[simp] lemma le_qqVerums (k : V) : k ≤ qqVerums k := by
  simpa [qqVerums] using len_le_conj (repeatVec ^⊤ k)


-- @@ L404-404 verbatim
section


-- @@ L406-406 expanded
instance qqVerums.defined :
    DefinedFunction₁ (V := V) HierarchySymbol.sigmaOne qqVerums qqVerumsGraph :=
  .mk fun v ↦ by simp [qqVerumsGraph]; rfl


-- @@ L408-408 expanded
instance qqVerums.definable : DefinableFunction₁ (V := V) HierarchySymbol.sigmaOne qqVerums :=
  qqVerums.defined.to_definable


-- @@ L410-410 expanded
instance qqVerums.definable' : DefinableFunction₁ (V := V) Γ-[m + 1] qqVerums :=
  .of_sigmaOne qqVerums.definable


-- @@ L412-412 verbatim
end


-- @@ L414-416 verbatim
@[simp] protected lemma IsSemiformula.qqVerums (k : V) : IsSemiformula L n (qqVerums k) := by
  simp only [qqVerums, qqConj_semiformula, len_repeatVec]
  intro i hi; simp [nth_repeatVec _ _ hi]


-- @@ L418-418 verbatim
@[simp] lemma qqVerums_zero : qqVerums (0 : V) = ^⊤ := by simp [qqVerums]


-- @@ L420-420 verbatim
@[simp] lemma qqVerums_succ (k : V) : qqVerums (k + 1) = ^⊤ ^⋏ qqVerums k := by simp [qqVerums]


-- @@ L422-422 verbatim
end verums


-- @@ L424-424 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping
