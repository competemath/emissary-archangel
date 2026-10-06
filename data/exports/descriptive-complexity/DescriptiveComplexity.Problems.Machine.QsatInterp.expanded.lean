/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Machine.QsatRun
import DescriptiveComplexity.Problems.Machine.Defs


-- @@ L10-30 verbatim
/-!
# The transcription: `QSAT ≤ᶠᵒ[≤] DTMAcceptSpace`

The first-order half of the reduction. The machine of a quantified Boolean
formula was built *semantically* in
`DescriptiveComplexity.Problems.Machine.QsatProgram`, and its correctness
`DescriptiveComplexity.QsatTM.qsatMachine_correct` proved in
`DescriptiveComplexity.Problems.Machine.QsatRun`. This file writes the defining
formulas of an interpretation of `Language.turing` in ordered QSAT instances and
shows each realizes exactly the corresponding predicate of the machine.

## Method

The method is that of `DescriptiveComplexity.Problems.Machine.Interp`, one level
up: the elements of the machine have only two shapes, `qCst s` and `qOne s x`,
so the binary symbols get one **shape helper** each
(`DescriptiveComplexity.QsatTM.qCstF`, `DescriptiveComplexity.QsatTM.qOneF`) with
one realization lemma, and every defining formula then matches on its *first*
tag alone. Comparisons of tags – which are static data – are decided in Lean
rather than in the formula, so `⊤` and `⊥` do most of the work.
-/


-- @@ L32-32 verbatim
namespace DescriptiveComplexity


-- @@ L34-34 verbatim
open FirstOrder


-- @@ L36-36 verbatim
namespace QsatTM


-- @@ L38-38 verbatim
open Language Structure


-- @@ L40-42 verbatim
/-- The vocabulary the reduction reads: quantified CNF instances with the
ambient order. -/
abbrev qsatOrd : Language := Language.qsat.sum Language.order


-- @@ L44-44 verbatim
/-! ### The symbols of the ordered expansion -/


-- @@ L46-47 verbatim
/-- The symbol for “is a quantified variable”. -/
abbrev isVarSym : qsatOrd.Relations 1 := Sum.inl qsIsVar


-- @@ L49-50 verbatim
/-- The symbol for “is universally quantified”. -/
abbrev allVarSym : qsatOrd.Relations 1 := Sum.inl qsAllVar


-- @@ L52-53 verbatim
/-- The symbol for the quantifier prefix. -/
abbrev precSym : qsatOrd.Relations 2 := Sum.inl qsPrefixLt


-- @@ L55-56 verbatim
/-- The symbol for “is a clause”. -/
abbrev isClSym : qsatOrd.Relations 1 := Sum.inl qsIsClause


-- @@ L58-59 verbatim
/-- The symbol for a positive occurrence. -/
abbrev posInSym : qsatOrd.Relations 2 := Sum.inl qsPosIn


-- @@ L61-62 verbatim
/-- The symbol for a negative occurrence. -/
abbrev negInSym : qsatOrd.Relations 2 := Sum.inl qsNegIn


-- @@ L64-65 verbatim
/-- The ambient order symbol. -/
abbrev ordSym : qsatOrd.Relations 2 := Sum.inr leSymb


-- @@ L67-67 verbatim
/-! ### The builders -/


-- @@ L69-69 verbatim
section Builders


-- @@ L71-71 verbatim
variable {α : Type}


-- @@ L73-74 expanded
/-- `x` is a quantified variable. -/
def vF (x : α) : qsatOrd.Formula α :=
  FirstOrder.Language.Relations.formula₁ isVarSym (FirstOrder.Language.Term.var x)


-- @@ L76-77 expanded
/-- `x` is universally quantified. -/
def aF (x : α) : qsatOrd.Formula α :=
  FirstOrder.Language.Relations.formula₁ allVarSym (FirstOrder.Language.Term.var x)


-- @@ L79-80 expanded
/-- `x` is quantified outside `y`. -/
def precF (x y : α) : qsatOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ precSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L82-83 expanded
/-- `x` is a clause. -/
def clF (x : α) : qsatOrd.Formula α :=
  FirstOrder.Language.Relations.formula₁ isClSym (FirstOrder.Language.Term.var x)


-- @@ L85-86 expanded
/-- `x` occurs positively in `c`. -/
def posF (c x : α) : qsatOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ posInSym (FirstOrder.Language.Term.var c)
    (FirstOrder.Language.Term.var x)


-- @@ L88-89 expanded
/-- `x` occurs negatively in `c`. -/
def negF (c x : α) : qsatOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ negInSym (FirstOrder.Language.Term.var c)
    (FirstOrder.Language.Term.var x)


-- @@ L91-92 expanded
/-- `x ≤ y` in the ambient order. -/
def ordF (x y : α) : qsatOrd.Formula α :=
  FirstOrder.Language.Relations.formula₂ ordSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L94-95 expanded
/-- `x = y`. -/
def eqF (x y : α) : qsatOrd.Formula α :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)


-- @@ L97-98 verbatim
/-- `x < y` in the ambient order. -/
def ordLtF (x y : α) : qsatOrd.Formula α := ordF x y ⊓ ∼(eqF x y)


-- @@ L100-102 expanded
/-- `x` is the least element of the ambient order. -/
noncomputable def minF (x : α) : qsatOrd.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (ordF (Sum.inl x) (Sum.inr 0))


-- @@ L104-108 expanded
/-- The tape order on elements: quantified variables first in prefix order,
everything else after them in the ambient order. -/
def pLeF (x y : α) : qsatOrd.Formula α :=
  vF x ⊓ (vF y ⊓ (eqF x y ⊔ precF x y)) ⊔
    (vF x ⊓ FirstOrder.Language.BoundedFormula.not (vF y) ⊔
      FirstOrder.Language.BoundedFormula.not (vF x) ⊓
        (FirstOrder.Language.BoundedFormula.not (vF y) ⊓ ordF x y))


-- @@ L110-112 expanded
/-- `c` is the lowest clause. -/
noncomputable def minClF (c : α) : qsatOrd.Formula α :=
  clF c ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1) ((clF (Sum.inr 0)).imp (ordF (Sum.inl c) (Sum.inr 0)))


-- @@ L114-116 expanded
/-- `c` is the highest clause. -/
noncomputable def maxClF (c : α) : qsatOrd.Formula α :=
  clF c ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1) ((clF (Sum.inr 0)).imp (ordF (Sum.inr 0) (Sum.inl c)))


-- @@ L118-120 expanded
/-- `c'` is the clause immediately above `c`. -/
noncomputable def nextClF (c c' : α) : qsatOrd.Formula α :=
  clF c ⊓
    (clF c' ⊓
      (ordLtF c c' ⊓
        FirstOrder.Language.Formula.iAlls (Fin 1)
          ((clF (Sum.inr 0)).imp
            ((ordLtF (Sum.inl c) (Sum.inr 0)).imp (ordF (Sum.inl c') (Sum.inr 0))))))


-- @@ L122-124 expanded
/-- There is no clause at all. -/
noncomputable def noClF : qsatOrd.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    (FirstOrder.Language.BoundedFormula.not (clF (Sum.inr 0)))


-- @@ L126-128 verbatim
/-- The cell of `x`, holding the value `b`, satisfies the clause `c`. -/
def litF (b : Bool) (c x : α) : qsatOrd.Formula α :=
  if b then posF c x else negF c x


-- @@ L130-131 verbatim
/-- The returning value `v` settles the quantifier at `x`. -/
def shortF (v : Bool) (x : α) : qsatOrd.Formula α := if v then ∼(aF x) else aF x


-- @@ L133-138 expanded
/-- Well-formedness of the instance, as a sentence with unused free
variables. -/
noncomputable def wfF : qsatOrd.Formula α :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    ((precF (Sum.inr 0) (Sum.inr 1)).imp (vF (Sum.inr 0) ⊓ vF (Sum.inr 1)) ⊓
      (FirstOrder.Language.BoundedFormula.not (precF (Sum.inr 0) (Sum.inr 0)) ⊓
        ((precF (Sum.inr 0) (Sum.inr 1)).imp
            ((precF (Sum.inr 1) (Sum.inr 2)).imp (precF (Sum.inr 0) (Sum.inr 2))) ⊓
          (vF (Sum.inr 0)).imp
            ((vF (Sum.inr 1)).imp
              ((FirstOrder.Language.BoundedFormula.not (eqF (Sum.inr 0) (Sum.inr 1))).imp
                (precF (Sum.inr 0) (Sum.inr 1) ⊔ precF (Sum.inr 1) (Sum.inr 0)))))))


-- @@ L140-140 verbatim
end Builders


-- @@ L142-142 verbatim
/-! ### Realization of the builders -/


-- @@ L144-144 verbatim
section BuilderRealize


-- @@ L146-146 verbatim
variable {α A : Type} [Language.qsat.Structure A] [LinearOrder A]

-- @@ L147-147 verbatim
variable {v : α → A}


-- @@ L149-150 verbatim
@[simp] theorem realize_vF {x : α} : (vF x).Realize v ↔ IsQVar (v x) := by
  simp [vF, IsQVar, Formula.realize_rel₁]


-- @@ L152-153 verbatim
@[simp] theorem realize_aF {x : α} : (aF x).Realize v ↔ IsQAll (v x) := by
  simp [aF, IsQAll, Formula.realize_rel₁]


-- @@ L155-156 verbatim
@[simp] theorem realize_precF {x y : α} : (precF x y).Realize v ↔ QPrec (v x) (v y) := by
  simp [precF, QPrec, Formula.realize_rel₂]


-- @@ L158-159 verbatim
@[simp] theorem realize_clF {x : α} : (clF x).Realize v ↔ QCl (v x) := by
  simp [clF, QCl, Formula.realize_rel₁]


-- @@ L161-162 verbatim
@[simp] theorem realize_posF {c x : α} : (posF c x).Realize v ↔ QPosIn (v c) (v x) := by
  simp [posF, QPosIn, Formula.realize_rel₂]


-- @@ L164-165 verbatim
@[simp] theorem realize_negF {c x : α} : (negF c x).Realize v ↔ QNegIn (v c) (v x) := by
  simp [negF, QNegIn, Formula.realize_rel₂]


-- @@ L167-169 verbatim
@[simp] theorem realize_ordF {x y : α} : (ordF x y).Realize v ↔ v x ≤ v y := by
  simp [ordF, Formula.realize_rel₂]
  rfl


-- @@ L171-172 verbatim
@[simp] theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]


-- @@ L174-177 verbatim
@[simp] theorem realize_ordLtF {x y : α} : (ordLtF x y).Realize v ↔ v x < v y := by
  rw [ordLtF]
  simp only [Formula.realize_inf, realize_ordF, Formula.realize_not, realize_eqF]
  exact ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨le_of_lt h, ne_of_lt h⟩⟩


-- @@ L179-182 verbatim
@[simp] theorem realize_minF {x : α} : (minF x).Realize v ↔ ∀ a : A, v x ≤ a := by
  rw [minF]
  simp only [Formula.realize_iAlls, realize_ordF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h a => h ![a], fun h i => h (i 0)⟩


-- @@ L184-187 verbatim
@[simp] theorem realize_pLeF {x y : α} : (pLeF x y).Realize v ↔ PLe (v x) (v y) := by
  rw [pLeF, PLe]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not, realize_vF,
    realize_eqF, realize_precF, realize_ordF]


-- @@ L189-193 verbatim
@[simp] theorem realize_clFAll {x : α} : (minClF x).Realize v ↔ QMinCl (v x) := by
  rw [minClF, QMinCl]
  simp only [Formula.realize_inf, realize_clF, Formula.realize_iAlls, Formula.realize_imp,
    realize_ordF, Sum.elim_inl, Sum.elim_inr]
  exact and_congr_right fun _ => ⟨fun h a => h ![a], fun h i => h (i 0)⟩


-- @@ L195-199 verbatim
@[simp] theorem realize_maxClF {x : α} : (maxClF x).Realize v ↔ QMaxCl (v x) := by
  rw [maxClF, QMaxCl]
  simp only [Formula.realize_inf, realize_clF, Formula.realize_iAlls, Formula.realize_imp,
    realize_ordF, Sum.elim_inl, Sum.elim_inr]
  exact and_congr_right fun _ => ⟨fun h a => h ![a], fun h i => h (i 0)⟩


-- @@ L201-207 verbatim
@[simp] theorem realize_nextClF {x y : α} :
    (nextClF x y).Realize v ↔ QNextCl (v x) (v y) := by
  rw [nextClF, QNextCl]
  simp only [Formula.realize_inf, realize_clF, realize_ordLtF, Formula.realize_iAlls,
    Formula.realize_imp, realize_ordF, Sum.elim_inl, Sum.elim_inr]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  exact ⟨fun h a => h ![a], fun h i => h (i 0)⟩


-- @@ L209-212 verbatim
@[simp] theorem realize_noClF : (noClF (α := α)).Realize v ↔ ∀ e : A, ¬QCl e := by
  rw [noClF]
  simp only [Formula.realize_iAlls, Formula.realize_not, realize_clF, Sum.elim_inr]
  exact ⟨fun h a => h ![a], fun h i => h (i 0)⟩


-- @@ L214-218 verbatim
@[simp] theorem realize_litF {b : Bool} {c x : α} :
    (litF b c x).Realize v ↔ QLit (v c) (v x) b := by
  cases b
  · simp [litF, QLit]
  · simp [litF, QLit]


-- @@ L220-224 verbatim
@[simp] theorem realize_shortF {b : Bool} {x : α} :
    (shortF b x).Realize v ↔ QShort b (v x) := by
  cases b
  · simp [shortF, QShort]
  · simp [shortF, QShort]


-- @@ L226-239 verbatim
@[simp] theorem realize_wfF : (wfF (α := α)).Realize v ↔ QsatWf A := by
  rw [wfF]
  simp only [Formula.realize_iAlls, Formula.realize_inf, Formula.realize_imp,
    Formula.realize_not, Formula.realize_sup, realize_precF, realize_vF, realize_eqF,
    Sum.elim_inr]
  constructor
  · intro h
    exact ⟨fun x y hxy => (h ![x, y, x]).1 hxy,
      fun x => (h ![x, x, x]).2.1,
      fun x y z hxy hyz => (h ![x, y, z]).2.2.1 hxy hyz,
      fun x y hx hy hne => (h ![x, y, x]).2.2.2 hx hy hne⟩
  · rintro ⟨h1, h2, h3, h4⟩ i
    exact ⟨fun hxy => h1 _ _ hxy, h2 _, fun hxy hyz => h3 _ _ _ hxy hyz,
      fun hx hy hne => h4 _ _ hx hy hne⟩


-- @@ L241-241 verbatim
end BuilderRealize


-- @@ L243-243 verbatim
/-! ### The two shapes of the machine's elements, as formulas -/


-- @@ L245-245 verbatim
section Shapes


-- @@ L247-249 verbatim
/-- The second argument of a binary symbol is the constant `qCst s`. -/
noncomputable def qCstF (s t' : QTag) : qsatOrd.Formula (Fin 2 × Fin 2) :=
  if t' = s then minF (1, 0) ⊓ minF (1, 1) else ⊥


-- @@ L251-254 verbatim
/-- The second argument of a binary symbol is `qOne s (v x)`. -/
noncomputable def qOneF (s : QTag) (x : Fin 2 × Fin 2) (t' : QTag) :
    qsatOrd.Formula (Fin 2 × Fin 2) :=
  if t' = s then eqF (1, 0) x ⊓ minF (1, 1) else ⊥


-- @@ L256-256 verbatim
variable {A : Type} [Language.qsat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

-- @@ L257-257 verbatim
variable {v : Fin 2 × Fin 2 → A}


-- @@ L259-273 verbatim
theorem realize_qCstF {s : QTag} {q : QV A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) :
    (qCstF s q.1).Realize v ↔ q = qCst s := by
  rw [qCstF]
  by_cases hs : q.1 = s
  · rw [ite_eq_left hs]
    simp only [Formula.realize_inf, realize_minF, h0, h1]
    constructor
    · rintro ⟨ha, hb⟩
      exact qV_ext hs (le_antisymm (ha qBot) (qBot_le _)) (le_antisymm (hb qBot) (qBot_le _))
    · rintro rfl
      exact ⟨fun a => qBot_le a, fun a => qBot_le a⟩
  · rw [ite_eq_right hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs (congrArg Prod.fst hq)


-- @@ L275-289 verbatim
theorem realize_qOneF {s : QTag} {x : Fin 2 × Fin 2} {q : QV A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) :
    (qOneF s x q.1).Realize v ↔ q = qOne s (v x) := by
  rw [qOneF]
  by_cases hs : q.1 = s
  · rw [ite_eq_left hs]
    simp only [Formula.realize_inf, realize_eqF, realize_minF, h0, h1]
    constructor
    · rintro ⟨ha, hb⟩
      exact qV_ext hs ha (le_antisymm (hb qBot) (qBot_le _))
    · rintro rfl
      exact ⟨rfl, fun a => qBot_le a⟩
  · rw [ite_eq_right hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs (congrArg Prod.fst hq)


-- @@ L291-291 verbatim
end Shapes


-- @@ L293-293 verbatim
/-! ### The defining formulas -/


-- @@ L295-300 verbatim
/-- Defining formula for `posn`. -/
noncomputable def posnF : QTag → qsatOrd.Formula (Fin 1 × Fin 2)
  | .pStart => minF (0, 0) ⊓ minF (0, 1)
  | .pCell => vF (0, 0) ⊓ minF (0, 1)
  | .pEnd => minF (0, 0) ⊓ minF (0, 1)
  | _ => ⊥


-- @@ L302-321 verbatim
/-- Defining formula for `tr`: the payload promises of
`DescriptiveComplexity.QsatTM.QTr`. -/
noncomputable def trF : QTag → qsatOrd.Formula (Fin 1 × Fin 2)
  | .tDescStart => minF (0, 0) ⊓ minF (0, 1)
  | .tDescCell _ _ => vF (0, 0) ⊓ minF (0, 1)
  | .tDescEndTrue => (minF (0, 0) ⊓ minF (0, 1)) ⊓ noClF
  | .tDescEndEval => minClF (0, 0) ⊓ minF (0, 1)
  | .tEval _ _ _ _ => clF (0, 0) ⊓ vF (0, 1)
  | .tTurnNext _ => nextClF (0, 0) (0, 1)
  | .tTurnLast _ => maxClF (0, 0) ⊓ minF (0, 1)
  | .tTurnFalse _ => clF (0, 0) ⊓ minF (0, 1)
  | .tToEndCell _ _ _ => vF (0, 0) ⊓ minF (0, 1)
  | .tToEndStart _ => minF (0, 0) ⊓ minF (0, 1)
  | .tToEndTurn _ => minF (0, 0) ⊓ minF (0, 1)
  | .tProcSkip b _ f =>
      vF (0, 0) ⊓ (minF (0, 1) ⊓ (shortF b (0, 0) ⊔ (if f then ⊤ else ⊥)))
  | .tProcSwitch b _ f =>
      vF (0, 0) ⊓ (minF (0, 1) ⊓ (∼(shortF b (0, 0)) ⊓ (if f then ⊥ else ⊤)))
  | .tProcAcc => minF (0, 0) ⊓ minF (0, 1)
  | _ => ⊥


-- @@ L323-326 verbatim
/-- Defining formula for `start`. -/
noncomputable def startF : QTag → qsatOrd.Formula (Fin 1 × Fin 2)
  | .qDesc => minF (0, 0) ⊓ minF (0, 1)
  | _ => ⊥


-- @@ L328-332 verbatim
/-- Defining formula for `acc`: the accepting state, guarded by
well-formedness of the instance. -/
noncomputable def accF : QTag → qsatOrd.Formula (Fin 1 × Fin 2)
  | .qAcc => wfF
  | _ => ⊥


-- @@ L334-337 verbatim
/-- Defining formula for `blank`. -/
noncomputable def blankF : QTag → qsatOrd.Formula (Fin 1 × Fin 2)
  | .sBlank => minF (0, 0) ⊓ minF (0, 1)
  | _ => ⊥


-- @@ L339-351 verbatim
/-- Defining formula for `right`: a static condition on the tag. -/
noncomputable def rightF : QTag → qsatOrd.Formula (Fin 1 × Fin 2)
  | .tDescStart => ⊤
  | .tDescCell _ _ => ⊤
  | .tEval _ _ _ d => if d then ⊤ else ⊥
  | .tTurnNext d => if d then ⊥ else ⊤
  | .tTurnLast d => if d then ⊥ else ⊤
  | .tTurnFalse d => if d then ⊥ else ⊤
  | .tToEndCell _ _ _ => ⊤
  | .tToEndStart _ => ⊤
  | .tProcSwitch _ _ _ => ⊤
  | .tProcAcc => ⊤
  | _ => ⊥


-- @@ L353-360 verbatim
/-- Defining formula for `le`: the tag indices are static, so only the
same-tag case needs a formula. -/
noncomputable def leTagF (t t' : QTag) : qsatOrd.Formula (Fin 2 × Fin 2) :=
  if qTagIdx t < qTagIdx t' then ⊤
  else if t = t' then
    (pLeF (0, 0) (1, 0) ⊓ ∼(eqF (0, 0) (1, 0))) ⊔
      (eqF (0, 0) (1, 0) ⊓ pLeF (0, 1) (1, 1))
  else ⊥


-- @@ L362-367 verbatim
/-- Defining formula for `inp`, the initial tape. -/
noncomputable def inpF : QTag → QTag → qsatOrd.Formula (Fin 2 × Fin 2)
  | .pStart, t' => qCstF .sStart t'
  | .pCell, t' => qOneF (.sVal false false) (0, 0) t'
  | .pEnd, t' => qCstF .sEnd t'
  | _, _ => ⊥


-- @@ L369-385 verbatim
/-- Defining formula for `tsrc`. -/
noncomputable def tsrcF : QTag → QTag → qsatOrd.Formula (Fin 2 × Fin 2)
  | .tDescStart, t' => qCstF .qDesc t'
  | .tDescCell _ _, t' => qCstF .qDesc t'
  | .tDescEndTrue, t' => qCstF .qDesc t'
  | .tDescEndEval, t' => qCstF .qDesc t'
  | .tEval _ _ fl d, t' => qOneF (.qEval fl d) (0, 0) t'
  | .tTurnNext d, t' => qOneF (.qEval true d) (0, 0) t'
  | .tTurnLast d, t' => qOneF (.qEval true d) (0, 0) t'
  | .tTurnFalse d, t' => qOneF (.qEval false d) (0, 0) t'
  | .tToEndCell b _ _, t' => qCstF (.qToEnd b) t'
  | .tToEndStart b, t' => qCstF (.qToEnd b) t'
  | .tToEndTurn b, t' => qCstF (.qToEnd b) t'
  | .tProcSkip b _ _, t' => qCstF (.qProc b) t'
  | .tProcSwitch b _ _, t' => qCstF (.qProc b) t'
  | .tProcAcc, t' => qCstF (.qProc true) t'
  | _, _ => ⊥


-- @@ L387-403 verbatim
/-- Defining formula for `tread`. -/
noncomputable def treadF : QTag → QTag → qsatOrd.Formula (Fin 2 × Fin 2)
  | .tDescStart, t' => qCstF .sStart t'
  | .tDescCell b f, t' => qOneF (.sVal b f) (0, 0) t'
  | .tDescEndTrue, t' => qCstF .sEnd t'
  | .tDescEndEval, t' => qCstF .sEnd t'
  | .tEval b f _ _, t' => qOneF (.sVal b f) (0, 1) t'
  | .tTurnNext d, t' => if d then qCstF .sEnd t' else qCstF .sStart t'
  | .tTurnLast d, t' => if d then qCstF .sEnd t' else qCstF .sStart t'
  | .tTurnFalse d, t' => if d then qCstF .sEnd t' else qCstF .sStart t'
  | .tToEndCell _ b f, t' => qOneF (.sVal b f) (0, 0) t'
  | .tToEndStart _, t' => qCstF .sStart t'
  | .tToEndTurn _, t' => qCstF .sEnd t'
  | .tProcSkip _ b f, t' => qOneF (.sVal b f) (0, 0) t'
  | .tProcSwitch _ b f, t' => qOneF (.sVal b f) (0, 0) t'
  | .tProcAcc, t' => qCstF .sStart t'
  | _, _ => ⊥


-- @@ L405-424 verbatim
/-- Defining formula for `tdst`: the only place the instance is consulted is
the evaluation sweep, where the new flag depends on the literal test. -/
noncomputable def tdstF : QTag → QTag → qsatOrd.Formula (Fin 2 × Fin 2)
  | .tDescStart, t' => qCstF .qDesc t'
  | .tDescCell _ _, t' => qCstF .qDesc t'
  | .tDescEndTrue, t' => qCstF (.qProc true) t'
  | .tDescEndEval, t' => qOneF (.qEval false false) (0, 0) t'
  | .tEval b _ fl d, t' =>
      (qOneF (.qEval true d) (0, 0) t' ⊓ (if fl then ⊤ else litF b (0, 0) (0, 1))) ⊔
        (qOneF (.qEval false d) (0, 0) t' ⊓ (if fl then ⊥ else ∼(litF b (0, 0) (0, 1))))
  | .tTurnNext d, t' => qOneF (.qEval false (!d)) (0, 1) t'
  | .tTurnLast _, t' => qCstF (.qToEnd true) t'
  | .tTurnFalse _, t' => qCstF (.qToEnd false) t'
  | .tToEndCell b _ _, t' => qCstF (.qToEnd b) t'
  | .tToEndStart b, t' => qCstF (.qToEnd b) t'
  | .tToEndTurn b, t' => qCstF (.qProc b) t'
  | .tProcSkip b _ _, t' => qCstF (.qProc b) t'
  | .tProcSwitch _ _ _, t' => qCstF .qDesc t'
  | .tProcAcc, t' => qCstF .qAcc t'
  | _, _ => ⊥


-- @@ L426-442 verbatim
/-- Defining formula for `twrite`. -/
noncomputable def twriteF : QTag → QTag → qsatOrd.Formula (Fin 2 × Fin 2)
  | .tDescStart, t' => qCstF .sStart t'
  | .tDescCell _ _, t' => qOneF (.sVal false false) (0, 0) t'
  | .tDescEndTrue, t' => qCstF .sEnd t'
  | .tDescEndEval, t' => qCstF .sEnd t'
  | .tEval b f _ _, t' => qOneF (.sVal b f) (0, 1) t'
  | .tTurnNext d, t' => if d then qCstF .sEnd t' else qCstF .sStart t'
  | .tTurnLast d, t' => if d then qCstF .sEnd t' else qCstF .sStart t'
  | .tTurnFalse d, t' => if d then qCstF .sEnd t' else qCstF .sStart t'
  | .tToEndCell _ b f, t' => qOneF (.sVal b f) (0, 0) t'
  | .tToEndStart _, t' => qCstF .sStart t'
  | .tToEndTurn _, t' => qCstF .sEnd t'
  | .tProcSkip _ b f, t' => qOneF (.sVal b f) (0, 0) t'
  | .tProcSwitch _ _ _, t' => qOneF (.sVal true true) (0, 0) t'
  | .tProcAcc, t' => qCstF .sStart t'
  | _, _ => ⊥


-- @@ L444-460 verbatim
/-- **The interpretation of the machine vocabulary in an ordered QSAT
instance.** -/
noncomputable def qsatTuringInterp : FOInterpretation qsatOrd Language.turing QTag 2 where
  relFormula {n} R ts :=
    match n, R with
    | _, .posn => posnF (ts 0)
    | _, .tr => trF (ts 0)
    | _, .start => startF (ts 0)
    | _, .acc => accF (ts 0)
    | _, .blank => blankF (ts 0)
    | _, .right => rightF (ts 0)
    | _, .le => leTagF (ts 0) (ts 1)
    | _, .tsrc => tsrcF (ts 0) (ts 1)
    | _, .tread => treadF (ts 0) (ts 1)
    | _, .tdst => tdstF (ts 0) (ts 1)
    | _, .twrite => twriteF (ts 0) (ts 1)
    | _, .inp => inpF (ts 0) (ts 1)


-- @@ L462-462 verbatim
/-! ### Each formula defines its predicate -/


-- @@ L464-464 verbatim
section Correct


-- @@ L466-466 verbatim
variable {A : Type} [Language.qsat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L468-470 verbatim
/-- The identity equivalence between the tagged tuples and the interpreted
universe. -/
def qsatMapEquiv : QV A ≃ qsatTuringInterp.Map A := Equiv.refl (QV A)


-- @@ L472-490 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_posn (p : QV A) : TMPosn (qsatMapEquiv p) ↔ QPosn p := by
  rw [TMPosn, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  have hmin : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((minF (0, 0) ⊓ minF (0, 1) : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
        IsMinTup w) := by
    intro v h0 h1
    simp only [Formula.realize_inf, realize_minF, h0, h1, IsMinTup]
  have hcell : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((vF (0, 0) ⊓ minF (0, 1) : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
        (IsQVar (w 0) ∧ ∀ a : A, w 1 ≤ a)) := by
    intro v h0 h1
    simp only [Formula.realize_inf, realize_vF, realize_minF, h0, h1]
  cases t
  case pStart => exact hmin _ rfl rfl
  case pCell => exact hcell _ rfl rfl
  case pEnd => exact hmin _ rfl rfl
  all_goals exact Iff.rfl


-- @@ L492-498 verbatim
omit [Finite A] [Nonempty A] in
private theorem realize_minPair {w : Fin 2 → A} :
    ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((minF (0, 0) ⊓ minF (0, 1) : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
        IsMinTup w) := by
  intro v h0 h1
  simp only [Formula.realize_inf, realize_minF, h0, h1, IsMinTup]


-- @@ L500-509 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_start (p : QV A) : TMStart (qsatMapEquiv p) ↔ QStart p := by
  rw [TMStart, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case qDesc => exact (realize_minPair _ rfl rfl).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  all_goals
    refine iff_of_false (by exact fun h => h) ?_
    rintro ⟨h, -⟩
    exact QTag.noConfusion h


-- @@ L511-520 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_acc (p : QV A) : TMAcc (qsatMapEquiv p) ↔ QAcc p := by
  rw [TMAcc, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case qAcc => exact realize_wfF.trans ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩
  all_goals
    refine iff_of_false (by exact fun h => h) ?_
    rintro ⟨-, h⟩
    exact QTag.noConfusion h


-- @@ L522-531 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_blank (p : QV A) : TMBlank (qsatMapEquiv p) ↔ QBlank p := by
  rw [TMBlank, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case sBlank => exact (realize_minPair _ rfl rfl).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  all_goals
    refine iff_of_false (by exact fun h => h) ?_
    rintro ⟨h, -⟩
    exact QTag.noConfusion h


-- @@ L533-557 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_right (p : QV A) : TMRight (qsatMapEquiv p) ↔ QRight p := by
  rw [TMRight, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tEval b f fl d =>
    cases d
    · exact iff_of_false (fun h => h) (fun h => Bool.noConfusion h)
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
  case tTurnNext d =>
    cases d
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
    · exact iff_of_false (fun h => h) (fun h => Bool.noConfusion h)
  case tTurnLast d =>
    cases d
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
    · exact iff_of_false (fun h => h) (fun h => Bool.noConfusion h)
  case tTurnFalse d =>
    cases d
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
    · exact iff_of_false (fun h => h) (fun h => Bool.noConfusion h)
  all_goals
    first
      | exact Iff.rfl
      | exact iff_of_true (Formula.realize_top.mpr trivial) trivial


-- @@ L559-579 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_le (p q : QV A) : TMLe (qsatMapEquiv p) (qsatMapEquiv q) ↔ QLe p q := by
  rw [TMLe, FOInterpretation.relMap_map]
  change (leTagF p.1 q.1).Realize _ ↔ _
  rw [leTagF, QLe]
  by_cases h1 : qTagIdx p.1 < qTagIdx q.1
  · rw [ite_eq_left h1]
    simp only [Formula.realize_top, true_iff]
    exact Or.inl h1
  · rw [ite_eq_right h1]
    by_cases h2 : p.1 = q.1
    · rw [ite_eq_left h2]
      simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
        realize_pLeF, realize_eqF]
      rw [QTupLe]
      exact ⟨fun h => Or.inr ⟨h2, h⟩, fun h => h.resolve_left h1 |>.2⟩
    · rw [ite_eq_right h2]
      simp only [Formula.realize_bot, false_iff]
      rintro (h | ⟨h, -⟩)
      · exact h1 h
      · exact h2 h


-- @@ L581-591 verbatim
omit [Language.qsat.Structure A] in
theorem qInp_pStart_iff {w : Fin 2 → A} {a : QV A} :
    QInp ((QTag.pStart, w) : QV A) a ↔ a = qCst .sStart := by
  constructor
  · rintro (⟨-, ht, hm⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · have h := isMinTup_unique hm isMinTup_qBot
      exact qV_ext ht (congrFun h 0) (congrFun h 1)
    · exact QTag.noConfusion h
    · exact QTag.noConfusion h
  · rintro rfl
    exact Or.inl ⟨rfl, rfl, isMinTup_qBot⟩


-- @@ L593-602 verbatim
omit [Language.qsat.Structure A] in
theorem qInp_pCell_iff {w : Fin 2 → A} {a : QV A} :
    QInp ((QTag.pCell, w) : QV A) a ↔ a = qOne (.sVal false false) (w 0) := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, ht, h0, h1⟩ | ⟨h, -⟩)
    · exact QTag.noConfusion h
    · exact qV_ext ht h0 (le_antisymm (h1 qBot) (qBot_le _))
    · exact QTag.noConfusion h
  · rintro rfl
    exact Or.inr (Or.inl ⟨rfl, rfl, rfl, fun b => qBot_le b⟩)


-- @@ L604-614 verbatim
omit [Language.qsat.Structure A] in
theorem qInp_pEnd_iff {w : Fin 2 → A} {a : QV A} :
    QInp ((QTag.pEnd, w) : QV A) a ↔ a = qCst .sEnd := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ht, hm⟩)
    · exact QTag.noConfusion h
    · exact QTag.noConfusion h
    · have h := isMinTup_unique hm isMinTup_qBot
      exact qV_ext ht (congrFun h 0) (congrFun h 1)
  · rintro rfl
    exact Or.inr (Or.inr ⟨rfl, rfl, isMinTup_qBot⟩)


-- @@ L616-625 verbatim
theorem relMap_inp (p q : QV A) : TMInp (qsatMapEquiv p) (qsatMapEquiv q) ↔ QInp p q := by
  rw [TMInp, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case pStart => exact (realize_qCstF rfl rfl).trans qInp_pStart_iff.symm
  case pCell => exact (realize_qOneF rfl rfl).trans qInp_pCell_iff.symm
  case pEnd => exact (realize_qCstF rfl rfl).trans qInp_pEnd_iff.symm
  all_goals
    refine iff_of_false (by exact fun h => h) ?_
    rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact QTag.noConfusion h


-- @@ L627-645 verbatim
theorem relMap_tsrc (p q : QV A) : TMSrc (qsatMapEquiv p) (qsatMapEquiv q) ↔ QSrc p q := by
  rw [TMSrc, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tDescStart => exact realize_qCstF rfl rfl
  case tDescCell _ _ => exact realize_qCstF rfl rfl
  case tDescEndTrue => exact realize_qCstF rfl rfl
  case tDescEndEval => exact realize_qCstF rfl rfl
  case tEval _ _ _ _ => exact realize_qOneF rfl rfl
  case tTurnNext _ => exact realize_qOneF rfl rfl
  case tTurnLast _ => exact realize_qOneF rfl rfl
  case tTurnFalse _ => exact realize_qOneF rfl rfl
  case tToEndCell _ _ _ => exact realize_qCstF rfl rfl
  case tToEndStart _ => exact realize_qCstF rfl rfl
  case tToEndTurn _ => exact realize_qCstF rfl rfl
  case tProcSkip _ _ _ => exact realize_qCstF rfl rfl
  case tProcSwitch _ _ _ => exact realize_qCstF rfl rfl
  case tProcAcc => exact realize_qCstF rfl rfl
  all_goals exact Iff.rfl


-- @@ L647-665 verbatim
theorem relMap_tread (p q : QV A) : TMRead (qsatMapEquiv p) (qsatMapEquiv q) ↔ QRead p q := by
  rw [TMRead, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tDescStart => exact realize_qCstF rfl rfl
  case tDescCell _ _ => exact realize_qOneF rfl rfl
  case tDescEndTrue => exact realize_qCstF rfl rfl
  case tDescEndEval => exact realize_qCstF rfl rfl
  case tEval _ _ _ _ => exact realize_qOneF rfl rfl
  case tTurnNext d => cases d <;> exact realize_qCstF rfl rfl
  case tTurnLast d => cases d <;> exact realize_qCstF rfl rfl
  case tTurnFalse d => cases d <;> exact realize_qCstF rfl rfl
  case tToEndCell _ _ _ => exact realize_qOneF rfl rfl
  case tToEndStart _ => exact realize_qCstF rfl rfl
  case tToEndTurn _ => exact realize_qCstF rfl rfl
  case tProcSkip _ _ _ => exact realize_qOneF rfl rfl
  case tProcSwitch _ _ _ => exact realize_qOneF rfl rfl
  case tProcAcc => exact realize_qCstF rfl rfl
  all_goals exact Iff.rfl


-- @@ L667-686 verbatim
theorem relMap_twrite (p q : QV A) :
    TMWrite (qsatMapEquiv p) (qsatMapEquiv q) ↔ QWrite p q := by
  rw [TMWrite, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tDescStart => exact realize_qCstF rfl rfl
  case tDescCell _ _ => exact realize_qOneF rfl rfl
  case tDescEndTrue => exact realize_qCstF rfl rfl
  case tDescEndEval => exact realize_qCstF rfl rfl
  case tEval _ _ _ _ => exact realize_qOneF rfl rfl
  case tTurnNext d => cases d <;> exact realize_qCstF rfl rfl
  case tTurnLast d => cases d <;> exact realize_qCstF rfl rfl
  case tTurnFalse d => cases d <;> exact realize_qCstF rfl rfl
  case tToEndCell _ _ _ => exact realize_qOneF rfl rfl
  case tToEndStart _ => exact realize_qCstF rfl rfl
  case tToEndTurn _ => exact realize_qCstF rfl rfl
  case tProcSkip _ _ _ => exact realize_qOneF rfl rfl
  case tProcSwitch _ _ _ => exact realize_qOneF rfl rfl
  case tProcAcc => exact realize_qCstF rfl rfl
  all_goals exact Iff.rfl


-- @@ L688-775 verbatim
omit [Finite A] [Nonempty A] in
theorem relMap_tr (p : QV A) : TMTr (qsatMapEquiv p) ↔ QTr p := by
  rw [TMTr, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  have hvm : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((vF (0, 0) ⊓ minF (0, 1) : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
        (IsQVar (w 0) ∧ ∀ a : A, w 1 ≤ a)) := by
    intro v h0 h1
    simp only [Formula.realize_inf, realize_vF, realize_minF, h0, h1]
  cases t
  case tDescStart => exact realize_minPair _ rfl rfl
  case tDescCell _ _ => exact hvm _ rfl rfl
  case tDescEndTrue =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        (((minF (0, 0) ⊓ minF (0, 1)) ⊓ noClF : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          (IsMinTup w ∧ ∀ e : A, ¬QCl e)) := by
      intro v h0 h1
      rw [Formula.realize_inf, realize_noClF]
      exact and_congr_left fun _ => realize_minPair v h0 h1
    exact key _ rfl rfl
  case tDescEndEval =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((minClF (0, 0) ⊓ minF (0, 1) : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          (QMinCl (w 0) ∧ ∀ a : A, w 1 ≤ a)) := by
      intro v h0 h1
      simp only [Formula.realize_inf, realize_clFAll, realize_minF, h0, h1]
    exact key _ rfl rfl
  case tEval _ _ _ _ =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((clF (0, 0) ⊓ vF (0, 1) : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          (QCl (w 0) ∧ IsQVar (w 1))) := by
      intro v h0 h1
      simp only [Formula.realize_inf, realize_clF, realize_vF, h0, h1]
    exact key _ rfl rfl
  case tTurnNext _ =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((nextClF (0, 0) (0, 1) : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          QNextCl (w 0) (w 1)) := by
      intro v h0 h1
      simp only [realize_nextClF, h0, h1]
    exact key _ rfl rfl
  case tTurnLast _ =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((maxClF (0, 0) ⊓ minF (0, 1) : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          (QMaxCl (w 0) ∧ ∀ a : A, w 1 ≤ a)) := by
      intro v h0 h1
      simp only [Formula.realize_inf, realize_maxClF, realize_minF, h0, h1]
    exact key _ rfl rfl
  case tTurnFalse _ =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((clF (0, 0) ⊓ minF (0, 1) : qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          (QCl (w 0) ∧ ∀ a : A, w 1 ≤ a)) := by
      intro v h0 h1
      simp only [Formula.realize_inf, realize_clF, realize_minF, h0, h1]
    exact key _ rfl rfl
  case tToEndCell _ _ _ => exact hvm _ rfl rfl
  case tToEndStart _ => exact realize_minPair _ rfl rfl
  case tToEndTurn _ => exact realize_minPair _ rfl rfl
  case tProcSkip b _ f =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((vF (0, 0) ⊓ (minF (0, 1) ⊓ (shortF b (0, 0) ⊔ (if f then ⊤ else ⊥))) :
            qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          (IsQVar (w 0) ∧ (∀ a : A, w 1 ≤ a) ∧ (QShort b (w 0) ∨ f = true))) := by
      intro v h0 h1
      rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_sup]
      refine and_congr (by simp only [realize_vF, h0])
        (and_congr (by simp only [realize_minF, h1])
          (or_congr (by simp only [realize_shortF, h0]) ?_))
      cases f
      · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h)
      · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
    exact key _ rfl rfl
  case tProcSwitch b _ f =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((vF (0, 0) ⊓ (minF (0, 1) ⊓ (∼(shortF b (0, 0)) ⊓ (if f then ⊥ else ⊤))) :
            qsatOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          (IsQVar (w 0) ∧ (∀ a : A, w 1 ≤ a) ∧ (¬QShort b (w 0) ∧ f = false))) := by
      intro v h0 h1
      rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_inf, Formula.realize_not]
      refine and_congr (by simp only [realize_vF, h0])
        (and_congr (by simp only [realize_minF, h1])
          (and_congr (by simp only [realize_shortF, h0]) ?_))
      cases f
      · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
      · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h)
    exact key _ rfl rfl
  case tProcAcc => exact realize_minPair _ rfl rfl
  all_goals exact Iff.rfl


-- @@ L777-818 verbatim
theorem relMap_tdst (p q : QV A) : TMDst (qsatMapEquiv p) (qsatMapEquiv q) ↔ QDst p q := by
  rw [TMDst, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tDescStart => exact realize_qCstF rfl rfl
  case tDescCell _ _ => exact realize_qCstF rfl rfl
  case tDescEndTrue => exact realize_qCstF rfl rfl
  case tDescEndEval => exact realize_qOneF rfl rfl
  case tTurnNext _ => exact realize_qOneF rfl rfl
  case tTurnLast _ => exact realize_qCstF rfl rfl
  case tTurnFalse _ => exact realize_qCstF rfl rfl
  case tToEndCell _ _ _ => exact realize_qCstF rfl rfl
  case tToEndStart _ => exact realize_qCstF rfl rfl
  case tToEndTurn _ => exact realize_qCstF rfl rfl
  case tProcSkip _ _ _ => exact realize_qCstF rfl rfl
  case tProcSwitch _ _ _ => exact realize_qCstF rfl rfl
  case tProcAcc => exact realize_qCstF rfl rfl
  case tEval b f fl d =>
    have key : ∀ v : Fin 2 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        v (1, 0) = q.2 0 → v (1, 1) = q.2 1 →
        (((qOneF (.qEval true d) (0, 0) q.1 ⊓ (if fl then ⊤ else litF b (0, 0) (0, 1))) ⊔
          (qOneF (.qEval false d) (0, 0) q.1 ⊓
            (if fl then ⊥ else ∼(litF b (0, 0) (0, 1))))).Realize v ↔
          ((q = stEval true d (w 0) ∧ (fl = true ∨ QLit (w 0) (w 1) b)) ∨
            (q = stEval false d (w 0) ∧ fl = false ∧ ¬QLit (w 0) (w 1) b))) := by
      intro v h0 h1 h2 h3
      rw [Formula.realize_sup, Formula.realize_inf, Formula.realize_inf]
      refine or_congr (and_congr ((realize_qOneF h2 h3).trans (by rw [h0])) ?_)
        (and_congr ((realize_qOneF h2 h3).trans (by rw [h0])) ?_)
      · cases fl
        · rw [ite_eq_right Bool.false_ne_true]
          refine Iff.trans (by simp only [realize_litF, h0, h1])
            ⟨fun h => Or.inr h, fun h => h.resolve_left (fun hc => Bool.noConfusion hc)⟩
        · exact iff_of_true (Formula.realize_top.mpr trivial) (Or.inl rfl)
      · cases fl
        · rw [ite_eq_right Bool.false_ne_true, Formula.realize_not]
          refine ⟨fun h => ⟨rfl, fun hl => h (by simp only [realize_litF, h0, h1]; exact hl)⟩, ?_⟩
          intro h hl
          exact h.2 (by simpa only [realize_litF, h0, h1] using hl)
        · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h.1)
    exact key _ rfl rfl rfl rfl
  all_goals exact Iff.rfl


-- @@ L820-820 verbatim
/-! ### The reduction -/


-- @@ L822-836 verbatim
/-- **The interpreted structure describes the machine of the instance.** -/
theorem agree_qsatMachine :
    (tmData (qsatTuringInterp.Map A)).Agree (qsatMapEquiv (A := A)).symm (qsatMachine A) where
  posn := relMap_posn
  le := relMap_le
  tr := relMap_tr
  start := relMap_start
  acc := relMap_acc
  blank := relMap_blank
  right := relMap_right
  src := relMap_tsrc
  read := relMap_tread
  dst := relMap_tdst
  write := relMap_twrite
  inp := relMap_inp


-- @@ L838-843 verbatim
/-- **The image is a yes-instance exactly when the formula is true.** -/
theorem dtmAcceptSpace_map_iff :
    DTMAcceptSpace (qsatTuringInterp.Map A) ↔ QsatHolds A :=
  (and_congr (agree_qsatMachine (A := A)).wellFormed
      (and_congr (agree_qsatMachine (A := A)).deterministic
        (agree_qsatMachine (A := A)).acceptsSpace)).trans qsatMachine_correct


-- @@ L845-845 verbatim
end Correct


-- @@ L847-853 verbatim
/-- **`QSAT ≤ᶠᵒ[≤] DTMAcceptSpace`**: the deterministic space-bounded machine
that evaluates a quantified Boolean formula, built inside its instance. -/
noncomputable def qsat_ordered_fo_reduction_dtmAcceptSpace : QSAT ≤ᶠᵒ[≤] DTMAcceptSpace where
  Tag := QTag
  dim := 2
  toInterpretation := qsatTuringInterp
  correct := fun _ _ _ _ => dtmAcceptSpace_map_iff.symm


-- @@ L855-855 verbatim
end QsatTM


-- @@ L857-857 verbatim
end DescriptiveComplexity
