/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ThreeSat.Defs
import DescriptiveComplexity.OccurrenceFormulas


-- @@ L9-30 verbatim
/-!
# 3SAT FO-reduces to SAT

This file constructs a first-order reduction from 3SAT to SAT,
`DescriptiveComplexity.threeSat_fo_reduction_sat : ThreeSAT ≤ᶠᵒ SAT`, over the identity
of vocabularies. The point of the reduction is the width bound: a 3SAT
instance is a SAT instance *plus* the promise that every clause has at most
three literals, and the promise is checked by a closed first-order sentence.

The interpretation (`DescriptiveComplexity.ThreeSatToSat.threeSatToSat`) is
identity-like – one tag, dimension one – with all relation formulas gated on
the sentence `DescriptiveComplexity.ThreeSatToSat.wideS` (“some clause has at least four
distinct literal occurrences”):

* if the input is not wide, the output is a copy of the input, so the output
  is satisfiable iff the input is (and the width promise holds);
* if the input is wide, every element of the output becomes an empty clause,
  so the output is unsatisfiable, matching the violated promise.

The order is not needed: this is an order-free FO reduction (though not a
quantifier-free one, since `wideS` quantifies over clauses and occurrences).
-/


-- @@ L32-32 verbatim
namespace DescriptiveComplexity


-- @@ L34-34 verbatim
open FirstOrder


-- @@ L36-36 verbatim
namespace ThreeSatToSat


-- @@ L38-38 verbatim
open Language Structure SatOcc


-- @@ L40-40 verbatim
/-! ### Order-free formulas over the vocabulary of CNF instances -/


-- @@ L42-42 verbatim
section Builders


-- @@ L44-44 verbatim
variable {α : Type}


-- @@ L46-48 verbatim
/-- `c` is a clause, as a formula. -/
def clF (c : α) : Language.sat.Formula α :=
  Relations.formula₁ satIsClause (Term.var c)


-- @@ L50-52 verbatim
/-- `x` occurs positively in `c`, as a formula. -/
def posF (c x : α) : Language.sat.Formula α :=
  Relations.formula₂ satPosIn (Term.var c) (Term.var x)


-- @@ L54-56 verbatim
/-- `x` occurs negatively in `c`, as a formula. -/
def negF (c x : α) : Language.sat.Formula α :=
  Relations.formula₂ satNegIn (Term.var c) (Term.var x)


-- @@ L58-60 verbatim
/-- `x = y`, as a formula. -/
def eqF (x y : α) : Language.sat.Formula α :=
  Term.equal (Term.var x) (Term.var y)


-- @@ L62-64 verbatim
/-- The literal `(x, s)` occurs in the clause `c`, as a formula. -/
def occF (s : Bool) (c x : α) : Language.sat.Formula α :=
  clF c ⊓ if s then posF c x else negF c x


-- @@ L66-66 verbatim
end Builders


-- @@ L68-77 verbatim
/-- Some clause has at least four distinct literal occurrences, as a sentence:
the clause is variable `0` and the four occurrence variables are `1`, …, `4`;
the disjunction ranges over the sign vectors, and distinctness is only
required between occurrences carrying the same sign. -/
noncomputable def wideS : Language.sat.Sentence :=
  (Formula.iSup fun s : Fin 4 → Bool =>
      (Formula.iInf fun i : Fin 4 =>
        occF (s i) (Sum.inr 0) (Sum.inr i.succ)) ⊓
      Formula.iInf fun p : {p : Fin 4 × Fin 4 // p.1 ≠ p.2 ∧ s p.1 = s p.2} =>
        ∼(eqF (Sum.inr (p.1.1.succ : Fin 5)) (Sum.inr p.1.2.succ))).iExs (Fin 5)


-- @@ L79-79 verbatim
section Semantics


-- @@ L81-81 verbatim
variable {A : Type} [Language.sat.Structure A] {α : Type} {v : α → A}


-- @@ L83-86 verbatim
@[simp]
theorem realize_clF {c : α} : (clF c).Realize v ↔ IsCl (v c) := by
  rw [clF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L88-91 verbatim
@[simp]
theorem realize_posF {c x : α} : (posF c x).Realize v ↔ PosIn (v c) (v x) := by
  rw [posF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L93-96 verbatim
@[simp]
theorem realize_negF {c x : α} : (negF c x).Realize v ↔ NegIn (v c) (v x) := by
  rw [negF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L98-100 verbatim
@[simp]
theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]


-- @@ L102-105 verbatim
@[simp]
theorem realize_occF {s : Bool} {c x : α} :
    (occF s c x).Realize v ↔ OccIn (v c) (v x) s := by
  cases s <;> simp [occF, OccIn]


-- @@ L107-107 verbatim
variable (A)


-- @@ L109-113 verbatim
/-- Some clause has at least four distinct literal occurrences. This is the
negation of the width bound of 3SAT (`wide_iff_not_widthAtMostThree`). -/
def Wide : Prop :=
  ∃ (c : A) (x : Fin 4 → A) (s : Fin 4 → Bool),
    (∀ i, OccIn c (x i) (s i)) ∧ ∀ i j, i ≠ j → s i = s j → x i ≠ x j


-- @@ L115-124 verbatim
theorem wide_iff_not_widthAtMostThree : Wide A ↔ ¬WidthAtMostThree A := by
  constructor
  · rintro ⟨c, x, s, hocc, hdist⟩ h
    obtain ⟨i, j, hij, hx, hs⟩ := h c x s hocc
    exact hdist i j hij hs hx
  · intro h
    rw [WidthAtMostThree] at h
    push Not at h
    obtain ⟨c, x, s, hocc, hdist⟩ := h
    exact ⟨c, x, s, hocc, fun i j hij hs hx => hdist i j hij hx hs⟩


-- @@ L126-138 verbatim
/-- Realization of the formula `wideS` (under any assignment of its – absent –
free variables). -/
@[simp]
theorem realize_wideS {w : Empty → A} : Formula.Realize wideS w ↔ Wide A := by
  simp only [wideS, Formula.realize_iExs, Formula.realize_iSup, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_not, realize_occF, realize_eqF, Sum.elim_inr]
  constructor
  · rintro ⟨e, s, hocc, hdist⟩
    exact ⟨e 0, fun i => e i.succ, s, hocc, fun i j hij hs => hdist ⟨(i, j), hij, hs⟩⟩
  · rintro ⟨c, x, s, hocc, hdist⟩
    refine ⟨Fin.cases c x, s, fun i => ?_, fun p => ?_⟩
    · simpa using hocc i
    · simpa using hdist p.1.1 p.1.2 p.2.1 p.2.2


-- @@ L140-144 verbatim
/-! ### The same check over the ordered expansion

The reductions that build gadgets over `SatOcc.satOrd` (Max Cut, 1-in-SAT)
gate themselves on the width check too, and need it as a formula of the
ordered vocabulary. -/


-- @@ L146-146 verbatim
section Ordered


-- @@ L148-148 verbatim
variable {α : Type}


-- @@ L150-156 verbatim
/-- Some clause has at least four distinct literal occurrences, as a formula
over the ordered expansion: `wideS` read there. -/
noncomputable def wideOrdF : SatOcc.satOrd.Formula α :=
  (Formula.iSup fun s : Fin 4 → Bool =>
      (Formula.iInf fun i : Fin 4 => SatOcc.occF (s i) (Sum.inr 0) (Sum.inr i.succ)) ⊓
      Formula.iInf fun p : {p : Fin 4 × Fin 4 // p.1 ≠ p.2 ∧ s p.1 = s p.2} =>
        ∼(SatOcc.eqF (Sum.inr (p.1.1.succ : Fin 5)) (Sum.inr p.1.2.succ))).iExs (Fin 5)


-- @@ L158-170 verbatim
@[simp]
theorem realize_wideOrdF {A : Type} [Language.sat.Structure A] [LinearOrder A]
    {v : α → A} : (wideOrdF (α := α)).Realize v ↔ Wide A := by
  simp only [wideOrdF, Formula.realize_iExs, Formula.realize_iSup, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_not, SatOcc.realize_occF, SatOcc.realize_eqF,
    Sum.elim_inr]
  constructor
  · rintro ⟨e, s, hocc, hdist⟩
    exact ⟨e 0, fun i => e i.succ, s, hocc, fun i j hij hs => hdist ⟨(i, j), hij, hs⟩⟩
  · rintro ⟨c, x, s, hocc, hdist⟩
    refine ⟨Fin.cases c x, s, fun i => ?_, fun p => ?_⟩
    · simpa using hocc i
    · simpa using hdist p.1.1 p.1.2 p.2.1 p.2.2


-- @@ L172-172 verbatim
end Ordered


-- @@ L174-174 verbatim
end Semantics


-- @@ L176-176 verbatim
/-! ### The interpretation -/


-- @@ L178-186 verbatim
/-- The identity-like interpretation of SAT instances in 3SAT instances,
gated on the width check: a faithful copy if no clause is wide, an
unsatisfiable structure made of empty clauses otherwise. -/
noncomputable def threeSatToSat : FOInterpretation Language.sat Language.sat Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun _ => clF (0, 0) ⊔ wideS.relabel Empty.elim
    | _, .posIn => fun _ => posF (0, 0) (1, 0) ⊓ ∼(wideS.relabel Empty.elim)
    | _, .negIn => fun _ => negF (0, 0) (1, 0) ⊓ ∼(wideS.relabel Empty.elim)


-- @@ L188-188 verbatim
section Characterizations


-- @@ L190-190 verbatim
variable {A : Type} [Language.sat.Structure A]


-- @@ L192-196 verbatim
@[simp]
theorem isClause_iff (w : Fin 1 → A) :
    RelMap (M := threeSatToSat.Map A) satIsClause ![((), w)] ↔ IsCl (w 0) ∨ Wide A := by
  rw [FOInterpretation.relMap_map]
  simp [threeSatToSat]


-- @@ L198-203 verbatim
@[simp]
theorem posIn_iff (wc wx : Fin 1 → A) :
    RelMap (M := threeSatToSat.Map A) satPosIn ![((), wc), ((), wx)] ↔
      PosIn (wc 0) (wx 0) ∧ ¬Wide A := by
  rw [FOInterpretation.relMap_map]
  simp [threeSatToSat]


-- @@ L205-210 verbatim
@[simp]
theorem negIn_iff (wc wx : Fin 1 → A) :
    RelMap (M := threeSatToSat.Map A) satNegIn ![((), wc), ((), wx)] ↔
      NegIn (wc 0) (wx 0) ∧ ¬Wide A := by
  rw [FOInterpretation.relMap_map]
  simp [threeSatToSat]


-- @@ L212-212 verbatim
end Characterizations


-- @@ L214-214 verbatim
/-! ### Correctness -/


-- @@ L216-257 verbatim
/-- Correctness of the reduction: a CNF structure is a yes-instance of 3SAT
iff the interpreted CNF structure is satisfiable. -/
theorem threeSatisfiable_iff_satisfiable (A : Type) [Language.sat.Structure A] :
    ThreeSatisfiable A ↔ Satisfiable (threeSatToSat.Map A) := by
  by_cases hw : Wide A
  · -- wide input: both sides fail
    refine iff_of_false
      (fun h => (wide_iff_not_widthAtMostThree A).mp hw h.1) ?_
    rintro ⟨ν, hν⟩
    have hw' := hw
    obtain ⟨c, -, -, -, -⟩ := hw'
    obtain ⟨⟨⟨⟩, wx⟩, hx⟩ := hν ((), fun _ => c) ((isClause_iff _).mpr (Or.inr hw))
    rcases hx with ⟨hpos, -⟩ | ⟨hneg, -⟩
    · exact ((posIn_iff _ _).mp hpos).2 hw
    · exact ((negIn_iff _ _).mp hneg).2 hw
  · -- non-wide input: faithful copy
    have hwidth : WidthAtMostThree A := by
      by_contra h
      exact hw ((wide_iff_not_widthAtMostThree A).mpr h)
    rw [ThreeSatisfiable, and_iff_right hwidth]
    constructor
    · rintro ⟨ν, hν⟩
      refine ⟨fun p => ν (p.2 0), ?_⟩
      rintro ⟨⟨⟩, w⟩ hcl
      rcases (isClause_iff w).mp hcl with hcl' | hcl'
      · obtain ⟨z, hz⟩ := hν (w 0) hcl'
        rcases hz with ⟨hp, hT⟩ | ⟨hn, hT⟩
        · exact ⟨((), fun _ => z), Or.inl ⟨(posIn_iff _ _).mpr ⟨hp, hw⟩, hT⟩⟩
        · exact ⟨((), fun _ => z), Or.inr ⟨(negIn_iff _ _).mpr ⟨hn, hw⟩, hT⟩⟩
      · exact absurd hcl' hw
    · rintro ⟨ν, hν⟩
      refine ⟨fun a => ν ((), fun _ => a), ?_⟩
      intro c hc
      obtain ⟨⟨⟨⟩, wz⟩, hz⟩ := hν ((), fun _ => c) ((isClause_iff _).mpr (Or.inl hc))
      -- transport along `(fun _ => wz 0) = wz`, at raw product type
      have hsub : ∀ (g : Unit × (Fin 1 → A) → Prop) (w : Fin 1 → A),
          g ((), w) ↔ g ((), fun _ => w 0) := fun g w => by
        have hw : (fun _ => w 0) = w := funext fun i => congrArg w (Subsingleton.elim 0 i)
        rw [hw]
      rcases hz with ⟨hp, hT⟩ | ⟨hn, hT⟩
      · exact ⟨wz 0, Or.inl ⟨((posIn_iff _ _).mp hp).1, (hsub ν wz).mp hT⟩⟩
      · exact ⟨wz 0, Or.inr ⟨((negIn_iff _ _).mp hn).1, fun h => hT ((hsub ν wz).mpr h)⟩⟩


-- @@ L259-259 verbatim
end ThreeSatToSat


-- @@ L261-270 verbatim
open ThreeSatToSat in
/-- **3SAT FO-reduces to SAT.** The identity-like interpretation
`ThreeSatToSat.threeSatToSat`, gated on the first-order width check, maps a
CNF structure to a satisfiable CNF instance iff it is a yes-instance of
3SAT. -/
noncomputable def threeSat_fo_reduction_sat : ThreeSAT ≤ᶠᵒ SAT where
  Tag := Unit
  dim := 1
  toInterpretation := threeSatToSat
  correct A _ _ _ := threeSatisfiable_iff_satisfiable A


-- @@ L272-272 verbatim
end DescriptiveComplexity
