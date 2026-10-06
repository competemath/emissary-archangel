/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CircuitNumber.Defs
import DescriptiveComplexity.Problems.Cvp.Membership
import DescriptiveComplexity.Counting.FP
import DescriptiveComplexity.Syntax


-- @@ L11-29 verbatim
/-!
# The number written by a circuit is in FP

`DescriptiveComplexity.circuitNumber_mem_FP`: a definition in QFO(LFP)
(`DescriptiveComplexity.QLFPDef`) of `DescriptiveComplexity.CircuitNumber`.

* The fixed point is the one of the circuit value problem: the ten gate rules
  `DescriptiveComplexity.Cvp.cvpRules`, read in the larger vocabulary
  (`DescriptiveComplexity.HornClause.onLang`), whose least model is the
  evaluation of the gates (`DescriptiveComplexity.CircNum.lfpAssign_numRules_iff`).
* The output is the quantitative term
  `Σg. [out(g) ∧ T(g)] · Πh. ([out(h) ∧ h ≠ g ∧ below(h, g)] + 1)`
  (`DescriptiveComplexity.CircNum.numOut`): the inner product is two to the
  number of outputs strictly below `g`, a factor being `2` for each of them and
  `1` for every other element. This is the shape of the normal form in the
  proof that QFO(LFP) captures FP
  ([Arenas, Muñoz, Riveros 2020][arenas2020descriptive], Theorem 4.4), a
  number being written digit by digit.
-/


-- @@ L31-31 verbatim
namespace DescriptiveComplexity


-- @@ L33-33 verbatim
open FirstOrder


-- @@ L35-35 verbatim
open Language Structure


-- @@ L37-37 verbatim
/-! ### Rules read in a larger vocabulary -/


-- @@ L39-39 verbatim
section OnLang


-- @@ L41-41 verbatim
variable {L L' : Language.{0, 0}} {B : SOBlock} {k : ℕ}


-- @@ L43-45 verbatim
/-- A rule, its guard read in a larger vocabulary. -/
def HornClause.onLang (Φ : L →ᴸ L') (c : HornClause L B k) : HornClause L' B k :=
  ⟨Φ.onFormula c.guard, c.body, c.head⟩


-- @@ L47-47 verbatim
variable {A : Type} [L.Structure A] [L'.Structure A]


-- @@ L49-64 verbatim
/-- Rules read in a larger vocabulary derive the same tuples, over an
expansion of the structure. -/
theorem derives_onLang (Φ : L →ᴸ L') [Φ.IsExpansionOn A] (rules : List (HornClause L B k))
    (q : Σ i : B.ι, Fin (B.arity i) → A) :
    Derives (rules.map (HornClause.onLang Φ)) q ↔ Derives rules q := by
  constructor
  · intro h
    induction h with
    | @rule c hc a ha v hg _ ih =>
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
      exact .rule hc₀ ha ((LHom.realize_onFormula Φ _).mp hg) ih
  · intro h
    induction h with
    | @rule c hc a ha v hg _ ih =>
      exact .rule (c := c.onLang Φ) (List.mem_map_of_mem hc) ha
        ((LHom.realize_onFormula Φ _).mpr hg) ih


-- @@ L66-69 verbatim
/-- The least fixed point of rules read in a larger vocabulary. -/
theorem lfpAssign_onLang (Φ : L →ᴸ L') [Φ.IsExpansionOn A] (rules : List (HornClause L B k)) :
    lfpAssign (A := A) (rules.map (HornClause.onLang Φ)) = lfpAssign rules :=
  funext fun i => funext fun x => propext (derives_onLang Φ rules ⟨i, x⟩)


-- @@ L71-71 verbatim
end OnLang


-- @@ L73-82 verbatim
/-- **A product of factors `1` and `2`** is two to the number of factors `2`:
the place value of a digit, as a product over the universe. -/
theorem finprod_boole_add_one {A : Type} [Finite A] (P : A → Prop) [DecidablePred P] :
    ∏ᶠ h : A, ((if P h then 1 else 0) + 1) = 2 ^ Nat.card {h : A // P h} := by
  let := Fintype.ofFinite A
  have h2 : ∀ h : A, ((if P h then 1 else 0) + 1 : ℕ) = if P h then 2 else 1 := fun h => by
    split_ifs <;> rfl
  rw [finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [h2]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]


-- @@ L84-84 verbatim
namespace CircNum


-- @@ L86-86 verbatim
/-! ### The fixed point: the gate rules -/


-- @@ L88-89 verbatim
/-- The vocabulary of the rules: circuits writing a number, with the order. -/
abbrev numLang : Language := Language.numCircuit.sum Language.order


-- @@ L91-94 verbatim
/-- The vocabulary of the rules of the circuit value problem, read in the one
of the rules here. -/
def ordHom : Cvp.cvLang →ᴸ numLang :=
  LHom.sumMap circuitOfNum (LHom.id Language.order)


-- @@ L96-99 verbatim
instance ordHom_isExpansionOn (A : Type) [Language.numCircuit.Structure A] [LinearOrder A] :
    ordHom.IsExpansionOn A where
  map_onFunction := fun {_} f _ => isEmptyElim f
  map_onRelation := fun {_} R _ => by cases R <;> rfl


-- @@ L101-104 verbatim
/-- The gate rules of `DescriptiveComplexity.Cvp.cvpRules`, over the larger
vocabulary. -/
noncomputable def numRules : List (HornClause numLang Cvp.valBlock Cvp.nvars) :=
  Cvp.cvpRules.map (HornClause.onLang ordHom)


-- @@ L106-110 verbatim
/-- **The least model of the rules is the evaluation of the gates.** -/
theorem lfpAssign_numRules_iff {A : Type} [Language.numCircuit.Structure A] [LinearOrder A]
    {b : Bool} {x : Fin 1 → A} : lfpAssign (A := A) numRules b x ↔ GateVal b (x 0) := by
  rw [numRules, lfpAssign_onLang]
  exact Cvp.lfpAssign_iff


-- @@ L112-112 verbatim
/-! ### The output term -/


-- @@ L114-115 verbatim
/-- The vocabulary of the output: the rules', and the two rails. -/
abbrev outLang : Language := numLang.sum Cvp.valBlock.lang


-- @@ L117-118 verbatim
/-- “Is an output gate”, in the vocabulary of the output. -/
abbrev oOut : outLang.Relations 1 := Sum.inl (Sum.inl ncOut)


-- @@ L120-121 verbatim
/-- The comparison of the outputs, in the vocabulary of the output. -/
abbrev oBelow : outLang.Relations 2 := Sum.inl (Sum.inl ncBelow)


-- @@ L123-124 verbatim
/-- The rail of the gates deriving `1`, in the vocabulary of the output. -/
abbrev oTrue : outLang.Relations 1 := Sum.inr (varSym Cvp.valBlock true)


-- @@ L126-129 verbatim
/-- “`g` is an output gate deriving `1`”. -/
noncomputable def bitF : outLang.Formula (Empty ⊕ Fin 1) :=
  Relations.formula₁ oOut (Term.var (Sum.inr 0)) ⊓
    Relations.formula₁ oTrue (Term.var (Sum.inr 0))


-- @@ L131-135 verbatim
/-- “`h` is an output gate strictly below `g`”. -/
noncomputable def lowF : outLang.Formula ((Empty ⊕ Fin 1) ⊕ Fin 1) :=
  Relations.formula₁ oOut (Term.var (Sum.inr 0)) ⊓
    ∼(Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl (Sum.inr 0)))) ⊓
    Relations.formula₂ oBelow (Term.var (Sum.inr 0)) (Term.var (Sum.inl (Sum.inr 0)))


-- @@ L137-142 expanded
/-- “The outputs are linearly ordered.” -/
noncomputable def outOrdS : outLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
        ((FirstOrder.Language.Relations.formula₁ oOut
              (FirstOrder.Language.Term.var (Sum.inr 0))).imp
          (FirstOrder.Language.Relations.formula₂ oBelow (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inr 0)))) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 1)
        (FirstOrder.Language.Formula.iAlls (Fin 1)
          (FirstOrder.Language.Formula.iAlls (Fin 1)
            ((FirstOrder.Language.Relations.formula₁ oOut
                  (FirstOrder.Language.Term.var (Sum.inl (Sum.inl (Sum.inr 0))))).imp
              ((FirstOrder.Language.Relations.formula₁ oOut
                    (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))).imp
                ((FirstOrder.Language.Relations.formula₁ oOut
                      (FirstOrder.Language.Term.var (Sum.inr 0))).imp
                  ((FirstOrder.Language.Relations.formula₂ oBelow
                        (FirstOrder.Language.Term.var (Sum.inl (Sum.inl (Sum.inr 0))))
                        (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))).imp
                    ((FirstOrder.Language.Relations.formula₂ oBelow
                          (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                          (FirstOrder.Language.Term.var (Sum.inr 0))).imp
                      (FirstOrder.Language.Relations.formula₂ oBelow
                        (FirstOrder.Language.Term.var (Sum.inl (Sum.inl (Sum.inr 0))))
                        (FirstOrder.Language.Term.var (Sum.inr 0)))))))))) ⊓
    (FirstOrder.Language.Formula.iAlls (Fin 1)
        (FirstOrder.Language.Formula.iAlls (Fin 1)
          ((FirstOrder.Language.Relations.formula₁ oOut
                (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))).imp
            ((FirstOrder.Language.Relations.formula₁ oOut
                  (FirstOrder.Language.Term.var (Sum.inr 0))).imp
              ((FirstOrder.Language.Relations.formula₂ oBelow
                    (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                    (FirstOrder.Language.Term.var (Sum.inr 0))).imp
                ((FirstOrder.Language.Relations.formula₂ oBelow
                      (FirstOrder.Language.Term.var (Sum.inr 0))
                      (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))).imp
                  (FirstOrder.Language.Term.equal
                    (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                    (FirstOrder.Language.Term.var (Sum.inr 0)))))))) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 1)
        (FirstOrder.Language.Formula.iAlls (Fin 1)
          ((FirstOrder.Language.Relations.formula₁ oOut
                (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))).imp
            ((FirstOrder.Language.Relations.formula₁ oOut
                  (FirstOrder.Language.Term.var (Sum.inr 0))).imp
              (FirstOrder.Language.Relations.formula₂ oBelow
                  (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                  (FirstOrder.Language.Term.var (Sum.inr 0)) ⊔
                FirstOrder.Language.Relations.formula₂ oBelow
                  (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0))))))))


-- @@ L144-147 verbatim
/-- **The output term**: `[the outputs are linearly ordered] · Σg. [g holds
the digit 1] · Πh. ([h is an output strictly below g] + 1)`. -/
noncomputable def numOut : QTerm outLang Empty :=
  .mul (.ind outOrdS) (.sum 1 (.mul (.ind bitF) (.prod 1 (.add (.ind lowF) (.const 1)))))


-- @@ L149-154 verbatim
/-- The definition of the number written by a circuit in QFO(LFP). -/
noncomputable def numDef : QLFPDef Language.numCircuit where
  B := Cvp.valBlock
  k := Cvp.nvars
  rules := numRules
  out := numOut


-- @@ L156-156 verbatim
section Value


-- @@ L158-158 verbatim
variable {A : Type} [Language.numCircuit.Structure A] [LinearOrder A]


-- @@ L160-166 verbatim
theorem realize_bitF (w : Fin 1 → A) :
    (@Formula.Realize outLang A
        (@sumStructure _ _ A _ (Cvp.valBlock.structure (lfpAssign (A := A) numRules))) _ bitF
        (Sum.elim default w)) ↔ OutBit (w 0) := by
  let := Cvp.valBlock.structure (lfpAssign (A := A) numRules)
  rw [bitF, Formula.realize_inf, Formula.realize_rel₁, Formula.realize_rel₁]
  exact and_congr Iff.rfl (lfpAssign_numRules_iff (b := true) (x := ![w 0]))


-- @@ L168-175 verbatim
theorem realize_lowF (w u : Fin 1 → A) :
    (@Formula.Realize outLang A
        (@sumStructure _ _ A _ (Cvp.valBlock.structure (lfpAssign (A := A) numRules))) _ lowF
        (Sum.elim (Sum.elim default w) u)) ↔ LowerOut (w 0) (u 0) := by
  let := Cvp.valBlock.structure (lfpAssign (A := A) numRules)
  rw [lowF, Formula.realize_inf, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Formula.realize_equal]
  exact and_assoc


-- @@ L177-190 verbatim
theorem realize_outOrdS :
    (@Sentence.Realize outLang A
        (@sumStructure _ _ A _ (Cvp.valBlock.structure (lfpAssign (A := A) numRules))) outOrdS) ↔
      OutOrder A := by
  let := Cvp.valBlock.structure (lfpAssign (A := A) numRules)
  rw [outOrdS, OutOrder, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, Formula.realize_rel₁, Formula.realize_rel₂, Formula.realize_equal,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  refine and_assoc.trans (and_congr ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩
    (and_congr ⟨fun h a b c => h (fun _ => a) (fun _ => b) fun _ => c,
        fun h i j k => h (i 0) (j 0) (k 0)⟩
      (and_congr ⟨fun h a b => h (fun _ => a) fun _ => b, fun h i j => h (i 0) (j 0)⟩
        ⟨fun h a b => h (fun _ => a) fun _ => b, fun h i j => h (i 0) (j 0)⟩)))


-- @@ L192-207 verbatim
open Classical in
/-- **The definition computes the number written by the circuit.** -/
theorem numDef_value [Finite A] : numDef.value A = circuitNumber A := by
  have hord := realize_outOrdS (A := A)
  let := Cvp.valBlock.structure (lfpAssign (A := A) numRules)
  have hprod : ∀ w : Fin 1 → A,
      ∏ᶠ u : Fin 1 → A, ((if LowerOut (w 0) (u 0) then 1 else 0) + 1) = 2 ^ outRank (w 0) :=
    fun w => (finprod_comp_equiv (Equiv.funUnique (Fin 1) A)
      (f := fun h => (if LowerOut (w 0) h then 1 else 0) + 1)).trans
        (finprod_boole_add_one _)
  rw [QLFPDef.value, QTerm.value, circuitNumber]
  change (numOut.eval (A := A) default) = _
  simp only [numOut, QTerm.eval, realize_bitF, realize_lowF, hprod, ite_mul, one_mul, zero_mul]
  have hord' : (Formula.Realize outOrdS (default : Empty → A)) ↔ OutOrder A := hord
  exact if_congr hord' (finsum_comp_equiv (Equiv.funUnique (Fin 1) A)
    (f := fun g => if OutBit g then 2 ^ outRank g else 0)) rfl


-- @@ L209-209 verbatim
end Value


-- @@ L211-211 verbatim
end CircNum


-- @@ L213-216 verbatim
/-- **The number written by a circuit is definable in QFO(LFP)**: the gate
rules, and a term writing the number digit by digit. -/
theorem circuitNumber_fpDefinable : FPDefinable CircuitNumber :=
  ⟨CircNum.numDef, fun _A _ _ _ _ => CircNum.numDef_value.symm⟩


-- @@ L218-220 verbatim
/-- **The number written by a circuit is in FP.** -/
theorem circuitNumber_mem_FP : CircuitNumber ∈ FP :=
  circuitNumber_fpDefinable


-- @@ L222-222 verbatim
end DescriptiveComplexity
