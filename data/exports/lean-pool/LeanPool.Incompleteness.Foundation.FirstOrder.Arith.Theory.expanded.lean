/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Hierarchy


-- @@ L10-10 verbatim
/-! # Theory -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO


-- @@ L17-17 verbatim
namespace FirstOrder


-- @@ L19-19 verbatim
open Arith


-- @@ L21-21 verbatim
variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]


-- @@ L23-25 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  Arrow.arrow (LO.FirstOrder.Rewriting.substitute φ (vecCons (Semiterm.numeral 0) ![]))
    (Arrow.arrow
      (UnivQuantifier.univ
        (Arrow.arrow (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 ![]))
          (LO.FirstOrder.Rewriting.substitute φ
            (vecCons (Semiterm.Operator.Add.add.operator ![#0, Semiterm.numeral 1]) ![]))))
      (UnivQuantifier.univ (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 ![]))))


-- @@ L27-29 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orderInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  Arrow.arrow
    (UnivQuantifier.univ
      (Arrow.arrow (Semiformula.ballLT (#0) (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 ![])))
        (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 ![]))))
    (UnivQuantifier.univ (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 ![])))


-- @@ L31-33 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def leastNumber {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  Arrow.arrow (ExQuantifier.ex (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 ![])))
    (ExQuantifier.ex
      (Wedge.wedge (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 ![]))
        (Semiformula.ballLT (#0)
          (Tilde.tilde (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 ![]))))))


-- @@ L35-35 verbatim
namespace Theory


-- @@ L37-37 verbatim
variable (L)


-- @@ L39-45 expanded
/-- Imported declaration from the Incompleteness formalization. -/
inductive CobhamR0 : Theory oRing
  | equal : ∀ φ ∈ eqAxiom, CobhamR0 φ
  |
  Ω₁ (n m : ℕ) :
    CobhamR0
      (Semiformula.Operator.operator Operator.Eq.eq
        ![Semiterm.Operator.Add.add.operator ![Semiterm.numeral n, Semiterm.numeral m],
          Semiterm.numeral (n + m)])
  |
  Ω₂ (n m : ℕ) :
    CobhamR0
      (Semiformula.Operator.operator Operator.Eq.eq
        ![Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral n, Semiterm.numeral m],
          Semiterm.numeral (n * m)])
  |
  Ω₃ (n m : ℕ) :
    n ≠ m →
      CobhamR0
        (Tilde.tilde
          (Semiformula.Operator.operator Operator.Eq.eq ![Semiterm.numeral n, Semiterm.numeral m]))
  |
  Ω₄ (n : ℕ) :
    CobhamR0
      (UnivQuantifier.univ
        (LogicalConnective.iff
          (Semiformula.Operator.operator Operator.LT.lt ![#0, Semiterm.numeral n])
          (disjLt (fun i ↦ Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral i])
            n)))


-- @@ L47-48 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐑₀" => CobhamR0


-- @@ L50-50 verbatim
variable {L}


-- @@ L52-53 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addZero : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.Eq.eq
    ![Semiterm.Operator.Add.add.operator ![&0, Semiterm.numeral 0], &0]


-- @@ L54-56 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addAssoc : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.Eq.eq
    ![Semiterm.Operator.Add.add.operator ![Semiterm.Operator.Add.add.operator ![&0, &1], &2],
      Semiterm.Operator.Add.add.operator ![&0, Semiterm.Operator.Add.add.operator ![&1, &2]]]


-- @@ L57-58 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addComm : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.Eq.eq
    ![Semiterm.Operator.Add.add.operator ![&0, &1], Semiterm.Operator.Add.add.operator ![&1, &0]]


-- @@ L59-61 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addEqOfLt : SyntacticFormula L :=
  Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![&0, &1])
    (ExQuantifier.ex
      (Semiformula.Operator.operator Operator.Eq.eq
        ![Semiterm.Operator.Add.add.operator ![&0, #0], &1]))


-- @@ L62-63 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.zeroLe : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.LE.le ![Semiterm.numeral 0, &0]


-- @@ L64-65 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.zeroLtOne : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 0, Semiterm.numeral 1]


-- @@ L66-67 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.oneLeOfZeroLt : SyntacticFormula L :=
  Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 0, &0])
    (Semiformula.Operator.operator Operator.LE.le ![Semiterm.numeral 1, &0])


-- @@ L68-70 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.addLtAdd : SyntacticFormula L :=
  Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![&0, &1])
    (Semiformula.Operator.operator Operator.LT.lt
      ![Semiterm.Operator.Add.add.operator ![&0, &2], Semiterm.Operator.Add.add.operator ![&1, &2]])


-- @@ L71-72 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulZero : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.Eq.eq
    ![Semiterm.Operator.Mul.mul.operator ![&0, Semiterm.numeral 0], Semiterm.numeral 0]


-- @@ L73-74 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulOne : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.Eq.eq
    ![Semiterm.Operator.Mul.mul.operator ![&0, Semiterm.numeral 1], &0]


-- @@ L75-77 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulAssoc : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.Eq.eq
    ![Semiterm.Operator.Mul.mul.operator ![Semiterm.Operator.Mul.mul.operator ![&0, &1], &2],
      Semiterm.Operator.Mul.mul.operator ![&0, Semiterm.Operator.Mul.mul.operator ![&1, &2]]]


-- @@ L78-79 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulComm : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.Eq.eq
    ![Semiterm.Operator.Mul.mul.operator ![&0, &1], Semiterm.Operator.Mul.mul.operator ![&1, &0]]


-- @@ L80-82 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.mulLtMul : SyntacticFormula L :=
  Arrow.arrow
    (Wedge.wedge (Semiformula.Operator.operator Operator.LT.lt ![&0, &1])
      (Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 0, &2]))
    (Semiformula.Operator.operator Operator.LT.lt
      ![Semiterm.Operator.Mul.mul.operator ![&0, &2], Semiterm.Operator.Mul.mul.operator ![&1, &2]])


-- @@ L83-85 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.distr : SyntacticFormula L :=
  Semiformula.Operator.operator Operator.Eq.eq
    ![Semiterm.Operator.Mul.mul.operator ![&0, Semiterm.Operator.Add.add.operator ![&1, &2]],
      Semiterm.Operator.Add.add.operator
        ![Semiterm.Operator.Mul.mul.operator ![&0, &1],
          Semiterm.Operator.Mul.mul.operator ![&0, &2]]]


-- @@ L86-87 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.ltIrrefl : SyntacticFormula L :=
  Tilde.tilde (Semiformula.Operator.operator Operator.LT.lt ![&0, &0])


-- @@ L88-90 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.ltTrans : SyntacticFormula L :=
  Arrow.arrow
    (Wedge.wedge (Semiformula.Operator.operator Operator.LT.lt ![&0, &1])
      (Semiformula.Operator.operator Operator.LT.lt ![&1, &2]))
    (Semiformula.Operator.operator Operator.LT.lt ![&0, &2])


-- @@ L91-93 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.Arith.ltTri : SyntacticFormula L :=
  Vee.vee (Semiformula.Operator.operator Operator.LT.lt ![&0, &1])
    (Vee.vee (Semiformula.Operator.operator Operator.Eq.eq ![&0, &1])
      (Semiformula.Operator.operator Operator.LT.lt ![&1, &0]))


-- @@ L95-114 expanded
/-- Imported declaration from the Incompleteness formalization. -/
inductive PeanoMinus : Theory oRing
  | equal : ∀ φ ∈ eqAxiom, PeanoMinus φ
  | addZero : PeanoMinus Arith.addZero
  | addAssoc : PeanoMinus Arith.addAssoc
  | addComm : PeanoMinus Arith.addComm
  | addEqOfLt : PeanoMinus Arith.addEqOfLt
  | zeroLe : PeanoMinus Arith.zeroLe
  | zeroLtOne : PeanoMinus Arith.zeroLtOne
  | oneLeOfZeroLt : PeanoMinus Arith.oneLeOfZeroLt
  | addLtAdd : PeanoMinus Arith.addLtAdd
  | mulZero : PeanoMinus Arith.mulZero
  | mulOne : PeanoMinus Arith.mulOne
  | mulAssoc : PeanoMinus Arith.mulAssoc
  | mulComm : PeanoMinus Arith.mulComm
  | mulLtMul : PeanoMinus Arith.mulLtMul
  | distr : PeanoMinus Arith.distr
  | ltIrrefl : PeanoMinus Arith.ltIrrefl
  | ltTrans : PeanoMinus Arith.ltTrans
  | ltTri : PeanoMinus Arith.ltTri


-- @@ L116-117 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐏𝐀⁻" => PeanoMinus


-- @@ L119-119 verbatim
variable (L)


-- @@ L121-123 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def indScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  { ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = succInd φ }


-- @@ L125-126 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev iOpen : Theory oRing :=
  PeanoMinus + indScheme oRing Semiformula.Open


-- @@ L128-129 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈open" => iOpen


-- @@ L131-132 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev indH (Γ : Polarity) (k : ℕ) : Theory oRing :=
  PeanoMinus + indScheme oRing (Arith.Hierarchy Γ k)


-- @@ L134-135 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:max "𝐈𝐍𝐃" => indH


-- @@ L137-138 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev iSigma (k : ℕ) : Theory oRing :=
  (indH SigmaSymbol.sigma) k


-- @@ L140-141 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:max "𝐈Sg" => iSigma


-- @@ L143-144 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈Sg0" => iSigma 0


-- @@ L146-147 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev iPi (k : ℕ) : Theory oRing :=
  (indH PiSymbol.pi) k


-- @@ L149-150 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:max "𝐈Pg" => iPi


-- @@ L152-153 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈Pg0" => iPi 0


-- @@ L155-156 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈Sg1" => iSigma 1


-- @@ L158-159 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐈Pg1" => iPi 1


-- @@ L161-162 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev peano : Theory oRing :=
  PeanoMinus + indScheme oRing Set.univ


-- @@ L164-165 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐏𝐀" => peano


-- @@ L167-167 verbatim
variable {L}


-- @@ L169-175 expanded
lemma coe_indH_subset_indH :
    (indScheme oRing (Arith.Hierarchy Γ ν) : Theory L) ⊆ indScheme L (Arith.Hierarchy Γ ν) :=
  by
  simp only [indScheme, Set.image_subset_iff, Set.preimage_ofPred_eq, Set.ofPred_subset_ofPred,
    forall_exists_index, and_imp]
  rintro _ φ Hp rfl
  exact
    ⟨Semiformula.lMap (Language.oringEmb : oRing →ᵥ L) φ, Hierarchy.oringEmb Hp, by
      simp [succInd, Semiformula.lMap_substs]⟩


-- @@ L177-180 expanded
lemma indScheme_subset (h : ∀ {φ : Semiformula oRing ℕ 1}, C φ → C' φ) :
    indScheme oRing C ⊆ indScheme oRing C' :=
  by
  rintro _ ⟨φ, hp, rfl⟩
  exact ⟨φ, h hp, rfl⟩


-- @@ L182-183 expanded
lemma iSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : iSigma s₁ ⊆ iSigma s₂ :=
  Set.union_subset_union_right _ (indScheme_subset (fun H ↦ H.mono h))


-- @@ L185-187 expanded
instance : WeakerThan PeanoMinus ((indH Γ) n) :=
  Entailment.WeakerThan.ofSubset
    (by
      rw [indH, Theory.add_def]
      exact Set.subset_union_left)


-- @@ L189-189 expanded
instance : WeakerThan eqAxiom CobhamR0 :=
  Entailment.WeakerThan.ofSubset <| fun φ hp ↦ CobhamR0.equal φ hp


-- @@ L191-191 expanded
instance : WeakerThan eqAxiom PeanoMinus :=
  Entailment.WeakerThan.ofSubset <| fun φ hp ↦ PeanoMinus.equal φ hp


-- @@ L193-193 expanded
instance : WeakerThan eqAxiom ((indH Γ) n) :=
  Entailment.WeakerThan.trans (inferInstance : WeakerThan eqAxiom PeanoMinus) inferInstance


-- @@ L195-195 expanded
instance : WeakerThan eqAxiom iOpen :=
  Entailment.WeakerThan.trans (inferInstance : WeakerThan eqAxiom PeanoMinus) inferInstance


-- @@ L197-199 expanded
instance (i) : WeakerThan iOpen (iSigma i) :=
  Entailment.WeakerThan.ofSubset <|
    Set.union_subset_union_right _ <| indScheme_subset Hierarchy.of_open


-- @@ L201-202 expanded
lemma iSigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : WeakerThan (iSigma s₁) (iSigma s₂) :=
  Entailment.WeakerThan.ofSubset (iSigma_subset_mono h)


-- @@ L204-204 expanded
instance : WeakerThan (iSigma 0) (iSigma 1) :=
  iSigma_weakerThan_of_le (by decide)


-- @@ L206-208 expanded
instance (i) : WeakerThan (iSigma i) peano :=
  Entailment.WeakerThan.ofSubset <|
    Set.union_subset_union_right _ <| indScheme_subset (by intros; trivial)


-- @@ L210-210 verbatim
example (a b : ℕ) : Set.Finite {a, b} := by simp only [Set.finite_singleton, Set.Finite.insert]


-- @@ L212-272 expanded
@[simp]
lemma _root_.LO.FirstOrder.Theory.PeanoMinus.finite : Set.Finite PeanoMinus :=
  by
  have :
    PeanoMinus =
      eqAxiom ∪
        { Arith.addZero, Arith.addAssoc, Arith.addComm, Arith.addEqOfLt, Arith.zeroLe,
          Arith.zeroLtOne, Arith.oneLeOfZeroLt, Arith.addLtAdd, Arith.mulZero, Arith.mulOne,
          Arith.mulAssoc, Arith.mulComm, Arith.mulLtMul, Arith.distr, Arith.ltIrrefl, Arith.ltTrans,
          Arith.ltTri } :=
    by
    ext φ; constructor
    · rintro ⟨⟩
      case equal => left; assumption
      case addZero => tauto
      case addAssoc => tauto
      case addComm => tauto
      case addEqOfLt => tauto
      case zeroLe => tauto
      case zeroLtOne => tauto
      case oneLeOfZeroLt => tauto
      case addLtAdd => tauto
      case mulZero => tauto
      case mulOne => tauto
      case mulAssoc => tauto
      case mulComm => tauto
      case mulLtMul => tauto
      case distr => tauto
      case ltIrrefl => tauto
      case ltTrans => tauto
      case ltTri => tauto
    · rintro
        (h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl)
      · exact PeanoMinus.equal _ h
      · exact PeanoMinus.addZero
      · exact PeanoMinus.addAssoc
      · exact PeanoMinus.addComm
      · exact PeanoMinus.addEqOfLt
      · exact PeanoMinus.zeroLe
      · exact PeanoMinus.zeroLtOne
      · exact PeanoMinus.oneLeOfZeroLt
      · exact PeanoMinus.addLtAdd
      · exact PeanoMinus.mulZero
      · exact PeanoMinus.mulOne
      · exact PeanoMinus.mulAssoc
      · exact PeanoMinus.mulComm
      · exact PeanoMinus.mulLtMul
      · exact PeanoMinus.distr
      · exact PeanoMinus.ltIrrefl
      · exact PeanoMinus.ltTrans
      · exact PeanoMinus.ltTri
  simp_all


-- @@ L274-274 verbatim
end Theory


-- @@ L276-276 verbatim
end FirstOrder


-- @@ L278-278 verbatim
end LO
