/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat.CountingDecision


-- @@ L8-33 verbatim
/-!
# SelMajSAT and SelEqSAT: complete problems for PP and C₌P

A CNF formula with a **selected variable** (`FirstOrder.Language.satSel`),
and the two counts of its models by the value of that variable
(`DescriptiveComplexity.SharpSelSAT true`, `DescriptiveComplexity.SharpSelSAT false`),
both in `#P`. The two decision problems comparing them:

* **SelMajSAT** (`DescriptiveComplexity.SelMajSAT`): the selected variable is
  true in more models than it is false – **`PP`-complete**
  (`DescriptiveComplexity.selMajSat_PP_complete`), the form the classical
  MajSAT of [Gill 1977][gill1977computational] takes when the instance may not
  count its own variables;
* **SelEqSAT** (`DescriptiveComplexity.SelEqSAT`): it is true in exactly as
  many models as it is false – **`C₌P`-complete**
  (`DescriptiveComplexity.selEqSat_CeqP_complete`).

Hardness is one construction for both: a problem of either class compares the
witness counts of two kernels; the pair kernel of
`DescriptiveComplexity.Counting.KernelPair` puts them in one kernel with a
selector, the parsimonious Tseitin interpretation turns it into a CNF formula
whose models are its witnesses, and the selected variable is the one of the
selector (`DescriptiveComplexity.PairSel.pairTseitinInterp`). The models in
which the selected variable is true are then the witnesses of the first
kernel, and the others those of the second.
-/


-- @@ L35-35 verbatim
namespace FirstOrder


-- @@ L37-37 verbatim
namespace Language


-- @@ L39-42 verbatim
/-- The symbol selecting a variable. -/
fo_language selMark with sm where
  /-- `sel x`: the variable `x` is selected. -/
  sel : 1


-- @@ L44-45 verbatim
/-- The relational language of CNF formulas with a selected variable. -/
abbrev satSel : Language.{0, 0} := Language.sat.sum Language.selMark


-- @@ L47-47 verbatim
end Language


-- @@ L49-49 verbatim
end FirstOrder


-- @@ L51-51 verbatim
namespace DescriptiveComplexity


-- @@ L53-53 verbatim
open FirstOrder


-- @@ L55-55 verbatim
open Language Structure


-- @@ L57-59 verbatim
/-- “Is selected”, in the vocabulary of CNF formulas with a selected
variable. -/
abbrev ssSel : Language.satSel.Relations 1 := Sum.inr smSel


-- @@ L61-64 verbatim
/-- A CNF formula with a selected variable is a CNF formula. -/
instance satSelStructure (A : Type) [Language.satSel.Structure A] :
    Language.sat.Structure A :=
  (LHom.sumInl : Language.sat →ᴸ Language.satSel).reduct A


-- @@ L66-69 verbatim
/-- The forgetful isomorphism of the underlying CNF formulas. -/
def satSelEquiv {A B : Type} [Language.satSel.Structure A] [Language.satSel.Structure B]
    (e : A ≃[Language.satSel] B) : A ≃[Language.sat] B :=
  ⟨e.toEquiv, fun {_} f _ => isEmptyElim f, fun {_} r x => e.map_rel' (Sum.inl r) x⟩


-- @@ L71-71 verbatim
/-! ### The two counts -/


-- @@ L73-73 verbatim
section Counts


-- @@ L75-75 verbatim
variable (A : Type) [Language.satSel.Structure A]


-- @@ L77-80 verbatim
/-- A model of the formula in which every selected variable has the value
`b`. -/
def SelModel (b : Bool) (ν : A → Prop) : Prop :=
  SatModel A ν ∧ ∀ x : A, RelMap ssSel ![x] → (ν x ↔ b = true)


-- @@ L82-84 verbatim
/-- The vocabulary of the kernel: CNF formulas with a selected variable, and
the truth-assignment variable. -/
abbrev selSOLang : Language := Language.satSel.sum satAssignBlock.lang


-- @@ L86-87 verbatim
/-- “Is selected”, in the kernel's vocabulary. -/
abbrev kSelSym : selSOLang.Relations 1 := Sum.inl ssSel


-- @@ L89-90 verbatim
/-- The truth-assignment symbol in the kernel's vocabulary. -/
abbrev kNuSelSym : selSOLang.Relations 1 := Sum.inr satNuSym


-- @@ L92-94 verbatim
/-- The kernel of `#SAT`, read in the kernel's vocabulary. -/
def selHom : satSOLang →ᴸ selSOLang :=
  LHom.sumMap LHom.sumInl (LHom.id _)


-- @@ L96-100 expanded
/-- The kernel: a model of the formula, in which every selected variable has
the value `b`. -/
noncomputable def selKernel (b : Bool) : selSOLang.Sentence :=
  selHom.onSentence sharpSatKernel ⊓
    if b then
      FirstOrder.Language.Formula.iAlls (Fin 1)
        ((FirstOrder.Language.Relations.formula₁ kSelSym
              (FirstOrder.Language.Term.var (Sum.inr 0))).imp
          (FirstOrder.Language.Relations.formula₁ kNuSelSym
            (FirstOrder.Language.Term.var (Sum.inr 0))))
    else
      FirstOrder.Language.Formula.iAlls (Fin 1)
        ((FirstOrder.Language.Relations.formula₁ kSelSym
              (FirstOrder.Language.Term.var (Sum.inr 0))).imp
          (FirstOrder.Language.BoundedFormula.not
            (FirstOrder.Language.Relations.formula₁ kNuSelSym
              (FirstOrder.Language.Term.var (Sum.inr 0)))))


-- @@ L102-102 verbatim
variable {A}


-- @@ L104-108 verbatim
instance selHom_isExpansionOn (ρ : satAssignBlock.Assignment A) :
    @LHom.IsExpansionOn _ _ selHom A (@sumStructure _ _ A _ (satAssignBlock.structure ρ))
      (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) :=
  let := satAssignBlock.structure ρ
  ⟨fun f _ => by rcases f with f | f <;> rfl, fun r _ => by rcases r with r | r <;> rfl⟩


-- @@ L110-130 verbatim
theorem realize_selKernel (b : Bool) (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize selSOLang A (@sumStructure _ _ A _ (satAssignBlock.structure ρ))
      (selKernel b)) ↔ SelModel A b ((satAssignEquiv A).symm ρ) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := selSOLang) (M := A) kNuSelSym w ↔ (satAssignEquiv A).symm ρ (w 0) := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [selKernel, SelModel]
  refine Formula.realize_inf.trans (and_congr ((LHom.realize_onSentence (φ := selHom) A
    sharpSatKernel).trans (realize_sharpSatKernel ρ)) ?_)
  cases b
  · rw [ite_eq_right (by simp)]
    simp only [Bool.false_eq_true, iff_false, Formula.realize_iAlls, Formula.realize_imp,
      Formula.realize_not, Formula.realize_rel₁, Term.realize_var, Sum.elim_inr, hsub]
    exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩
  · rw [ite_eq_left rfl]
    simp only [iff_true, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
      Term.realize_var, Sum.elim_inr, hsub]
    exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩


-- @@ L132-135 verbatim
theorem card_selModel_eq_witnessCount (b : Bool) :
    Nat.card {ν : A → Prop // SelModel A b ν} = witnessCount satAssignBlock (selKernel b) A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_selKernel, Equiv.symm_apply_apply])


-- @@ L137-137 verbatim
end Counts


-- @@ L139-145 verbatim
/-- **The number of models of a CNF formula in which the selected variable
has the value `b`.** -/
noncomputable def SharpSelSAT (b : Bool) : CountingProblem Language.satSel where
  Count := fun A inst => Nat.card {ν : A → Prop // @SelModel A inst b ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_selModel_eq_witnessCount, card_selModel_eq_witnessCount]
    exact witnessCount_iso satAssignBlock (selKernel b) e


-- @@ L147-149 verbatim
theorem sharpSelSat_apply (b : Bool) (A : Type) [Language.satSel.Structure A] :
    SharpSelSAT b A = Nat.card {ν : A → Prop // SelModel A b ν} :=
  rfl


-- @@ L151-154 verbatim
/-- Both counts are in `#P`. -/
theorem sharpSelSat_mem_sharpP (b : Bool) : SharpSelSAT b ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_selModel_eq_witnessCount (A := A) b).symm)
    (sharpPDefinable_ofKernel satAssignBlock (selKernel b))


-- @@ L156-156 verbatim
/-! ### The two problems -/


-- @@ L158-163 verbatim
/-- **SelMajSAT**: the selected variable is true in more models than it is
false. -/
noncomputable def SelMajSAT : DecisionProblem Language.satSel where
  Holds := fun A inst => @SharpSelSAT false A inst < @SharpSelSAT true A inst
  iso_invariant := fun e => by
    rw [(SharpSelSAT false).iso_invariant e, (SharpSelSAT true).iso_invariant e]


-- @@ L165-170 verbatim
/-- **SelEqSAT**: the selected variable is true in exactly as many models as
it is false. -/
noncomputable def SelEqSAT : DecisionProblem Language.satSel where
  Holds := fun A inst => @SharpSelSAT true A inst = @SharpSelSAT false A inst
  iso_invariant := fun e => by
    rw [(SharpSelSAT false).iso_invariant e, (SharpSelSAT true).iso_invariant e]


-- @@ L172-174 verbatim
theorem selMajSat_mem_PP : SelMajSAT ∈ PP :=
  mem_countClass_of_sharpP (sharpSelSat_mem_sharpP true) (sharpSelSat_mem_sharpP false)
    fun _ _ _ _ => ⟨trivial, Iff.rfl⟩


-- @@ L176-178 verbatim
theorem selEqSat_mem_CeqP : SelEqSAT ∈ CeqP :=
  mem_countClass_of_sharpP (sharpSelSat_mem_sharpP true) (sharpSelSat_mem_sharpP false)
    fun _ _ _ _ => ⟨trivial, Iff.rfl⟩


-- @@ L180-181 verbatim
/-! ### Hardness: the Tseitin formula of a pair kernel, with the selector
selected -/


-- @@ L183-183 verbatim
namespace PairSel


-- @@ L185-185 verbatim
open Tseitin


-- @@ L187-188 verbatim
variable {L : Language.{0, 0}} (B B' : SOBlock) (φ : (L.sum B.lang).Sentence)
  (φ' : (L.sum B'.lang).Sentence)


-- @@ L190-191 verbatim
/-- The selector of the pair block. -/
abbrev pairZ : (pairBlock B B').ι := Sum.inr (Sum.inr ())


-- @@ L193-194 verbatim
/-- The block and the kernel of the pair, abbreviated. -/
abbrev PB : SOBlock := pairBlock B B'


-- @@ L196-197 verbatim
/-- The pair kernel, abbreviated. -/
noncomputable abbrev PK : (L.sum (PB B B').lang).Sentence := pairKernel B B' φ φ'


-- @@ L199-214 verbatim
open Classical in
/-- **The Tseitin formula of the pair kernel, with the selector's variable
selected.** -/
noncomputable def pairTseitinInterp :
    FOInterpretation (L.sum Language.order) Language.satSel
      (SharpTseitinTag (PB B B') (PK B B' φ φ')) (tseitinDim (PB B B') (PK B B' φ φ')) where
  relFormula {n} R :=
    match R with
    | Sum.inl r => (sharpTseitinInterp (PB B B') (PK B B' φ φ')).relFormula r
    | Sum.inr s =>
      match n, s with
      | _, .sel => fun t =>
          match t 0 with
          | Sum.inl (Sum.inr (Sum.inl i)) =>
              if i = pairZ B B' then canonF ((PB B B').arity i) fun j => ((0 : Fin 1), j) else ⊥
          | _ => ⊥


-- @@ L216-216 verbatim
section Correct


-- @@ L218-218 verbatim
variable {B B' φ φ'} {A : Type} [L.Structure A] [LinearOrder A]


-- @@ L220-224 verbatim
/-- The underlying CNF formula is the parsimonious Tseitin formula. -/
def satEquiv :
    (pairTseitinInterp B B' φ φ').Map A ≃[Language.sat]
      (sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A :=
  ⟨Equiv.refl _, fun {_} f _ => isEmptyElim f, fun {_} _ _ => Iff.rfl⟩


-- @@ L226-231 verbatim
variable (B B' φ φ') in
/-- The variable point of the selector, at a tuple. (The kernels are explicit:
left to unification, they would make it unfold the pair kernel.) -/
def selPt (x : Fin (tseitinDim (PB B B') (PK B B' φ φ')) → A) :
    (pairTseitinInterp B B' φ φ').Map A :=
  (Sum.inl (Sum.inr (Sum.inl (pairZ B B'))), x)


-- @@ L233-264 verbatim
/-- The selected points are the canonical variable points of the selector. -/
theorem sel_iff (p : (pairTseitinInterp B B' φ φ').Map A) :
    RelMap (M := (pairTseitinInterp B B' φ φ').Map A) ssSel ![p] ↔
      ∃ x, p = selPt B B' φ φ' x ∧ Canon 0 x := by
  classical
  obtain ⟨t, w⟩ := p
  rw [FOInterpretation.relMap_map]
  rcases t with (tc | vt) | i
  · refine iff_of_false id fun ⟨x, hx, _⟩ => ?_
    have h : Sum.inl (Sum.inl tc) = Sum.inl (Sum.inr (Sum.inl (pairZ B B'))) := (Prod.mk.inj hx).1
    exact Sum.inl_ne_inr (Sum.inl.inj h)
  · rcases vt with i | σ
    · change (if i = pairZ B B' then canonF ((PB B B').arity i) fun j => ((0 : Fin 1), j)
        else ⊥ : (L.sum Language.order).Formula (Fin 1 × Fin _)).Realize _ ↔ _
      by_cases hi : i = pairZ B B'
      · subst hi
        rw [ite_eq_left rfl, realize_canonF]
        exact ⟨fun h => ⟨w, rfl, h⟩, fun ⟨x, hx, hc⟩ => by
          obtain rfl : w = x := (Prod.mk.inj hx).2
          exact hc⟩
      · rw [ite_eq_right hi]
        refine iff_of_false id fun ⟨x, hx, _⟩ => hi ?_
        have h : Sum.inl (Sum.inr (Sum.inl i)) = Sum.inl (Sum.inr (Sum.inl (pairZ B B'))) :=
          (Prod.mk.inj hx).1
        exact Sum.inl.inj (Sum.inr.inj (Sum.inl.inj h))
    · refine iff_of_false id fun ⟨x, hx, _⟩ => ?_
      have h : Sum.inl (Sum.inr (Sum.inr σ)) = Sum.inl (Sum.inr (Sum.inl (pairZ B B'))) :=
        (Prod.mk.inj hx).1
      exact Sum.inr_ne_inl (Sum.inr.inj (Sum.inl.inj h))
  · refine iff_of_false id fun ⟨x, hx, _⟩ => ?_
    have h : Sum.inr i = Sum.inl (Sum.inr (Sum.inl (pairZ B B'))) := (Prod.mk.inj hx).1
    exact Sum.inr_ne_inl h


-- @@ L266-278 verbatim
/-- The models of the marked formula are the models of the plain Tseitin
formula: the two universes meet only through this map. -/
def modelsEquiv :
    {ν : (pairTseitinInterp B B' φ φ').Map A → Prop //
        SatModel ((pairTseitinInterp B B' φ φ').Map A) ν} ≃
      {ν : (sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A → Prop //
        SatModel ((sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A) ν} where
  toFun ν := ⟨fun y => ν.1 (satEquiv.symm y), by
    have h := (satModel_equiv satEquiv.symm ν.1).mpr ν.2
    exact h⟩
  invFun ν := ⟨fun x => ν.1 (satEquiv x), (satModel_equiv satEquiv ν.1).mpr ν.2⟩
  left_inv ν := rfl
  right_inv ν := rfl


-- @@ L280-280 verbatim
variable [Finite A] [Nonempty A]


-- @@ L282-332 verbatim
/-- **The models with the selected variable at `b` are the witnesses of the
pair kernel whose selector is `b`.** -/
theorem sharpSelSat_eq (b : Bool) :
    SharpSelSAT b ((pairTseitinInterp B B' φ φ').Map A) =
      Nat.card {w : Witness (PB B B') (PK B B' φ φ') A // pairSel w.1 ↔ b = true} := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rw [sharpSelSat_apply]
  -- the selected point, kept opaque: unfolding it makes the elaborator evaluate the dimension
  obtain ⟨pt, hpt⟩ : ∃ pt : (pairTseitinInterp B B' φ φ').Map A,
      pt = selPt B B' φ φ' (pad a₀ finZeroElim) := ⟨_, rfl⟩
  have hsel : RelMap (M := (pairTseitinInterp B B' φ φ').Map A) ssSel ![pt] :=
    (sel_iff (B := B) (B' := B') (φ := φ) (φ' := φ') pt).mpr
      ⟨pad a₀ finZeroElim, hpt, canon_pad ha₀ 0 finZeroElim⟩
  have hpt' : ∀ p : (pairTseitinInterp B B' φ φ').Map A,
      RelMap (M := (pairTseitinInterp B B' φ φ').Map A) ssSel ![p] → p = pt := by
    intro p hp
    obtain ⟨x, rfl, hx⟩ := (sel_iff (B := B) (B' := B') (φ := φ) (φ' := φ') p).mp hp
    rw [hpt, ← pad_pref_of_canon ha₀ (Nat.zero_le _) hx]
    exact congrArg (fun w => selPt B B' φ φ' (pad a₀ w)) (Subsingleton.elim _ _)
  have e1 : {ν : (pairTseitinInterp B B' φ φ').Map A → Prop //
        SelModel ((pairTseitinInterp B B' φ φ').Map A) b ν} ≃
      {ν : (pairTseitinInterp B B' φ φ').Map A → Prop //
        SatModel ((pairTseitinInterp B B' φ φ').Map A) ν ∧ (ν pt ↔ b = true)} := by
    refine Equiv.subtypeEquivRight fun ν => ?_
    refine and_congr Iff.rfl ⟨fun h => h _ hsel, fun h p hp => ?_⟩
    rw [hpt' p hp]
    exact h
  have e2 := (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun ν : (pairTseitinInterp B B' φ φ').Map A → Prop =>
      SatModel ((pairTseitinInterp B B' φ φ').Map A) ν)
    fun ν => ν pt ↔ b = true).symm
  have e3 : {ν : {ν : (pairTseitinInterp B B' φ φ').Map A → Prop //
        SatModel ((pairTseitinInterp B B' φ φ').Map A) ν} // ν.1 pt ↔ b = true} ≃
      {ν : {ν : (sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A → Prop //
        SatModel ((sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A) ν} //
          ν.1 (satEquiv.symm.symm pt) ↔ b = true} :=
    Equiv.subtypeEquiv modelsEquiv fun ν => Iff.rfl
  have e4 : {ν : {ν : (sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A → Prop //
        SatModel ((sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A) ν} //
          ν.1 (satEquiv.symm.symm pt) ↔ b = true} ≃
      {μ : {μ : (PB B B').Assignment A // RealizeWith μ (PK B B' φ φ') finZeroElim} //
        μ.1 (pairZ B B') finZeroElim ↔ b = true} := by
    refine Equiv.subtypeEquiv (sharpModelEquiv (PB B B') (PK B B' φ φ') A ha₀) fun ν => ?_
    subst hpt
    exact Iff.rfl
  have e5 : {μ : {μ : (PB B B').Assignment A // RealizeWith μ (PK B B' φ φ') finZeroElim} //
        μ.1 (pairZ B B') finZeroElim ↔ b = true} ≃
      {w : Witness (PB B B') (PK B B' φ φ') A // pairSel w.1 ↔ b = true} :=
    Equiv.subtypeEquiv (Equiv.subtypeEquivRight fun μ =>
      (realize_iff_realizeWith (PB B B') (PK B B' φ φ') μ).symm) fun μ => Iff.rfl
  exact Nat.card_congr (e1.trans (e2.trans (e3.trans (e4.trans e5))))


-- @@ L334-337 verbatim
theorem sharpSelSat_true :
    SharpSelSAT true ((pairTseitinInterp B B' φ φ').Map A) = witnessCount B φ A := by
  rw [sharpSelSat_eq, ← card_pairWitness_sel (φ := φ) (φ' := φ')]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun w => by simp)


-- @@ L339-342 verbatim
theorem sharpSelSat_false :
    SharpSelSAT false ((pairTseitinInterp B B' φ φ').Map A) = witnessCount B' φ' A := by
  rw [sharpSelSat_eq, ← card_pairWitness_not_sel (φ := φ) (φ' := φ')]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun w => by simp)


-- @@ L344-344 verbatim
end Correct


-- @@ L346-346 verbatim
end PairSel


-- @@ L348-348 verbatim
section Hardness


-- @@ L350-350 verbatim
variable {L : Language.{0, 0}} [L.IsRelational]


-- @@ L352-373 verbatim
/-- **Every problem defined by a relation between two witness counts reduces
to the comparison of the two counts of a CNF formula by its selected
variable.** -/
noncomputable def CountDefinable.orderedReduction_sel (R : ℕ → ℕ → Prop)
    {P : DecisionProblem L} (B : SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence)
    (B' : SOBlock) (φ' : ((L.sum Language.order).sum B'.lang).Sentence)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ R (witnessCount B φ A) (witnessCount B' φ' A)) :
    P ≤ᶠᵒ[≤] ⟨fun A inst => R (@SharpSelSAT true A inst) (@SharpSelSAT false A inst),
      fun e => by
        rw [(SharpSelSAT false).iso_invariant e, (SharpSelSAT true).iso_invariant e]⟩ where
  Tag := SharpTseitinTag (PairSel.PB B B') (PairSel.PK B B' φ φ')
  dim := tseitinDim (PairSel.PB B B') (PairSel.PK B B' φ φ')
  toInterpretation := (PairSel.pairTseitinInterp B B' φ φ').liftSource (orderCollapse L)
  correct A _ _ _ _ := by
    rw [h A]
    change _ ↔ R (SharpSelSAT true _) (SharpSelSAT false _)
    rw [(SharpSelSAT true).iso_invariant
        ((PairSel.pairTseitinInterp B B' φ φ').liftSourceLEquiv (orderCollapse L) A),
      (SharpSelSAT false).iso_invariant
        ((PairSel.pairTseitinInterp B B' φ φ').liftSourceLEquiv (orderCollapse L) A),
      PairSel.sharpSelSat_true, PairSel.sharpSelSat_false]


-- @@ L375-379 verbatim
theorem selMajSat_PP_hard : PP.Hard SelMajSAT := by
  refine (hard_countClass_iff SelMajSAT).mpr ?_
  rintro L'' _ Q ⟨B, φ, B', φ', hφ⟩
  exact ⟨(CountDefinable.orderedReduction_sel (fun c d => d < c) B φ B' φ'
    fun A _ _ _ _ => (hφ A).2).toRel⟩


-- @@ L381-385 verbatim
theorem selEqSat_CeqP_hard : CeqP.Hard SelEqSAT := by
  refine (hard_countClass_iff SelEqSAT).mpr ?_
  rintro L'' _ Q ⟨B, φ, B', φ', hφ⟩
  exact ⟨(CountDefinable.orderedReduction_sel (fun c d => c = d) B φ B' φ'
    fun A _ _ _ _ => (hφ A).2).toRel⟩


-- @@ L387-389 verbatim
/-- **SelMajSAT is `PP`-complete.** -/
theorem selMajSat_PP_complete : PP.Complete SelMajSAT :=
  ⟨selMajSat_mem_PP, selMajSat_PP_hard⟩


-- @@ L391-393 verbatim
/-- **SelEqSAT is `C₌P`-complete.** -/
theorem selEqSat_CeqP_complete : CeqP.Complete SelEqSAT :=
  ⟨selEqSat_mem_CeqP, selEqSat_CeqP_hard⟩


-- @@ L395-395 verbatim
end Hardness


-- @@ L397-397 verbatim
end DescriptiveComplexity
