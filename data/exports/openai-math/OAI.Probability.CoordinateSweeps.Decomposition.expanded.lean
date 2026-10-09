import Mathlib
import OAI.Probability.CoordinateSweeps.Conditioning
import OAI.RepresentationTheory.SignedTensor.Blocks


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

-- @@ L9-9 verbatim
attribute [local instance] Classical.propDecidable

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator

-- @@ L12-12 verbatim
attribute [local instance] Classical.propDecidable

-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
open scoped BigOperators ComplexOrder MatrixOrder

-- @@ L15-15 verbatim
attribute [local instance] Classical.propDecidable

-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
open scoped BigOperators ENNReal

-- @@ L18-18 verbatim
open MeasureTheory

-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

-- @@ L21-21 verbatim
noncomputable section

-- @@ L22-22 verbatim
open scoped BigOperators

-- @@ L23-23 verbatim
attribute [local instance] Classical.propDecidable

-- @@ L24-24 verbatim
noncomputable section

-- @@ L25-25 verbatim
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

-- @@ L26-26 verbatim
attribute [local instance] Classical.propDecidable

-- @@ L27-27 verbatim
noncomputable section

-- @@ L28-28 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L30-30 verbatim
namespace CoordinateSweeps

-- @@ L31-39 verbatim
lemma schattenMoment_unitary_left {d : ℕ} (q : ℕ) (A U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U.conjTranspose*U=1) : schattenMoment q (U*A)=schattenMoment q A := by
  unfold schattenMoment
  rw [Matrix.conjTranspose_mul]
  have hh : A.conjTranspose*U.conjTranspose*(U*A)=A.conjTranspose*A := by
    calc
      _ = A.conjTranspose*(U.conjTranspose*U)*A := by noncomm_ring
      _ = _ := by rw [hU,mul_one]
  rw [hh]


-- @@ L41-41 verbatim
namespace Grid.Holes

-- @@ L42-42 verbatim
variable {G : Grid} {h : ℕ} (H : G.Holes h)


-- @@ L44-50 verbatim
def residualWithReference (ω0 : {ω : G.Choices // H.Compatible ω})
    (ω : {ω : G.Choices // H.Compatible ω}) : H.stabilizer :=
  ⟨(G.sweep ω0.val)⁻¹*G.sweep ω.val,by
    intro i
    change (G.sweep ω0.val).symm (G.sweep ω.val (H.path i 0))=_
    apply (Equiv.symm_apply_eq _).mpr
    exact (ω.property i (Fin.last _)).trans (ω0.property i (Fin.last _)).symm⟩


-- @@ L52-60 verbatim
lemma residualWithReference_eq (hf : H.Feasible)
    (ω0 ω : {ω : G.Choices // H.Compatible ω}) :
    H.residualWithReference ω0 ω=H.residualWithReference ω0 ⟨H.reference hf,H.reference_compatible hf⟩*
      H.residual hf ω := by
  apply Subtype.ext
  change (G.sweep ω0.val)⁻¹*G.sweep ω.val=
    ((G.sweep ω0.val)⁻¹*G.sweep (H.reference hf))*
      ((G.sweep (H.reference hf))⁻¹*G.sweep ω.val)
  group


-- @@ L62-67 verbatim
def averageWithReference (ω0 : {ω : G.Choices // H.Compatible ω}) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ :=
  ∑ ω : {ω : G.Choices // H.Compatible ω}, ((G.choiceWeight z ω.val/H.probability z : ℝ) : ℂ) •
    ρ.matrix (H.residualWithReference ω0 ω)

/- Arbitrary feasible reference choices preserve the literal, unnormalized moment. -/

-- @@ L68-81 verbatim
theorem averageWithReference_moment (hf : H.Feasible)
    (ω0 : {ω : G.Choices // H.Compatible ω}) (z : ℝ) (ρ : UnitaryIrrep H.stabilizer) (q : ℕ) :
    schattenMoment q (H.averageWithReference ω0 z ρ)=schattenMoment q (H.conditionalAverage hf z ρ) := by
  have he : H.averageWithReference ω0 z ρ=
      ρ.matrix (H.residualWithReference ω0 ⟨H.reference hf,H.reference_compatible hf⟩)*
        H.conditionalAverage hf z ρ := by
    rw [H.conditionalAverage_eq_sum]
    unfold averageWithReference
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    rw [H.residualWithReference_eq hf ω0 ω,map_mul,Matrix.mul_smul]
  rw [he]
  exact schattenMoment_unitary_left q _ _ (ρ.unitary _)


-- @@ L83-83 verbatim
end Grid.Holes


-- @@ L85-85 verbatim
namespace Grid.Holes

-- @@ L86-86 verbatim
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)


-- @@ L88-91 verbatim
def junctionIrrep (hf : H.Feasible) (ρ : UnitaryIrrep H.stabilizer) : UnitaryIrrep H.JunctionFix :=
  ρ.pullback (H.junctionEquiv hf).symm

/- Attachment of the checked law-level factorization to the exact main target. -/

-- @@ L92-104 verbatim
theorem conditionalAverage_eq_junction (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) :
    H.conditionalAverage hf z ρ=H.columnAverage hf z (H.junctionIrrep hf ρ).matrix*
      H.rowAverage hf z (H.junctionIrrep hf ρ).matrix := by
  rw [H.conditionalAverage_eq_sum]
  have hh := H.junction_average_split hf z (H.junctionIrrep hf ρ).matrix
  refine Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  change ρ.matrix (H.residual hf ω)=ρ.matrix ((H.junctionEquiv hf).symm
    (H.junctionEquiv hf (H.residual hf ω)))
  rw [MulEquiv.symm_apply_apply]


-- @@ L106-106 verbatim
end Grid.Holes

-- @@ L107-107 verbatim
end CoordinateSweeps


-- @@ L109-109 verbatim
namespace CoordinateSweeps.Grid.Holes

-- @@ L110-110 verbatim
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

-- @@ L111-111 verbatim
abbrev JunctionFree := H.FreeAt (suffixTime A B 0)

-- @@ L112-112 verbatim
def rowLabel (x : H.JunctionFree) : B.Slot := (splitSlots A B x.val).2

-- @@ L113-113 verbatim
def columnLabel (x : H.JunctionFree) : A.Slot := (splitSlots A B x.val).1


-- @@ L115-117 verbatim
lemma junctionTime : prefixTime A B (Fin.last A.b)=suffixTime A B 0 := by apply Fin.ext; simp [prefixTime,suffixTime]

/- The actual free row at the split layer is the child's terminal free set. -/

-- @@ L118-148 verbatim
def freeRow (y : B.Slot) : {x : H.JunctionFree // H.rowLabel x=y} ≃
    (H.rowHoles y).FreeAt (Fin.last A.b) where
  toFun x := ⟨(splitSlots A B x.val.val).1,by
    intro i hi
    apply x.val.property (H.rowCards y i).val
    apply (splitSlots A B).injective
    apply Prod.ext
    · simpa only [rowHoles,junctionTime] using hi
    · change H.rowLabel x.val=_
      rw [x.property]
      exact ((H.rowCards y i).property).symm.trans (H.row_constant _ (Fin.last A.b)).symm⟩
  invFun x := ⟨⟨(splitSlots A B).symm (x.val,y),by
    intro i hi
    have hh := congrArg (splitSlots A B) hi
    simp only [Equiv.apply_symm_apply] at hh
    have hy : H.rowOf i=y := (H.row_constant i (Fin.last A.b)).symm.trans (congrArg Prod.snd hh).symm
    let j := (H.rowCards y).symm ⟨i,hy⟩
    have hj : (H.rowCards y j).val=i := congrArg Subtype.val ((H.rowCards y).apply_symm_apply ⟨i,hy⟩)
    apply x.property j
    change x.val=(splitSlots A B (H.path (H.rowCards y j).val (prefixTime A B (Fin.last A.b)))).1
    rw [hj,junctionTime]
    exact congrArg Prod.fst hh⟩,by simp [rowLabel]⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply (splitSlots A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext rfl x.property.symm
  right_inv x := by apply Subtype.ext; simp

/- The actual free column at the split layer is the child's initial free set. -/

-- @@ L149-176 verbatim
def freeColumn (x : A.Slot) : {y : H.JunctionFree // H.columnLabel y=x} ≃
    (H.columnHoles x).FreeAt 0 where
  toFun y := ⟨(splitSlots A B y.val.val).2,by
    intro i hi
    apply y.val.property (H.columnCards x i).val
    apply (splitSlots A B).injective
    apply Prod.ext
    · change H.columnLabel y.val=_
      exact y.property.trans (H.columnCards x i).property.symm
    · exact hi⟩
  invFun y := ⟨⟨(splitSlots A B).symm (x,y.val),by
    intro i hi
    have hh := congrArg (splitSlots A B) hi
    simp only [Equiv.apply_symm_apply] at hh
    have hx : H.columnOf i=x := (congrArg Prod.fst hh).symm
    let j := (H.columnCards x).symm ⟨i,hx⟩
    have hj : (H.columnCards x j).val=i := congrArg Subtype.val ((H.columnCards x).apply_symm_apply ⟨i,hx⟩)
    apply y.property j
    change y.val=(splitSlots A B (H.path (H.columnCards x j).val (suffixTime A B 0))).2
    rw [hj]
    exact congrArg Prod.snd hh⟩,by simp [columnLabel]⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    apply (splitSlots A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext y.property.symm rfl
  right_inv y := by apply Subtype.ext; simp


-- @@ L178-180 verbatim
lemma card_freeRow (y : B.Slot) :
    Fintype.card {x : H.JunctionFree // H.rowLabel x=y}=A.size-H.rowCount y :=
  (Fintype.card_congr (H.freeRow y)).trans ((H.rowHoles y).card_freeAt _)

-- @@ L181-183 verbatim
lemma card_freeColumn (x : A.Slot) :
    Fintype.card {y : H.JunctionFree // H.columnLabel y=x}=B.size-H.columnCount x :=
  (Fintype.card_congr (H.freeColumn x)).trans ((H.columnHoles x).card_freeAt _)


-- @@ L185-185 verbatim
end CoordinateSweeps.Grid.Holes


-- @@ L187-187 verbatim
namespace CoordinateSweeps.Grid

-- @@ L188-194 verbatim
lemma rowSweep_inv_apply (A B : Grid) (ω : B.Slot → A.Choices) (x : (concat A B).Slot) :
    splitSlots A B ((rowSweep A B ω)⁻¹ x)=
      ((A.sweep (ω (splitSlots A B x).2))⁻¹ (splitSlots A B x).1,(splitSlots A B x).2) := by
  change splitSlots A B ((splitSlots A B).symm
    ((A.sweep (ω (splitSlots A B x).2)).symm (splitSlots A B x).1,(splitSlots A B x).2))=_
  rw [Equiv.apply_symm_apply]
  rfl

-- @@ L195-201 verbatim
lemma columnSweep_inv_apply (A B : Grid) (ω : A.Slot → B.Choices) (x : (concat A B).Slot) :
    splitSlots A B ((columnSweep A B ω)⁻¹ x)=
      ((splitSlots A B x).1,(B.sweep (ω (splitSlots A B x).1))⁻¹ (splitSlots A B x).2) := by
  change splitSlots A B ((splitSlots A B).symm
    ((splitSlots A B x).1,(B.sweep (ω (splitSlots A B x).1)).symm (splitSlots A B x).2))=_
  rw [Equiv.apply_symm_apply]
  rfl

-- @@ L202-202 verbatim
end CoordinateSweeps.Grid


-- @@ L204-204 verbatim
namespace CoordinateSweeps.Grid.Holes

-- @@ L205-205 verbatim
variable {G : Grid} {h : ℕ} (J : G.Holes h)


-- @@ L207-209 verbatim
def outputStabilizerEquiv (ω₀ : {ω : G.Choices // J.Compatible ω}) :
    J.stabilizer ≃* Equiv.Perm (J.FreeAt (Fin.last G.b)) :=
  J.stabilizerFreeEquiv.trans (J.freeBoundary ω₀ (Fin.last _)).permCongrHom


-- @@ L211-216 verbatim
lemma outputStabilizer_residual (ω₀ ω : {ω : G.Choices // J.Compatible ω})
    (x : J.FreeAt (Fin.last G.b)) :
    (J.outputStabilizerEquiv ω₀ (J.residualWithReference ω₀ ω) x).val=
      G.sweep ω.val ((G.sweep ω₀.val)⁻¹ x.val) := by
  change G.sweep ω₀.val (((G.sweep ω₀.val)⁻¹*G.sweep ω.val) ((G.sweep ω₀.val)⁻¹ x.val))=_
  simp only [Equiv.Perm.mul_apply,Equiv.Perm.coe_inv,Equiv.apply_symm_apply]


-- @@ L218-218 verbatim
variable {A B : Grid} (H : (concat A B).Holes h)


-- @@ L220-221 verbatim
def junctionFreeEquiv : H.JunctionFix ≃* Equiv.Perm H.JunctionFree :=
  Marked.freePermEquiv (fun i => H.path i (suffixTime A B 0))


-- @@ L223-230 verbatim
lemma rowResidual_split (hf : H.Feasible) (ω : H.RowChoices) (x : (concat A B).Slot) :
    splitSlots A B ((H.rowResidual hf ω).val x)=
      (A.sweep (ω (splitSlots A B x).2).val
        ((A.sweep ((H.refPair hf).1 (splitSlots A B x).2).val)⁻¹ (splitSlots A B x).1),
       (splitSlots A B x).2) := by
  change splitSlots A B (H.rowAction ω ((H.rowAction (H.refPair hf).1)⁻¹ x))=_
  rw [rowAction,rowSweep_apply]
  rw [rowAction,rowSweep_inv_apply]


-- @@ L232-237 verbatim
lemma columnResidual_split (hf : H.Feasible) (ω : H.ColumnChoices) (x : (concat A B).Slot) :
    splitSlots A B ((H.columnResidual hf ω).val x)=
      ((splitSlots A B x).1,(B.sweep ((H.refPair hf).2 (splitSlots A B x).1).val)⁻¹
        (B.sweep (ω (splitSlots A B x).1).val (splitSlots A B x).2)) := by
  change splitSlots A B ((H.columnAction (H.refPair hf).2)⁻¹ (H.columnAction ω x))=_
  rw [columnAction,columnSweep_inv_apply,columnAction,columnSweep_apply]


-- @@ L239-242 verbatim
lemma rowResidual_label (hf : H.Feasible) (ω : H.RowChoices) (x : H.JunctionFree) :
    H.rowLabel (H.junctionFreeEquiv (H.rowResidual hf ω) x)=H.rowLabel x := by
  have hh := congrArg Prod.snd (H.rowResidual_split hf ω x.val)
  exact hh

-- @@ L243-249 verbatim
lemma columnResidual_label (hf : H.Feasible) (ω : H.ColumnChoices) (x : H.JunctionFree) :
    H.columnLabel (H.junctionFreeEquiv (H.columnResidual hf ω) x)=H.columnLabel x := by
  have hh := congrArg Prod.fst (H.columnResidual_split hf ω x.val)
  exact hh

/- Literal row-fiber permutation and the child's compatible residual agree in
its output frame. -/

-- @@ L250-266 verbatim
theorem rowResidual_fiber (hf : H.Feasible) (ω : H.RowChoices) (y : B.Slot)
    (x : {x : H.JunctionFree // H.rowLabel x=y}) :
    H.freeRow y ⟨H.junctionFreeEquiv (H.rowResidual hf ω) x.val,
      (H.rowResidual_label hf ω x.val).trans x.property⟩=
    (H.rowHoles y).outputStabilizerEquiv ((H.refPair hf).1 y)
      ((H.rowHoles y).residualWithReference ((H.refPair hf).1 y) (ω y)) (H.freeRow y x) := by
  apply Subtype.ext
  rw [outputStabilizer_residual]
  change (splitSlots A B ((H.rowResidual hf ω).val x.val.val)).1=_
  rw [H.rowResidual_split]
  change A.sweep (ω (H.rowLabel x.val)).val
    ((A.sweep ((H.refPair hf).1 (H.rowLabel x.val)).val)⁻¹ (splitSlots A B x.val.val).1)=_
  rw [x.property]
  rfl

/- Literal column-fiber permutation and the child's residual agree in its
input frame; this is where the row/column orientations differ. -/

-- @@ L267-279 verbatim
theorem columnResidual_fiber (hf : H.Feasible) (ω : H.ColumnChoices) (y : A.Slot)
    (x : {x : H.JunctionFree // H.columnLabel x=y}) :
    H.freeColumn y ⟨H.junctionFreeEquiv (H.columnResidual hf ω) x.val,
      (H.columnResidual_label hf ω x.val).trans x.property⟩=
    (H.columnHoles y).stabilizerFreeEquiv
      ((H.columnHoles y).residualWithReference ((H.refPair hf).2 y) (ω y)) (H.freeColumn y x) := by
  apply Subtype.ext
  change (splitSlots A B ((H.columnResidual hf ω).val x.val.val)).2=_
  rw [H.columnResidual_split]
  change (B.sweep ((H.refPair hf).2 (H.columnLabel x.val)).val)⁻¹
    (B.sweep (ω (H.columnLabel x.val)).val (splitSlots A B x.val.val).2)=_
  rw [x.property]
  rfl

-- @@ L280-280 verbatim
end CoordinateSweeps.Grid.Holes


-- @@ L282-282 verbatim
namespace CoordinateSweeps.Grid.Holes

-- @@ L283-283 verbatim
open FiberBlocks

-- @@ L284-284 verbatim
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

-- @@ L285-285 verbatim
def rowIndex (x : H.JunctionFree) : Fin (Fintype.card B.Slot) := Fintype.equivFin B.Slot (H.rowLabel x)

-- @@ L286-286 verbatim
def columnIndex (x : H.JunctionFree) : Fin (Fintype.card A.Slot) := Fintype.equivFin A.Slot (H.columnLabel x)

-- @@ L287-287 verbatim
def rowSite (_ : (concat A B).Holes h) (i : Fin (Fintype.card B.Slot)) : B.Slot := (Fintype.equivFin B.Slot).symm i

-- @@ L288-288 verbatim
def columnSite (_ : (concat A B).Holes h) (i : Fin (Fintype.card A.Slot)) : A.Slot := (Fintype.equivFin A.Slot).symm i


-- @@ L290-293 verbatim
def rowLocalChart (i : Fin (Fintype.card B.Slot)) : Fin (FiberBlocks.size H.rowIndex i) ≃
    (H.rowHoles (H.rowSite i)).FreeAt (Fin.last A.b) :=
  (cards H.rowIndex i).trans ((Equiv.subtypeEquivRight (fun x => by
    exact (Fintype.equivFin B.Slot).eq_symm_apply.symm)).trans (H.freeRow (H.rowSite i)))

-- @@ L294-297 verbatim
def columnLocalChart (i : Fin (Fintype.card A.Slot)) : Fin (FiberBlocks.size H.columnIndex i) ≃
    (H.columnHoles (H.columnSite i)).FreeAt 0 :=
  (cards H.columnIndex i).trans ((Equiv.subtypeEquivRight (fun x => by
    exact (Fintype.equivFin A.Slot).eq_symm_apply.symm)).trans (H.freeColumn (H.columnSite i)))


-- @@ L299-302 verbatim
def rowChildEquiv (hf : H.Feasible) (i : Fin (Fintype.card B.Slot)) :
    (H.rowHoles (H.rowSite i)).stabilizer ≃* Equiv.Perm (Fin (FiberBlocks.size H.rowIndex i)) :=
  ((H.rowHoles (H.rowSite i)).outputStabilizerEquiv ((H.refPair hf).1 (H.rowSite i))).trans
    (H.rowLocalChart i).symm.permCongrHom


-- @@ L304-306 verbatim
def columnChildEquiv (i : Fin (Fintype.card A.Slot)) :
    (H.columnHoles (H.columnSite i)).stabilizer ≃* Equiv.Perm (Fin (FiberBlocks.size H.columnIndex i)) :=
  (H.columnHoles (H.columnSite i)).stabilizerFreeEquiv.trans (H.columnLocalChart i).symm.permCongrHom


-- @@ L308-310 verbatim
lemma rowResidual_index (hf : H.Feasible) (ω : H.RowChoices) (x : H.JunctionFree) :
    H.rowIndex (H.junctionFreeEquiv (H.rowResidual hf ω) x)=H.rowIndex x :=
  congrArg (Fintype.equivFin B.Slot) (H.rowResidual_label hf ω x)

-- @@ L311-313 verbatim
lemma columnResidual_index (hf : H.Feasible) (ω : H.ColumnChoices) (x : H.JunctionFree) :
    H.columnIndex (H.junctionFreeEquiv (H.columnResidual hf ω) x)=H.columnIndex x :=
  congrArg (Fintype.equivFin A.Slot) (H.columnResidual_label hf ω x)


-- @@ L315-334 verbatim
theorem row_restrict_eq (hf : H.Feasible) (ω : H.RowChoices) (i : Fin (Fintype.card B.Slot)) :
    restrict H.rowIndex (H.junctionFreeEquiv (H.rowResidual hf ω)) (H.rowResidual_index hf ω) i=
      H.rowChildEquiv hf i ((H.rowHoles (H.rowSite i)).residualWithReference
        ((H.refPair hf).1 (H.rowSite i)) (ω (H.rowSite i))) := by
  apply Equiv.ext
  intro j
  apply (H.rowLocalChart i).injective
  have hh := H.rowResidual_fiber hf ω (H.rowSite i)
    ⟨(cards H.rowIndex i j).val,(Fintype.equivFin B.Slot).eq_symm_apply.mpr (cards H.rowIndex i j).property⟩
  change H.rowLocalChart i (restrict H.rowIndex _ _ i j)=
    H.rowLocalChart i ((H.rowLocalChart i).symm
      ((H.rowHoles (H.rowSite i)).outputStabilizerEquiv ((H.refPair hf).1 (H.rowSite i))
        ((H.rowHoles (H.rowSite i)).residualWithReference ((H.refPair hf).1 (H.rowSite i)) (ω (H.rowSite i)))
        (H.rowLocalChart i j)))
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  have he := congrArg Subtype.val hh
  change (splitSlots A B (cards H.rowIndex i (restrict H.rowIndex _ _ i j)).val.val).1=_
  rw [restrict_apply]
  exact he


-- @@ L336-355 verbatim
theorem column_restrict_eq (hf : H.Feasible) (ω : H.ColumnChoices) (i : Fin (Fintype.card A.Slot)) :
    restrict H.columnIndex (H.junctionFreeEquiv (H.columnResidual hf ω)) (H.columnResidual_index hf ω) i=
      H.columnChildEquiv i ((H.columnHoles (H.columnSite i)).residualWithReference
        ((H.refPair hf).2 (H.columnSite i)) (ω (H.columnSite i))) := by
  apply Equiv.ext
  intro j
  apply (H.columnLocalChart i).injective
  have hh := H.columnResidual_fiber hf ω (H.columnSite i)
    ⟨(cards H.columnIndex i j).val,(Fintype.equivFin A.Slot).eq_symm_apply.mpr (cards H.columnIndex i j).property⟩
  change H.columnLocalChart i (restrict H.columnIndex _ _ i j)=
    H.columnLocalChart i ((H.columnLocalChart i).symm
      ((H.columnHoles (H.columnSite i)).stabilizerFreeEquiv
        ((H.columnHoles (H.columnSite i)).residualWithReference ((H.refPair hf).2 (H.columnSite i)) (ω (H.columnSite i)))
        (H.columnLocalChart i j)))
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  have he := congrArg Subtype.val hh
  change (splitSlots A B (cards H.columnIndex i (restrict H.columnIndex _ _ i j)).val.val).2=_
  rw [restrict_apply]
  exact he


-- @@ L357-364 verbatim
lemma rowResidual_as_fibers (hf : H.Feasible) (ω : H.RowChoices) :
    H.junctionFreeEquiv (H.rowResidual hf ω)=action H.rowIndex (fun i =>
      H.rowChildEquiv hf i ((H.rowHoles (H.rowSite i)).residualWithReference
        ((H.refPair hf).1 (H.rowSite i)) (ω (H.rowSite i)))) := by
  rw [← action_restrict H.rowIndex _ (H.rowResidual_index hf ω)]
  congr 1
  funext i
  exact H.row_restrict_eq hf ω i

-- @@ L365-372 verbatim
lemma columnResidual_as_fibers (hf : H.Feasible) (ω : H.ColumnChoices) :
    H.junctionFreeEquiv (H.columnResidual hf ω)=action H.columnIndex (fun i =>
      H.columnChildEquiv i ((H.columnHoles (H.columnSite i)).residualWithReference
        ((H.refPair hf).2 (H.columnSite i)) (ω (H.columnSite i)))) := by
  rw [← action_restrict H.columnIndex _ (H.columnResidual_index hf ω)]
  congr 1
  funext i
  exact H.column_restrict_eq hf ω i

-- @@ L373-373 verbatim
end CoordinateSweeps.Grid.Holes


-- @@ L375-375 verbatim
namespace CoordinateSweeps.Grid.Holes

-- @@ L376-376 verbatim
open FiberBlocks SignedTensor UnitaryIrrep

-- @@ L377-377 verbatim
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)


-- @@ L379-380 verbatim
abbrev RowLocalChoices (i : Fin (Fintype.card B.Slot)) :=
  {ω : A.Choices // (H.rowHoles (H.rowSite i)).Compatible ω}

-- @@ L381-382 verbatim
abbrev ColumnLocalChoices (i : Fin (Fintype.card A.Slot)) :=
  {ω : B.Choices // (H.columnHoles (H.columnSite i)).Compatible ω}

-- @@ L383-383 verbatim
instance (i : Fin (Fintype.card B.Slot)) : Fintype (H.RowLocalChoices i) := Subtype.fintype _

-- @@ L384-384 verbatim
instance (i : Fin (Fintype.card A.Slot)) : Fintype (H.ColumnLocalChoices i) := Subtype.fintype _


-- @@ L386-388 verbatim
def rowChoiceFinEquiv : H.RowChoices ≃ (∀ i, H.RowLocalChoices i) :=
  (Equiv.piCongrLeft (fun y => {ω : A.Choices // (H.rowHoles y).Compatible ω})
    (Fintype.equivFin B.Slot).symm).symm

-- @@ L389-391 verbatim
def columnChoiceFinEquiv : H.ColumnChoices ≃ (∀ i, H.ColumnLocalChoices i) :=
  (Equiv.piCongrLeft (fun x => {ω : B.Choices // (H.columnHoles x).Compatible ω})
    (Fintype.equivFin A.Slot).symm).symm


-- @@ L393-394 verbatim
def rowLocalWeight (z : ℝ) (i : Fin (Fintype.card B.Slot)) (ω : H.RowLocalChoices i) : ℂ :=
  ((A.choiceWeight z ω.val/(H.rowHoles (H.rowSite i)).probability z : ℝ) : ℂ)

-- @@ L395-396 verbatim
def columnLocalWeight (z : ℝ) (i : Fin (Fintype.card A.Slot)) (ω : H.ColumnLocalChoices i) : ℂ :=
  ((B.choiceWeight z ω.val/(H.columnHoles (H.columnSite i)).probability z : ℝ) : ℂ)

-- @@ L397-398 verbatim
def rowLocalPerm (hf : H.Feasible) (i : Fin (Fintype.card B.Slot)) (ω : H.RowLocalChoices i) :=
  H.rowChildEquiv hf i ((H.rowHoles (H.rowSite i)).residualWithReference ((H.refPair hf).1 (H.rowSite i)) ω)

-- @@ L399-400 verbatim
def columnLocalPerm (hf : H.Feasible) (i : Fin (Fintype.card A.Slot)) (ω : H.ColumnLocalChoices i) :=
  H.columnChildEquiv i ((H.columnHoles (H.columnSite i)).residualWithReference ((H.refPair hf).2 (H.columnSite i)) ω)


-- @@ L402-404 verbatim
def junctionTensorAction (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) :
    H.JunctionFix →* Matrix (Word p (Fintype.card H.JunctionFree)) (Word p (Fintype.card H.JunctionFree)) ℂ :=
  (SignedTensor.action p _).comp (e.symm.permCongrHom.toMonoidHom.comp H.junctionFreeEquiv.toMonoidHom)


-- @@ L406-420 verbatim
theorem rowAverage_eq_ambient (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) :
    H.rowAverage hf z (H.junctionTensorAction p e)=
      ambientAverage (p := p) (FiberBlocks.size H.rowIndex) (total H.rowIndex)
        (regroup H.rowIndex e) (H.rowLocalWeight z) (H.rowLocalPerm hf) := by
  unfold rowAverage ambientAverage averageMatrix
  apply Fintype.sum_equiv H.rowChoiceFinEquiv
  intro ω
  congr 1
  · rw [Complex.ofReal_prod]
    exact ((Fintype.equivFin B.Slot).symm.prod_comp
      (fun y => ((A.choiceWeight z (ω y).val/(H.rowHoles y).probability z : ℝ) : ℂ))).symm
  · change matrix (Equiv.permCongr e.symm (H.junctionFreeEquiv (H.rowResidual hf ω)))=_
    rw [H.rowResidual_as_fibers,ambient_action]
    rfl


-- @@ L422-436 verbatim
theorem columnAverage_eq_ambient (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) :
    H.columnAverage hf z (H.junctionTensorAction p e)=
      ambientAverage (p := p) (FiberBlocks.size H.columnIndex) (total H.columnIndex)
        (regroup H.columnIndex e) (H.columnLocalWeight z) (H.columnLocalPerm hf) := by
  unfold columnAverage ambientAverage averageMatrix
  apply Fintype.sum_equiv H.columnChoiceFinEquiv
  intro ω
  congr 1
  · rw [Complex.ofReal_prod]
    exact ((Fintype.equivFin A.Slot).symm.prod_comp
      (fun x => ((B.choiceWeight z (ω x).val/(H.columnHoles x).probability z : ℝ) : ℂ))).symm
  · change matrix (Equiv.permCongr e.symm (H.junctionFreeEquiv (H.columnResidual hf ω)))=_
    rw [H.columnResidual_as_fibers,ambient_action]
    rfl


-- @@ L438-445 verbatim
theorem rowLocalMoment (hf : H.Feasible) (z : ℝ) (q : ℕ) (i : Fin (Fintype.card B.Slot))
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.rowIndex i)))) :
    (Matrix.trace (((averageMatrix ρ.matrix (H.rowLocalWeight z i) (H.rowLocalPerm hf i)).conjTranspose*
      averageMatrix ρ.matrix (H.rowLocalWeight z i) (H.rowLocalPerm hf i))^q)).re=
      schattenMoment q ((H.rowHoles (H.rowSite i)).conditionalAverage
        (H.rowHoles (H.rowSite i)).feasible_of_disjoint z (ρ.pullback (H.rowChildEquiv hf i))) := by
  exact (H.rowHoles (H.rowSite i)).averageWithReference_moment
    (H.rowHoles (H.rowSite i)).feasible_of_disjoint ((H.refPair hf).1 (H.rowSite i)) z (ρ.pullback (H.rowChildEquiv hf i)) q


-- @@ L447-454 verbatim
theorem columnLocalMoment (hf : H.Feasible) (z : ℝ) (q : ℕ) (i : Fin (Fintype.card A.Slot))
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.columnIndex i)))) :
    (Matrix.trace (((averageMatrix ρ.matrix (H.columnLocalWeight z i) (H.columnLocalPerm hf i)).conjTranspose*
      averageMatrix ρ.matrix (H.columnLocalWeight z i) (H.columnLocalPerm hf i))^q)).re=
      schattenMoment q ((H.columnHoles (H.columnSite i)).conditionalAverage
        (H.columnHoles (H.columnSite i)).feasible_of_disjoint z (ρ.pullback (H.columnChildEquiv i))) := by
  exact (H.columnHoles (H.columnSite i)).averageWithReference_moment
    (H.columnHoles (H.columnSite i)).feasible_of_disjoint ((H.refPair hf).2 (H.columnSite i)) z (ρ.pullback (H.columnChildEquiv i)) q


-- @@ L456-456 verbatim
end CoordinateSweeps.Grid.Holes


-- @@ L458-458 verbatim
namespace CoordinateSweeps

-- @@ L459-459 verbatim
open scoped ComplexOrder

-- @@ L460-466 verbatim
lemma evenTrace_real {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (q : ℕ) :
    Matrix.trace ((K.conjTranspose*K)^q)=((Matrix.trace ((K.conjTranspose*K)^q)).re : ℂ) := by
  have ht := ((Matrix.posSemidef_conjTranspose_mul_self K).pow q).trace_nonneg
  apply Complex.ext
  · rfl
  · simpa using ht.2.symm

-- @@ L467-467 verbatim
end CoordinateSweeps


-- @@ L469-469 verbatim
namespace CoordinateSweeps.Grid.Holes

-- @@ L470-470 verbatim
open FiberBlocks SignedTensor UnitaryIrrep

-- @@ L471-471 verbatim
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)


-- @@ L473-491 verbatim
theorem row_projected_moment (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) {q : ℕ} (hq : q ≠ 0)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.rowIndex i)))) :
    let P := ambientProjector (p := p) (FiberBlocks.size H.rowIndex) (total H.rowIndex) (regroup H.rowIndex e) ρ
    let X := H.rowAverage hf z (H.junctionTensorAction p e)
    (Matrix.trace (((P*X).conjTranspose*(P*X))^q)).re=
      ∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
        (matrixRepresentation (SignedTensor.action p (FiberBlocks.size H.rowIndex i)))) : ℝ)*
        schattenMoment q ((H.rowHoles (H.rowSite i)).conditionalAverage
          (H.rowHoles (H.rowSite i)).feasible_of_disjoint z ((ρ i).pullback (H.rowChildEquiv hf i))) := by
  dsimp only
  rw [H.rowAverage_eq_ambient,ambient_projected_moment _ _ _ _ _ _ hq]
  have he (i : Fin (Fintype.card B.Slot)) :
      Matrix.trace (((averageMatrix (ρ i).matrix (H.rowLocalWeight z i) (H.rowLocalPerm hf i)).conjTranspose*
        averageMatrix (ρ i).matrix (H.rowLocalWeight z i) (H.rowLocalPerm hf i))^q)=
        (schattenMoment q ((H.rowHoles (H.rowSite i)).conditionalAverage
          (H.rowHoles (H.rowSite i)).feasible_of_disjoint z ((ρ i).pullback (H.rowChildEquiv hf i))) : ℂ) := by
    rw [evenTrace_real,H.rowLocalMoment]
  simp only [he,← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_prod,Complex.ofReal_re]


-- @@ L493-511 verbatim
theorem column_projected_moment (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) {q : ℕ} (hq : q ≠ 0)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.columnIndex i)))) :
    let P := ambientProjector (p := p) (FiberBlocks.size H.columnIndex) (total H.columnIndex) (regroup H.columnIndex e) ρ
    let Y := H.columnAverage hf z (H.junctionTensorAction p e)
    (Matrix.trace (((P*Y).conjTranspose*(P*Y))^q)).re=
      ∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
        (matrixRepresentation (SignedTensor.action p (FiberBlocks.size H.columnIndex i)))) : ℝ)*
        schattenMoment q ((H.columnHoles (H.columnSite i)).conditionalAverage
          (H.columnHoles (H.columnSite i)).feasible_of_disjoint z ((ρ i).pullback (H.columnChildEquiv i))) := by
  dsimp only
  rw [H.columnAverage_eq_ambient,ambient_projected_moment _ _ _ _ _ _ hq]
  have he (i : Fin (Fintype.card A.Slot)) :
      Matrix.trace (((averageMatrix (ρ i).matrix (H.columnLocalWeight z i) (H.columnLocalPerm hf i)).conjTranspose*
        averageMatrix (ρ i).matrix (H.columnLocalWeight z i) (H.columnLocalPerm hf i))^q)=
        (schattenMoment q ((H.columnHoles (H.columnSite i)).conditionalAverage
          (H.columnHoles (H.columnSite i)).feasible_of_disjoint z ((ρ i).pullback (H.columnChildEquiv i))) : ℂ) := by
    rw [evenTrace_real,H.columnLocalMoment]
  simp only [he,← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_prod,Complex.ofReal_re]


-- @@ L513-513 verbatim
end CoordinateSweeps.Grid.Holes


-- @@ L515-515 verbatim
namespace CoordinateSweeps.Grid.Holes

-- @@ L516-516 verbatim
open FiberBlocks SignedTensor UnitaryIrrep

-- @@ L517-517 verbatim
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

-- @@ L518-522 verbatim
lemma row_size_le (i : Fin (Fintype.card B.Slot)) : FiberBlocks.size H.rowIndex i ≤ A.size := by
  have hc := Fintype.card_congr (H.rowLocalChart i)
  rw [Fintype.card_fin,(H.rowHoles (H.rowSite i)).card_freeAt] at hc
  rw [hc]
  exact Nat.sub_le _ _

-- @@ L523-527 verbatim
lemma column_size_le (i : Fin (Fintype.card A.Slot)) : FiberBlocks.size H.columnIndex i ≤ B.size := by
  have hc := Fintype.card_congr (H.columnLocalChart i)
  rw [Fintype.card_fin,(H.columnHoles (H.columnSite i)).card_freeAt] at hc
  rw [hc]
  exact Nat.sub_le _ _


-- @@ L529-542 verbatim
theorem row_moment_bound (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) {q : ℕ} (hq : q ≠ 0)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.rowIndex i))))
    (E : Fin (Fintype.card B.Slot) → ℝ)
    (hE : ∀ i, schattenMoment q ((H.rowHoles (H.rowSite i)).conditionalAverage
      (H.rowHoles (H.rowSite i)).feasible_of_disjoint z ((ρ i).pullback (H.rowChildEquiv hf i))) ≤ Real.exp (E i)) :
    let P := ambientProjector (p := p) (FiberBlocks.size H.rowIndex) (total H.rowIndex) (regroup H.rowIndex e) ρ
    let X := H.rowAverage hf z (H.junctionTensorAction p e)
    (Matrix.trace (((P*X).conjTranspose*(P*X))^q)).re ≤
      ((A.size+1 : ℕ) : ℝ)^(B.size*((2*p)*(2*p)))*Real.exp (∑ i, E i) := by
  dsimp only
  rw [H.row_projected_moment p e hf z hq ρ]
  simpa only [card_slot] using child_product_bound (FiberBlocks.size H.rowIndex) A.size
    H.row_size_le ρ _ E (fun i => (H.rowHoles (H.rowSite i)).conditionalMoment_nonneg _ _ _ _) hE


-- @@ L544-560 verbatim
theorem column_moment_bound (p : ℕ) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) {q : ℕ} (hq : q ≠ 0)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size H.columnIndex i))))
    (E : Fin (Fintype.card A.Slot) → ℝ)
    (hE : ∀ i, schattenMoment q ((H.columnHoles (H.columnSite i)).conditionalAverage
      (H.columnHoles (H.columnSite i)).feasible_of_disjoint z ((ρ i).pullback (H.columnChildEquiv i))) ≤ Real.exp (E i)) :
    let P := ambientProjector (p := p) (FiberBlocks.size H.columnIndex) (total H.columnIndex) (regroup H.columnIndex e) ρ
    let Y := H.columnAverage hf z (H.junctionTensorAction p e)
    (Matrix.trace (((Y*P).conjTranspose*(Y*P))^q)).re ≤
      ((B.size+1 : ℕ) : ℝ)^(A.size*((2*p)*(2*p)))*Real.exp (∑ i, E i) := by
  dsimp only
  have hc : _*_=_*_ := ambientProjector_commute_average (p := p) (FiberBlocks.size H.columnIndex)
    (total H.columnIndex) (regroup H.columnIndex e) ρ (H.columnLocalWeight z) (H.columnLocalPerm hf)
  rw [← H.columnAverage_eq_ambient] at hc
  rw [← hc,H.column_projected_moment p e hf z hq ρ]
  simpa only [card_slot] using child_product_bound (FiberBlocks.size H.columnIndex) B.size
    H.column_size_le ρ _ E (fun i => (H.columnHoles (H.columnSite i)).conditionalMoment_nonneg _ _ _ _) hE


-- @@ L562-562 verbatim
end CoordinateSweeps.Grid.Holes


-- @@ L564-564 verbatim
end

-- @@ L565-565 verbatim
end

-- @@ L566-566 verbatim
end

-- @@ L567-567 verbatim
end

-- @@ L568-568 verbatim
end

-- @@ L569-569 verbatim
end

-- @@ L570-570 verbatim
end

-- @@ L571-571 verbatim
end

-- @@ L572-572 verbatim
open scoped Matrix.Norms.L2Operator


-- @@ L574-574 verbatim
end OAI
