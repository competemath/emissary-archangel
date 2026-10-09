import OAI.Analysis.CharacterCriterion.InfiniteTensor


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped TensorProduct

-- @@ L7-7 verbatim
open scoped InnerProductSpace

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Set Module

-- @@ L10-10 verbatim
open Topology

-- @@ L11-11 verbatim
open NormedSpace

-- @@ L12-12 verbatim
open scoped ComplexOrder

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped InnerProductSpace

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open NormedSpace

-- @@ L17-17 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L18-18 verbatim
open UniformSpace

-- @@ L19-19 verbatim
variable [KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L21-21 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L22-22 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L24-24 verbatim
open Filter Topology

-- @@ L25-25 verbatim
open Topology

-- @@ L26-26 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L27-27 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L28-28 verbatim
open NormedSpace

-- @@ L29-29 verbatim
open scoped ComplexOrder

-- @@ L30-30 verbatim
open scoped ComplexOrder

-- @@ L31-31 verbatim
open scoped InnerProductSpace

-- @@ L32-32 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L33-33 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L34-34 verbatim
open UniformSpace


-- @@ L36-36 verbatim
namespace KirchbergRordam.DropMatrixRepresentations

-- @@ L37-37 verbatim
open MatrixDiagonalPath MatrixBlockReindex

-- @@ L38-38 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L39-39 verbatim
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

-- @@ L40-45 verbatim
lemma left_injective [Nonempty κ] : Function.Injective (MatrixTensor.leftMatrix (ι:=ι) (κ:=κ)) := by
  intro a b h
  ext i j
  let k : κ := Classical.choice inferInstance
  have he := congrArg (fun m : Mat (ι×κ) => m (i,k) (j,k)) h
  simpa [left_apply] using he

-- @@ L46-51 verbatim
lemma right_injective [Nonempty ι] : Function.Injective (MatrixTensor.rightMatrix (ι:=ι) (κ:=κ)) := by
  intro a b h
  ext i j
  let k : ι := Classical.choice inferInstance
  have he := congrArg (fun m : Mat (ι×κ) => m (k,i) (k,j)) h
  simpa [right_apply] using he

-- @@ L52-52 verbatim
variable (p q : ℕ) [instNeZerop : NeZero p] [instNeZeroq : NeZero q]

-- @@ L53-53 verbatim
def leftValue (f : PrimeDimensionDrop.Algebra p q) : Mat (Fin p) := Classical.choose f.property.1

-- @@ L54-61 verbatim
omit instNeZerop instNeZeroq in
lemma leftValue_spec
    (p : ℕ)
    (q : ℕ)
    [NeZero p]
    [NeZero q]
    (f : PrimeDimensionDrop.Algebra p q) :
    MatrixTensor.leftMatrix (κ:=Fin q) (leftValue p q f)=f.val 0 := Classical.choose_spec f.property.1

-- @@ L62-62 verbatim
def rightValue (f : PrimeDimensionDrop.Algebra p q) : Mat (Fin q) := Classical.choose f.property.2

-- @@ L63-70 verbatim
omit instNeZerop instNeZeroq in
lemma rightValue_spec
    (p : ℕ)
    (q : ℕ)
    [NeZero p]
    [NeZero q]
    (f : PrimeDimensionDrop.Algebra p q) :
    MatrixTensor.rightMatrix (ι:=Fin p) (rightValue p q f)=f.val 1 := Classical.choose_spec f.property.2

-- @@ L71-78 verbatim
def leftEvaluation : PrimeDimensionDrop.Algebra p q →⋆ₐ[ℂ] Mat (Fin p) where
  toFun := leftValue p q
  map_zero' := left_injective (κ:=Fin q) (by rw [map_zero,leftValue_spec]; rfl)
  map_one' := left_injective (κ:=Fin q) (by rw [map_one,leftValue_spec]; rfl)
  map_add' a b := left_injective (κ:=Fin q) (by rw [leftValue_spec,map_add,leftValue_spec,leftValue_spec]; rfl)
  map_mul' a b := left_injective (κ:=Fin q) (by rw [leftValue_spec,map_mul,leftValue_spec,leftValue_spec]; rfl)
  commutes' z := left_injective (κ:=Fin q) (by rw [AlgHomClass.commutes,leftValue_spec]; rfl)
  map_star' a := left_injective (κ:=Fin q) (by rw [leftValue_spec,map_star,leftValue_spec]; rfl)

-- @@ L79-86 verbatim
def rightEvaluation : PrimeDimensionDrop.Algebra p q →⋆ₐ[ℂ] Mat (Fin q) where
  toFun := rightValue p q
  map_zero' := right_injective (ι:=Fin p) (by rw [map_zero,rightValue_spec]; rfl)
  map_one' := right_injective (ι:=Fin p) (by rw [map_one,rightValue_spec]; rfl)
  map_add' a b := right_injective (ι:=Fin p) (by rw [rightValue_spec,map_add,rightValue_spec,rightValue_spec]; rfl)
  map_mul' a b := right_injective (ι:=Fin p) (by rw [rightValue_spec,map_mul,rightValue_spec,rightValue_spec]; rfl)
  commutes' z := right_injective (ι:=Fin p) (by rw [AlgHomClass.commutes,rightValue_spec]; rfl)
  map_star' a := right_injective (ι:=Fin p) (by rw [rightValue_spec,map_star,rightValue_spec]; rfl)

-- @@ L87-91 verbatim
lemma two_three (r : ℕ) (hr : 2≤r) : ∃ a b : ℕ, 2*a+3*b=r := by
  by_cases h : r%2=0
  · exact ⟨r/2,0,by omega⟩
  · have hr3 : 3≤r := by omega
    exact ⟨(r-3)/2,1,by omega⟩

-- @@ L92-95 verbatim
def blockRepresentation (a b : ℕ) : DimensionDrop23 →⋆ₐ[ℂ]
    Mat ((Fin 2×Fin a) ⊕ (Fin 3×Fin b)) :=
  sumBlock.comp (((MatrixTensor.leftMatrix (κ:=Fin a)).comp (leftEvaluation 2 3)).prod
    ((MatrixTensor.leftMatrix (κ:=Fin b)).comp (rightEvaluation 2 3)))

-- @@ L96-103 verbatim
def representation (ι : Type*) [Fintype ι] [DecidableEq ι] (hι : 2≤Fintype.card ι) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ι := by
  let a := (two_three (Fintype.card ι) hι).choose
  let b := (two_three (Fintype.card ι) hι).choose_spec.choose
  have h : 2*a+3*b=Fintype.card ι := (two_three (Fintype.card ι) hι).choose_spec.choose_spec
  let e : ((Fin 2×Fin a) ⊕ (Fin 3×Fin b)) ≃ ι :=
    BalancedDropSystem.cardEquiv (by simpa using h)
  exact (CStarMatrix.reindexₐ ℂ ℂ e).toStarAlgHom.comp (blockRepresentation a b)

-- @@ L104-104 verbatim
end KirchbergRordam.DropMatrixRepresentations

-- @@ L105-105 verbatim
namespace KirchbergRordam.EndpointMultiplicity

-- @@ L106-106 verbatim
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration

-- @@ L107-107 verbatim
open scoped ComplexOrder CStarAlgebra

-- @@ L108-109 verbatim
variable {P Q R : Type*} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]

-- @@ L110-121 verbatim
def leftExpand : P ⊕ ((P×Q)×R) ≃ P × (Unit ⊕ (Q×R)) where
  toFun x := match x with
    | .inl a => (a,.inl ())
    | .inr ((a,b),r) => (a,.inr (b,r))
  invFun x := match x.2 with
    | .inl _ => .inl x.1
    | .inr (b,r) => .inr ((x.1,b),r)
  left_inv x := by rcases x with a|⟨⟨a,b⟩,r⟩ <;> rfl
  right_inv x := by
    rcases x with ⟨a,u|⟨b,r⟩⟩
    · cases u; rfl
    · rfl

-- @@ L122-133 verbatim
def rightExpand : Q ⊕ ((P×Q)×R) ≃ Q × (Unit ⊕ (P×R)) where
  toFun x := match x with
    | .inl b => (b,.inl ())
    | .inr ((a,b),r) => (b,.inr (a,r))
  invFun x := match x.2 with
    | .inl _ => .inl x.1
    | .inr (a,r) => .inr ((a,x.1),r)
  left_inv x := by rcases x with b|⟨⟨a,b⟩,r⟩ <;> rfl
  right_inv x := by
    rcases x with ⟨b,u|⟨a,r⟩⟩
    · cases u; rfl
    · rfl

-- @@ L134-145 verbatim
lemma leftExpand_matrix (a : Mat P) :
    CStarMatrix.reindexₐ ℂ ℂ (leftExpand (Q:=Q) (R:=R))
      (sumBlock (a,block (fun _ : R => MatrixTensor.leftMatrix (κ:=Q) a))) =
      MatrixTensor.leftMatrix (κ:=Unit ⊕ (Q×R)) a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  rcases k with u|⟨b,r⟩ <;> rcases l with v|⟨c,s⟩
  · cases u; cases v; change a i j = a i j * 1; simp
  · cases u; change 0 = a i j * 0; simp
  · cases v; change 0 = a i j * 0; simp
  · change (if r=s then a i j * (if b=c then 1 else 0) else 0) =
      a i j * (if (Sum.inr (b,r) : Unit ⊕ Q×R)=.inr (c,s) then 1 else 0)
    by_cases hb : b=c <;> by_cases hr : r=s <;> simp [hb,hr,Prod.ext_iff]

-- @@ L146-157 verbatim
lemma rightExpand_matrix (a : Mat Q) :
    CStarMatrix.reindexₐ ℂ ℂ (rightExpand (P:=P) (R:=R))
      (sumBlock (a,block (fun _ : R => MatrixTensor.rightMatrix (ι:=P) a))) =
      MatrixTensor.leftMatrix (κ:=Unit ⊕ (P×R)) a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  rcases k with u|⟨b,r⟩ <;> rcases l with v|⟨c,s⟩
  · cases u; cases v; change a i j = a i j * 1; simp
  · cases u; change 0 = a i j * 0; simp
  · cases v; change 0 = a i j * 0; simp
  · change (if r=s then (if b=c then 1 else 0) * a i j else 0) =
      a i j * (if (Sum.inr (b,r) : Unit ⊕ P×R)=.inr (c,s) then 1 else 0)
    by_cases hb : b=c <;> by_cases hr : r=s <;> simp [hb,hr,Prod.ext_iff]

-- @@ L158-158 verbatim
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

-- @@ L159-166 verbatim
def constHom (ι : Type*) : A →⋆ₐ[ℂ] (ι→A) where
  toFun a _ := a
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

-- @@ L167-168 verbatim
def prodUnitary (u : unitary A) (v : unitary B) : unitary (A×B) :=
  ⟨(u,v),⟨Prod.ext u.property.1 v.property.1,Prod.ext u.property.2 v.property.2⟩⟩

-- @@ L169-172 verbatim
lemma map_conj (φ : A →⋆ₐ[ℂ] B) (u : unitary A) (a : A) :
    φ (conj u a) = conj (Unitary.map (StarMonoidHom.ofClass φ) u) (φ a) := by
  change φ ((u:A)*a*star (u:A)) = φ (u:A)*φ a*star (φ (u:A))
  rw [map_mul,map_mul,map_star]

-- @@ L173-175 verbatim
def duplicate : Mat P × Mat Q →⋆ₐ[ℂ] Mat (P ⊕ (Q×R)) :=
  sumBlock.comp ((StarAlgHom.fst ℂ (Mat P) (Mat Q)).prod
    ((block.comp (constHom R)).comp (StarAlgHom.snd ℂ (Mat P) (Mat Q))))

-- @@ L176-178 verbatim
def duplicateUnitary (v : unitary (Mat Q)) : unitary (Mat (P⊕(Q×R))) :=
  Unitary.map (StarMonoidHom.ofClass (duplicate (P:=P) (Q:=Q) (R:=R)))
    (prodUnitary (1:unitary (Mat P)) v)

-- @@ L179-189 verbatim
lemma conj_duplicate (v : unitary (Mat Q)) (a : Mat P) (b : Mat Q) :
    conj (duplicateUnitary (P:=P) (Q:=Q) (R:=R) v) (sumBlock (a,block (fun _ : R => b))) =
      sumBlock (a,block (fun _ : R => conj v b)) := by
  have hm := map_conj (duplicate (P:=P) (Q:=Q) (R:=R)) (prodUnitary 1 v) (a,b)
  change duplicate (conj (prodUnitary 1 v) (a,b)) = _ at hm
  change conj (Unitary.map (StarMonoidHom.ofClass (duplicate (P:=P) (Q:=Q) (R:=R))) (prodUnitary 1 v))
    (duplicate (a,b)) = _
  rw [← hm]
  change duplicate ((1:Mat P)*a*star (1:Mat P),conj v b)=_
  simp only [star_one,one_mul,mul_one]
  rfl

-- @@ L190-190 verbatim
end KirchbergRordam.EndpointMultiplicity

-- @@ L191-191 verbatim
namespace KirchbergRordam.EndpointMultiplicity

-- @@ L192-192 verbatim
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration

-- @@ L193-193 verbatim
open scoped ComplexOrder CStarAlgebra

-- @@ L194-195 verbatim
variable {P Q R : Type*} [Fintype P] [Fintype Q] [Fintype R]
  [DecidableEq P] [DecidableEq Q] [DecidableEq R]


-- @@ L197-200 verbatim
def leftBase (h : 2≤Fintype.card (Unit ⊕ (Q×R))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (P⊕((P×Q)×R)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (leftExpand (P:=P) (Q:=Q) (R:=R)).symm).toStarAlgHom.comp
    (MatrixTensor.rightMatrix.comp (DropMatrixRepresentations.representation _ h))

-- @@ L201-204 verbatim
def rightBase (h : 2≤Fintype.card (Unit ⊕ (P×R))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (Q⊕((P×Q)×R)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (rightExpand (P:=P) (Q:=Q) (R:=R)).symm).toStarAlgHom.comp
    (MatrixTensor.rightMatrix.comp (DropMatrixRepresentations.representation _ h))

-- @@ L205-220 verbatim
lemma leftBase_commute (h : 2≤Fintype.card (Unit ⊕ (Q×R))) (a : Mat P)
    (d : DimensionDrop23) :
    Commute (leftBase (P:=P) h d)
      (sumBlock (a,block (fun _ : R => MatrixTensor.leftMatrix (κ:=Q) a))) := by
  let e := CStarMatrix.reindexₐ ℂ ℂ (leftExpand (P:=P) (Q:=Q) (R:=R))
  apply e.injective
  change e (leftBase h d * _)=e (_ * leftBase h d)
  rw [map_mul,map_mul,leftExpand_matrix]
  have he : e (leftBase (P:=P) h d)=MatrixTensor.rightMatrix
      (DropMatrixRepresentations.representation _ h d) := by
    simp only [leftBase,StarAlgHom.comp_apply,
      CStarMatrix.reindexₐ_symm]
    change e (e.symm (MatrixTensor.rightMatrix (DropMatrixRepresentations.representation _ h d))) = _
    exact e.apply_symm_apply _
  rw [he]
  exact (MatrixTensor.legs_commute a _).symm.eq

-- @@ L221-236 verbatim
lemma rightBase_commute (h : 2≤Fintype.card (Unit ⊕ (P×R))) (a : Mat Q)
    (d : DimensionDrop23) :
    Commute (rightBase (Q:=Q) h d)
      (sumBlock (a,block (fun _ : R => MatrixTensor.rightMatrix (ι:=P) a))) := by
  let e := CStarMatrix.reindexₐ ℂ ℂ (rightExpand (P:=P) (Q:=Q) (R:=R))
  apply e.injective
  change e (rightBase h d * _)=e (_ * rightBase h d)
  rw [map_mul,map_mul,rightExpand_matrix]
  have he : e (rightBase (Q:=Q) h d)=MatrixTensor.rightMatrix
      (DropMatrixRepresentations.representation _ h d) := by
    simp only [rightBase,StarAlgHom.comp_apply,
      CStarMatrix.reindexₐ_symm]
    change e (e.symm (MatrixTensor.rightMatrix (DropMatrixRepresentations.representation _ h d))) = _
    exact e.apply_symm_apply _
  rw [he]
  exact (MatrixTensor.legs_commute a _).symm.eq


-- @@ L238-240 verbatim
def leftRep (h : 2≤Fintype.card (Unit ⊕ (Q×R))) (v : unitary (Mat (P×Q))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (P⊕((P×Q)×R)) :=
  (conj (duplicateUnitary (P:=P) (Q:=P×Q) (R:=R) v)).toStarAlgHom.comp (leftBase (P:=P) (Q:=Q) (R:=R) h)

-- @@ L241-243 verbatim
def rightRep (h : 2≤Fintype.card (Unit ⊕ (P×R))) (v : unitary (Mat (P×Q))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (Q⊕((P×Q)×R)) :=
  (conj (duplicateUnitary (P:=Q) (Q:=P×Q) (R:=R) v)).toStarAlgHom.comp (rightBase (P:=P) (Q:=Q) (R:=R) h)

-- @@ L244-254 verbatim
lemma leftRep_commute (h : 2≤Fintype.card (Unit ⊕ (Q×R))) (v : unitary (Mat (P×Q)))
    (a : Mat P) (d : DimensionDrop23) :
    Commute (leftRep h v d)
      (sumBlock (a,block (fun _ : R => conj v (MatrixTensor.leftMatrix (κ:=Q) a)))) := by
  have hc := (leftBase_commute h a d).map
    (conj (duplicateUnitary (P:=P) (Q:=P×Q) (R:=R) v)).toRingHom
  change Commute (conj (duplicateUnitary (P:=P) (Q:=P×Q) (R:=R) v) (leftBase h d))
    (conj (duplicateUnitary (P:=P) (Q:=P×Q) (R:=R) v)
      (sumBlock (a,block (fun _ : R => MatrixTensor.leftMatrix (κ:=Q) a)))) at hc
  rw [conj_duplicate] at hc
  exact hc

-- @@ L255-265 verbatim
lemma rightRep_commute (h : 2≤Fintype.card (Unit ⊕ (P×R))) (v : unitary (Mat (P×Q)))
    (a : Mat Q) (d : DimensionDrop23) :
    Commute (rightRep h v d)
      (sumBlock (a,block (fun _ : R => conj v (MatrixTensor.rightMatrix (ι:=P) a)))) := by
  have hc := (rightBase_commute h a d).map
    (conj (duplicateUnitary (P:=Q) (Q:=P×Q) (R:=R) v)).toRingHom
  change Commute (conj (duplicateUnitary (P:=Q) (Q:=P×Q) (R:=R) v) (rightBase h d))
    (conj (duplicateUnitary (P:=Q) (Q:=P×Q) (R:=R) v)
      (sumBlock (a,block (fun _ : R => MatrixTensor.rightMatrix (ι:=P) a)))) at hc
  rw [conj_duplicate] at hc
  exact hc


-- @@ L267-267 verbatim
variable {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]

-- @@ L268-281 verbatim
lemma commutator_approx (ρ : D →⋆ₐ[ℂ] B) (a b : B) (d : D) {ε : ℝ}
    (hc : Commute (ρ d) b) (h : ‖a-b‖≤ε) :
    ‖ρ d*a-a*ρ d‖≤2*ε*‖d‖ := by
  have he : ρ d*a-a*ρ d=ρ d*(a-b)-(a-b)*ρ d := by
    rw [mul_sub,sub_mul,hc.eq]
    abel
  rw [he]
  calc
    _ ≤ ‖ρ d‖*‖a-b‖+‖a-b‖*‖ρ d‖ := (norm_sub_le _ _).trans
      (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖d‖*ε+ε*‖d‖ := add_le_add
      (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le ρ d) h (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul h (NonUnitalStarAlgHom.norm_apply_le ρ d) (norm_nonneg _) (le_trans (norm_nonneg _) h))
    _ = _ := by ring

-- @@ L282-287 verbatim
lemma duplicate_difference (a : Mat P) (x y : Mat Q) :
    ‖sumBlock (a,block (fun _ : R => x))-sumBlock (a,block (fun _ : R => y))‖≤‖x-y‖ := by
  change ‖duplicate (a,x)-duplicate (a,y)‖≤_
  rw [←map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le (duplicate (P:=P) (Q:=Q) (R:=R)) _).trans
    (by simp [Prod.norm_def])

-- @@ L288-294 verbatim
lemma leftRep_bound (h : 2≤Fintype.card (Unit ⊕ (Q×R))) (v : unitary (Mat (P×Q)))
    (a : Mat P) (x : Mat (P×Q)) (d : DimensionDrop23) {ε : ℝ}
    (hx : ‖x-conj v (MatrixTensor.leftMatrix (κ:=Q) a)‖≤ε) :
    ‖leftRep h v d*sumBlock (a,block (fun _ : R => x))-
      sumBlock (a,block (fun _ : R => x))*leftRep h v d‖≤2*ε*‖d‖ :=
  commutator_approx (leftRep h v) _ _ d (leftRep_commute h v a d)
    ((duplicate_difference a x _).trans hx)

-- @@ L295-301 verbatim
lemma rightRep_bound (h : 2≤Fintype.card (Unit ⊕ (P×R))) (v : unitary (Mat (P×Q)))
    (a : Mat Q) (x : Mat (P×Q)) (d : DimensionDrop23) {ε : ℝ}
    (hx : ‖x-conj v (MatrixTensor.rightMatrix (ι:=P) a)‖≤ε) :
    ‖rightRep h v d*sumBlock (a,block (fun _ : R => x))-
      sumBlock (a,block (fun _ : R => x))*rightRep h v d‖≤2*ε*‖d‖ :=
  commutator_approx (rightRep h v) _ _ d (rightRep_commute h v a d)
    ((duplicate_difference a x _).trans hx)

-- @@ L302-302 verbatim
end KirchbergRordam.EndpointMultiplicity

-- @@ L303-303 verbatim
end


-- @@ L305-305 verbatim
end OAI
