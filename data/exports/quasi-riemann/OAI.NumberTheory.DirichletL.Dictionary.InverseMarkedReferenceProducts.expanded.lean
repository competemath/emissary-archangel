import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceTuples


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.DetectorDictionaryInverseMarkedReference

-- @@ L9-9 verbatim
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge InverseInitialOverlap

-- @@ L10-10 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L11-11 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]


-- @@ L13-14 verbatim
def assignedIdeal (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J) : Ideal O :=
  ∏i:↥J,(x i).val


-- @@ L16-17 verbatim
def remainingIdeal (L:ι→Finset (Ideal O))(J:Finset ι)(y:Remaining L J) : Ideal O :=
  ∏i:{i:ι // i∉J},(y i).val


-- @@ L19-22 verbatim
omit [Fintype ι] in
@[simp] theorem joinTuple_assigned (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:↥J) : joinTuple L J x y i.val=x i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]


-- @@ L24-27 verbatim
omit [Fintype ι] in
@[simp] theorem joinTuple_remaining (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:{i:ι // i∉J}) : joinTuple L J x y i.val=y i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]


-- @@ L29-34 verbatim
omit [Fintype ι] in
theorem joinTuple_assigned_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i∈J,(joinTuple L J x y i).val)=assignedIdeal L J x := by
  rw [←Finset.prod_coe_sort J (fun i=>(joinTuple L J x y i).val)]
  simp only [joinTuple_assigned,assignedIdeal]


-- @@ L36-46 verbatim
theorem joinTuple_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i,(joinTuple L J x y i).val)=assignedIdeal L J x*remainingIdeal L J y := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>(joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp


-- @@ L48-59 verbatim
theorem joinTuple_coefficient_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(coeff:ι→Ideal O→ℂ) :
    (∏i,coeff i (joinTuple L J x y i).val)=
      (∏i:↥J,coeff i.val (x i).val)*(∏i:{i:ι // i∉J},coeff i.val (y i).val) := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>coeff i (joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp


-- @@ L61-64 verbatim
omit [Fintype ι] [DecidableEq ι] in
theorem assignedIdeal_ne_zero (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J) : assignedIdeal L J x≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi=>(hprime i.val _ (x i).property).ne_zero)


-- @@ L66-69 verbatim
theorem residual_join (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J)(y:Remaining L J) :
    residual (∏i,(joinTuple L J x y i).val) (assignedIdeal L J x)=remainingIdeal L J y := by
  rw [joinTuple_product,InverseInitialOverlap.residual,quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]


-- @@ L71-91 verbatim
theorem original_selected_grouped_products (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*
      ∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
        originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
          (assignedIdeal L J x) η a W Z r z u := by
  rw [original_selected_grouped S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [joinTuple_coefficient_product,joinTuple_product,joinTuple_assigned_product]
  ring


-- @@ L93-93 verbatim
end SevenEighths.DetectorDictionaryInverseMarkedReference


-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
end OAI
