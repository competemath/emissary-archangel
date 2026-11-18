import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceProducts


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.DetectorDictionaryInverseMarkedReference

-- @@ L9-9 verbatim
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge

-- @@ L10-10 verbatim
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic CanonicalRowCompletion

-- @@ L11-11 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L12-12 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]


-- @@ L14-20 verbatim
def remainingResidual (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)(a:Ideal O→ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,star ((∏i:{i:ι // i∉J},coeff i.val (y i).val)*
    (moebius (remainingIdeal L J y):ℂ))*
    conjugatedResidual S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) η a W Z r z G u


-- @@ L22-29 verbatim
theorem assigned_remaining_squarefree (L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(y:Remaining L J) :
    Squarefree (assignedIdeal L J x*remainingIdeal L J y) := by
  rw [←joinTuple_product]
  exact tuple_product_squarefree _ (fun i=>hprime i _ (joinTuple L J x y i).property)
    (tuple_injective L hdis _)


-- @@ L31-49 verbatim
theorem assigned_source_eq_remainingResidual (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(u:O) :
    (∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
      originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
        (assignedIdeal L J x) η a W Z r z u)=
    (moebius (assignedIdeal L J x):ℂ)*(Z^(-G):ℝ)*η (assignedIdeal L J x)^2*
      (idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z G u) := by
  unfold remainingResidual
  simp only [star_sum,star_mul,star_star,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [originalFixedPolynomial_eq_conjugatedResidual S
    (assigned_remaining_squarefree L hprime hdis J x y) (dvd_mul_right _ _) η a W hZ r z G,
    InverseInitialOverlap.residual,quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]
  ring


-- @@ L51-68 verbatim
theorem original_selected_overlap (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)
    (hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
      (Z^(-G J):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z (G J) u) := by
  rw [original_selected_grouped_products S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [assigned_source_eq_remainingResidual S L hprime hdis J x coeff η a W Z r z (G J) hZ u]
  ring


-- @@ L70-70 verbatim
end SevenEighths.DetectorDictionaryInverseMarkedReference


-- @@ L72-72 verbatim
end


-- @@ L74-74 verbatim
end OAI
