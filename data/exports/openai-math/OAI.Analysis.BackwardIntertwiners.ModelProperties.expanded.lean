import OAI.Analysis.BackwardIntertwiners.ProductSymbols


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace BackwardIntertwiners

-- @@ L6-6 verbatim
open Filter

-- @@ L7-7 verbatim
open scoped Topology

-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open Topology MeasureTheory Set

-- @@ L11-11 verbatim
open scoped ENNReal


-- @@ L13-13 verbatim
open scoped Classical


-- @@ L15-15 verbatim
universe u

-- @@ L16-16 verbatim
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


-- @@ L18-18 verbatim
attribute [local instance] realOperatorTower realOperatorCommute complexNormalCalculus complexClosedCalculus realSelfAdjointCalculus


-- @@ L20-20 verbatim
open InnerProductSpace ContinuousLinearMap



-- @@ L23-35 verbatim
structure OrdinaryStructuralProperties (D : DirectModelData) : Prop where
  tails : ∀ h : ℤ, ∃ L : Submodule ℂ GlobalHilbert,
    (∀ f : GlobalHilbert, f ∈ L ↔ ∀ᵐ x ∂baseMeasure, f x ∈ coordinateTail h) ∧
    IsClosed (L : Set GlobalHilbert) ∧ L ≠ ⊥ ∧ L ≠ ⊤ ∧
    OperatorInvariant L D.S ∧ ¬OperatorInvariant L D.V
  fiber_compact : ∀ x : Base, IsCompactOperator (D.Sx x)
  global_not_compact : ¬IsCompactOperator D.S
  multiplier_witness : ∃ Q : GlobalHilbert →L[ℂ] GlobalHilbert,
    IsStarProjection Q ∧
    (∀ f : GlobalHilbert, Q f =ᵐ[baseMeasure] fun x => lp.single 2 0 (f x 0)) ∧
    Q * D.S ≠ D.S * Q ∧
    (∀ g : Lp ℂ ∞ baseMeasure, Q * scalarMultiplier g = scalarMultiplier g * Q) ∧
    Q ∉ Set.range (scalarMultiplier (μ:=baseMeasure))





-- @@ L40-62 verbatim
structure PolarFamilyProperties (D : DirectModelData)
    (U : (GlobalHilbert →L[ℂ] GlobalHilbert)ˣ)
    (A : ℤ → GlobalHilbert →L[ℂ] GlobalHilbert) : Prop where
  unitary : star (U : GlobalHilbert →L[ℂ] GlobalHilbert) =
    ((U⁻¹ : (GlobalHilbert →L[ℂ] GlobalHilbert)ˣ) : GlobalHilbert →L[ℂ] GlobalHilbert)
  unitary_coordinates : ∀ f : GlobalHilbert, ∀ᵐ x ∂baseMeasure, ∀ j : ℤ,
    (U : GlobalHilbert →L[ℂ] GlobalHilbert) f x j = f x (j-1)
  modulus : A 0 = CFC.sqrt (star D.S * D.S)
  polar : D.S = (U : GlobalHilbert →L[ℂ] GlobalHilbert) * A 0
  injective : Function.Injective (A 0)
  dense_range : DenseRange (A 0)
  conjugates : ∀ n : ℤ, A n =
    ((U^(-n) : (GlobalHilbert →L[ℂ] GlobalHilbert)ˣ) : GlobalHilbert →L[ℂ] GlobalHilbert) *
      A 0 * ((U^n : (GlobalHilbert →L[ℂ] GlobalHilbert)ˣ) : GlobalHilbert →L[ℂ] GlobalHilbert)
  diagonal : ∀ n : ℤ, ∀ f : GlobalHilbert, ∀ᵐ x ∂baseMeasure, ∀ j : ℤ,
    A n f x j = (explicitBeta x (j+n):ℂ) * f x j
  finite_atomic : ∀ F : Finset ℤ, AtomicAlgebra (strongGenerated (A '' (F : Set ℤ)))
  modulus_pure_point : PurePointResolution (A 0)
  full_multiplication : ∀ T : GlobalHilbert →L[ℂ] GlobalHilbert,
    T ∈ strongGenerated (Set.range A) ↔ IsProductMultiplier T
  abelian : ∀ T ∈ strongGenerated (Set.range A), ∀ R ∈ strongGenerated (Set.range A), T*R=R*T
  diffuse : DiffuseAlgebra (strongGenerated (Set.range A))
  not_contained_in_commutant : ∃ T ∈ strongGenerated (Set.range A), T * D.S ≠ D.S * T


-- @@ L64-66 verbatim
def PolarStructuralProperties (D : DirectModelData) : Prop :=
  ∃ (U : (GlobalHilbert →L[ℂ] GlobalHilbert)ˣ)
    (A : ℤ → GlobalHilbert →L[ℂ] GlobalHilbert), PolarFamilyProperties D U A



-- @@ L69-91 verbatim
lemma coordinateTail_eq_closedSpan (h : ℤ) :
    coordinateTail h = (Submodule.span ℂ
      (Set.range (fun j : {j : ℤ // h ≤ j} => (lp.single 2 j.val (1:ℂ) : Fiber)))).topologicalClosure := by
  let P := Submodule.span ℂ (Set.range (fun j : {j : ℤ // h ≤ j} => (lp.single 2 j.val (1:ℂ) : Fiber)))
  apply le_antisymm
  · intro v hv
    apply (Submodule.isClosed_topologicalClosure P).mem_of_tendsto
      (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ∞) v)
    apply Eventually.of_forall
    intro s
    apply P.topologicalClosure.sum_mem
    intro j _
    by_cases hj : j < h
    · rw [hv j hj,lp.single_zero]
      exact P.topologicalClosure.zero_mem
    · apply Submodule.le_topologicalClosure
      have hg : (lp.single 2 j (1:ℂ) : Fiber) ∈ P :=
        Submodule.subset_span ⟨⟨j,by omega⟩,rfl⟩
      simpa only [←lp.single_smul,smul_eq_mul,mul_one] using P.smul_mem (v j) hg
  · apply Submodule.topologicalClosure_minimal _ ?_ (coordinateTail_isClosed h)
    apply Submodule.span_le.mpr
    rintro v ⟨j,rfl⟩
    exact single_mem_coordinateTail j.property 1


-- @@ L93-101 verbatim
lemma explicitDirectModel_ordinary : OrdinaryStructuralProperties explicitDirectModel where
  tails h := ⟨globalTail h, fun f => mem_globalTail h f,
    globalTail_closed h,globalTail_nonzero h,globalTail_proper h,
    globalTail_forward h,globalTail_not_backward h⟩
  fiber_compact := forwardFiber_compact
  global_not_compact := forwardOperator_not_compact
  multiplier_witness := ⟨sliceProjection 0, sliceProjection_isStarProjection 0,
    sliceProjection_ae 0,sliceProjection_zero_not_commute,
    sliceProjection_scalar_commute 0,sliceProjection_zero_not_scalar⟩


-- @@ L103-119 verbatim
lemma explicitDirectModel_polarFamily : PolarFamilyProperties explicitDirectModel shiftUnit polarDiagonal where
  unitary := coordinateShift_star 1
  unitary_coordinates := coordinateShift_ae 1
  modulus := polar_modulus.symm
  polar := forward_polar_factor
  injective := polarDiagonal_injective
  dense_range := polarDiagonal_denseRange
  conjugates n := by
    rw [shiftUnit_zpow,shiftUnit_zpow]
    exact (polarDiagonal_conjugate n).symm
  diagonal := polarDiagonal_ae
  finite_atomic := finitePolarAlgebra_atomic
  modulus_pure_point := polarDiagonal_purePoint
  full_multiplication := polarAlgebra_mem_iff_productMultiplier
  abelian := fun _ hT _ hR => polarAlgebra_commutative hT hR
  diffuse := polarAlgebra_diffuse
  not_contained_in_commutant := ⟨polarDiagonal 0,polarDiagonal_mem 0,polarDiagonal_not_commute⟩





-- @@ L124-127 verbatim
theorem direct_model_complete : ∃ D : DirectModelData,
    DirectModelProperties D ∧ OrdinaryStructuralProperties D ∧ PolarStructuralProperties D := by
  exact ⟨explicitDirectModel,explicitDirectModel_properties,
    explicitDirectModel_ordinary,shiftUnit,polarDiagonal,explicitDirectModel_polarFamily⟩



-- @@ L130-130 verbatim
end

-- @@ L131-131 verbatim
end BackwardIntertwiners


-- @@ L133-133 verbatim
end OAI
