import OAI.NumberTheory.DirichletL.Inversion.InitialCommonPool


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge

-- @@ L9-9 verbatim
open FirstCauchyArithmetic SecondPassArithmetic

-- @@ L10-10 verbatim
namespace SevenEighths.InverseInitialCommonForcing

-- @@ L11-11 verbatim
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge

-- @@ L12-12 verbatim
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool

-- @@ L13-13 verbatim
open InverseInitialEnergyCallerWindow InverseInitialEnergyCallerSelector

-- @@ L14-14 verbatim
local notation "Eis"=>ActualEisensteinCubic.O


-- @@ L16-38 verbatim
theorem common_selector_window
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)(A:Finset (primePool F)) :
    (if (∏i∈A,i.val)∈columns (originalSource Z r b) P j then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) =
    (if residual P j∣(∏i∈A,i.val) then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) := by
  by_cases hm : rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j)=0
  · simp only [hm,mul_zero]
  by_cases hw : residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))=0
  · simp only [hw,ite_self,zero_mul]
  have hA := InitialMeanSquare.poolProduct_admissible F hF A
  have hcop := mask_nonzero_coprime F j (admissible_of_dvd hP hj) A hm
  by_cases hd : residual P j∣(∏i∈A,i.val)
  · have hmem := (mem_columns hP.2.1 hj).mpr ⟨hA.2.1,hcop,hd,
      reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hd hw⟩
    simp only [hd,hmem,ite_true]
  · have hn : (∏i∈A,i.val)∉columns (originalSource Z r b) P j :=
      fun h=>hd ((mem_columns hP.2.1 hj).mp h).2.2.1
    simp only [hd,hn,ite_false]


-- @@ L40-78 verbatim
theorem residual_eq_common_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)
    (hcop:∀I∈F,IsCoprime I j)(hsub:columns (originalSource Z r b) P j⊆F)
    (η:Ideal Eis→*ℂ)(u:Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_eq_common_input _ F hP hj hF hcop hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he := common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm : rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A
        (primaryGenerator j) := by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  dsimp only
  rw [hm]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he


-- @@ L80-80 verbatim
end SevenEighths.InverseInitialCommonForcing


-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
