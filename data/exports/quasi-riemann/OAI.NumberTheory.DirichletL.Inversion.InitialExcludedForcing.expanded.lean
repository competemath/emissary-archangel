import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedOverlap


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge

-- @@ L9-9 verbatim
open FirstCauchyArithmetic SecondPassArithmetic UniqueFactorizationMonoid

-- @@ L10-10 verbatim
namespace SevenEighths.InverseInitialExcludedForcing

-- @@ L11-11 verbatim
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge

-- @@ L12-12 verbatim
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool

-- @@ L13-13 verbatim
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialLargePool

-- @@ L14-14 verbatim
open InverseInitialExcludedPool InverseInitialExcludedOverlap

-- @@ L15-15 verbatim
open InverseInitialCommonTuples InverseInitialCommonTransform

-- @@ L16-16 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L18-24 verbatim
theorem pool_product_outside (F E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (hF:∀I∈F,outside E I)(A:Finset (primePool F)):
    outside E (∏i∈A,i.val) := by
  intro Q hQ hd
  obtain ⟨i,hi,hQi⟩:=((hE Q hQ).dvd_finsetProd_iff (fun i:primePool F=>i.val)).mp hd
  obtain ⟨I,hIF,hfactor⟩:=mem_primePool_iff.mp i.property
  exact hF I hIF Q hQ (hQi.trans (dvd_of_mem_normalizedFactors hfactor))


-- @@ L26-69 verbatim
theorem residual_excluded_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    {P j:Ideal O}(hP:Admissible P)(hj:j∣P)(hPE:outside E P)
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:columns (originalOutside (originalSource Z r b) E) P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(u:O):
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_filtered _ E hE hP.2.1 hj hPE η hη,
    residual_eq_large_input _ F hP hj hF hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:=common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j):=by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  have hmem:((∏i∈A,i.val)∈columns (originalOutside (originalSource Z r b) E) P j)↔
      ((∏i∈A,i.val)∈columns (originalSource Z r b) P j):=by
    rw [columns_filter _ E hE hP.2.1 hj hPE,Finset.mem_filter]
    exact and_iff_left (pool_product_outside F E hE hFE A)
  dsimp only
  simp only [hm,hmem]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he


-- @@ L71-71 verbatim
variable {κ:Type*}

-- @@ L72-100 verbatim
theorem original_tuples_excluded_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:tupleColumns (originalOutside (originalSource Z r b) E) T P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(a:κ→ℂ)(u:O) :
    let S := originalSource Z r b
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [input_finset_sum (poolPrimary F) (poolPrimary_good F hF)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_excluded_forcing W Z r z G b hZ hW E hE (hP k hk) (hj k hk) (hPE k hk) F hF hFE
    (fun c hc=>hsub (Finset.mem_biUnion.mpr ⟨k,hk,hc⟩)) η hη u]
  ring


-- @@ L102-102 verbatim
end SevenEighths.InverseInitialExcludedForcing


-- @@ L104-104 verbatim
end


-- @@ L106-106 verbatim
end OAI
