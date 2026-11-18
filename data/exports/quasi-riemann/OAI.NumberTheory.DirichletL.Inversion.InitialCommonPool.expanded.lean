import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindow


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge

-- @@ L9-9 verbatim
open UniqueFactorizationMonoid SecondPassArithmetic

-- @@ L10-10 verbatim
namespace SevenEighths.InverseInitialCommonPool

-- @@ L11-11 verbatim
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge

-- @@ L12-12 verbatim
open InverseInitialRayAttachment

-- @@ L13-13 verbatim
local notation "Eis"=>ActualEisensteinCubic.O


-- @@ L15-16 verbatim
def commonColumns (S Ps : Finset (Ideal Eis)) (j : Ideal Eis) : Finset (Ideal Eis) :=
  Ps.biUnion (fun P=>columns S P j)


-- @@ L18-21 verbatim
theorem columns_subset (S Ps : Finset (Ideal Eis)) (j : Ideal Eis)
    {P : Ideal Eis} (hP : P∈Ps) : columns S P j⊆commonColumns S Ps j := by
  intro c hc
  exact Finset.mem_biUnion.mpr ⟨P,hP,hc⟩


-- @@ L23-29 verbatim
theorem common_admissible (S Ps : Finset (Ideal Eis)) (j : Ideal Eis)
    (hPs : ∀P∈Ps,Admissible P) (hj : ∀P∈Ps,j∣P)
    (hS : ∀n∈S,Squarefree n→Supported n) :
    ∀c∈commonColumns S Ps j,Admissible c := by
  intro c hc
  obtain ⟨P,hP,hc⟩ := Finset.mem_biUnion.mp hc
  exact columns_admissible S (hPs P hP) (hj P hP) hS hc


-- @@ L31-36 verbatim
theorem common_coprime (S Ps : Finset (Ideal Eis)) (j : Ideal Eis)
    (hPs : ∀P∈Ps,Admissible P) (hj : ∀P∈Ps,j∣P) :
    ∀c∈commonColumns S Ps j,IsCoprime c j := by
  intro c hc
  obtain ⟨P,hP,hc⟩ := Finset.mem_biUnion.mp hc
  exact ((mem_columns (hPs P hP).2.1 (hj P hP)).mp hc).2.1


-- @@ L38-80 verbatim
theorem residual_eq_common_input
    (S F : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j∣P) (hF : ∀I∈F,Admissible I)
    (hcop : ∀I∈F,IsCoprime I j) (hsub : columns S P j⊆F)
    (η : Ideal Eis→*ℂ) (a : Ideal Eis→ℂ) (W : ℝ→ℂ)
    (Z r z G : ℝ) (u : Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if (∏i∈A,i.val)∈columns S P j then
          a (reconstruct P j (∏i∈A,i.val))*residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let H : Ideal Eis→ℂ := fun c=>if c∈columns S P j then
    a (reconstruct P j c)*residualOverlapWindow P j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G)) else 0
  have hfilter : F.filter (fun c=>c∈columns S P j)=columns S P j := by
    ext c
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h=>hsub h)
  have he : (∑c∈columns S P j,
      overlapResidualCoefficient P j η a W Z r z G c*star (CanonicalRowCompletion.idealRowHom u c))=
      ∑c∈F,(moebius c:ℂ)*η c*H c*star (CanonicalRowCompletion.idealRowHom u c) := by
    conv_rhs => arg 2;ext c;dsimp only [H];simp only [mul_ite,mul_zero,ite_mul,zero_mul]
    rw [←Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro c hc
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  unfold residualNormalizedPolynomial
  rw [he,selected_conjugate_row F hF j (admissible_of_dvd hP hj) hcop η H u]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  congr 1
  funext A
  dsimp [H]
  by_cases hc : (∏i∈A,i.val)∈columns S P j
  · simp only [hc,hsub hc,ite_true]
  · simp only [hc,ite_false,ite_self]


-- @@ L82-82 verbatim
end SevenEighths.InverseInitialCommonPool


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end OAI
