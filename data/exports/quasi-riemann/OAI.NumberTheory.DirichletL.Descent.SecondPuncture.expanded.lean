import OAI.NumberTheory.DirichletL.Descent.SecondSquarefree


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseMoment

-- @@ L6-6 verbatim
open scoped BigOperators Classical

-- @@ L7-7 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss

-- @@ L8-8 verbatim
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-14 verbatim
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})


-- @@ L16-26 verbatim
omit [DecidableEq ι] in
theorem rowCoprimeMask_radical_generator (S : Finset ι) (a : Eis) :
    rowCoprimeMask (fun i => Ideal.span {p i}) S a =
      rowCoprimeMask (fun i => Ideal.span {p i}) S
        (ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical) := by
  have he (i : ι) : a ∈ Ideal.span {p i} ↔
      ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical ∈ Ideal.span {p i} := by
    rw [←Ideal.span_singleton_le_iff_mem,←Ideal.span_singleton_le_iff_mem,
      ConcretePrimeRowBridge.span_idealGenerator]
    exact (inferInstance : (Ideal.span {p i}).IsPrime).radical_le_iff.symm
  simp only [rowCoprimeMask,he]


-- @@ L28-36 verbatim
omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_radical_puncture (F : Finset ι) (Ψ : Eis →* ℂ)
    (m f k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ
        (ConcretePrimeRowBridge.idealGenerator (Ideal.span {m}).radical) f k slots lists a W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn,
    ←rowCoprimeMask_radical_generator p]


-- @@ L38-53 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_le_radical_primeProduct (B : Finset ι) (v : ι → ℕ) :
    sourceIdeal p B ≤ (Ideal.span {primeProduct p B v} : Ideal Eis).radical := by
  simp only [sourceIdeal,primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
  induction B using Finset.induction_on with
  | empty => simp
  | @insert i B hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Ideal.radical_mul]
    apply le_inf
    · apply Ideal.mul_le_left.trans
      by_cases hv : v i = 0
      · rw [hv,pow_zero,Ideal.one_eq_top]
        exact le_trans le_top Ideal.le_radical
      · rw [Ideal.radical_pow _ hv]
        exact Ideal.le_radical
    · exact Ideal.mul_le_right.trans ih


-- @@ L55-69 verbatim
theorem actual_second_q0_radical_norm (hp : ∀ i, p i ≠ 0)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0.radical : ℝ) ≤
      primeProductNorm p x.cube.support := by
  have hd := Ideal.absNorm_dvd_absNorm_of_le (sourceIdeal_le_radical_primeProduct p x.cube.support
    (fun i => b0Exponent (x.cube.leftExponent i+x.cube.rightExponent i) (x.cube.leftBit i) (x.cube.rightBit i)))
  have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (sourceIdeal_ne_zero p hp x.cube.support))) hd
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}).radical : ℝ) ≤ _
  have he : (Ideal.absNorm (sourceIdeal p x.cube.support) : ℝ) = primeProductNorm p x.cube.support := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ x.cube.support,p i)).symm
  rw [←he]
  exact_mod_cast hb


-- @@ L71-72 verbatim
def actualSecondRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  ConcretePrimeRowBridge.idealGenerator (Ideal.span {actualSecondPuncture m γ}).radical


-- @@ L74-80 verbatim
theorem secondCanonicalPolynomial_radical_puncture
    (F : Finset ι) (Ψ : InverseSecondFibers.OuterTriple → Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : InverseSecondFibers.OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) :
    secondCanonicalPolynomial p hp hcop hg F Ψ (actualSecondPuncture m) slots lists a W X c =
      secondCanonicalPolynomial p hp hcop hg F Ψ (actualSecondRadicalPuncture m) slots lists a W X c :=
  finiteCanonicalMarkedRow_radical_puncture p hp hcop hg F (Ψ c.1) _ _ _ slots lists a (W c.1) X


-- @@ L82-99 verbatim
theorem radical_product_norm_le (I J B R : Ideal Eis) (hI : I ≠ 0) (hB : B ≠ 0)
    (hR : R ≠ 0) (hBJ : B ≤ J.radical) :
    (Ideal.absNorm (I*J*R).radical : ℝ) ≤
      (Ideal.absNorm I.radical : ℝ)*Ideal.absNorm B*Ideal.absNorm R := by
  have hi : I.radical ≠ 0 := by
    intro he
    apply hI
    exact le_antisymm (he ▸ Ideal.le_radical) bot_le
  have hle : I.radical*B*R ≤ (I*J*R).radical := by
    rw [Ideal.radical_mul,Ideal.radical_mul]
    refine le_inf (le_inf ?_ ?_) ?_
    · exact Ideal.mul_le_left.trans Ideal.mul_le_left
    · exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans hBJ
    · exact Ideal.mul_le_right.trans Ideal.le_radical
  have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (mul_ne_zero (mul_ne_zero hi hB) hR))) (Ideal.absNorm_dvd_absNorm_of_le hle)
  simpa only [map_mul,Nat.cast_mul] using (show (Ideal.absNorm (I*J*R).radical : ℝ) ≤
    Ideal.absNorm (I.radical*B*R) from by exact_mod_cast hb)


-- @@ L101-125 verbatim
include hp in

theorem actual_second_radical_puncture_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) *
        primeProductNorm p x.cube.support * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hspan : Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} =
      (Ideal.span {m} : Ideal Eis) *
      Ideal.span {b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit} * sourceIdeal p (x.second.sourceCommon\x.second.divisor) := by
    rw [←actual_second_puncture_span p hp hpr x hE u v m]
    simp only [←Ideal.span_singleton_mul_span_singleton,secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [actualSecondRadicalPuncture,ConcretePrimeRowBridge.span_idealGenerator,hspan]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ)=primeProductNorm p S := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ S,p i)).symm
  rw [←hn x.cube.support,←hn (x.second.sourceCommon\x.second.divisor)]
  exact radical_product_norm_le _ _ _ _ (Ideal.span_singleton_eq_bot.not.mpr hm)
    (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    (sourceIdeal_le_radical_primeProduct p _ _)


-- @@ L127-128 verbatim
def actualSecondInheritedPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondPuncture (m*ConcretePrimeRowBridge.idealGenerator γ.quotient) γ


-- @@ L130-131 verbatim
def actualSecondInheritedRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondRadicalPuncture (m*ConcretePrimeRowBridge.idealGenerator γ.quotient) γ


-- @@ L133-155 verbatim
include hp in

theorem actual_second_inherited_puncture_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) * Ideal.absNorm x.quotient *
        primeProductNorm p x.cube.support * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hm' := mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero x.quotient ht)
  have hb := actual_second_radical_puncture_norm p hp hpr x hE u v
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) hm'
  change ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) (actualSecondChild p u v x).1)‖^2 ≤ _
  apply hb.trans
  have ho : (Ideal.absNorm (Ideal.span {m*ConcretePrimeRowBridge.idealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ)*Ideal.absNorm x.quotient := by
    rw [←Ideal.span_singleton_mul_span_singleton,ConcretePrimeRowBridge.span_idealGenerator]
    simpa only [mul_one,map_one,Nat.cast_one] using radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
      (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ho (primeProductNorm_pos p hp _).le) (primeProductNorm_pos p hp _).le


-- @@ L157-165 verbatim
include hp in

theorem actualSecondTriples_q0_radical_bound
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn)) (B : ℝ)
    (hB : ∀ x ∈ source, primeProductNorm p x.cube.support ≤ B) :
    ∀ γ ∈ actualSecondTriples p u v source, (Ideal.absNorm γ.q0.radical : ℝ) ≤ B := by
  intro γ hγ
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact (actual_second_q0_radical_norm p hp x u v).trans (hB x hx)


-- @@ L167-167 verbatim
end

-- @@ L168-168 verbatim
end SevenEighths.InverseMoment


-- @@ L170-170 verbatim
end OAI
