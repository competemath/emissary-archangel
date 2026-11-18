import OAI.NumberTheory.DirichletL.Eisenstein.FixedThetaTwists


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open MulChar AddChar

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open MeasureTheory Real

-- @@ L13-13 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L14-14 verbatim
open Finset Complex

-- @@ L15-15 verbatim
open scoped Classical

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open Filter Real Asymptotics

-- @@ L18-18 verbatim
open ActualEisensteinCubic

-- @@ L19-19 verbatim
open Filter

-- @@ L20-20 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L21-21 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L22-22 verbatim
open Filter

-- @@ L23-23 verbatim
open scoped Topology

-- @@ L24-24 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L25-25 verbatim
open MulChar AddChar

-- @@ L26-26 verbatim
open Filter Asymptotics

-- @@ L27-27 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L28-28 verbatim
open Filter

-- @@ L29-29 verbatim
open MulChar AddChar

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L32-32 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L33-33 verbatim
open scoped Topology

-- @@ L34-34 verbatim
open Filter Asymptotics

-- @@ L35-35 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Filter Asymptotics

-- @@ L41-41 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L42-42 verbatim
open scoped Topology

-- @@ L43-43 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L44-44 verbatim
open Filter

-- @@ L45-45 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L46-46 verbatim
open scoped Topology

-- @@ L47-47 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L48-48 verbatim
open scoped Topology

-- @@ L49-49 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L50-50 verbatim
open scoped Topology

-- @@ L51-51 verbatim
open MeasureTheory Real

-- @@ L52-52 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L53-53 verbatim
open scoped BigOperators Classical

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical

-- @@ L61-61 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open MeasureTheory Set

-- @@ L67-67 verbatim
open scoped BigOperators

-- @@ L68-68 verbatim
open scoped BigOperators Classical

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L71-71 verbatim
open scoped BigOperators

-- @@ L72-72 verbatim
open scoped BigOperators

-- @@ L73-73 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L74-74 verbatim
open scoped BigOperators Classical


-- @@ L76-76 verbatim
open scoped Classical BigOperators ContDiff


-- @@ L78-78 verbatim
namespace CompletedGauss.FreeReflection

-- @@ L79-79 verbatim
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve

-- @@ L80-80 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L82-83 verbatim
abbrev FixedBranchIndex (c:Eis) (hc:c≠0) (I Q Q0:Ideal Eis) :=
  FixedReflectionRay c hc×(pool I Q Q0→Fin 6)


-- @@ L85-101 verbatim
def fixedRayFiber (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount c hc) (fixedCuspLevelBound c) K I F Q := by
  let R:SixReflectionIndex (fixedReflectionRayCount c hc) I Q Q0→FixedReflectionRay c hc:=
    fun x=>(fixedReflectionRayEquiv c hc).symm x.1
  let G:=fun x=>fixedFourierGeometry c hc (R x).1
  exact sixPhaseFixedCuspFiber (fixedReflectionRayCount c hc) I F Q Q0 hI hQ K
    (fixedCuspLevelBound c) (fun x=>(G x).levelScale)
    (fun x=>(G x).levelScale_pos) (fun x=>(G x).levelScale_le hc)
    (fun x=>(G x).shape.index) (fun x=>(R x).2.2)
    (fun x=>(G x).staticPhase (R x).2.1 (R x).2.2)
    (fun x=>(G x).staticPhase_norm_le_one (R x).2.1 (R x).2.2)
    (fun x=>rayWeight (R x,x.2)) (fun x=>hray (R x,x.2))
    (fun x=>rowPhase (R x,x.2)) (fun x=>hrow (R x,x.2))


-- @@ L103-108 verbatim
lemma fixedRayFiber_pool (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) :
    (fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).pool=pool I Q Q0 := rfl


-- @@ L110-144 verbatim
theorem fixedRayFiber_value (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑r:FixedReflectionRay c hc,∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*rayWeight (r,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (fixedReflectionRayEquiv c hc r,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  calc
    _=∑r:FixedReflectionRay c hc,∑e:pool I Q Q0→Fin 6,
        reflectionSixInactiveWeight I F Q Q0 e*
          (rayWeight (r,e)*((fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).branch
            (fixedReflectionRayEquiv c hc r,e)).value W X ρ q k) := by
      apply Fintype.sum_equiv (fixedReflectionRayEquiv c hc).symm
      intro t
      apply Finset.sum_congr rfl
      intro e he
      simp only [Equiv.apply_symm_apply]
      change (rayWeight ((fixedReflectionRayEquiv c hc).symm t,e)*
        reflectionSixInactiveWeight I F Q Q0 e)*_= _
      ring
    _=_:=by
      apply Finset.sum_congr rfl
      intro r hr
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro e he
      exact (mul_assoc _ _ _).symm


-- @@ L146-146 verbatim
end CompletedGauss.FreeReflection


-- @@ L148-148 verbatim
open scoped BigOperators Classical


-- @@ L150-150 verbatim
namespace CompletedGauss


-- @@ L152-152 verbatim
section

-- @@ L153-153 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets

-- @@ L154-154 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L156-157 verbatim
def residualArgumentPhase (K:Ideal Eis) (z:Eis) (D E:Ideal Eis) : ℂ :=
  quadraticRow K (z*primaryGenerator (D*E))


-- @@ L159-160 verbatim
lemma residualArgumentPhase_norm_le_one (K:Ideal Eis) (z:Eis) (D E:Ideal Eis) :
    ‖residualArgumentPhase K z D E‖≤1 := quadraticRow_norm_le_one _ _


-- @@ L162-178 verbatim
theorem residual_bracket_extracted_argument (I F Q:Ideal Eis) (hFQ:F∣Q)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (z:Eis) (D E n b:Ideal Eis) :
    (∏P:PrimeIndex (rowResidualPart I Q),
      bracket (actualSextic P.val
        (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) P))
        (completedLocalExponent I F P.val)
        (Ideal.Quotient.mk P.val
          (z*primaryGenerator (D*n)*(primaryGenerator (E*b))^3)))=
      residualArgumentPhase (rowResidualPart I Q) z D E *
        quadraticRow (rowResidualPart I Q) (primaryGenerator (n*b)) := by
  simp_rw [completedLocalExponent_residual I F Q hFQ]
  rw [residual_bracket_product]
  rw [←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad),
    ←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad)]
  simp only [primaryGenerator_mul,residualArgumentPhase,
    canonical_quadraticRow_argument_mul _ (rowResidualPart_admissible I Q hbad)]
  ring


-- @@ L180-182 verbatim
def residualArgumentRowPhase {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (residualArgument:ℕ→Eis) (D E:Ideal Eis) (m:ℕ) (k:idealRange K) : ℂ :=
  rowPhase m k*residualArgumentPhase k.val (residualArgument m) D E


-- @@ L184-190 verbatim
lemma residualArgumentRowPhase_norm_le_one {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (hphase:∀m k,‖rowPhase m k‖≤1) (residualArgument:ℕ→Eis)
    (D E:Ideal Eis) (m:ℕ) (k:idealRange K) :
    ‖residualArgumentRowPhase rowPhase residualArgument D E m k‖≤1 := by
  rw [residualArgumentRowPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m k)).trans (residualArgumentPhase_norm_le_one k.val _ D E)


-- @@ L192-215 verbatim
theorem residual_coefficient_eq_canonical_argument {ι:Type*} [Fintype ι]
    (I F Q:Ideal Eis) (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (residualArgument:ℕ→Eis)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (rowPhase:ℕ→ℂ) (m:ℕ) (n b:Ideal Eis) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    (rowPhase m*(∏p:PrimeIndex (rowResidualPart I Q),
        bracket (actualSextic p.val (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) p))
          (completedLocalExponent I F p.val)
          (Ideal.Quotient.mk p.val (residualArgument m*primaryGenerator (D*n)*(primaryGenerator (E*b))^3))) *
      η m (D*n) (E*b)*reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*b)))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*b):ℝ):ℝ):ℂ)=
      4*canonicalRawBranchCoefficient P hg j e ρ q
        (fun l a c=>η l (D*a) (E*c))
        (fun l=>rowPhase l*residualArgumentPhase (rowResidualPart I Q) (residualArgument l) D E)
        (rowResidualPart I Q) m n b := by
  dsimp only
  rw [residual_bracket_extracted_argument I F Q hFQ hbad]
  unfold canonicalRawBranchCoefficient reflectedDyadicCoefficient
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring


-- @@ L217-217 verbatim
end


-- @@ L219-219 verbatim
section

-- @@ L220-220 verbatim
open ActualEisensteinCubic CubicEisenstein LocalReflectionBrackets

-- @@ L221-221 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L223-236 verbatim
lemma reflectedBranch_local_support {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (n b:Eis) (hne:reflectedBranch P hg j e n b≠0) :
    (∀i,j i=4 → e i=1 → n∈P i) ∧
    (∀i,j i=4 → e i=2 → n∉P i ∧ b∈P i) := by
  have hi (i:ι):reflectedLocalPiece (P i) (hg i) (j i) (e i) n b≠0:=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  constructor
  · intro i hj he
    by_contra hn
    exact hi i (by simp [reflectedLocalPiece,hj,exceptionalPiece,he,hn])
  · intro i hj he
    by_contra hn
    exact hi i (by simp [reflectedLocalPiece,hj,exceptionalPiece,he,hn])


-- @@ L238-263 verbatim
lemma reflectionExtractedDivisor_dvd_of_local {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (v:Fin 3) (A:Ideal Eis)
    (hA:∀i,(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) → P i∣A) :
    reflectionExtractedDivisor P j e v∣A := by
  unfold reflectionExtractedDivisor
  apply Fintype.prod_dvd_of_coprime
  · intro i k hik
    change IsCoprime (reflectionExtractedPrime (P i) (j i) (e i) v)
      (reflectionExtractedPrime (P k) (j k) (e k) v)
    unfold reflectionExtractedPrime
    by_cases hi:(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0)
    · rw [ite_eq_left hi]
      by_cases hk:(j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0)
      · rw [ite_eq_left hk]
        exact hcop hik
      · rw [ite_eq_right hk]
        exact isCoprime_one_right
    · rw [ite_eq_right hi]
      exact isCoprime_one_left
  · intro i
    unfold reflectionExtractedPrime
    split_ifs with hi
    · exact hA i hi
    · exact one_dvd _


-- @@ L265-280 verbatim
theorem reflectedBranch_extracted_divisibility {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (n b:Eis) (hne:reflectedBranch P hg j e n b≠0) :
    reflectionExtractedDivisor P j e 1∣Ideal.span {n} ∧
    reflectionExtractedDivisor P j e 2∣Ideal.span {b} ∧
    (∀i,j i=4 → e i=2 → n∉P i) := by
  have hs:=reflectedBranch_local_support P hg j e n b hne
  refine ⟨reflectionExtractedDivisor_dvd_of_local P hcop j e 1 _ ?_,
    reflectionExtractedDivisor_dvd_of_local P hcop j e 2 _ ?_,fun i hj he=>(hs.2 i hj he).1⟩
  · intro i hi
    have h:j i=4 ∧ e i=1:=by simpa using hi
    exact Ideal.dvd_span_singleton.mpr (hs.1 i h.1 h.2)
  · intro i hi
    have h:j i=4 ∧ e i=2:=by simpa using hi
    exact Ideal.dvd_span_singleton.mpr (hs.2 i h.1 h.2).2


-- @@ L282-287 verbatim
def fixedCuspBranchNumerator {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase cusp u phaseArray m n b *
    reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)


-- @@ L289-305 verbatim
theorem fixedCuspBranchNumerator_support {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (hne:fixedCuspBranchNumerator P hg j e cusp u phaseArray m n b≠0) :
    reflectionExtractedDivisor P j e 1∣n ∧ reflectionExtractedDivisor P j e 2∣b ∧
    (∀i,j i=4 → e i=2 → primaryGenerator n∉P i) := by
  have hn:(fixedCuspArrayWithPhase cusp u phaseArray m n b)≠0:=
    (mul_ne_zero_iff.mp hne).1
  have he:fixedCuspArrayEligible n b:=by
    by_contra he
    exact hn (fixedCuspArrayWithPhase_zero cusp u phaseArray m n b he)
  have hb:reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)≠0:=
    (mul_ne_zero_iff.mp hne).2
  have hs:=reflectedBranch_extracted_divisibility P hg hcop j e _ _ hb
  rwa [(primaryGenerator_spec n he.2.1).1,(primaryGenerator_spec b he.2.2).1] at hs


-- @@ L307-307 verbatim
end


-- @@ L309-309 verbatim
open ActualEisensteinCubic CubicEisenstein

-- @@ L310-310 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L312-315 verbatim
def nonzeroDualDilation (D E:Ideal Eis) (hD:D≠0) (hE:E≠0)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℕ×NonzeroDualIdeal×NonzeroDualIdeal :=
  (x.1,⟨D*x.2.1.val,mul_ne_zero hD x.2.1.property⟩,
    ⟨E*x.2.2.val,mul_ne_zero hE x.2.2.property⟩)


-- @@ L317-327 verbatim
lemma nonzeroDualDilation_injective (D E:Ideal Eis) (hD:D≠0) (hE:E≠0) :
    Function.Injective (nonzeroDualDilation D E hD hE) := by
  intro x y h
  apply Prod.ext
  · have ht:=congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.1) h
    exact ht
  · apply Prod.ext
    · apply Subtype.ext
      exact mul_left_cancel₀ hD (congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.2.1.val) h)
    · apply Subtype.ext
      exact mul_left_cancel₀ hE (congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.2.2.val) h)


-- @@ L329-360 verbatim
theorem tsum_nonzeroDualDilation (D E:Ideal Eis) (hD:D≠0) (hE:E≠0)
    (f:(ℕ×NonzeroDualIdeal×NonzeroDualIdeal)→ℂ)
    (hsupport:∀x,f x≠0 → D∣x.2.1.val ∧ E∣x.2.2.val) :
    (∑'x,f x)=∑'x,f (nonzeroDualDilation D E hD hE x) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun x:Function.support (fun y=>f (nonzeroDualDilation D E hD hE y))=>
      nonzeroDualDilation D E hD hE x.val)
  · exact (nonzeroDualDilation_injective D E hD hE).comp Subtype.val_injective
  · intro x hx
    obtain ⟨hn,hb⟩:=hsupport x hx
    obtain ⟨n,hn⟩:=hn
    obtain ⟨b,hb⟩:=hb
    have hn0:n≠0:=by
      intro hz
      apply x.2.1.property
      rw [hn,hz,mul_zero]
    have hb0:b≠0:=by
      intro hz
      apply x.2.2.property
      rw [hb,hz,mul_zero]
    let y:ℕ×NonzeroDualIdeal×NonzeroDualIdeal:=(x.1,⟨n,hn0⟩,⟨b,hb0⟩)
    have hy:nonzeroDualDilation D E hD hE y=x:=by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact Subtype.ext hn.symm
        · exact Subtype.ext hb.symm
    refine ⟨⟨y,?_⟩,hy⟩
    change f (nonzeroDualDilation D E hD hE y)≠0
    rwa [hy]
  · intro x
    rfl


-- @@ L362-383 verbatim
theorem fixedCuspBranch_tsum_extract {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ)
    (kernel:(ℕ×NonzeroDualIdeal×NonzeroDualIdeal)→ℂ) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    let hD:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 1
    let hE:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      fixedCuspBranchNumerator P hg j e cusp u phaseArray x.1 x.2.1.val x.2.2.val*kernel x)=
    ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      fixedCuspBranchNumerator P hg j e cusp u phaseArray x.1 (D*x.2.1.val) (E*x.2.2.val)*
        kernel (nonzeroDualDilation D E hD hE x) := by
  dsimp only
  apply tsum_nonzeroDualDilation
  intro x hx
  have hcoeff:fixedCuspBranchNumerator P hg j e cusp u phaseArray x.1 x.2.1.val x.2.2.val≠0:=
    (mul_ne_zero_iff.mp hx).1
  have hs:=fixedCuspBranchNumerator_support P hg hcop j e cusp u phaseArray x.1 x.2.1.val x.2.2.val hcoeff
  exact ⟨hs.1,hs.2.1⟩


-- @@ L385-385 verbatim
end CompletedGauss


-- @@ L387-387 verbatim
open scoped BigOperators Classical MatrixGroups


-- @@ L389-389 verbatim
namespace CubicEisenstein


-- @@ L391-391 verbatim
section

-- @@ L392-392 verbatim
open ActualEisensteinCubic CompletedGauss CubicKubota CubicJacobiGlobal ConcreteTraceCRT

-- @@ L393-393 verbatim
open LocalReflectionBrackets

-- @@ L394-394 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L396-407 verbatim
lemma fixedConjugateCuspArray_nonzero (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedConjugateCuspArray j u m I J≠0) :
    fixedCuspArrayEligible I J ∧
      (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0 := by
  have helig:fixedCuspArrayEligible I J:=by
    by_contra he
    apply h
    simp only [fixedConjugateCuspArray,fixedCuspArray,ite_eq_right he,star_zero]
  refine ⟨helig,?_⟩
  intro hz
  apply h
  simp only [fixedConjugateCuspArray,fixedCuspArray,ite_eq_left helig,hz,zero_div,star_zero]


-- @@ L409-425 verbatim
lemma fixedCusp_ramified_index_pos (j:Fin 3) (hj:j≠0) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) : 0<m := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hp:lambda∣ramifiedTraceLambda:=by
    change lambda∣paperLambda
    rw [paperLambda_eq]
    exact dvd_mul_left lambda _
  have hd:=hp.trans (sourceCuspCoefficients_ramified_divisibility j hj _ h)
  simp only [fixedCuspArrayIndex,hm,pow_zero,mul_one] at hd
  have hu:IsCoprime lambda (u:Eis):=⟨0,(↑u⁻¹:Eis),by simp⟩
  have hni:IsCoprime lambda (primaryGenerator I):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec I helig.2.1).2)
  have hnj:IsCoprime lambda (primaryGenerator J):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec J helig.2.2).2)
  exact residue_lambda_prime.not_isUnit (((hu.mul_right hni).mul_right hnj.pow_right).isUnit_of_dvd hd)


-- @@ L427-428 verbatim
def sourcePhaseUnit (j:Fin 3) (w u:Eisˣ) : Eisˣ :=
  if j=0 then paperLambdaUnit*w^2*u else -(w^2*u*paperLambdaUnit⁻¹)


-- @@ L430-431 verbatim
def sourcePhaseExponent (j:Fin 3) (m:ℕ) : ℕ :=
  if j=0 then m+1 else m-1


-- @@ L433-451 verbatim
lemma paperLambdaQuotient_succ (u:Eisˣ) (m:ℕ) (n b:Eis) :
    paperLambdaQuotient ((u.val*lambda^(m+1))*n*b^3)=
      (paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3 := by
  have hp:ramifiedTraceLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=
      (u.val*lambda^(m+1))*n*b^3 := by
    change paperLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=_
    rw [paperLambda_eq,pow_succ]
    have hi:(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1:=by simp
    calc
      _=((paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ))*(u.val*lambda^m*lambda*n*b^3):=by ring
      _=_:=by rw [hi,one_mul];ring
  have hd:ramifiedTraceLambda∣(u.val*lambda^(m+1))*n*b^3:=⟨_,hp.symm⟩
  have hn:ramifiedTraceLambda≠0:=by
    intro hz
    have he:=ramifiedEmbedding_traceLambda
    rw [hz,map_zero] at he
    exact eisLam_ne_zero he.symm
  apply mul_left_cancel₀ hn
  rw [paperLambdaQuotient_mul _ hd,hp]


-- @@ L453-474 verbatim
theorem sourceCuspPhaseNumerator_columns (j:Fin 3) (w u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) :
    sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J)=
      ((sourcePhaseUnit j w u).val*lambda^(sourcePhaseExponent j m))*
        (primaryGenerator I*(primaryGenerator J)^3) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,ite_true,
      fixedCuspArrayIndex,Units.val_mul,Units.val_pow_eq_pow_val]
    change paperLambda*w.val^2*((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)=_
    rw [paperLambda_eq,pow_succ]
    ring
  · have hm:=fixedCusp_ramified_index_pos j hj u m I J helig h
    cases m with
    | zero => omega
    | succ m =>
      simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,ite_eq_right hj,
        fixedCuspArrayIndex,Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Units.val_neg,Units.val_mul,
        Units.val_pow_eq_pow_val]
      rw [paperLambdaQuotient_succ]
      ring


-- @@ L476-490 verbatim
theorem fixedCuspArray_phase_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (exponent:ι→ℕ)
    (j:Fin 3) (w u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    fixedConjugateCuspArray j u m I J*
      (∏i,bracket (actualSextic (P i) (hg i)) (exponent i)
        (Ideal.Quotient.mk (P i) (sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J))))=
    fixedConjugateCuspArray j u m I J*
      ramifiedBranchPhase P hg exponent (sourcePhaseUnit j w u) (sourcePhaseExponent j m)*
      ∑e:ι→Fin 3,reflectedBranch P hg exponent e (primaryGenerator I) (primaryGenerator J) := by
  by_cases hz:fixedConjugateCuspArray j u m I J=0
  · rw [hz,zero_mul,zero_mul,zero_mul]
  · obtain ⟨he,hh⟩:=fixedConjugateCuspArray_nonzero j u m I J hz
    rw [sourceCuspPhaseNumerator_columns j w u m I J he hh,
      ramified_bracket_full_expansion]
    ring


-- @@ L492-492 verbatim
end


-- @@ L494-494 verbatim
open ActualEisensteinCubic CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal ConcreteTraceCRT

-- @@ L495-495 verbatim
open LocalReflectionBrackets ShortDraftCusp

-- @@ L496-496 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L498-498 verbatim
namespace FixedCuspShape

-- @@ L499-499 verbatim
variable {H:SL(2,Eis)} (s:FixedCuspShape H)


-- @@ L501-501 verbatim
def phaseUpperUnit : Eisˣ := s.upper_unit.unit


-- @@ L503-503 verbatim
lemma phaseUpperUnit_val : (s.phaseUpperUnit:Eis)=s.upper 0 0 := s.upper_unit.unit_spec


-- @@ L505-506 verbatim
def modelDualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator s.index (s.upper 0 0) (fixedCuspArrayIndex u m I J)


-- @@ L508-541 verbatim
theorem model_array_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (c0:Eis) (hc0:c0≠0) (d U:Eis) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    (s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J))*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=
    ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
      (sourcePhaseExponent s.index m)*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u) m I J*
        reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J) := by
  let φ:=s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u
  have hA:φ m I J*fixedConjugateCuspArray s.index u m I J=
      s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J) := by
    rw [A4BadPhase_as_fixed_residue]
    exact s.fixedCuspArrayWithPhase_reflectionStaticPhase c0 hc0 _ _ u m I J
  have hbr:=fixedCuspArray_phase_brackets P hg j s.index s.phaseUpperUnit u m I J
  rw [s.phaseUpperUnit_val] at hbr
  change fixedConjugateCuspArray s.index u m I J*
    (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=_ at hbr
  rw [←hA]
  calc
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))) := by ring
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
        (sourcePhaseExponent s.index m)*
        ∑e:ι→Fin 3,reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J)) := by rw [hbr]
    _=_ := by
      simp only [fixedCuspArrayWithPhase]
      rw [←Finset.mul_sum]
      dsimp only [φ]
      ring


-- @@ L543-543 verbatim
end FixedCuspShape


-- @@ L545-545 verbatim
namespace ControlledStratumArithmetic

-- @@ L546-546 verbatim
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

-- @@ L547-548 verbatim
noncomputable local instance coefficientField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P

-- @@ L549-550 verbatim
noncomputable local instance coefficientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _


-- @@ L552-556 verbatim
def activePhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) : ℂ :=
  ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)


-- @@ L558-569 verbatim
lemma activePhase_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6) :
    ‖D.activePhase hp hg j‖=1 := by
  rw [activePhase,norm_prod]
  have he (i:ι):‖(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)‖=1 := by
    rw [norm_mul,FiniteRayExpansion.norm_char_unit,one_mul]
    exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (quotientTrace (p i) (hp i))
      (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) (j i) (hj i) (D.epsilon i)
  simp only [he,Finset.prod_const_one]


-- @@ L571-576 verbatim
lemma bracketProduct_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) :
    D.bracketProduct hp hg j x=D.activePhase hp hg j*
      ∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  exact Finset.prod_mul_distrib


-- @@ L578-584 verbatim
def modelRowPhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (u:Eisˣ) (m:ℕ) : ℂ :=
  star D.fixedFactor*D.activePhase hp hg j*
    ramifiedBranchPhase (fun i=>Ideal.span {p i}) hg j
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)


-- @@ L586-595 verbatim
theorem modelRowPhase_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (u:Eisˣ) (m:ℕ) : ‖D.modelRowPhase s hp hg j u m‖=1 := by
  rw [modelRowPhase,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN hr hbase,
    D.activePhase_norm hp hg hchar j hj,ramifiedBranchPhase_norm,one_mul,one_mul]


-- @@ L597-619 verbatim
theorem model_coefficient (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    s.amplitude u m I J*
      (star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
      D.bracketProduct hp hg j (s.modelDualNumerator u m I J)=
    D.modelRowPhase s hp hg j u m*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
            (s.modelDualNumerator u) u) m I J*
        reflectedBranch (fun i=>Ideal.span {p i}) hg j e (primaryGenerator I) (primaryGenerator J) := by
  rw [D.bracketProduct_eq]
  have he:=s.model_array_brackets (fun i=>Ideal.span {p i}) hg j c0 hc0
    (D.matrix (fun _=>1) 1 1) D.U u m I J
  calc
    _=(star D.fixedFactor*D.activePhase hp hg j)*
      ((s.amplitude u m I J*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
        (∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (s.modelDualNumerator u m I J)))) := by ring
    _=_ := by rw [he];dsimp only [modelRowPhase];ring


-- @@ L621-621 verbatim
end ControlledStratumArithmetic


-- @@ L623-627 verbatim
lemma fixed_stratum_kernel_scale (j:Fin 3) (c0 r:Eis) :
    27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0*r}):ℝ)^2=
      fixedCuspLevelScale j c0*(Ideal.absNorm (Ideal.span {r}):ℝ)^2 := by
  rw [←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,mul_pow,fixedCuspLevelScale]
  ring


-- @@ L629-629 verbatim
end CubicEisenstein


-- @@ L631-631 verbatim
end


-- @@ L633-633 verbatim
end OAI
