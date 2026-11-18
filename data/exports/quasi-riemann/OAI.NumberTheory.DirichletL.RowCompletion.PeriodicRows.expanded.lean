import OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts


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
open scoped BigOperators Classical


-- @@ L78-78 verbatim
namespace CanonicalRowCompletion

-- @@ L79-79 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler

-- @@ L80-80 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L82-90 verbatim
lemma numeratorBadTwist_zero_of_not_supported (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (n:Eis) (hn:¬Supported (Ideal.span {n})) :
    numeratorBadTwist u a b r hr n=0 := by
  have hu:unitSupplement u n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [ite_eq_right hn]
  change ((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n=0
  rw [hu,zero_mul,zero_mul,zero_mul]


-- @@ L92-100 verbatim
lemma rowTwist_zero_of_not_supported (Ψ:Eis→*ℂ) (m f z n:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (hn:¬Supported (Ideal.span {n})) :
    rowTwist Ψ m f z n=0 := by
  have hu:unitSupplement (1:Eisˣ) n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [ite_eq_right hn]
  have h:=congrArg (fun T:Eis→*ℂ=>T n) (rowTwist_unitSupplement Ψ m f z (1:Eisˣ) hmLam hm2)
  change rowTwist Ψ m f ((1:Eisˣ).val*z) n=unitSupplement (1:Eisˣ) n*rowTwist Ψ m f z n at h
  simpa only [Units.val_one,one_mul,hu,zero_mul] using h


-- @@ L102-104 verbatim
def actualPeriodicRow (Ψ:Eis→*ℂ) (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) : Eis→*ℂ :=
  Ψ * coprimalityMask m * numeratorBadTwist u a b r hr * movingNumeratorRow r hr


-- @@ L106-115 verbatim
lemma actualPeriodicRow_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) (n:Eis) :
    ‖actualPeriodicRow Ψ m u a b r hr n‖≤1 := by
  change ‖((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n‖≤1
  simp only [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    (hΨ n)).trans (coprimalityMask_norm m n))).trans (numeratorBadTwist_norm u a b r hr n))).trans
    (movingNumeratorRow_norm r hr n)


-- @@ L117-131 verbatim
lemma actualPeriodicRow_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ:x-y∈Q:=Ideal.mul_le_left (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hm:x-y∈Ideal.span {m}:=Ideal.mul_le_right (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have h72:x-y∈Ideal.span {(72:Eis)}:=Ideal.mul_le_right (Ideal.mul_le_left hxy)
  have hrxy:x-y∈Ideal.span {r}:=Ideal.mul_le_right hxy
  change ((Ψ x*coprimalityMask m x)*numeratorBadTwist u a b r hr x)*movingNumeratorRow r hr x=
    ((Ψ y*coprimalityMask m y)*numeratorBadTwist u a b r hr y)*movingNumeratorRow r hr y
  rw [hΨ x y hQ,coprimalityMask_periodic m x y hm,numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_periodic r hr x y hrxy]


-- @@ L133-146 verbatim
theorem rowTwist_eq_actualPeriodicRow_primary (Ψ:Eis→*ℂ) (m f z:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n := by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ m f z n hn,hx,
      idealRowHom_factor_numerator u a b r n hr hpr hn hpn]
    change _=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    ring
  · rw [rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]
    change 0=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    rw [numeratorBadTwist_zero_of_not_supported u a b r hr n hn,mul_zero,zero_mul]


-- @@ L148-166 verbatim
theorem exists_actual_periodic_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hQ:Q≠0) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(u:Eisˣ)(a b:ℕ)(r:Eis)(hr:Supported (Ideal.span {r})),
      lambda^2∣r-1 ∧ f^4*z=u.val*lambda^a*(2:Eis)^b*r ∧
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})≠0 ∧
      CanonicalCoefficientClass.FactorsModulo
        (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
        (actualPeriodicRow Ψ m u a b r hr) ∧
      (∀n,‖actualPeriodicRow Ψ m u a b r hr n‖≤1) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n) := by
  obtain ⟨u,a,b,r,hr,hpr,hx⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  refine ⟨u,a,b,r,hr,hpr,hx,?_,actualPeriodicRow_periodic Ψ Q hΨ m u a b r hr,
    actualPeriodicRow_norm Ψ hΨnorm m u a b r hr,?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hQ (by
      simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hm))
      (by simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot];norm_num)) hr.1
  · exact fun n hpn=>rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx n hpn


-- @@ L168-168 verbatim
end CanonicalRowCompletion


-- @@ L170-170 verbatim
namespace CompletedGauss


-- @@ L172-172 verbatim
section

-- @@ L173-173 verbatim
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid

-- @@ L174-174 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L176-177 verbatim
def completedReflectionPool (I Q:Ideal Eis) : Finset (Ideal Eis) :=
  (primeSupport (I*Q)).filter (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q)


-- @@ L179-184 verbatim
lemma mem_completedReflectionPool (I Q P:Ideal Eis) (hI:I≠0) (hQ:Q≠0) :
    P∈completedReflectionPool I Q ↔
      Prime P ∧ P∣I*Q ∧ lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q := by
  simp only [completedReflectionPool,Finset.mem_filter,primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)]
  aesop


-- @@ L186-191 verbatim
lemma completedReflectionPool_maximal (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    P.val.IsMaximal := by
  have hm: P.val∈normalizedFactors (I*Q):=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp P.property).1
  have hp:=prime_of_normalized_factor P.val hm
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero


-- @@ L193-194 verbatim
lemma completedReflectionPool_good (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    lambda∉P.val := (Finset.mem_filter.mp P.property).2.1


-- @@ L196-197 verbatim
lemma completedReflectionPool_odd (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    ringChar (Eis⧸P.val)≠2 := (Finset.mem_filter.mp P.property).2.2.1


-- @@ L199-200 verbatim
lemma completedReflectionPool_nonresidual (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    ¬P.val∣rowResidualPart I Q := (Finset.mem_filter.mp P.property).2.2.2


-- @@ L202-204 verbatim
lemma completedReflectionPool_divides (I Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (P:completedReflectionPool I Q) : P.val∣I*Q :=
  ((mem_completedReflectionPool I Q P.val hI hQ).mp P.property).2.1


-- @@ L206-210 verbatim
lemma completedReflectionPool_coprime (I Q:Ideal Eis) :
    Pairwise (fun P R:completedReflectionPool I Q=>IsCoprime P.val R.val) := by
  let (P:completedReflectionPool I Q):P.val.IsMaximal:=completedReflectionPool_maximal I Q P
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)


-- @@ L212-225 verbatim
theorem completedReflectionPool_eq_on_fiber (I J Q:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q) :
    completedReflectionPool I Q=completedReflectionPool J Q := by
  ext P
  rw [mem_completedReflectionPool I Q P hI hQ,mem_completedReflectionPool J Q P hJ hQ]
  constructor
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivJ,hresJ,_⟩:=nonresidual_prime_transport I J 1 Q P hI hJ hP hA hT hdiv hres
    exact ⟨hP,hdivJ,hgood,hodd,hresJ⟩
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivI,hresI,_⟩:=nonresidual_prime_transport J I 1 Q P hJ hI hP hA.symm hT.symm hdiv hres
    exact ⟨hP,hdivI,hgood,hodd,hresI⟩


-- @@ L227-235 verbatim
lemma completedReflectionPool_exponent_eq (I J F Q:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q)
    (P:completedReflectionPool I Q) :
    completedLocalExponent I F P.val=completedLocalExponent J F P.val := by
  rcases (mem_completedReflectionPool I Q P.val hI hQ).mp P.property with
    ⟨hP,hdiv,_,_,hres⟩
  exact (nonresidual_prime_transport I J F Q P.val hI hJ hP hA hT hdiv hres).2.2


-- @@ L237-246 verbatim
theorem completedBranchScale_eq_on_fiber {ι:Type*} [Fintype ι]
    (K X:ℝ) (I J F Q:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q)
    (P:ι→Ideal Eis) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι→Fin 3) :
    completedBranchScale K X I F Q P e=completedBranchScale K X J F Q P e := by
  have hj:(fun i=>completedLocalExponent I F (P i))=(fun i=>completedLocalExponent J F (P i)):=by
    funext i
    exact completedReflectionPool_exponent_eq I J F Q hI hJ hQ hA hT ⟨P i,hP i⟩
  simp only [completedBranchScale,completedResidualScale_eq_on_fiber K I J Q hA hT,hj]


-- @@ L248-248 verbatim
end


-- @@ L250-250 verbatim
section


-- @@ L252-252 verbatim
def reflectionSixActive (e:Fin 6) : Prop := 3≤e.val


-- @@ L254-254 verbatim
def reflectionSixLabel (e:Fin 6) : Fin 3 := ⟨e.val%3,Nat.mod_lt _ (by decide)⟩


-- @@ L256-257 verbatim
def reflectionSixValid {ι:Type*} (e:ι→Fin 6) : Prop :=
  ∀i,e i=0 ∨ reflectionSixActive (e i)


-- @@ L259-259 verbatim
variable {ι:Type*} [Fintype ι] [DecidableEq ι]


-- @@ L261-262 verbatim
def encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) : ι→Fin 6 := fun i=>
  if h:i∈x.1 then ⟨3+(x.2 ⟨i,h⟩).val,by have ht:=(x.2 ⟨i,h⟩).isLt; omega⟩ else 0


-- @@ L264-265 verbatim
def reflectionSixSupport (e:ι→Fin 6) : Finset ι :=
  Finset.univ.filter (fun i=>reflectionSixActive (e i))


-- @@ L267-268 verbatim
def decodeReflectionSix (e:ι→Fin 6) : ΣA:Finset ι,A→Fin 3 :=
  ⟨reflectionSixSupport e,fun i=>reflectionSixLabel (e i.val)⟩


-- @@ L270-275 verbatim
omit [Fintype ι] in
lemma reflectionSixActive_encode (x:ΣA:Finset ι,A→Fin 3) (i:ι) :
    reflectionSixActive (encodeReflectionSix x i) ↔ i∈x.1 := by
  by_cases hi:i∈x.1
  · simp [encodeReflectionSix,hi,reflectionSixActive]
  · simp [encodeReflectionSix,hi,reflectionSixActive]


-- @@ L277-284 verbatim
omit [Fintype ι] in
lemma encodeReflectionSix_valid (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixValid (encodeReflectionSix x) := by
  intro i
  by_cases hi:i∈x.1
  · exact Or.inr ((reflectionSixActive_encode x i).mpr hi)
  · left
    simp [encodeReflectionSix,hi]


-- @@ L286-290 verbatim
lemma reflectionSixSupport_encode (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixSupport (encodeReflectionSix x)=x.1 := by
  ext i
  simp only [reflectionSixSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    reflectionSixActive_encode]


-- @@ L292-307 verbatim
lemma encodeReflectionSix_injective :
    Function.Injective (encodeReflectionSix (ι:=ι)) := by
  intro x y hxy
  have hsets:x.1=y.1:=by
    rw [←reflectionSixSupport_encode x,←reflectionSixSupport_encode y,hxy]
  rcases x with ⟨A,e⟩
  rcases y with ⟨B,f⟩
  dsimp only at hsets
  subst B
  congr 1
  funext i
  have he:=congrFun hxy i.val
  simp only [encodeReflectionSix,dite_eq_left i.property] at he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  exact Nat.add_left_cancel hv


-- @@ L309-323 verbatim
lemma encode_decodeReflectionSix (e:ι→Fin 6) (he:reflectionSixValid e) :
    encodeReflectionSix (decodeReflectionSix e)=e := by
  funext i
  by_cases hi:reflectionSixActive (e i)
  · have him:i∈reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    dsimp only [encodeReflectionSix, decodeReflectionSix]
    rw [dite_eq_left him]
    apply Fin.ext
    change 3 + (e i).val % 3 = (e i).val
    have hl:=(e i).isLt
    dsimp only [reflectionSixActive] at hi
    omega
  · have him:i∉reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    have hz:e i=0:=(he i).resolve_right hi
    simp [encodeReflectionSix,decodeReflectionSix,him,hz]


-- @@ L325-327 verbatim
lemma decode_encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) :
    decodeReflectionSix (encodeReflectionSix x)=x :=
  encodeReflectionSix_injective (encode_decodeReflectionSix _ (encodeReflectionSix_valid x))


-- @@ L329-333 verbatim
def reflectionSixEquiv : (ΣA:Finset ι,A→Fin 3) ≃ {e:ι→Fin 6 // reflectionSixValid e} where
  toFun x:=⟨encodeReflectionSix x,encodeReflectionSix_valid x⟩
  invFun e:=decodeReflectionSix e.val
  left_inv:=decode_encodeReflectionSix
  right_inv e:=Subtype.ext (encode_decodeReflectionSix e.val e.property)


-- @@ L335-357 verbatim
theorem sum_active_exceptional_eq_six {V:Type*} [AddCommMonoid V]
    (F:∀A:Finset ι,(A→Fin 3)→V) :
    (∑A:Finset ι,∑e:A→Fin 3,F A e)=
      ∑e:ι→Fin 6,if reflectionSixValid e then
        F (decodeReflectionSix e).1 (decodeReflectionSix e).2 else 0 := by
  have he:=Equiv.sum_comp (reflectionSixEquiv (ι:=ι))
    (fun e:{e:ι→Fin 6 // reflectionSixValid e}=>
      F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2)
  have hs:(∑x:ΣA:Finset ι,A→Fin 3,F x.1 x.2)=
      ∑e:{e:ι→Fin 6 // reflectionSixValid e},F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2 := by
    calc
      _=∑x:ΣA:Finset ι,A→Fin 3,
          F (decodeReflectionSix (encodeReflectionSix x)).1
            (decodeReflectionSix (encodeReflectionSix x)).2 := by
        apply Finset.sum_congr rfl
        intro x _
        exact (congrArg (fun y:ΣA:Finset ι,A→Fin 3=>F y.1 y.2)
          (decode_encodeReflectionSix x)).symm
      _=_ := he
  rw [Fintype.sum_sigma] at hs
  rw [hs,←Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter reflectionSixValid)
    (by simp) (fun e:ι→Fin 6=>F (decodeReflectionSix e).1 (decodeReflectionSix e).2)).symm


-- @@ L359-359 verbatim
end

-- @@ L360-360 verbatim
section


-- @@ L362-362 verbatim
open ActualEisensteinCubic LocalReflectionBrackets

-- @@ L363-363 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L364-365 verbatim
noncomputable local instance reflectionWeightField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P

-- @@ L366-367 verbatim
noncomputable local instance reflectionWeightFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _


-- @@ L369-369 verbatim
variable {ι:Type*} [Fintype ι] [DecidableEq ι]


-- @@ L371-377 verbatim
def reflectionStratumWeight (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) : ℂ :=
  (∏i∈A,(((actualSextic (P i) (hg i))⁻¹)^2) (σ A i)*
    phase (actualSextic (P i) (hg i)) (ψ A i) (j i) (ε A i))*
  (∏i∈(Finset.univ:Finset ι)\A,zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i))


-- @@ L379-400 verbatim
lemma reflectionStratumWeight_norm_le_one (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hc:∀i,ringChar (Eis⧸P i)≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀A i,(ψ A i).IsPrimitive)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) :
    ‖reflectionStratumWeight P hg j ψ σ ε A‖≤1 := by
  have hactive (i:ι) : ‖(((actualSextic (P i) (hg i))⁻¹)^2) (σ A i)*
      phase (actualSextic (P i) (hg i)) (ψ A i) (j i) (ε A i)‖=1 := by
    rw [norm_mul,FiniteRayExpansion.norm_char_unit]
    simpa only [one_mul,actualSextic] using canonical_phase_norm (P i) (hg i) (hc i)
      (ψ A i) (hψ A i) (j i) (hj i) (ε A i)
  have hinactive (i:ι) : ‖zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i)‖≤1 := by
    by_cases hi:j i=0
    · rw [hi]
      exact zeroFourierCoefficient_zero_norm_le_one _
    · have he:=canonical_zeroFourierCoefficient (P i) (hg i) (hc i) (j i) (hj i)
      have hz:zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i)=0 := by
        simpa only [actualSextic,ite_eq_right hi] using he
      rw [hz]
      simp
  rw [reflectionStratumWeight,norm_mul,norm_prod,norm_prod]
  simp only [hactive,Finset.prod_const_one,one_mul]
  exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hinactive i)


-- @@ L402-406 verbatim
def reflectionSixWeight (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (e:ι→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionStratumWeight P hg j ψ σ ε (reflectionSixSupport e) else 0


-- @@ L408-416 verbatim
lemma reflectionSixWeight_norm_le_one (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hc:∀i,ringChar (Eis⧸P i)≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀A i,(ψ A i).IsPrimitive)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (e:ι→Fin 6) :
    ‖reflectionSixWeight P hg j ψ σ ε e‖≤1 := by
  unfold reflectionSixWeight
  split_ifs
  · exact reflectionStratumWeight_norm_le_one P hg hc j hj ψ hψ σ ε _
  · simp


-- @@ L418-429 verbatim
theorem sum_reflectionStratumWeight_eq_six (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ)
    (G:∀A:Finset ι,(A→Fin 3)→ℂ) :
    (∑A:Finset ι,∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*G A e)=
      ∑e:ι→Fin 6,reflectionSixWeight P hg j ψ σ ε e*
        G (decodeReflectionSix e).1 (decodeReflectionSix e).2 := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e <;> simp [reflectionSixWeight,he,decodeReflectionSix]


-- @@ L431-445 verbatim
theorem stratum_weighted_brackets_eq_branches (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) (n b:Eis) :
    reflectionStratumWeight P hg j ψ σ ε A*
      (∏i:A,bracket (actualSextic (P i.val) (hg i.val)) (j i.val)
        (Ideal.Quotient.mk (P i.val) (n*b^3)))=
    ∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*
      reflectedBranch (fun i:A=>P i.val) (fun i=>hg i.val) (fun i=>j i.val) e n b := by
  rw [prod_bracket_eq_full_branches,Finset.mul_sum]
  apply Finset.sum_congr
  · ext e
    simp
  · intro e _
    rfl


-- @@ L447-459 verbatim
theorem sum_reflectionSixWeight_unpad (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (G:(ι→Fin 6)→ℂ) :
    (∑e:ι→Fin 6,reflectionSixWeight P hg j ψ σ ε e*G e)=
      ∑A:Finset ι,∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*
        G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_reflectionStratumWeight_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [encode_decodeReflectionSix e he]
  · simp only [reflectionSixWeight,ite_eq_right he,zero_mul]


-- @@ L461-461 verbatim
end

-- @@ L462-462 verbatim
section


-- @@ L464-464 verbatim
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic

-- @@ L465-465 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L467-469 verbatim
def reflectionChoiceValue (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6)
    (P:Ideal Eis) : Fin 6 :=
  if h:P∈completedReflectionPool I Q then e ⟨P,h⟩ else 0


-- @@ L471-472 verbatim
def reflectionActivePool (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6) : Finset (Ideal Eis) :=
  (completedReflectionPool I Q).filter (fun P=>reflectionSixActive (reflectionChoiceValue I Q e P))


-- @@ L474-475 verbatim
lemma reflectionActivePool_subset (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6) :
    reflectionActivePool I Q e⊆completedReflectionPool I Q := Finset.filter_subset _ _


-- @@ L477-482 verbatim
lemma mem_reflectionActivePool (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6)
    (P:completedReflectionPool I Q) :
    P.val∈reflectionActivePool I Q e ↔ reflectionSixActive (e P) := by
  rw [reflectionActivePool, Finset.mem_filter]
  simp only [P.property, true_and]
  rw [reflectionChoiceValue, dite_eq_left P.property]


-- @@ L484-496 verbatim
lemma reflectionActivePool_encode (I Q:Ideal Eis)
    (A:Finset (completedReflectionPool I Q)) (e:A→Fin 3) :
    reflectionActivePool I Q (encodeReflectionSix ⟨A,e⟩)=A.image Subtype.val := by
  ext P
  constructor
  · intro hP
    let p:completedReflectionPool I Q:=⟨P,reflectionActivePool_subset I Q _ hP⟩
    have hp:p∈A:=(reflectionSixActive_encode ⟨A,e⟩ p).mp
      ((mem_reflectionActivePool I Q _ p).mp hP)
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  · intro hP
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hP
    exact (mem_reflectionActivePool I Q _ p).mpr ((reflectionSixActive_encode ⟨A,e⟩ p).mpr hp)


-- @@ L498-500 verbatim
def reflectionActiveLabel (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6)
    (P:reflectionActivePool I Q e) : Fin 3 :=
  reflectionSixLabel (e ⟨P.val,reflectionActivePool_subset I Q e P.property⟩)


-- @@ L502-529 verbatim
def sixReflectedBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6)
    (amplitude:ℕ→Ideal Eis→Ideal Eis→ℂ) (hamp:∀m n b,‖amplitude m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q where
  levelScale:=levelScale
  levelScale_pos:=hlevel
  levelScale_le:=hbound
  primes:=reflectionActivePool I Q e
  maximal:=fun P=>completedReflectionPool_maximal I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  good:=fun P=>completedReflectionPool_good I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  coprime:=by
    intro P R hPR
    let : P.val.IsMaximal:=completedReflectionPool_maximal I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
    let : R.val.IsMaximal:=completedReflectionPool_maximal I Q ⟨R.val,reflectionActivePool_subset I Q e R.property⟩
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)
  divides:=fun P=>completedReflectionPool_divides I Q hI hQ ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  nonresidual:=fun P=>completedReflectionPool_nonresidual I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  label:=reflectionActiveLabel I Q e
  nColumns:=fun i=>dualIdealDyad i.2.2
  bColumns:=fun i=>dualIdealDyad i.2.1
  nBounds:=fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
  bBounds:=fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
  amplitude:=fun i=>amplitude i.1
  amplitude_bound:=fun i n _ b _=>hamp i.1 n b
  rowPhase:=fun i=>rowPhase i.1
  rowPhase_bound:=fun i k=>hrow i.1 k


-- @@ L531-537 verbatim
def sixFixedCuspBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q hI hQ K levelBound levelScale hlevel hbound e
    (fixedConjugateCuspArray cusp u) (fixedConjugateCuspArray_norm_le_one cusp u) rowPhase hrow).withExtractedFixedCuspArray cusp u rowPhase hrow


-- @@ L539-544 verbatim
lemma sixFixedCuspBranch_primes (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u rowPhase hrow).primes=
      reflectionActivePool I Q e := rfl


-- @@ L546-553 verbatim
lemma sixFixedCuspBranch_scale (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q e=>P.val) (reflectionActiveLabel I Q e) := rfl


-- @@ L555-555 verbatim
end


-- @@ L557-557 verbatim
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets

-- @@ L558-558 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L559-560 verbatim
local instance poolMaximal (I Q:Ideal Eis) (P:completedReflectionPool I Q) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q P

-- @@ L561-562 verbatim
noncomputable local instance poolField (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val

-- @@ L563-564 verbatim
noncomputable local instance poolFintype (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _


-- @@ L566-569 verbatim
def reflectionInactiveStratumWeight (I F Q:Ideal Eis) (A:Finset (completedReflectionPool I Q)) : ℂ :=
  ∏P∈(Finset.univ:Finset (completedReflectionPool I Q))\A,
    zeroFourierCoefficient (actualSextic P.val (completedReflectionPool_good I Q P))
      (completedLocalExponent I F P.val)


-- @@ L571-586 verbatim
lemma reflectionInactiveStratumWeight_norm_le_one (I F Q:Ideal Eis)
    (A:Finset (completedReflectionPool I Q)) : ‖reflectionInactiveStratumWeight I F Q A‖≤1 := by
  rw [reflectionInactiveStratumWeight,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
  intro P _
  by_cases hj:completedLocalExponent I F P.val=0
  · rw [hj]
    exact zeroFourierCoefficient_zero_norm_le_one _
  · have he:=canonical_zeroFourierCoefficient P.val (completedReflectionPool_good I Q P)
      (completedReflectionPool_odd I Q P) (completedLocalExponent I F P.val)
      (Nat.mod_lt _ (by decide : 0<6))
    have hz:zeroFourierCoefficient (actualSextic P.val (completedReflectionPool_good I Q P))
        (completedLocalExponent I F P.val)=0 := by
      simpa only [actualSextic,ite_eq_right hj] using he
    rw [hz]
    simp


-- @@ L588-589 verbatim
def reflectionSixInactiveWeight (I F Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionInactiveStratumWeight I F Q (reflectionSixSupport e) else 0


-- @@ L591-596 verbatim
lemma reflectionSixInactiveWeight_norm_le_one (I F Q:Ideal Eis)
    (e:completedReflectionPool I Q→Fin 6) : ‖reflectionSixInactiveWeight I F Q e‖≤1 := by
  unfold reflectionSixInactiveWeight
  split_ifs
  · exact reflectionInactiveStratumWeight_norm_le_one I F Q _
  · simp


-- @@ L598-609 verbatim
lemma sum_reflectionSixInactiveWeight_unpad (I F Q:Ideal Eis)
    (G:(completedReflectionPool I Q→Fin 6)→ℂ) :
    (∑e:completedReflectionPool I Q→Fin 6,reflectionSixInactiveWeight I F Q e*G e)=
      ∑A:Finset (completedReflectionPool I Q),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q A*G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [ite_eq_left he,encode_decodeReflectionSix e he]
    simp only [reflectionSixInactiveWeight,ite_eq_left he,decodeReflectionSix]
  · simp only [ite_eq_right he,reflectionSixInactiveWeight,zero_mul]


-- @@ L611-612 verbatim
abbrev SixReflectionIndex (rays:ℕ) (I Q:Ideal Eis) :=
  Fin rays×(completedReflectionPool I Q→Fin 6)


-- @@ L614-631 verbatim
def sixFixedCuspFiber (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=completedReflectionPool I Q
  maximal:=completedReflectionPool_maximal I Q
  divides:=completedReflectionPool_divides I Q hI hQ
  branch:=fun x=>sixFixedCuspBranch I F Q hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q x.2)


-- @@ L633-667 verbatim
theorem sixFixedCuspFiber_value (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixFixedCuspFiber rays I F Q hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑t:Fin rays,∑A:Finset (completedReflectionPool I Q),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q A*rayWeight (t,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (t,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _=∑e:completedReflectionPool I Q→Fin 6,reflectionSixInactiveWeight I F Q e*
      (rayWeight (t,e)*(sixFixedCuspBranch I F Q hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixFixedCuspFiber]
      exact (mul_assoc _ _ _).symm


-- @@ L669-669 verbatim
end CompletedGauss


-- @@ L671-671 verbatim
end


-- @@ L673-673 verbatim
end OAI
