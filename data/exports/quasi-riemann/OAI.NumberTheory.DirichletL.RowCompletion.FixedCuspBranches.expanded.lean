import OAI.NumberTheory.DirichletL.Eisenstein.FixedConductor


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


-- @@ L80-80 verbatim
section

-- @@ L81-81 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid

-- @@ L82-82 verbatim
open ConcretePrimeRowBridge

-- @@ L83-83 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L85-87 verbatim
lemma prime_dvd_iff_factor_count_pos (P A:Ideal Eis) (hP:Prime P) (hA:A≠0) :
    P∣A ↔ 0<(normalizedFactors A).count P := by
  simp only [Multiset.count_pos,UniqueFactorizationMonoid.mem_normalizedFactors_iff hA,hP,true_and]


-- @@ L89-104 verbatim
theorem goodMaskMovingIdeal_dvd_iff (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    P∣goodMaskMovingIdeal g r ↔ P∣I*(Ideal.span {m}*F) := by
  have hP:Prime P:=Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hmI:(Ideal.span {m}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm0
  rw [prime_dvd_iff_factor_count_pos P _ hP (goodMaskMovingIdeal_supported g r hg hr).1,
    prime_dvd_iff_factor_count_pos P _ hP (mul_ne_zero hI (mul_ne_zero hmI hF)),
    goodMaskMovingIdeal_count I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P hgood hodd,
    normalizedFactors_mul hI (mul_ne_zero hmI hF),normalizedFactors_mul hmI hF]
  simp only [Multiset.count_add]
  omega


-- @@ L106-136 verbatim
theorem goodMaskMovingIdeal_primeSupport (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    IdealMobiusDivisorSum.primeSupport (goodMaskMovingIdeal g r)=
      (IdealMobiusDivisorSum.primeSupport (I*(Ideal.span {m}*F))).filter
        (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2) := by
  have hs:=goodMaskMovingIdeal_supported g r hg hr
  have hmI:(Ideal.span {m}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm0
  have hprod:=mul_ne_zero hI (mul_ne_zero hmI hF)
  ext P
  simp only [IdealMobiusDivisorSum.primeSupport,Finset.mem_filter,Multiset.mem_toFinset]
  constructor
  · intro hP
    obtain ⟨hmax,hgood,hodd⟩:=supported_factors_good _ hs P hP
    let:P.IsMaximal:=hmax
    have hp:Prime P:=prime_of_normalized_factor P hP
    have hd: P∣goodMaskMovingIdeal g r:=
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hs.1).mp hP).2
    exact ⟨(UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mpr ⟨hp,
      (goodMaskMovingIdeal_dvd_iff I F hI hF m f z hm0 hf hz um am bm g hg hm
        u a b r hr hx P hgood hodd).mp hd⟩,hgood,hodd⟩
  · rintro ⟨hP,hgood,hodd⟩
    have hp:Prime P:=prime_of_normalized_factor P hP
    let:P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hd:=((UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mp hP).2
    exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hs.1).mpr ⟨hp,
      (goodMaskMovingIdeal_dvd_iff I F hI hF m f z hm0 hf hz um am bm g hg hm
        u a b r hr hx P hgood hodd).mpr hd⟩


-- @@ L138-140 verbatim
def goodMaskNonresidualPool (I F:Ideal Eis) (m g r:Eis) : Finset (Ideal Eis) :=
  (IdealMobiusDivisorSum.primeSupport (goodMaskMovingIdeal g r)).filter
    (fun P=>¬P∣rowResidualPart I (Ideal.span {m}*F))


-- @@ L142-153 verbatim
theorem goodMaskNonresidualPool_eq (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    goodMaskNonresidualPool I F m g r=completedReflectionPool I (Ideal.span {m}*F) := by
  rw [goodMaskNonresidualPool,
    goodMaskMovingIdeal_primeSupport I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx]
  ext P
  simp only [Finset.mem_filter,completedReflectionPool]
  tauto


-- @@ L155-170 verbatim
theorem goodMaskNonresidualPool_eq_on_fiber (I J F:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hF:F≠0) (m f z w:Eis) (hm0:m≠0)
    (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I) (hw:Ideal.span {w}=J)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (u':Eisˣ) (a' b':ℕ) (r':Eis) (hr':Supported (Ideal.span {r'}))
    (hx':f^4*w=u'.val*lambda^a'*(2:Eis)^b'*r')
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I (Ideal.span {m}*F)=rowMaskPart J (Ideal.span {m}*F)) :
    goodMaskNonresidualPool I F m g r=goodMaskNonresidualPool J F m g r' := by
  rw [goodMaskNonresidualPool_eq I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx,
    goodMaskNonresidualPool_eq J F hJ hF m f w hm0 hf hw um am bm g hg hm u' a' b' r' hr' hx']
  exact completedReflectionPool_eq_on_fiber I J (Ideal.span {m}*F) hI hJ
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF) hA hT


-- @@ L172-180 verbatim
theorem goodMaskNonresidualPool_free_eq (I F Q0:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    (goodMaskNonresidualPool I F m g r).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I (Ideal.span {m}*F)).filter (fun P=>¬Q0≤P) := by
  rw [goodMaskNonresidualPool_eq I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx]


-- @@ L182-182 verbatim
end


-- @@ L184-184 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid

-- @@ L185-185 verbatim
open ConcretePrimeRowBridge CanonicalUnitEuler

-- @@ L186-186 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L188-210 verbatim
theorem goodMaskMovingIdeal_principal_row (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) (n:Eis) :
    idealRowHom n (goodMaskMovingIdeal g r)=
      principalSexticRow (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val)
        (primeIndex_pairwise_coprime (goodMaskMovingIdeal g r))
        (fun P=>(supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
          P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>completedLocalExponent I F P.val)
        (finitePrimeModulus (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [idealRowHom_eq_principalSexticRow _ (goodMaskMovingIdeal_supported g r hg hr)]
  have he:(fun P:PrimeIndex (goodMaskMovingIdeal g r)=>(normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6)=
      (fun P=>completedLocalExponent I F P.val):=by
    funext P
    have hdata:=supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
      P.val (Multiset.mem_toFinset.mp P.property)
    exact goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm
      u a b r hr hx P.val hdata.2.1 hdata.2.2
  rw [he]


-- @@ L212-232 verbatim
theorem rowTwist_eq_computed_principal_row
    (Ψ:Eis→*ℂ) (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hpr:lambda^2∣r-1) (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=(Ψ*numeratorBadTwist u a b r hr) n *
      principalSexticRow (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val)
        (primeIndex_pairwise_coprime (goodMaskMovingIdeal g r))
        (fun P=>(supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
          P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>completedLocalExponent I F P.val)
        (finitePrimeModulus (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2 um am bm g hg hm
    u a b r hr hpr hx n hpn]
  change _*idealRowHom n (goodMaskMovingIdeal g r)=_
  rw [goodMaskMovingIdeal_principal_row I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx n]


-- @@ L234-255 verbatim
theorem goodMaskMovingIdeal_exponent_eq_on_fiber
    (I J F:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hF:Squarefree F)
    (m f z w:Eis) (hm0:m≠0)
    (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I) (hw:Ideal.span {w}=J)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (u':Eisˣ) (a' b':ℕ) (r':Eis) (hr':Supported (Ideal.span {r'}))
    (hx':f^4*w=u'.val*lambda^a'*(2:Eis)^b'*r')
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I (Ideal.span {m}*F)=rowMaskPart J (Ideal.span {m}*F))
    (P:completedReflectionPool I (Ideal.span {m}*F)) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=
      (normalizedFactors (goodMaskMovingIdeal g r')).count P.val%6 := by
  let:P.val.IsMaximal:=completedReflectionPool_maximal I (Ideal.span {m}*F) P
  have hgood:=completedReflectionPool_good I (Ideal.span {m}*F) P
  have hodd:=completedReflectionPool_odd I (Ideal.span {m}*F) P
  rw [goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val hgood hodd,
    goodMaskMovingIdeal_exponent J F hJ hF m f w hf hw um am bm g hg hm u' a' b' r' hr' hx' P.val hgood hodd]
  exact completedReflectionPool_exponent_eq I J F (Ideal.span {m}*F) hI hJ
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P


-- @@ L257-257 verbatim
end CanonicalRowCompletion


-- @@ L259-259 verbatim
namespace CubicEisenstein


-- @@ L261-261 verbatim
section

-- @@ L262-262 verbatim
open scoped Classical BigOperators MatrixGroups Matrix


-- @@ L264-264 verbatim
open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic

-- @@ L265-265 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L266-266 verbatim
namespace FixedCuspShape

-- @@ L267-267 verbatim
variable {H:SL(2,Eis)} (s:FixedCuspShape H)


-- @@ L269-278 verbatim
lemma amplitude_source_nonzero (p:ThetaFullIndex)
    (hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val≠0) :
    (sourceCuspCoefficients s.index).value (thetaFullFrequency p)≠0 := by
  intro hz
  apply hp
  have hz':(sourceCuspCoefficients s.index).value
      (fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val)=0:=by
    simpa only [thetaFullFrequency_eq_fixedCuspArrayIndex] using hz
  simp only [amplitude,fixedConjugateCuspArray,fixedCuspArray,hz',zero_div,ite_self,
    star_zero,zero_mul]


-- @@ L280-291 verbatim
lemma amplitude_integral_phase (p:ThetaFullIndex) (c d:Eis) (hc:c≠0) :
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
        (eisEmbedding d/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (-(eisEmbedding d*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  by_cases hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val=0
  · rw [hp,zero_mul,zero_mul]
  · rw [sourceCuspPhaseNumerator_phase s.index (s.upper 0 0) (thetaFullFrequency p) c d hc
      (s.amplitude_source_nonzero p hp)]


-- @@ L293-317 verbatim
lemma datum_integral_phase (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) (p:ThetaFullIndex) :
    (fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency p))*
      ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
        ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      ShortDraftTrace.breveE (-(eisEmbedding (((g:SL(2,Eis))*H) 1 1)*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  have hphase:=s.datum_additive_phase g (by rwa [hg])
    (cuspFrequency (thetaFullFrequency p)) (sourceCuspScale s.index:ℂ)
  simp only [hg] at hphase
  calc
    _=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
          (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) := by
      rw [show -cuspFrequency (thetaFullFrequency p)*
          ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))=
        -cuspFrequency (thetaFullFrequency p)*(s.datum g (by rwa [hg])).dualPoint/
          (sourceCuspScale s.index:ℂ) by ring,hphase]
      unfold amplitude
      rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
      ring
    _=_:=s.amplitude_integral_phase p c _ hc


-- @@ L319-321 verbatim
def stratumShapeFactor (c:Eis) : ℂ :=
  -star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2*
    ((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)/eisEmbedding c^2


-- @@ L323-331 verbatim
lemma datum_common_row_factor (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) :
    (s.datum g (by rwa [hg])).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)=
      s.stratumShapeFactor c*star (levelTwoComplexCharacter g) := by
  have hm:=s.smoothed_row_factor g (by rwa [hg])
  simp only [s.datum_heightScale,hg,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hm
  rw [hm]
  unfold stratumShapeFactor
  ring


-- @@ L333-333 verbatim
end FixedCuspShape

-- @@ L334-334 verbatim
end


-- @@ L336-336 verbatim
open scoped Classical BigOperators ContDiff MatrixGroups Matrix


-- @@ L338-338 verbatim
open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic

-- @@ L339-339 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L340-340 verbatim
namespace FixedCuspShape

-- @@ L341-341 verbatim
variable {H:SL(2,Eis)} (s:FixedCuspShape H)


-- @@ L343-408 verbatim
theorem sum_smoothedKernel_integral_phase {ι:Type*} [Fintype ι]
    (g:ι→levelTwo) (c:Eis) (hc:c≠0) (hC:∀v,((g v:SL(2,Eis))*H) 1 0=c)
    (w:ι→ℂ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑v,w v*(s.datum (g v) (by rw [hC v];exact hc)).smoothedKernel W X)=
      fixedRadialCoefficientScalar*s.stratumShapeFactor c*
      ∑'p:ThetaFullIndex,
        (s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val /
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)*
        (∑v,w v*star (levelTwoComplexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
              eisEmbedding c)) := by
  let d:ι→SourceCuspDatum:=fun v=>s.datum (g v) (by rw [hC v];exact hc)
  have hindex:∀v,(d v).index=s.index:=fun _=>rfl
  have hheight:∀v,(d v).heightScale=(Ideal.absNorm (Ideal.span {c}):ℝ):=by
    intro v
    dsimp only [d]
    rw [s.datum_heightScale,hC v,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  have he:=sum_smoothedKernel_common_cusp d w s.index (Ideal.absNorm (Ideal.span {c}):ℝ)
    hindex hheight W a b ha hsupp hW X hX
  rw [he]
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*z)
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [sourceCusp_full_index_kernel_argument p s.index (Ideal.absNorm (Ideal.span {c}):ℝ) X]
  let A:ℂ:=fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
    sourceFrequencyAngle (thetaFullFrequency p)
  let B:ℂ:=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val
  let lengthScale:ι→ℂ:=fun v=>w v*((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
    ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*((d v).dualPoint/(sourceCuspScale s.index:ℂ)))
  let R:ι→ℂ:=fun v=>w v*star (levelTwoComplexCharacter (g v))*
    ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
      (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c)
  have hs:A*(∑v,lengthScale v)=s.stratumShapeFactor c*B*(∑v,R v):=by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [lengthScale,R]
    calc
      _=w v*(((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
          (A*ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d v).dualPoint/(sourceCuspScale s.index:ℂ))))):=by ring
      _=w v*((s.stratumShapeFactor c*star (levelTwoComplexCharacter (g v)))*
          (B*ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c))):=by
        rw [s.datum_common_row_factor (g v) c hc (hC v),s.datum_integral_phase (g v) c hc (hC v) p]
      _=_:=by ring
  let D:ℂ:=((ramifiedScale 1 completedRamifiedStep p.2.1*
    Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)
  let K:ℂ:=CubicReflectionKernel.paperKernel (Vstar W)
    ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
      (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)
  change A/D*K*(∑v,lengthScale v)=s.stratumShapeFactor c*(B/D*K*(∑v,R v))
  calc
    _=(A*(∑v,lengthScale v))/D*K:=by ring
    _=(s.stratumShapeFactor c*B*(∑v,R v))/D*K:=by rw [hs]
    _=_:=by ring


-- @@ L410-420 verbatim
lemma stratumShapeFactor_norm (c:Eis) (hc:c≠0) : ‖s.stratumShapeFactor c‖=1 := by
  have hu:‖eisEmbedding (s.upper 0 0)‖=1:=by
    rcases s.upper_unit with ⟨u,hu⟩
    rw [←hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hn:‖eisEmbedding c‖^2≠0:=pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc))
  rw [stratumShapeFactor,norm_div,norm_mul,norm_mul,norm_neg,norm_star,
    norm_levelTwoComplexCharacter,norm_pow,hu,one_pow,one_mul,one_mul,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  exact div_self hn


-- @@ L422-422 verbatim
end FixedCuspShape

-- @@ L423-423 verbatim
end CubicEisenstein


-- @@ L425-425 verbatim
open scoped BigOperators Classical ContDiff


-- @@ L427-427 verbatim
namespace CompletedGauss


-- @@ L429-429 verbatim
section

-- @@ L430-430 verbatim
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic

-- @@ L431-431 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L433-435 verbatim
def fixedCuspArrayWithPhase (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  phaseArray m n b*fixedConjugateCuspArray cusp u m n b


-- @@ L437-442 verbatim
lemma fixedCuspArrayWithPhase_norm_le_one (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖fixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 := by
  rw [fixedCuspArrayWithPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m n b)).trans (fixedConjugateCuspArray_norm_le_one cusp u m n b)


-- @@ L444-448 verbatim
lemma fixedCuspArrayWithPhase_zero (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible n b) : fixedCuspArrayWithPhase cusp u phaseArray m n b=0 := by
  simp only [fixedCuspArrayWithPhase,fixedConjugateCuspArray,
    fixedCuspArray_zero_of_ineligible _ _ _ _ _ h,star_zero,mul_zero]


-- @@ L450-450 verbatim
namespace ReflectedBranchData


-- @@ L452-459 verbatim
def extractedFixedCuspArrayWithPhase {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase cusp u phaseArray m
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1*n)
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2*b)


-- @@ L461-465 verbatim
lemma extractedFixedCuspArrayWithPhase_norm_le_one {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 :=
  fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m _ _


-- @@ L467-476 verbatim
lemma extractedFixedCuspArrayWithPhase_eq {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) :
    d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b=
      phaseArray m
        (reflectionExtractedDivisor (fun p:d.primes=>p.val)
          (fun p=>completedLocalExponent I F p.val) d.label 1*n)
        (reflectionExtractedDivisor (fun p:d.primes=>p.val)
          (fun p=>completedLocalExponent I F p.val) d.label 2*b)*
      d.extractedFixedCuspArray cusp u m n b := rfl


-- @@ L478-487 verbatim
lemma extractedFixedCuspArrayWithPhase_zero {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 1*n)
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 2*b)) :
    d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b=0 :=
  fixedCuspArrayWithPhase_zero cusp u phaseArray m _ _ h


-- @@ L489-496 verbatim
def withExtractedFixedCuspArrayWithPhase {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  d.withCanonicalCuspArray (d.extractedFixedCuspArrayWithPhase cusp u phaseArray)
    (fun m n b=>d.extractedFixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m n.val b.val)
    rowPhase hrow


-- @@ L498-504 verbatim
lemma withExtractedFixedCuspArrayWithPhase_amplitude {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    (d.withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow).amplitude i n b=
      d.extractedFixedCuspArrayWithPhase cusp u phaseArray i.1 n b := rfl


-- @@ L506-521 verbatim
theorem withExtractedFixedCuspArrayWithPhase_value {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow).value W X ρ q k=
      d.rawValue (d.extractedFixedCuspArrayWithPhase cusp u phaseArray) rowPhase W X ρ q k :=
  d.withCanonicalCuspArray_value (d.extractedFixedCuspArrayWithPhase cusp u phaseArray)
    (fun m n b=>d.extractedFixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m n.val b.val)
    rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk


-- @@ L523-523 verbatim
end ReflectedBranchData

-- @@ L524-524 verbatim
end

-- @@ L525-525 verbatim
section


-- @@ L527-527 verbatim
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic

-- @@ L528-528 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L530-538 verbatim
def sixPhaseFixedCuspBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow


-- @@ L540-546 verbatim
lemma sixPhaseFixedCuspBranch_primes (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow).primes=reflectionActivePool I Q e := rfl


-- @@ L548-560 verbatim
lemma sixPhaseFixedCuspBranch_amplitude (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    let d:=sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    let D:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1
    let E:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2
    d.amplitude i n b=phaseArray i.1 (D*n) (E*b)*fixedConjugateCuspArray cusp u i.1 (D*n) (E*b) := rfl


-- @@ L562-571 verbatim
lemma sixPhaseFixedCuspBranch_scale (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q e=>P.val) (reflectionActiveLabel I Q e) := rfl


-- @@ L573-573 verbatim
end


-- @@ L575-575 verbatim
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets

-- @@ L576-576 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L578-597 verbatim
def sixPhaseFixedCuspFiber (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=completedReflectionPool I Q
  maximal:=completedReflectionPool_maximal I Q
  divides:=completedReflectionPool_divides I Q hI hQ
  branch:=fun x=>sixPhaseFixedCuspBranch I F Q hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (phaseArray x) (hphase x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q x.2)


-- @@ L599-635 verbatim
theorem sixPhaseFixedCuspFiber_value (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixPhaseFixedCuspFiber rays I F Q hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit phaseArray hphase rayWeight hray rowPhase hrow
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
      (rayWeight (t,e)*(sixPhaseFixedCuspBranch I F Q hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (phaseArray (t,e)) (hphase (t,e)) (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixPhaseFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixPhaseFixedCuspFiber]
      exact (mul_assoc _ _ _).symm


-- @@ L637-637 verbatim
end CompletedGauss


-- @@ L639-639 verbatim
end


-- @@ L641-641 verbatim
end OAI
