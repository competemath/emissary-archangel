import OAI.NumberTheory.DirichletL.Eisenstein.ReflectionFibers


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
section

-- @@ L77-77 verbatim
open scoped BigOperators Classical


-- @@ L79-79 verbatim
namespace CanonicalRowCompletion


-- @@ L81-81 verbatim
section

-- @@ L82-82 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid

-- @@ L83-83 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L85-86 verbatim
def freePrimePool (lengthScale Q0:Ideal Eis) : Finset (Ideal Eis) :=
  (CompletedGauss.primeSupport lengthScale).filter (fun P=>¬Q0≤P)


-- @@ L88-90 verbatim
lemma mem_freePrimePool (lengthScale Q0 P:Ideal Eis) :
    P∈freePrimePool lengthScale Q0 ↔ P∈CompletedGauss.primeSupport lengthScale ∧ ¬Q0≤P := by
  simp only [freePrimePool,Finset.mem_filter]


-- @@ L92-97 verbatim
lemma residual_nonresidual_disjoint (I Q Q0:Ideal Eis) :
    Disjoint (CompletedGauss.primeSupport (rowResidualPart I Q)) (FreeReflection.pool I Q Q0) := by
  apply Finset.disjoint_left.mpr
  intro P hP ht
  exact FreeReflection.pool_nonresidual I Q Q0 ⟨P,ht⟩
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))


-- @@ L99-143 verbatim
theorem freePrimePool_eq_residual_union (lengthScale I Q Q0:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hcop:IsCoprime Q0 (rowResidualPart I Q))
    (hs:CompletedGauss.primeSupport lengthScale=
      (CompletedGauss.primeSupport (I*Q)).filter
        (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2)) :
    freePrimePool lengthScale Q0=
      CompletedGauss.primeSupport (rowResidualPart I Q) ∪ FreeReflection.pool I Q Q0 := by
  have hk:=rowResidualPart_admissible I Q hbad
  ext P
  constructor
  · intro hP
    obtain ⟨hL,hfree⟩:=Finset.mem_filter.mp hP
    rw [hs] at hL
    obtain ⟨hprod,hgood,hodd⟩:=Finset.mem_filter.mp hL
    have hp:Prime P:=prime_of_normalized_factor P (Multiset.mem_toFinset.mp hprod)
    by_cases hr:P∣rowResidualPart I Q
    · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
        ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hk.1).mpr ⟨hp,hr⟩))
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hprod,hgood,hodd,hr⟩,hfree⟩
  · intro hP
    rcases Finset.mem_union.mp hP with hr|ht
    · have hfactor:=Multiset.mem_toFinset.mp hr
      have hp:Prime P:=prime_of_normalized_factor P hfactor
      have hrow:=rowResidualPart_prime_exponent I Q P hfactor
      have hgood:=hk.2.2 P hfactor
      have hfree:¬Q0≤P:=by
        intro hQP
        exact hp.not_isUnit (hcop.isUnit_of_dvd'
          (Ideal.dvd_iff_le.mpr hQP) (dvd_of_mem_normalizedFactors hfactor))
      apply Finset.mem_filter.mpr
      refine ⟨?_,hfree⟩
      rw [hs]
      apply Finset.mem_filter.mpr
      exact ⟨Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)).mpr
        ⟨hp,dvd_mul_of_dvd_left (dvd_of_mem_normalizedFactors hrow.1) Q⟩),hgood⟩
    · obtain ⟨hpool,hfree⟩:=Finset.mem_filter.mp ht
      obtain ⟨hprod,hgood,hodd,_⟩:=Finset.mem_filter.mp hpool
      apply Finset.mem_filter.mpr
      refine ⟨?_,hfree⟩
      rw [hs]
      exact Finset.mem_filter.mpr ⟨hprod,hgood,hodd⟩


-- @@ L145-154 verbatim
def primeUnionToFree (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T) :
    PrimeIndex k ⊕ T → FreePrimeIndex lengthScale Q0 := fun P=>by
  have hm:(Sum.elim Subtype.val Subtype.val P)∈freePrimePool lengthScale Q0:=by
    rw [hs]
    cases P with
    | inl P=>exact Finset.mem_union_left _ P.property
    | inr P=>exact Finset.mem_union_right _ P.property
  exact ⟨⟨Sum.elim Subtype.val Subtype.val P,(Finset.mem_filter.mp hm).1⟩,
    (Finset.mem_filter.mp hm).2⟩


-- @@ L156-158 verbatim
lemma primeUnionToFree_val (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T) (P:PrimeIndex k⊕T) :
    (primeUnionToFree lengthScale Q0 k T hs P).val.val=Sum.elim Subtype.val Subtype.val P := rfl


-- @@ L160-185 verbatim
lemma primeUnionToFree_bijective (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) :
    Function.Bijective (primeUnionToFree lengthScale Q0 k T hs) := by
  constructor
  · intro P R he
    have hv:=congrArg (fun S:FreePrimeIndex lengthScale Q0=>S.val.val) he
    change Sum.elim Subtype.val Subtype.val P=Sum.elim Subtype.val Subtype.val R at hv
    cases P with
    | inl P=>cases R with
      | inl R=>exact congrArg Sum.inl (Subtype.ext hv)
      | inr R=>
        change P.val=R.val at hv
        exact (Finset.disjoint_left.mp hd P.property (hv.symm ▸ R.property)).elim
    | inr P=>cases R with
      | inl R=>
        change P.val=R.val at hv
        exact (Finset.disjoint_left.mp hd R.property (hv ▸ P.property)).elim
      | inr R=>exact congrArg Sum.inr (Subtype.ext hv)
  · intro P
    have hm:P.val.val∈CompletedGauss.primeSupport k∪T:=by
      rw [←hs]
      exact Finset.mem_filter.mpr ⟨P.val.property,P.property⟩
    rcases Finset.mem_union.mp hm with hl|hr
    · exact ⟨Sum.inl ⟨P.val.val,hl⟩,Subtype.ext (Subtype.ext rfl)⟩
    · exact ⟨Sum.inr ⟨P.val.val,hr⟩,Subtype.ext (Subtype.ext rfl)⟩


-- @@ L187-191 verbatim
noncomputable def primeUnionEquiv (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) :
    PrimeIndex k⊕T ≃ FreePrimeIndex lengthScale Q0 :=
  Equiv.ofBijective (primeUnionToFree lengthScale Q0 k T hs) (primeUnionToFree_bijective lengthScale Q0 k T hs hd)


-- @@ L193-196 verbatim
lemma primeUnionEquiv_val (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) (P:PrimeIndex k⊕T) :
    (primeUnionEquiv lengthScale Q0 k T hs hd P).val.val=Sum.elim Subtype.val Subtype.val P := rfl


-- @@ L198-206 verbatim
theorem prod_freePrimeIndex_eq {M:Type*} [CommMonoid M]
    (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) (f:Ideal Eis → M) :
    (∏P:FreePrimeIndex lengthScale Q0,f P.val.val)=(∏P:PrimeIndex k,f P.val)*(∏P:T,f P.val) := by
  calc
    _=(∏P:PrimeIndex k⊕T,f (Sum.elim Subtype.val Subtype.val P)):=
      (Fintype.prod_equiv (primeUnionEquiv lengthScale Q0 k T hs hd) _ _ (fun P=>rfl)).symm
    _=_:=Fintype.prod_sum_type _


-- @@ L208-208 verbatim
end


-- @@ L210-210 verbatim
section

-- @@ L211-211 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid

-- @@ L212-212 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L214-221 verbatim
variable (I F Q0:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))


-- @@ L223-223 verbatim
include I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop


-- @@ L225-232 verbatim
theorem goodMaskFreePrimePool :
    freePrimePool (goodMaskMovingIdeal g r) Q0=
      CompletedGauss.primeSupport (rowResidualPart I (Ideal.span {m}*F)) ∪
        FreeReflection.pool I (Ideal.span {m}*F) Q0 := by
  apply freePrimePool_eq_residual_union _ _ _ _ hI
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hbad hcop
  exact goodMaskMovingIdeal_primeSupport I F hI hF.ne_zero m f z hm0 hf hz
    um am bm g hg hm u a b r hr hx


-- @@ L234-239 verbatim
noncomputable def goodMaskFreePrimeEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool I (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex (goodMaskMovingIdeal g r) Q0 :=
  primeUnionEquiv _ _ _ _
    (goodMaskFreePrimePool I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop)
    (residual_nonresidual_disjoint I (Ideal.span {m}*F) Q0)


-- @@ L241-244 verbatim
lemma goodMaskFreePrimeEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop P).val.val=
      Sum.elim Subtype.val Subtype.val P := rfl


-- @@ L246-255 verbatim
lemma goodMaskFreePrimeEquiv_residual_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop
        (Sum.inl P)).val.val%6=1 := by
  change (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=1
  have hp:=(rowResidualPart_admissible I (Ideal.span {m}*F) hbad).2.2
    P.val (Multiset.mem_toFinset.mp P.property)
  rw [goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val hp.1 hp.2]
  exact completedLocalExponent_residual I F _ (dvd_mul_left F (Ideal.span {m})) P


-- @@ L257-266 verbatim
lemma goodMaskFreePrimeEquiv_nonresidual_exponent
    (P:FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop
        (Sum.inr P)).val.val%6=completedLocalExponent I F P.val := by
  change (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=completedLocalExponent I F P.val
  let:P.val.IsMaximal:=FreeReflection.pool_maximal I (Ideal.span {m}*F) Q0 P
  exact goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val
    (FreeReflection.pool_good I (Ideal.span {m}*F) Q0 P)
    (FreeReflection.pool_odd I (Ideal.span {m}*F) Q0 P)


-- @@ L268-279 verbatim
theorem goodMaskFreePrimeEquiv_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop P).val.val%6=
      Sum.elim (fun _=>1) (fun R=>completedLocalExponent I F R.val) P := by
  cases P with
  | inl P=>
    exact goodMaskFreePrimeEquiv_residual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop P
  | inr P=>
    exact goodMaskFreePrimeEquiv_nonresidual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop P


-- @@ L281-281 verbatim
end


-- @@ L283-283 verbatim
section


-- @@ L285-285 verbatim
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]


-- @@ L287-288 verbatim
def optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) : Finset β :=
  Finset.univ.filter (fun b=>e (Sum.inr b)∈A)


-- @@ L290-293 verbatim
omit [Fintype α] [Fintype γ] in
lemma mem_optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) (b:β) :
    b∈optionalPrimeActive e A ↔ e (Sum.inr b)∈A := by
  simp only [optionalPrimeActive,Finset.mem_filter,Finset.mem_univ,true_and]


-- @@ L295-298 verbatim
def activePrimeUnionMap (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A → A :=
  Sum.elim (fun a=>⟨e (Sum.inl a),hA a⟩)
    (fun b=>⟨e (Sum.inr b.val),(mem_optionalPrimeActive e A b.val).mp b.property⟩)


-- @@ L300-319 verbatim
omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionMap_bijective (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : Function.Bijective (activePrimeUnionMap e A hA) := by
  constructor
  · intro x y hxy
    have hv:=congrArg Subtype.val hxy
    cases x with
    | inl x=>cases y with
      | inl y=>exact congrArg Sum.inl (Sum.inl.inj (e.injective hv))
      | inr y=>cases e.injective hv
    | inr x=>cases y with
      | inl y=>cases e.injective hv
      | inr y=>exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj (e.injective hv)))
  · intro a
    obtain ⟨x,hx⟩:=e.surjective a.val
    cases x with
    | inl x=>exact ⟨Sum.inl x,Subtype.ext hx⟩
    | inr x=>
      have hm:x∈optionalPrimeActive e A:=(mem_optionalPrimeActive e A x).mpr (hx.symm ▸ a.property)
      exact ⟨Sum.inr ⟨x,hm⟩,Subtype.ext hx⟩


-- @@ L321-323 verbatim
noncomputable def activePrimeUnionEquiv (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A ≃ A :=
  Equiv.ofBijective (activePrimeUnionMap e A hA) (activePrimeUnionMap_bijective e A hA)


-- @@ L325-328 verbatim
omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inl (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (a:α) :
    (activePrimeUnionEquiv e A hA (Sum.inl a)).val=e (Sum.inl a) := rfl


-- @@ L330-333 verbatim
omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inr (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (b:optionalPrimeActive e A) :
    (activePrimeUnionEquiv e A hA (Sum.inr b)).val=e (Sum.inr b.val) := rfl


-- @@ L335-344 verbatim
omit [Fintype γ] in
theorem prod_activePrimeUnionEquiv {M:Type*} [CommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∏a:A,f a)=
      (∏a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))*
        (∏b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∏x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.prod_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.prod_sum_type _


-- @@ L346-355 verbatim
omit [Fintype γ] in
theorem sum_activePrimeUnionEquiv {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∑a:A,f a)=
      (∑a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))+
        (∑b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∑x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.sum_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.sum_sum_type _


-- @@ L357-360 verbatim
theorem sum_prime_active_sets {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (f:Finset γ → M) :
    (∑A:Finset γ,f A)=∑A:Finset (α⊕β),f (A.map e.toEmbedding) := by
  exact (Fintype.sum_equiv e.finsetCongr _ _ (fun _=>rfl)).symm


-- @@ L362-362 verbatim
end


-- @@ L364-364 verbatim
section

-- @@ L365-365 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid

-- @@ L366-366 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L368-377 verbatim
def nonresidualPoolEquiv (R I Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R Q=rowMaskPart I Q) :
    FreeReflection.pool R Q Q0 ≃ FreeReflection.pool I Q Q0 := by
  have he:=FreeReflection.pool_eq_on_fiber R I Q Q0 hR hI hQ hA hT
  exact {
    toFun:=fun P=>⟨P.val,he ▸ P.property⟩
    invFun:=fun P=>⟨P.val,he.symm ▸ P.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }


-- @@ L379-382 verbatim
lemma nonresidualPoolEquiv_val (R I Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I) (hT:rowMaskPart R Q=rowMaskPart I Q)
    (P:FreeReflection.pool R Q Q0) :
    (nonresidualPoolEquiv R I Q Q0 hR hI hQ hA hT P).val=P.val := rfl


-- @@ L384-390 verbatim
lemma nonresidualPoolEquiv_exponent (R I F Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I) (hT:rowMaskPart R Q=rowMaskPart I Q)
    (P:FreeReflection.pool R Q Q0) :
    completedLocalExponent I F (nonresidualPoolEquiv R I Q Q0 hR hI hQ hA hT P).val=
      completedLocalExponent R F P.val :=
  (completedReflectionPool_exponent_eq R I F Q hR hI hQ hA hT
    ⟨P.val,FreeReflection.pool_subset R Q Q0 P.property⟩).symm


-- @@ L392-401 verbatim
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

-- @@ L402-402 verbatim
include R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT


-- @@ L404-410 verbatim
noncomputable def goodMaskFreePrimeFiberEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex (goodMaskMovingIdeal g r) Q0 :=
  (Equiv.sumCongr (Equiv.refl _)
    (nonresidualPoolEquiv R I (Ideal.span {m}*F) Q0 hR hI
      (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT)).trans
    (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop)


-- @@ L412-416 verbatim
lemma goodMaskFreePrimeFiberEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
      hbad hcop hA hT P).val.val=Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl


-- @@ L418-434 verbatim
theorem goodMaskFreePrimeFiberEquiv_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
        hbad hcop hA hT P).val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val) P := by
  cases P with
  | inl P=>
    exact goodMaskFreePrimeEquiv_residual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop P
  | inr P=>
    exact (goodMaskFreePrimeEquiv_nonresidual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop
      (nonresidualPoolEquiv R I (Ideal.span {m}*F) Q0 hR hI
        (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P)).trans
      (nonresidualPoolEquiv_exponent R I F (Ideal.span {m}*F) Q0 hR hI
        (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P)


-- @@ L436-436 verbatim
end


-- @@ L438-438 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid

-- @@ L439-439 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L441-441 verbatim
section

-- @@ L442-451 verbatim
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

-- @@ L452-452 verbatim
include R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT


-- @@ L454-454 verbatim
local notation "splitIndex" => (goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT)


-- @@ L456-460 verbatim
noncomputable def goodMaskActivePrimeEquiv
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A) :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A ≃ A :=
  activePrimeUnionEquiv splitIndex A hactive


-- @@ L462-467 verbatim
lemma goodMaskActivePrimeEquiv_residual_val
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) :
    (goodMaskActivePrimeEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
      hbad hcop hA hT A hactive (Sum.inl P)).val.val.val=P.val := rfl


-- @@ L469-474 verbatim
lemma goodMaskActivePrimeEquiv_nonresidual_val
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:optionalPrimeActive splitIndex A) :
    (goodMaskActivePrimeEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
      hbad hcop hA hT A hactive (Sum.inr P)).val.val.val=P.val.val := rfl


-- @@ L476-490 verbatim
theorem goodMaskActivePrimeEquiv_exponent
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskActivePrimeEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
        hbad hcop hA hT A hactive P).val.val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val.val) P := by
  cases P with
  | inl P=>
    exact goodMaskFreePrimeFiberEquiv_exponent R I F Q0 hR hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop hA hT (Sum.inl P)
  | inr P=>
    exact goodMaskFreePrimeFiberEquiv_exponent R I F Q0 hR hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop hA hT (Sum.inr P.val)


-- @@ L492-492 verbatim
end


-- @@ L494-497 verbatim
lemma reflection_row_mask_bad (q:ℕ) (m:Eis) (F:Ideal Eis) :
    ∀P∈fixedBadPrimes,P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F := by
  intro P hP
  exact excluded_prime_dvd_row_mask q m F P (reflectionExcludedPrimes_bad q hP)


-- @@ L499-504 verbatim
lemma residual_coprime_free_base (q:ℕ) (hq:q≠0) (m:Eis) (F I:Ideal Eis) :
    IsCoprime (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)})
      (rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) := by
  have hc:=residual_coprime_fixed_conductor q hq m F I
  rw [reflectionConductor_ideal] at hc
  exact hc.of_isCoprime_of_dvd_left (dvd_mul_left _ (Ideal.span {(9:Eis)}))


-- @@ L506-506 verbatim
end CanonicalRowCompletion


-- @@ L508-509 verbatim
local instance (priority := 2000) residualLabelDecidableEq (A B:Type*) : DecidableEq (A⊕B) :=
  Classical.decEq _

-- @@ L510-510 verbatim
namespace CompletedGauss

-- @@ L511-511 verbatim
open ActualEisensteinCubic LocalReflectionBrackets

-- @@ L512-512 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L513-513 verbatim
variable {α β:Type*} [Fintype α] [Fintype β]


-- @@ L515-515 verbatim
def residualZeroLabel (e:β→Fin 3) : α⊕β→Fin 3 := Sum.elim (fun _=>0) e


-- @@ L517-534 verbatim
theorem sum_labels_drop_residual (f:(α⊕β→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (Sum.inl i)≠0)→f e=0) :
    (∑e:α⊕β→Fin 3,f e)=∑e:β→Fin 3,f (residualZeroLabel e) := by
  rw [←(Equiv.sumArrowEquivProdArrow α β (Fin 3)).symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_eq_single (fun _ : α=>0)]
  · rfl
  · intro d hd hn
    apply hzero
    have hx:∃i:α,d i≠0:=by
      by_contra h
      push Not at h
      exact hn (funext h)
    obtain ⟨i,hi⟩:=hx
    exact ⟨i,hi⟩
  · simp


-- @@ L536-544 verbatim
lemma reflectedBranch_residual_label_zero
    (P:α⊕β→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (hbad:∃i:α,e (Sum.inl i)≠0) (n b:Eis) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_eq_right hi]


-- @@ L546-556 verbatim
lemma reflectionExtractedDivisor_drop_residual
    (P:α⊕β→Ideal Eis) (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j e v=
      reflectionExtractedDivisor (fun i:β=>P (Sum.inr i)) (fun i=>j (Sum.inr i))
        (fun i=>e (Sum.inr i)) v := by
  simp only [reflectionExtractedDivisor,Fintype.prod_sum_type]
  have hz:(∏i:α,reflectionExtractedPrime (P (Sum.inl i)) (j (Sum.inl i)) (e (Sum.inl i)) v)=1 := by
    simp only [hj,reflectionExtractedPrime,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,
      false_and,false_or,ite_false,Finset.prod_const_one]
  rw [hz,one_mul]


-- @@ L558-571 verbatim
lemma reflectedBranch_drop_residual
    (P:α⊕β→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:β→Fin 3) (n b:Eis) :
    reflectedBranch P hg j (residualZeroLabel e) n b=
      (∏i:α,bracket (actualSextic (P (Sum.inl i)) (hg (Sum.inl i))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (Sum.inr i)) (fun i=>hg (Sum.inr i))
        (fun i=>j (Sum.inr i)) e n b := by
  simp only [reflectedBranch,Fintype.prod_sum_type,residualZeroLabel,Sum.elim_inl,Sum.elim_inr]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_true]


-- @@ L573-573 verbatim
end CompletedGauss

-- @@ L574-574 verbatim
end


-- @@ L576-576 verbatim
open scoped BigOperators Classical


-- @@ L578-579 verbatim
local instance (priority := 2000) residualEquivDecidableEq (A B:Type*) : DecidableEq (A⊕B) :=
  Classical.decEq _

-- @@ L580-580 verbatim
namespace CompletedGauss

-- @@ L581-581 verbatim
open ActualEisensteinCubic LocalReflectionBrackets

-- @@ L582-582 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L583-583 verbatim
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι]


-- @@ L585-586 verbatim
def residualLabelVia (E:α⊕β≃ι) (e:β→Fin 3) : ι→Fin 3 :=
  residualZeroLabel e ∘ E.symm


-- @@ L588-591 verbatim
omit [Fintype α] [Fintype β] [Fintype ι] in
lemma residualLabelVia_apply (E:α⊕β≃ι) (e:β→Fin 3) (i:α⊕β) :
    residualLabelVia E e (E i)=residualZeroLabel e i := by
  simp only [residualLabelVia,Function.comp_apply,Equiv.symm_apply_apply]


-- @@ L593-603 verbatim
theorem sum_labels_drop_residual_equiv (E:α⊕β≃ι) (f:(ι→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (E (Sum.inl i))≠0)→f e=0) :
    (∑e:ι→Fin 3,f e)=∑e:β→Fin 3,f (residualLabelVia E e) := by
  let e:=Equiv.arrowCongr E (Equiv.refl (Fin 3))
  rw [←e.sum_comp f]
  apply sum_labels_drop_residual
  intro l hl
  apply hzero
  obtain ⟨i,hi⟩:=hl
  refine ⟨i,?_⟩
  simpa only [e,Equiv.arrowCongr_apply,Function.comp_apply,Equiv.refl_apply,Equiv.symm_apply_apply] using hi


-- @@ L605-614 verbatim
omit [Fintype α] [Fintype β] in
lemma reflectedBranch_residual_zero_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:ι→Fin 3) (hbad:∃i:α,e (E (Sum.inl i))≠0) (n b:Eis) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (E (Sum.inl i)))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_eq_right hi]


-- @@ L616-628 verbatim
lemma reflectionExtractedDivisor_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j (residualLabelVia E e) v=
      reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e v := by
  calc
    _=reflectionExtractedDivisor (fun i=>P (E i)) (fun i=>j (E i)) (residualZeroLabel e) v := by
      unfold reflectionExtractedDivisor
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectionExtractedDivisor_drop_residual _ _ hj _ _


-- @@ L630-646 verbatim
lemma reflectedBranch_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (n b:Eis) :
    reflectedBranch P hg j (residualLabelVia E e) n b=
      (∏i:α,bracket (actualSextic (P (E (Sum.inl i))) (hg (E (Sum.inl i)))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (E (Sum.inr i))) (fun i=>hg (E (Sum.inr i)))
        (fun i=>j (E (Sum.inr i))) e n b := by
  calc
    _=reflectedBranch (fun i=>P (E i)) (fun i=>hg (E i)) (fun i=>j (E i)) (residualZeroLabel e) n b := by
      unfold reflectedBranch
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectedBranch_drop_residual _ _ _ hj _ _ _


-- @@ L648-648 verbatim
end CompletedGauss


-- @@ L650-650 verbatim
end


-- @@ L652-652 verbatim
end OAI
