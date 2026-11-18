import OAI.NumberTheory.DirichletL.ChineseRemainder.PrimaryCompletions


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
namespace ShortDraftCusp

-- @@ L77-77 verbatim
open scoped BigOperators Classical MatrixGroups Matrix


-- @@ L79-79 verbatim
section

-- @@ L80-80 verbatim
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase IdealGaussCRT

-- @@ L81-81 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L83-89 verbatim
lemma A4_bad_modulus_ne_zero (c0:Eis) (hc0:c0≠0) : ramifiedTraceLambda^3*c0≠0 := by
  apply mul_ne_zero _ hc0
  apply pow_ne_zero
  intro hz
  have he:=ramifiedEmbedding_traceLambda
  rw [hz,map_zero] at he
  exact eisLam_ne_zero he.symm


-- @@ L91-93 verbatim
def A4BadPhase (c0:Eis) (hc0:c0≠0) (d U x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (Ideal.Quotient.mk _ (-d*U*x))


-- @@ L95-102 verbatim
lemma A4BadPhase_eq (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    A4BadPhase c0 hc0 d U x =
      ShortDraftTrace.breveE (-(eisEmbedding d*eisEmbedding U*(eisEmbedding x/eisLam^4))/eisEmbedding c0) := by
  change ShortDraftTrace.breveE
    (eisEmbedding (-d*U*x)/(eisEmbedding (ramifiedTraceLambda^3*c0)*eisLam))=_
  simp only [map_mul,map_pow,map_neg,ramifiedEmbedding_traceLambda]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc0]


-- @@ L104-105 verbatim
noncomputable local instance A4phaseField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

-- @@ L106-107 verbatim
noncomputable local instance A4phaseFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


-- @@ L109-156 verbatim
theorem A4_phase_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
      (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹) := by
  let hr : (∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hs:=ShortDraftCRT.normalized_crt_pair eisEmbedding ShortDraftTrace.breveE
    ramifiedTraceLambda c0 (∏i,p i) d x U w
    (by simpa only [ramifiedEmbedding_traceLambda] using eisLam_ne_zero)
    (eisEmbedding_ne_zero hc0) (eisEmbedding_ne_zero hr) hbez
  simp only [ramifiedEmbedding_traceLambda] at hs
  rw [hs,←A4BadPhase_eq c0 hc0 d U x]
  congr 1
  have he : ShortDraftTrace.breveE (eisEmbedding (-d*w*x)/(eisLam*eisEmbedding (∏i,p i)))=
      quotientTrace (∏i,p i) hr (Ideal.Quotient.mk _ (-d*w*x)) := by
    simp only [quotientTrace,eisTraceModChar,traceModChar_mk]
    congr 1
    rw [mul_comm eisLam]
  rw [he,addChar_finite_crt_factor (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [productElementCRT_mk]
  obtain ⟨t,v,hlocal⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
  have hc:=coordinate_trace_character p hp hcop i t v hlocal
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (quotientTrace (∏i,p i) hr) i (Ideal.Quotient.mk _ (-d*w*x))=_
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates (∏i,p i) hr) i
    (Ideal.Quotient.mk _ (-d*w*x))=_
  rw [hc]
  change quotientTrace (p i) (hp i)
    (Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (-d*w*x))=_
  apply congrArg (quotientTrace (p i) (hp i))
  have hinv:=A4_complement_inverse p c0 U w hbez i v t hlocal
  have hphase:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).2
  rw [hinv] at hphase
  convert hphase using 1 ; simp only [map_mul,map_neg] ; ring


-- @@ L158-158 verbatim
end


-- @@ L160-160 verbatim
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase

-- @@ L161-161 verbatim
open CompletedGauss LocalReflectionBrackets

-- @@ L162-162 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L163-164 verbatim
noncomputable local instance A4frequencyField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

-- @@ L165-166 verbatim
noncomputable local instance A4frequencyFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


-- @@ L168-199 verbatim
theorem A3_A4_frequency_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    star (eisEmbedding (CubicJacobiGlobal.symbol a (∏i,p i)))*
      ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (h i) := by
  rw [conjugate_symbol_product_frequency p hg a σ h ha,
    A4_phase_product p hp hcop a b c0 d U w x hc0 hdet hbez σ ε h ha hε]
  calc
    _ = A4BadPhase c0 hc0 d U x *
      ((∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        ((σ i:Eis⧸Ideal.span {p i})*h i))*
       ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹)) := by ring
    _ = _ := by
      congr 1
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hn:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).1
      simp only [frequencyMultiplier,ite_eq_right hn]


-- @@ L201-209 verbatim
lemma A4BadPhase_eq_of_residue (c0:Eis) (hc0:c0≠0) (d U d' U' x:Eis)
    (hres:ramifiedTraceLambda^3*c0∣d*U-d'*U') :
    A4BadPhase c0 hc0 d U x=A4BadPhase c0 hc0 d' U' x := by
  unfold A4BadPhase
  congr 1
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd:=dvd_mul_of_dvd_left hres (-x)
  convert hd using 1 ; ring


-- @@ L211-214 verbatim
lemma A4BadPhase_norm (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    ‖A4BadPhase c0 hc0 d U x‖=1 := by
  rw [A4BadPhase_eq]
  exact breveE_norm _


-- @@ L216-216 verbatim
end ShortDraftCusp


-- @@ L218-218 verbatim
open scoped BigOperators Classical


-- @@ L220-220 verbatim
namespace IdealGaussCRT

-- @@ L221-221 verbatim
open CubicEisenstein


-- @@ L223-233 verbatim
lemma finiteAdditiveFourierCoeff_mulShift {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (k h : R) :
    finiteAdditiveFourierCoeff (ψ.mulShift k) φ h=
      finiteAdditiveFourierCoeff ψ φ (k*h) := by
  unfold finiteAdditiveFourierCoeff
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [AddChar.mulShift_apply]
  congr 2
  ring


-- @@ L235-249 verbatim
theorem finite_fourier_weighted_shift_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (ψi : ∀i,AddChar (R i) ℂ) (k : ∀i,(R i)ˣ)
    (hψ : ∀i,coordinateAddChar R e ψ i=(ψi i).mulShift (k i:R i))
    (φ κ : ∀i,R i→ℂ) :
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h *
      ∏i,κ i ((k i:R i)*e h i))=
      ∏i,∑h:R i,finiteAdditiveFourierCoeff (ψi i) (φ i) h*κ i h := by
  rw [finite_fourier_weighted_crt R e ψ φ (fun i h=>κ i ((k i:R i)*h))]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [hψ,finiteAdditiveFourierCoeff_mulShift]
  exact Equiv.sum_comp (k i).mulLeft
    (fun h:R i=>finiteAdditiveFourierCoeff (ψi i) (φ i) h*κ i h)


-- @@ L251-277 verbatim
theorem finiteAdditiveFourierCoeff_pair {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    [Fintype T] [Fintype R] [Fintype S]
    (e : T≃+*R×S) (ψ : AddChar T ℂ) (φ : R→ℂ) (f : S→ℂ) (h : T) :
    finiteAdditiveFourierCoeff ψ (fun t=>φ (e t).1*f (e t).2) h=
      finiteAdditiveFourierCoeff (leftAddChar e ψ) φ (e h).1 *
      finiteAdditiveFourierCoeff (rightAddChar e ψ) f (e h).2 := by
  have hs : (∑x:T,(φ (e x).1*f (e x).2)*ψ (-h*x))=
      (∑x:R,φ x*leftAddChar e ψ (-(e h).1*x))*
        (∑y:S,f y*rightAddChar e ψ (-(e h).2*y)) := by
    calc
      _ = ∑x:T,(φ (e x).1*leftAddChar e ψ (-(e h).1*(e x).1))*
          (f (e x).2*rightAddChar e ψ (-(e h).2*(e x).2)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [addChar_crt_factor e ψ (-h*x)]
        simp only [map_mul,map_neg,Prod.fst_mul,Prod.snd_mul,Prod.fst_neg,Prod.snd_neg]
        ring
      _ = ∑x:R×S,(φ x.1*leftAddChar e ψ (-(e h).1*x.1))*
          (f x.2*rightAddChar e ψ (-(e h).2*x.2)) :=
        Equiv.sum_comp e.toEquiv (fun x:R×S=>(φ x.1*leftAddChar e ψ (-(e h).1*x.1))*
          (f x.2*rightAddChar e ψ (-(e h).2*x.2)))
      _ = _ := by rw [Fintype.sum_prod_type,Finset.sum_mul_sum]
  have hc : (Fintype.card T:ℂ)=(Fintype.card R:ℂ)*(Fintype.card S:ℂ) := by
    rw [Fintype.card_congr e.toEquiv,Fintype.card_prod,Nat.cast_mul]
  simp only [finiteAdditiveFourierCoeff,hs,hc]
  ring


-- @@ L279-279 verbatim
end IdealGaussCRT


-- @@ L281-281 verbatim
namespace LocalReflectionBrackets

-- @@ L282-282 verbatim
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss

-- @@ L283-283 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L284-285 verbatim
noncomputable local instance canonicalShiftField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

-- @@ L286-287 verbatim
noncomputable local instance canonicalShiftFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


-- @@ L289-322 verbatim
theorem canonical_finite_reflection_shifted_crt {ι T : Type*} [Fintype ι]
    [CommRing T] [Fintype T]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e : T≃+*∀i,Eis⧸P i) (ψ : AddChar T ℂ)
    (ψi : ∀i,AddChar (Eis⧸P i) ℂ) (hψi : ∀i,(ψi i).IsPrimitive)
    (k : ∀i,(Eis⧸P i)ˣ)
    (hshift : ∀i,coordinateAddChar (fun i=>Eis⧸P i) e ψ i=(ψi i).mulShift (k i:Eis⧸P i))
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i) :
    let χ := fun i=>actualSextic (P i) (hg i)
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let χ := fun i=>actualSextic (P i) (hg i)
  let f := fun i=>frequencyRow (χ i) (ψi i) (j i) (σ i) (ε i) (x i)
  have hsum : (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=
      ∑h:∀i,Eis⧸P i,∏i,f i (h i) := by
    rw [finite_fourier_weighted_shift_crt (fun i=>Eis⧸P i) e ψ ψi k hshift
      (fun i t=>(χ i^j i) t) (fun i=>frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i))]
    exact Fintype.prod_sum f
  have hactive (i : ι) : (∑h:(Eis⧸P i)ˣ,f i h)=
      (((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i) := by
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψi i)
      (hψi i) (j i) (hj i) (σ i) (ε i) (x i)
  have hzero (i : ι) : f i 0=if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0 := by
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψi i) (j i) (hj i) (σ i) (ε i) (x i)
  change (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=_
  rw [hsum,FixedRayActiveSet.product_sum_by_active_set (fun i=>Eis⧸P i) f]
  simp only [hactive,hzero]
  rfl


-- @@ L324-324 verbatim
end LocalReflectionBrackets


-- @@ L326-326 verbatim
namespace FiniteGaussPhase


-- @@ L328-328 verbatim
section

-- @@ L329-329 verbatim
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT

-- @@ L330-330 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L332-353 verbatim
theorem exists_product_trace_shifts {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∃k : ∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k i:Eis⧸Ideal.span {p i})=1) ∧
      ∀i,coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k i:Eis⧸Ideal.span {p i}) := by
  have hone (i : ι) : ∃k : (Eis⧸Ideal.span {p i})ˣ,
      Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k:Eis⧸Ideal.span {p i})=1 ∧
      coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k:Eis⧸Ideal.span {p i}) := by
    obtain ⟨u,v,hbez⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
    have hv : Ideal.Quotient.mk (Ideal.span {p i}) v*
        Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)=1 := by
      simpa only [mul_comm] using bezout_inverse_left hbez
    refine ⟨Units.mkOfMulEqOne _ _ hv,?_,?_⟩
    · simpa only [Units.val_mkOfMulEqOne,mul_comm] using hv
    · exact coordinate_trace_character p hp hcop i u v hbez
  choose k hki hkψ using hone
  exact ⟨k,hki,hkψ⟩


-- @@ L355-359 verbatim
noncomputable def productTraceShift {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∀i,(Eis⧸Ideal.span {p i})ˣ :=
  (exists_product_trace_shifts p hp hcop).choose


-- @@ L361-366 verbatim
lemma productTraceShift_inverse {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*
      (productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})=1 :=
  (exists_product_trace_shifts p hp hcop).choose_spec.1 i


-- @@ L368-375 verbatim
lemma productTraceShift_character {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) (i:ι) :
    coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
        (quotientTrace (p i) (hp i)).mulShift
          (productTraceShift p hp hcop i:Eis⧸Ideal.span {p i}) :=
  (exists_product_trace_shifts p hp hcop).choose_spec.2 i


-- @@ L377-377 verbatim
end


-- @@ L379-379 verbatim
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT

-- @@ L380-380 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L382-395 verbatim
theorem product_trace_fourier_factor {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ : ∀i,(Eis⧸Ideal.span {p i})→ℂ) (H:Eis⧸Ideal.span {∏i,p i}) :
    finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H=
    ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i)
      ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i) := by
  rw [finiteAdditiveFourierCoeff_crt]
  apply Finset.prod_congr rfl
  intro i hi
  rw [productTraceShift_character,finiteAdditiveFourierCoeff_mulShift]


-- @@ L397-409 verbatim
theorem product_trace_fourier_weighted {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ κ : ∀i,(Eis⧸Ideal.span {p i})→ℂ) :
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H *
      ∏i,κ i ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
    ∏i,∑h:Eis⧸Ideal.span {p i},finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i) h*κ i h := by
  exact finite_fourier_weighted_shift_crt (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop) _ (fun i=>quotientTrace (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop) φ κ


-- @@ L411-411 verbatim
end FiniteGaussPhase


-- @@ L413-413 verbatim
namespace LocalReflectionBrackets

-- @@ L414-414 verbatim
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss FiniteGaussPhase

-- @@ L415-415 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L416-417 verbatim
noncomputable local instance productReflectionField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

-- @@ L418-419 verbatim
noncomputable local instance productReflectionFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _


-- @@ L421-452 verbatim
theorem canonical_product_reflection_crt {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hchar : ∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (x : ∀i,Eis⧸Ideal.span {p i})
    [Fintype (Eis⧸Ideal.span {∏i,p i})] :
    let χ := fun i=>actualSextic (Ideal.span {p i}) (hg i)
    let ψ := quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
    let ψi := fun i=>quotientTrace (p i) (hp i)
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff ψ
      (principalSexticRow (fun i=>Ideal.span {p i}) hcop hg j (∏i,p i)
        (span_finset_prod Finset.univ p)) H *
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i)
        ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸Ideal.span {p i}):ℂ)⁻¹ else 0) := by
  let e:=productElementCRT p hcop
  have hrow : principalSexticRow (fun i=>Ideal.span {p i}) hcop hg j (∏i,p i)
      (span_finset_prod Finset.univ p)=
      fun t=>∏i,(actualSextic (Ideal.span {p i}) (hg i)^j i) (e t i) := by
    funext t
    rfl
  dsimp only
  rw [hrow]
  exact canonical_finite_reflection_shifted_crt (fun i=>Ideal.span {p i}) e _
    (fun i=>quotientTrace (p i) (hp i))
    (fun i=>GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop)
    hg hchar j hj σ ε x


-- @@ L454-454 verbatim
end LocalReflectionBrackets


-- @@ L456-456 verbatim
open scoped Classical BigOperators


-- @@ L458-458 verbatim
namespace ShortDraftCusp

-- @@ L459-459 verbatim
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT

-- @@ L460-460 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L462-475 verbatim
theorem A4BadPhase_strong_sector (M c0 r r0 d d0 U U0 x:Eis) (hc0:c0≠0)
    (hM:ramifiedTraceLambda^3∣M) (hc:c0∣M)
    (hr:M^2∣r-r0) (hd:M*c0∣d-d0)
    (hcop:IsCoprime (ramifiedTraceLambda^3*c0) r)
    (hU:ramifiedTraceLambda^3*c0∣U*r-1)
    (hU0:ramifiedTraceLambda^3*c0∣U0*r0-1) :
    A4BadPhase c0 hc0 d U x=A4BadPhase c0 hc0 d0 U0 x := by
  obtain ⟨hrr,hdd⟩:=ShortDraftCRT.strong_sector_additive_congruences
    M ramifiedTraceLambda c0 r r0 d d0 hM hc hr hd
  apply A4BadPhase_eq_of_residue
  have he:=ShortDraftCRT.inverse_weight_residue_congr
    (ramifiedTraceLambda^3*c0) r r0 U U0 d d0 hcop hrr hU hU0 hdd
  have hn:=dvd_neg.mpr he
  convert hn using 1 ; ring


-- @@ L477-480 verbatim
def A4PhaseFromResidue (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (v*Ideal.Quotient.mk _ x)


-- @@ L482-486 verbatim
lemma A4BadPhase_as_fixed_residue (c0:Eis) (hc0:c0≠0) (d U:Eis) :
    A4BadPhase c0 hc0 d U=
      A4PhaseFromResidue c0 hc0 (Ideal.Quotient.mk _ (-d*U)) := by
  funext x
  simp only [A4BadPhase,A4PhaseFromResidue,map_mul]


-- @@ L488-496 verbatim
lemma A4PhaseFromResidue_range (c0:Eis) (hc0:c0≠0) :
    (Set.range (A4PhaseFromResidue c0 hc0)).Finite ∧
      (Set.range (A4PhaseFromResidue c0 hc0)).ncard≤
        Ideal.absNorm (Ideal.span {ramifiedTraceLambda^3*c0}) := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  refine ⟨Set.finite_range _,?_⟩
  have h:=Set.ncard_image_le (s:=Set.univ) (f:=A4PhaseFromResidue c0 hc0)
  simpa only [Set.image_univ,Set.ncard_univ,Ideal.absNorm_apply,Submodule.cardQuot_apply] using h


-- @@ L498-498 verbatim
end ShortDraftCusp


-- @@ L500-500 verbatim
namespace CompletedGauss

-- @@ L501-501 verbatim
open ActualEisensteinCubic CubicEisenstein

-- @@ L502-502 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L504-504 verbatim
variable (Ψ Φ:Eis→*ℂ) (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n)

-- @@ L505-505 verbatim
include h


-- @@ L507-511 verbatim
lemma columnWeight_congr_primary (I:Ideal Eis) : columnWeight Ψ I=columnWeight Φ I := by
  by_cases hi:primaryGenerator I=0
  · simp only [columnWeight,squarefreeGaussCoefficient,hi,ne_eq,not_true_eq_false,and_false,
      dite_false,zero_mul]
  · rw [columnWeight,columnWeight,h _ (primaryGenerator_spec I hi).2]


-- @@ L513-520 verbatim
lemma cubeWeight_congr_primary (I:Ideal Eis) : cubeWeight Ψ I=cubeWeight Φ I := by
  change star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Ψ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)=star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Φ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)
  by_cases hi:primaryGenerator I=0
  · simp only [hi,FiniteGaussPhase.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
      div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
  · rw [h _ (primaryGenerator_spec I hi).2]


-- @@ L522-528 verbatim
theorem completedT_congr_primary (W:ℝ→ℂ) (X:ℝ) : completedT Ψ W X=completedT Φ W X := by
  unfold completedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]


-- @@ L530-533 verbatim
lemma completedMellinCoefficient_congr_primary (p:CompletedMellinIndex) :
    completedMellinCoefficient Ψ p=completedMellinCoefficient Φ p := by
  unfold completedMellinCoefficient
  rw [columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]


-- @@ L535-539 verbatim
theorem completedBesselProfile_congr_primary (q:ℝ) :
    completedBesselProfile Ψ q=completedBesselProfile Φ q := by
  have he:completedMellinCoefficient Ψ=completedMellinCoefficient Φ:=
    funext (completedMellinCoefficient_congr_primary Ψ Φ h)
  simp only [completedBesselProfile,he]


-- @@ L541-541 verbatim
end CompletedGauss


-- @@ L543-543 verbatim
namespace CubicEisenstein

-- @@ L544-544 verbatim
open ActualEisensteinCubic

-- @@ L545-545 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L546-551 verbatim
lemma fixedThetaTwist_congr_primary (Ψ Φ:Eis→*ℂ)
    (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n) : fixedThetaTwist Ψ=fixedThetaTwist Φ := by
  funext n
  by_cases hn:lambda^2∣n-1
  · rw [fixedThetaTwist_primary Ψ n hn,fixedThetaTwist_primary Φ n hn,h n hn]
  · rw [fixedThetaTwist_not_primary Ψ n hn,fixedThetaTwist_not_primary Φ n hn]

-- @@ L552-552 verbatim
end CubicEisenstein


-- @@ L554-554 verbatim
open scoped Classical BigOperators


-- @@ L556-556 verbatim
namespace ShortDraftCRT

-- @@ L557-557 verbatim
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT

-- @@ L558-558 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L559-559 verbatim
variable {ι:Type*} [Fintype ι]


-- @@ L561-562 verbatim
def finiteCrossNumerator (a c l:Eis) (p h:ι→Eis) : Eis :=
  a*(∏i,p i)+l^2*c*∑i,h i*cofactor p i


-- @@ L564-565 verbatim
lemma prime_dvd_other_cofactor (p:ι→Eis) {i k:ι} (hik:i≠k) : p i∣cofactor p k := by
  exact Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hik,Finset.mem_univ i⟩)


-- @@ L567-585 verbatim
lemma finiteCrossNumerator_local (a c l:Eis) (p h:ι→Eis) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (finiteCrossNumerator a c l p h)=
      Ideal.Quotient.mk (Ideal.span {p i}) (l^2*c*cofactor p i)*
        Ideal.Quotient.mk (Ideal.span {p i}) (h i) := by
  let q:=Ideal.Quotient.mk (Ideal.span {p i})
  have hz:q (∏k,p k)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨cofactor p i, (prime_mul_cofactor p i).symm⟩
  have hs:(∑k,q (h k)*q (cofactor p k))=q (h i)*q (cofactor p i) := by
    apply Finset.sum_eq_single i
    · intro k hk hki
      have hk0:q (cofactor p k)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr (prime_dvd_other_cofactor p hki.symm))
      rw [hk0,mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  change q (finiteCrossNumerator a c l p h)=q (l^2*c*cofactor p i)*q (h i)
  simp only [finiteCrossNumerator,map_add,map_mul,map_sum,map_pow,hz,mul_zero,zero_add,hs]
  ring


-- @@ L587-590 verbatim
lemma finiteCrossNumerator_fixed (N a c l:Eis) (p h:ι→Eis)
    (hh:∀i,N∣h i) : N∣finiteCrossNumerator a c l p h-a*(∏i,p i) := by
  have hs:N∣∑i,h i*cofactor p i:=Finset.dvd_sum (fun i _=>dvd_mul_of_dvd_left (hh i) _)
  convert dvd_mul_of_dvd_right hs (l^2*c) using 1 ; simp [finiteCrossNumerator]


-- @@ L592-602 verbatim
lemma finiteCrossNumerator_fixed_sector {κ:Type*} [Fintype κ]
    (M a c l:Eis) (p h:ι→Eis) (p0 h0:κ→Eis)
    (hc:c∣M) (hh:∀i,M^2∣h i) (hh0:∀i,M^2∣h0 i)
    (hr:M^2∣(∏i,p i)-(∏i,p0 i)) :
    M*c∣finiteCrossNumerator a c l p h-finiteCrossNumerator a c l p0 h0 := by
  have hmc:M*c∣M^2:=by simpa only [pow_two] using mul_dvd_mul_left M hc
  apply hmc.trans
  have h1:=finiteCrossNumerator_fixed (M^2) a c l p h hh
  have h0:=finiteCrossNumerator_fixed (M^2) a c l p0 h0 hh0
  have h2:=dvd_mul_of_dvd_right hr a
  convert dvd_sub (dvd_add h1 h2) h0 using 1 ; ring


-- @@ L604-627 verbatim
lemma finiteCrossNumerator_coprime (a c l:Eis) (p h:ι→Eis)
    (hbase:IsCoprime a c) (hpair:Pairwise (Function.onFun IsCoprime p))
    (hc:∀i,IsCoprime c (p i)) (hl:∀i,IsCoprime l (p i))
    (hh:∀i,IsCoprime (h i) (p i)) :
    IsCoprime (finiteCrossNumerator a c l p h) (c*∏i,p i) := by
  have hmodc:c∣finiteCrossNumerator a c l p h-a*(∏i,p i):=by
    refine ⟨l^2*(∑i,h i*cofactor p i),?_⟩
    unfold finiteCrossNumerator
    ring
  have hcR:IsCoprime c (∏i,p i):=IsCoprime.prod_right (fun i _=>hc i)
  have hca:IsCoprime c (finiteCrossNumerator a c l p h):=
    (CanonicalRowCompletion.isCoprime_congr_mod c _ _ hmodc).mpr (hbase.symm.mul_right hcR)
  apply hca.symm.mul_right
  apply IsCoprime.prod_right
  intro i hi
  have hcof:IsCoprime (p i) (cofactor p i):=
    IsCoprime.prod_right (fun k hk=>hpair (Ne.symm (Finset.mem_erase.mp hk).1))
  have hterm:IsCoprime (p i) (l^2*c*cofactor p i*h i):=
    (((hl i).symm.pow_right : IsCoprime (p i) (l^2)).mul_right (hc i).symm).mul_right hcof |>.mul_right (hh i).symm
  have he:=finiteCrossNumerator_local a c l p h i
  rw [←map_mul] at he
  have hd:p i∣finiteCrossNumerator a c l p h-l^2*c*cofactor p i*h i:=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ((CanonicalRowCompletion.isCoprime_congr_mod (p i) _ _ hd).mpr hterm).symm


-- @@ L629-629 verbatim
end ShortDraftCRT


-- @@ L631-631 verbatim
end


-- @@ L633-633 verbatim
end OAI
