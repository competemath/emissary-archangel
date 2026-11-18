import OAI.NumberTheory.DirichletL.RowCompletion.ControlledPrimeStrata
import OAI.NumberTheory.DirichletL.RowCompletion.FreePrimePools


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open MulChar AddChar

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L12-12 verbatim
open scoped Topology

-- @@ L13-13 verbatim
open MeasureTheory Real

-- @@ L14-14 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L15-15 verbatim
open Finset Complex

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open scoped Classical

-- @@ L18-18 verbatim
open Filter Real Asymptotics

-- @@ L19-19 verbatim
open ActualEisensteinCubic

-- @@ L20-20 verbatim
open Filter

-- @@ L21-21 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L22-22 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L23-23 verbatim
open Filter

-- @@ L24-24 verbatim
open scoped Topology

-- @@ L25-25 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L26-26 verbatim
open MulChar AddChar

-- @@ L27-27 verbatim
open Filter Asymptotics

-- @@ L28-28 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L29-29 verbatim
open Filter

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open MulChar AddChar

-- @@ L32-32 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L33-33 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L34-34 verbatim
open scoped Topology

-- @@ L35-35 verbatim
open Filter Asymptotics

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L41-41 verbatim
open Filter Asymptotics

-- @@ L42-42 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L43-43 verbatim
open scoped Topology

-- @@ L44-44 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L45-45 verbatim
open Filter

-- @@ L46-46 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L47-47 verbatim
open scoped Topology

-- @@ L48-48 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L49-49 verbatim
open scoped Topology

-- @@ L50-50 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L51-51 verbatim
open scoped Topology

-- @@ L52-52 verbatim
open MeasureTheory Real

-- @@ L53-53 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L59-59 verbatim
open scoped BigOperators Classical

-- @@ L60-60 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L61-61 verbatim
open scoped BigOperators Classical

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L65-65 verbatim
open scoped BigOperators Classical

-- @@ L66-66 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L67-67 verbatim
open MeasureTheory Set

-- @@ L68-68 verbatim
open scoped BigOperators

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open scoped BigOperators Classical

-- @@ L71-71 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L72-72 verbatim
open scoped BigOperators

-- @@ L73-73 verbatim
open scoped BigOperators

-- @@ L74-74 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L75-75 verbatim
open scoped BigOperators Classical


-- @@ L77-77 verbatim
open scoped BigOperators Classical ContDiff


-- @@ L79-79 verbatim
namespace CompletedGauss

-- @@ L80-80 verbatim
open ActualEisensteinCubic CubicEisenstein

-- @@ L81-81 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L82-82 verbatim
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι]


-- @@ L84-101 verbatim
lemma nonzeroDualDilation_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1) (e:β→Fin 3)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    nonzeroDualDilation
      (reflectionExtractedDivisor P j (residualLabelVia E e) 1)
      (reflectionExtractedDivisor P j (residualLabelVia E e) 2)
      (reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) j _ 1)
      (reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) j _ 2) x=
    nonzeroDualDilation
      (reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e 1)
      (reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e 2)
      (reflectionExtractedDivisor_ne_zero _ (fun _i=>NeZero.ne _) _ _ 1)
      (reflectionExtractedDivisor_ne_zero _ (fun _i=>NeZero.ne _) _ _ 2) x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> apply Subtype.ext <;>
      simp only [nonzeroDualDilation,reflectionExtractedDivisor_drop_residual_equiv E P j hj]


-- @@ L103-114 verbatim
lemma unextractedCuspCoefficient_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1) (e:β→Fin 3)
    (ρ q:ℝ) (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ) (m:ℕ) (I J:Ideal Eis) :
    unextractedCuspCoefficient P hg j (residualLabelVia E e) ρ q η σ m I J=
      (σ m*(∏i:α,LocalReflectionBrackets.bracket (actualSextic (P (E (Sum.inl i))) (hg (E (Sum.inl i)))) 1
        (Ideal.Quotient.mk _ (primaryGenerator I*(primaryGenerator J)^3)))*
        η m I J*reflectedBranch (fun i:β=>P (E (Sum.inr i))) (fun i=>hg (E (Sum.inr i)))
          (fun i=>j (E (Sum.inr i))) e (primaryGenerator I) (primaryGenerator J))/
        ((CompletedDyadic.ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [unextractedCuspCoefficient,reflectedBranch_drop_residual_equiv E P hg j hj]
  ring


-- @@ L116-116 verbatim
end CompletedGauss


-- @@ L118-118 verbatim
namespace CubicEisenstein

-- @@ L119-119 verbatim
open ActualEisensteinCubic CompletedGauss CompletedDyadic

-- @@ L120-120 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L121-121 verbatim
namespace FixedFourierGeometry

-- @@ L122-122 verbatim
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)

-- @@ L123-123 verbatim
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι] {p:ι→Eis} {N:Eis}


-- @@ L125-135 verbatim
omit [Fintype α] [Fintype β] in
lemma stratumBranchTerm_residual_zero_equiv (E:α⊕β≃ι)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (hres:∀i:α,j (E (Sum.inl i))=1)
    (u:Eisˣ) (e:ι→Fin 3) (hbad:∃i:α,e (E (Sum.inl i))≠0)
    (W:ℝ→ℂ) (X:ℝ) (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    G.stratumBranchTerm D hp hg j u e W X x=0 := by
  dsimp only [stratumBranchTerm,rawDualKernelTerm,unextractedCuspCoefficient]
  rw [reflectedBranch_residual_zero_equiv E _ hg j hres e hbad,mul_zero,zero_div,zero_mul]


-- @@ L137-186 verbatim
theorem smoothedValue_eq_nonresidual_equiv (E:α⊕β≃ι)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0)
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6) (hres:∀i:α,j (E (Sum.inl i))=1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hN hr G.primary G.shape hp G.denominator_ne_zero hg j W X=
      fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:β→Fin 3,
          let P:β→Ideal Eis:=fun i=>Ideal.span {p (E (Sum.inr i))}
          let jβ:β→ℕ:=fun i=>j (E (Sum.inr i))
          let A:=reflectionExtractedDivisor P jβ e 1
          let B:=reflectionExtractedDivisor P jβ e 2
          let hA:=reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) jβ e 1
          let hB:=reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) jβ e 2
          ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
            G.stratumBranchTerm D hp hg j u (residualLabelVia E e) W X (nonzeroDualDilation A B hA hB x) := by
  rw [G.smoothedValue_eq_extracted_branch_sums D hN hr hp hcop hg hchar j hj W a b ha hsupp hW X hX]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro u
  let f:(ι→Fin 3)→ℂ:=fun e=>
    ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      G.stratumBranchTerm D hp hg j u e W X
        (nonzeroDualDilation
          (reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1)
          (reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2)
          (reflectionExtractedDivisor_ne_zero _ (fun i=>NeZero.ne _) j e 1)
          (reflectionExtractedDivisor_ne_zero _ (fun i=>NeZero.ne _) j e 2) x)
  change (∑e,f e)=_
  have hz:∀e,(∃i:α,e (E (Sum.inl i))≠0)→f e=0 := by
    intro e he
    calc
      f e=∑'(_x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal),(0:ℂ) := by
        apply tsum_congr
        intro x
        exact G.stratumBranchTerm_residual_zero_equiv E D hp hg j hres u e he W X _
      _=0:=tsum_zero
  rw [sum_labels_drop_residual_equiv E f hz]
  apply Finset.sum_congr rfl
  intro e he
  dsimp only [f]
  apply tsum_congr
  intro x
  rw [nonzeroDualDilation_residual_equiv E _ j hres]


-- @@ L188-188 verbatim
end FixedFourierGeometry

-- @@ L189-189 verbatim
end CubicEisenstein


-- @@ L191-191 verbatim
open scoped BigOperators Classical MatrixGroups


-- @@ L193-193 verbatim
namespace CubicEisenstein


-- @@ L195-195 verbatim
section

-- @@ L196-196 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota CubicJacobiGlobal

-- @@ L197-197 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L199-200 verbatim
noncomputable local instance primeQuotientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _


-- @@ L202-207 verbatim
def primeInactiveFourierWeight {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (A:Finset ι) : ℂ :=
  ∏i∈(Finset.univ:Finset ι)\A,
    finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun x=>(actualSextic (Ideal.span {p i}) (hg i)^j i) x) 0


-- @@ L209-229 verbatim
lemma primeRow_fourier_by_active {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (n:Eis) :
    finiteSexticRow (fun i=>Ideal.span {p i}) hg j n=
    ∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
      ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
        ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val)
          (fun i:A=>hp i.val) (fun i:A=>hg i.val) (fun i=>j i.val) v*
        ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n) := by
  let (i:ι) : Field (Eis⧸Ideal.span {p i}) := Ideal.Quotient.field _
  have hpow:(Finset.univ:Finset ι).powerset=(Finset.univ:Finset (Finset ι)):=by
    ext A
    simp only [Finset.mem_powerset,Finset.subset_univ,Finset.mem_univ]
  have hFourier:=FixedRayActiveSet.fourier_inversion_by_active_set
    (fun i=>Eis⧸Ideal.span {p i})
    (fun i=>quotientTrace (p i) (hp i))
    (fun i=>GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (fun i x=>(actualSextic (Ideal.span {p i}) (hg i)^j i) x)
    (fun i=>Ideal.Quotient.mk (Ideal.span {p i}) n)
  simpa only [hpow,finiteSexticRow,primeInactiveFourierWeight,
    ControlledStratumArithmetic.fourierWeight] using hFourier


-- @@ L231-240 verbatim
def activeStratumDatum {ι:Type*} [Fintype ι]
    (p:ι→Eis) (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
    {N a0 c0:Eis} {mode:Bool}
    (D:∀A:Finset ι,ControlledStratumArithmetic (fun i:A=>p i.val) N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hc0:c0≠0)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (A:Finset ι) (v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ) : SourceCuspDatum :=
  (D A).datum hN (primary_finset_product Finset.univ (fun i:A=>p i.val)
    (fun i _=>hprimary i.val)) hbase s (fun i=>hp i.val) hc0 v


-- @@ L242-296 verbatim
theorem activeStratum_fourier_multiplier {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {N a0 c0:Eis} {mode:Bool}
    (D:∀A:Finset ι,ControlledStratumArithmetic (fun i:A=>p i.val) N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hc0:c0≠0)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)) (n:Eis) :
    (∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
      ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
        ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val) (fun i:A=>hp i.val) (fun i:A=>hg i.val)
          (fun i=>j i.val) v*
        ShortDraftTrace.breveE (-cuspFrequency n*
          (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point))=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        finiteSexticRow (fun i=>Ideal.span {p i}) hg j n := by
  have hlocal (A:Finset ι) (v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ) :
      ShortDraftTrace.breveE (-cuspFrequency n*
        (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point)=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n) :=
    (D A).datum_fourier_phase hN
      (primary_finset_product Finset.univ (fun i:A=>p i.val) (fun i _=>hprimary i.val))
      hbase s (fun i=>hp i.val) hc0 v n
  calc
    _=∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
        ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
          ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val)
            (fun i:A=>hp i.val) (fun i:A=>hg i.val) (fun i=>j i.val) v*
          (ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
            ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n)):=by
      apply Finset.sum_congr rfl
      intro A hA
      apply congrArg (fun z:ℂ=>primeInactiveFourierWeight p hp hg j A*z)
      apply Finset.sum_congr rfl
      intro v hv
      exact congrArg (fun z:ℂ=>ControlledStratumArithmetic.fourierWeight
        (p:=fun i:A=>p i.val) (fun i:A=>hp i.val) (fun i:A=>hg i.val)
        (fun i=>j i.val) v*z) (hlocal A v)
    _=ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        (∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
            ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val)
              (fun i:A=>hp i.val) (fun i:A=>hg i.val) (fun i=>j i.val) v*
            ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _=_:=congrArg (fun z:ℂ=>
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*z)
      (primeRow_fourier_by_active p hp hg j n).symm


-- @@ L298-298 verbatim
end


-- @@ L300-300 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota CubicJacobiGlobal

-- @@ L301-301 verbatim
open CanonicalRowCompletion

-- @@ L302-302 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L304-305 verbatim
noncomputable local instance fixedActiveQuotientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _


-- @@ L307-308 verbatim
abbrev FixedActiveCuspIndex {ι:Type*} (c:Eis) (p:ι→Eis) :=
  Σ_h:Eis⧸Ideal.span {c},ΣA:Finset ι,∀i:A,(Eis⧸Ideal.span {p i.val})ˣ


-- @@ L310-310 verbatim
variable {ι:Type*} [Fintype ι] (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]

-- @@ L311-311 verbatim
variable (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)

-- @@ L312-312 verbatim
variable (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)

-- @@ L313-313 verbatim
variable (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]

-- @@ L314-314 verbatim
variable (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h) (N:Eis)

-- @@ L315-315 verbatim
variable (hN:∀h,(9:Eis)*(G h).c0∣N)

-- @@ L316-317 verbatim
variable (D:∀h:Eis⧸Ideal.span {c},∀A:Finset ι,
  ControlledStratumArithmetic (fun i:A=>p i.val) N (G h).a0 (G h).c0 (G h).mode)


-- @@ L319-321 verbatim
def fixedActiveCuspDatum (t:FixedActiveCuspIndex c p) : SourceCuspDatum :=
  activeStratumDatum p hp hprimary (D t.1) (hN t.1) (G t.1).denominator_ne_zero
    (G t.1).primary (G t.1).shape t.2.1 t.2.2


-- @@ L323-326 verbatim
def fixedActiveCuspWeight (φ:Eis→*ℂ) (t:FixedActiveCuspIndex c p) : ℂ :=
  fixedThetaRowCoeff c hc φ t.1*primeInactiveFourierWeight p hp hg j t.2.1*
    ControlledStratumArithmetic.fourierWeight (p:=fun i:t.2.1=>p i.val)
      (fun i:t.2.1=>hp i.val) (fun i:t.2.1=>hg i.val) (fun i=>j i.val) t.2.2


-- @@ L328-362 verbatim
theorem fixedActiveCusp_fourier_multiplier (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ)
    (hχ:∀n,χ n=finiteSexticRow (fun i=>Ideal.span {p i}) hg j n) (n:Eis) :
    (∑t:FixedActiveCuspIndex c p,fixedActiveCuspWeight p hp hg j c hc φ t*
      ShortDraftTrace.breveE (-cuspFrequency n*
        (fixedActiveCuspDatum p hp hprimary c G N hN D t).point))=
      fixedThetaTwist (φ*χ) n := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveCuspWeight,fixedActiveCuspDatum]
  rw [fixedThetaTwist_fixed_fourier c hc Q hcQ φ χ hφ n]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _=fixedThetaRowCoeff c hc φ h*
        (∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
            ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val) (fun i:A=>hp i.val) (fun i:A=>hg i.val)
              (fun i=>j i.val) v*
            ShortDraftTrace.breveE (-cuspFrequency n*
              (activeStratumDatum p hp hprimary (D h) (hN h) (G h).denominator_ne_zero
                (G h).primary (G h).shape A v).point)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _=fixedThetaRowCoeff c hc φ h*
        (ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding (G h).a0/eisEmbedding (G h).c0))*
          finiteSexticRow (fun i=>Ideal.span {p i}) hg j n):=by
      rw [activeStratum_fourier_multiplier p hp hprimary hg j (D h) (hN h)
        (G h).denominator_ne_zero (G h).primary (G h).shape n]
    _=fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n*χ n:=by
      rw [(G h).point,←hχ n, fixedRowFourierPhase_translation]
      ring


-- @@ L364-395 verbatim
theorem completedT_fixed_active_strata (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ)
    (hχ:∀n,χ n=finiteSexticRow (fun i=>Ideal.span {p i}) hg j n)
    (hφχ:∀n,‖(φ*χ) n‖≤1) (Qall:Ideal Eis)
    (hperiod:CanonicalCoefficientClass.FactorsModulo Qall (φ*χ))
    (call:Eis) (hcall:call≠0) [Fintype (Eis⧸Ideal.span {call})]
    (hcallQ:Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (φ*χ) W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*
        ∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          (D h A).smoothedValue (hN h)
            (primary_finset_product Finset.univ (fun i:A=>p i.val) (fun i _=>hprimary i.val))
            (G h).primary (G h).shape (fun i=>hp i.val) (G h).denominator_ne_zero
            (fun i=>hg i.val) (fun i=>j i.val) W X := by
  rw [completedT_of_finite_cusp_multiplier (φ*χ) hφχ Qall hperiod call hcall hcallQ
    (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveCuspWeight p hp hg j c hc φ)
    (fixedActiveCusp_fourier_multiplier p hp hprimary hg j c hc G N hN D Q hcQ φ χ hφ hχ)
    W lo hi hlo hsupp hW X hX]
  congr 1
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveCuspWeight,fixedActiveCuspDatum,
    ControlledStratumArithmetic.smoothedValue,activeStratumDatum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  ring


-- @@ L397-397 verbatim
end CubicEisenstein


-- @@ L399-399 verbatim
open scoped BigOperators Classical ContDiff


-- @@ L401-401 verbatim
namespace CanonicalRowCompletion


-- @@ L403-403 verbatim
section

-- @@ L404-404 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal

-- @@ L405-405 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L407-426 verbatim
def actualControlledSource (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (φ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  exact thetaDerivativeScalar⁻¹*
    ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*
      ∑A:Finset (FreePrimeIndex I Q),
        primeInactiveFourierWeight (freePrimaryPrime I Q) (freePrimaryPrime_ne_zero I Q hI)
          (freePrimaryPrime_good I Q hI)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6) A*
        (freePrimaryControlledStratum I Q hI c hcQ h (G h) A).smoothedValue
          (mul_dvd_mul_left 9 (G h).denominator_dvd)
          (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime I Q P.val)
            (fun P _=>freePrimaryPrime_primary I Q hI P.val))
          (G h).primary (G h).shape (fun P=>freePrimaryPrime_ne_zero I Q hI P.val)
          (G h).denominator_ne_zero (fun P=>freePrimaryPrime_good I Q hI P.val)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val.val%6) W X


-- @@ L428-458 verbatim
theorem fixedFree_completedT_eq_actualControlledSource (I Q:Ideal Eis) (hI:Supported I)
    (hQ:Q≠0) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (hφn:∀n,‖φ n‖≤1)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (φ*freePrimeRow I hI Q) W X=actualControlledSource I Q hI c hc hcQ G φ W X := by
  let : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  let Qall:Ideal Eis:=Q*(∏P:FreePrimeIndex I Q,P.val.val)
  have hQall:Qall≠0:=mul_ne_zero hQ
    (finite_prime_product_ne_bot (fun P:FreePrimeIndex I Q=>P.val.val))
  let call:=ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall:call≠0:=by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}):=ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}):=Fintype.ofFinite _
  have hcallQ:Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall:=by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact completedT_fixed_active_strata (freePrimaryPrime I Q) (freePrimaryPrime_ne_zero I Q hI)
    (freePrimaryPrime_primary I Q hI) (freePrimaryPrime_good I Q hI)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
    c hc G (9*c) (fun h=>mul_dvd_mul_left 9 (G h).denominator_dvd)
    (fun h A=>freePrimaryControlledStratum I Q hI c hcQ h (G h) A)
    Q hcQ.le φ (freePrimeRow I hI Q) hφ (freePrimeRow_eq_primary_family I Q hI)
    (fixedFreeRow_norm I hI Q φ hφn) Qall (fixedFreeRow_periodic I hI Q φ hφ)
    call hcall hcallQ W lo hi hlo hsupp hW X hX


-- @@ L460-482 verbatim
theorem rowTwist_completedT_eq_actualControlledSource
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Q:Ideal Eis) (hQ:Q≠0)
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (Ψ:Eis→*ℂ) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedThetaRowCoeff c hc φ h‖≤1) ∧
      ∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→Function.support W⊆Set.Icc lo hi→ContDiff ℝ ∞ W→
        ∀X:ℝ,0<X→completedT (rowTwist Ψ m f z) W X=
          actualControlledSource I (Q*Ideal.span {(72:Eis)}) hI c hc hcQ G φ W X := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hmod,hperiod,hnorm,hT⟩:=
    exists_actual_coprime_completed_row Ψ Q hQ hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,fixedThetaRowCoeff_norm c hc φ hφn,?_⟩
  intro W lo hi hlo hsupp hW X hX
  rw [hT W X]
  apply fixedFree_completedT_eq_actualControlledSource I _ hI _ c hc hcQ G φ hφ hφn W lo hi hlo hsupp hW X hX
  apply mul_ne_zero hQ
  simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
  norm_num


-- @@ L484-484 verbatim
end

-- @@ L485-485 verbatim
section


-- @@ L487-487 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein

-- @@ L488-488 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L490-504 verbatim
structure GoodMaskRowData (m f z:Eis) where
  maskUnit:Eisˣ
  maskLambda:ℕ
  maskTwo:ℕ
  maskGood:Eis
  maskSupported:Supported (Ideal.span {maskGood})
  maskPrimary:lambda^2∣maskGood-1
  maskFactor:m=maskUnit.val*lambda^maskLambda*(2:Eis)^maskTwo*maskGood
  numeratorUnit:Eisˣ
  numeratorLambda:ℕ
  numeratorTwo:ℕ
  numeratorGood:Eis
  numeratorSupported:Supported (Ideal.span {numeratorGood})
  numeratorPrimary:lambda^2∣numeratorGood-1
  numeratorFactor:f^4*z=numeratorUnit.val*lambda^numeratorLambda*(2:Eis)^numeratorTwo*numeratorGood


-- @@ L506-511 verbatim
theorem exists_goodMaskRowData (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) :
    Nonempty (GoodMaskRowData m f z) := by
  obtain ⟨um,am,bm,g,hg,hpg,hmf⟩:=exists_supported_numerator_factorization m hm
  obtain ⟨u,a,b,r,hr,hpr,hxf⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  exact ⟨⟨um,am,bm,g,hg,hpg,hmf,u,a,b,r,hr,hpr,hxf⟩⟩


-- @@ L513-514 verbatim
noncomputable def goodMaskRowData (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) :
    GoodMaskRowData m f z := Classical.choice (exists_goodMaskRowData m f z hm hf hz)


-- @@ L516-516 verbatim
namespace GoodMaskRowData

-- @@ L517-517 verbatim
variable {m f z:Eis} (D:GoodMaskRowData m f z)


-- @@ L519-519 verbatim
def movingIdeal : Ideal Eis := goodMaskMovingIdeal D.maskGood D.numeratorGood


-- @@ L521-522 verbatim
lemma movingSupported : Supported D.movingIdeal :=
  goodMaskMovingIdeal_supported D.maskGood D.numeratorGood D.maskSupported D.numeratorSupported


-- @@ L524-526 verbatim
def fixedFactor (Ψ:Eis→*ℂ) (Q:Ideal Eis) : Eis→*ℂ :=
  (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported)*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)})


-- @@ L528-533 verbatim
lemma numeratorFactor_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖(Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
      D.numeratorSupported) n‖≤1 := by
  change ‖Ψ n*numeratorBadTwist _ _ _ _ _ n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (numeratorBadTwist_norm _ _ _ _ _ n)


-- @@ L535-545 verbatim
lemma fixedFactor_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) :
    CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) (D.fixedFactor Ψ Q) := by
  have hn:=fixedNumeratorTwist_periodic Ψ Q hΨ D.numeratorUnit D.numeratorLambda
    D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported) x*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) x=
    (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported) y*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) y
  rw [hn x y hxy,basePrimeRow_periodic D.movingIdeal D.movingSupported _ x y hxy]


-- @@ L547-552 verbatim
lemma fixedFactor_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖D.fixedFactor Ψ Q n‖≤1 := by
  change ‖((Ψ*numeratorBadTwist _ _ _ _ _) n)*(basePrimeRow _ _ _ n)‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (D.numeratorFactor_norm Ψ hΨ n)).trans (basePrimeRow_norm _ _ _ n)


-- @@ L554-565 verbatim
theorem row_primary (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=D.fixedFactor Ψ Q n*
      freePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) n := by
  rw [rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn]
  change (Ψ*numeratorBadTwist _ _ _ _ _) n*idealRowHom n D.movingIdeal= _
  rw [idealRowHom_fixed_conductor_split D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) n]
  simp only [fixedFactor,MonoidHom.mul_apply]
  ring


-- @@ L567-572 verbatim
theorem completedT_eq_fixedFactor (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (W:ℝ→ℂ) (X:ℝ) :
    completedT (rowTwist Ψ m f z) W X=
      completedT (D.fixedFactor Ψ Q*freePrimeRow D.movingIdeal D.movingSupported
        (Q*Ideal.span {(72:Eis)})) W X :=
  completedT_congr_primary _ _ (D.row_primary Ψ Q hmLam hm2) W X


-- @@ L574-577 verbatim
lemma fixedCoefficient_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})] (h:Eis⧸Ideal.span {c}) :
    ‖fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h‖≤1 :=
  fixedThetaRowCoeff_norm c hc _ (D.fixedFactor_norm Ψ Q hΨ) h


-- @@ L579-579 verbatim
end GoodMaskRowData


-- @@ L581-581 verbatim
end


-- @@ L583-583 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid

-- @@ L584-584 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L585-585 verbatim
namespace GoodMaskRowData

-- @@ L586-586 verbatim
variable {m f z:Eis} (D:GoodMaskRowData m f z)

-- @@ L587-592 verbatim
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (hm:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

-- @@ L593-593 verbatim
include R I F Q0 hR hI hF hm hf hz hbad hcop hA hT


-- @@ L595-601 verbatim
noncomputable def primeFiberEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex D.movingIdeal Q0 :=
  goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm hf hz
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorFactor hbad hcop hA hT


-- @@ L603-607 verbatim
lemma primeFiberEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT P).val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl


-- @@ L609-617 verbatim
lemma primeFiberEquiv_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (normalizedFactors D.movingIdeal).count
      (D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT P).val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val) P :=
  goodMaskFreePrimeFiberEquiv_exponent R I F Q0 hR hI hF m f z hm hf hz
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorFactor hbad hcop hA hT P


-- @@ L619-619 verbatim
local notation "splitIndex" => D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT


-- @@ L621-624 verbatim
noncomputable def activePrimeEquiv (A:Finset (FreePrimeIndex D.movingIdeal Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A) :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A ≃ A :=
  activePrimeUnionEquiv splitIndex A hactive


-- @@ L626-634 verbatim
lemma activePrimeEquiv_exponent (A:Finset (FreePrimeIndex D.movingIdeal Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A) :
    (normalizedFactors D.movingIdeal).count
      (D.activePrimeEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT A hactive P).val.val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val.val) P := by
  cases P with
  | inl P=>exact D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inl P)
  | inr P=>exact D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P.val)


-- @@ L636-636 verbatim
end GoodMaskRowData


-- @@ L638-645 verbatim
noncomputable def fiberGoodMaskRowData (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (m:Eis)
    (hm:m≠0) (hF:F≠0) (hrows:∀I∈rows,I≠0) (u:Eisˣ)
    (I:representativeRowFiber rows R (Ideal.span {m}*F)) :
    GoodMaskRowData m (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I.val) :=
  goodMaskRowData _ _ _ hm (ConcretePrimeRowBridge.idealGenerator_ne_zero F hF)
    (mul_ne_zero u.ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero I.val
      (hrows I.val (Finset.mem_filter.mp I.property).1)))


-- @@ L647-647 verbatim
end CanonicalRowCompletion


-- @@ L649-649 verbatim
end


-- @@ L651-651 verbatim
end OAI
