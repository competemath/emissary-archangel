import OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases


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
namespace CubicEisenstein


-- @@ L78-78 verbatim
section

-- @@ L79-79 verbatim
open scoped BigOperators Classical MatrixGroups Matrix


-- @@ L81-81 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota

-- @@ L82-82 verbatim
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets

-- @@ L83-83 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L84-84 verbatim
namespace ControlledStratumArithmetic

-- @@ L85-85 verbatim
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}


-- @@ L87-88 verbatim
def fixedCusp (a0 c0:Eis) (mode:Bool) : SL(2,Eis) :=
  if mode then lowerCuspMatrix c0 else A3WeylCusp a0


-- @@ L90-99 verbatim
lemma relative (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(fixedCusp a0 c0 mode)⁻¹∈levelThree := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact D.unramified_relative h3N hr hbase a0 (by simp) v
  · exact D.ramified_relative h3N hr hbase c0 (by simp) v


-- @@ L101-105 verbatim
def relativeGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : levelThree :=
  ⟨D.matrix v*(fixedCusp a0 c0 mode)⁻¹,D.relative hN hr hbase v⟩


-- @@ L107-112 verbatim
lemma relativeGamma_mul (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.relativeGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v := by
  exact inv_mul_cancel_right (D.matrix v) (fixedCusp a0 c0 mode)


-- @@ L114-118 verbatim
def fixedFactor (D:ControlledStratumArithmetic p N a0 c0 mode) : ℂ :=
  if mode then
    eisEmbedding (symbol (-c0) (D.matrix (fun _=>1) 0 0-c0*D.matrix (fun _=>1) 0 1)*
      symbol 1 (D.matrix (fun _=>1) 0 0))
  else eisEmbedding (symbol (D.matrix (fun _=>1) 0 0) c0)


-- @@ L120-130 verbatim
theorem relative_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter (D.relativeGamma hN hr hbase v)=
      D.fixedFactor*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  cases mode
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.false_eq_true,↓reduceIte,
      unramifiedFixedFactor] using D.unramified_character hN hr hbase a0 (by simp) v
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.true_eq,↓reduceIte,
      ramifiedFixedFactor] using D.ramified_character hN hr hbase c0 1 (by simp) (by simp) v


-- @@ L132-143 verbatim
theorem fixedFactor_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1) : ‖D.fixedFactor‖=1 := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact norm_A3_unramified_fixed_factor _ _ _ _ _ (D.determinant (fun _=>1)) hbase
  · apply norm_A3_ramified_fixed_factor _ _ 1 (∏i,p i) _ c0
    · simpa only [one_mul] using D.determinant (fun _=>1)
    · exact D.numerator_primary h3N hr hbase (fun _=>1)
    · exact A3_ramified_relative_primary (D.matrix (fun _=>1)) c0
        (D.ramified_relative h3N hr hbase c0 (by simp) (fun _=>1))


-- @@ L145-150 verbatim
noncomputable def fourierWeight [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
    (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)


-- @@ L152-161 verbatim
noncomputable def multiplierSum (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
    fourierWeight hp hg j v*star (complexCharacter (D.relativeGamma hN hr hbase v))*
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))


-- @@ L163-170 verbatim
noncomputable def bracketProduct (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Field (Eis⧸Ideal.span {p i}):=Ideal.Quotient.field _
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)*
    bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x)


-- @@ L172-188 verbatim
theorem multiplierSum_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6) (x:Eis) :
    D.multiplierSum hN hr hbase hp hg j x=
      (star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U x)*
        D.bracketProduct hp hg j x := by
  exact stratum_multiplier_of_cubic_factor p hp hcop hg hchar c0 D.U D.w x
    (D.matrix (fun _=>1) 1 1) hc0 D.bezout
    (fun v=>D.matrix v 0 0) (fun v=>D.matrix v 0 1) (fun v=>D.matrix v 1 1)
    (fun v=>complexCharacter (D.relativeGamma hN hr hbase v)) D.fixedFactor
    (D.relative_character hN hr hbase) D.determinant (D.inverse_fixed hN)
    D.sigma D.epsilon D.frequency_congruence D.epsilon_value j hj


-- @@ L190-190 verbatim
end ControlledStratumArithmetic

-- @@ L191-191 verbatim
end


-- @@ L193-193 verbatim
section

-- @@ L194-194 verbatim
open scoped BigOperators Classical ContDiff MatrixGroups Matrix


-- @@ L196-196 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic CubicKubota

-- @@ L197-197 verbatim
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets

-- @@ L198-198 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L199-199 verbatim
namespace ControlledStratumArithmetic

-- @@ L200-200 verbatim
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}


-- @@ L202-206 verbatim
def sourceGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : levelTwo :=
  sourceLevelInclusion (D.relativeGamma hN hr hbase v)


-- @@ L208-213 verbatim
lemma sourceGamma_mul (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v :=
  D.relativeGamma_mul hN hr hbase v


-- @@ L215-221 verbatim
lemma sourceGamma_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    levelTwoComplexCharacter (D.sourceGamma hN hr hbase v)=
      complexCharacter (D.relativeGamma hN hr hbase v) :=
  sourceLevelInclusion_character _


-- @@ L223-230 verbatim
def datum (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : SourceCuspDatum :=
  s.datum (D.sourceGamma hN hr hbase v) (by
    rw [D.sourceGamma_mul,D.denominator]
    exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))


-- @@ L232-241 verbatim
lemma datum_point (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.datum hN hr hbase s hp hc0 v).point=eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i) := by
  rw [datum,s.datum_point,D.sourceGamma_mul,D.numerator,D.denominator]
  simpa only [ramifiedEmbedding_traceLambda] using
    finiteCrossNumerator_fraction a0 c0 ramifiedTraceLambda p (D.lift v) hc0 hp


-- @@ L243-252 verbatim
noncomputable def smoothedValue (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,fourierWeight hp hg j v*
    (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X


-- @@ L254-271 verbatim
noncomputable def reflectedValue (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*
    ∑'t:ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1*
          Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*
      ((star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U
        (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))*
          D.bracketProduct hp hg j
            (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))


-- @@ L273-308 verbatim
theorem smoothed_eq_reflected (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hN hr hbase s hp hc0 hg j W X=D.reflectedValue s hp hc0 hg j W X := by
  let (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  have hc:c0*(∏i,p i)≠0:=mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  have hC:∀v,((D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode) 1 0=c0*∏i,p i := by
    intro v
    rw [D.sourceGamma_mul,D.denominator]
  have he:=s.sum_smoothedKernel_integral_phase (D.sourceGamma hN hr hbase) _ hc hC
    (fourierWeight hp hg j) W lo hi hlo hsupp hW X hX
  change D.smoothedValue hN hr hbase s hp hc0 hg j W X=_ at he
  rw [he]
  unfold reflectedValue
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*z)
  apply tsum_congr
  intro t
  apply congrArg (fun z:ℂ=>
    (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*z)
  simpa only [multiplierSum,D.sourceGamma_character,D.sourceGamma_mul,map_mul] using
    D.multiplierSum_eq hN hr hbase hp hc0 hcop hg hchar j hj
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))


-- @@ L310-310 verbatim
end ControlledStratumArithmetic


-- @@ L312-330 verbatim
theorem exists_constructed_stratum_reflection {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (N a0 c0:Eis) (hc0:c0≠0) (hN:(9:Eis)*c0∣N)
    (mode:Bool) (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hac:IsCoprime a0 c0) (hNp:∀i,IsCoprime N (p i)) :
    ∃s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode),
      ∃D:ControlledStratumArithmetic p N a0 c0 mode,
      ∀j:ι→ℕ,(∀i,j i<6)→∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→
        Function.support W⊆Set.Icc lo hi→ContDiff ℝ ∞ W→∀X:ℝ,0<X→
        D.smoothedValue hN (primary_finset_product Finset.univ p (fun i _=>hprimary i))
          hbase s hp hc0 hg j W X=D.reflectedValue s hp hc0 hg j W X := by
  obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)
  obtain ⟨D⟩:=exists_controlledStratumArithmetic p hp hcop hprimary N a0 c0 hc0 hN mode hbase hac hNp
  refine ⟨s,D,?_⟩
  intro j hj W lo hi hlo hsupp hW X hX
  exact D.smoothed_eq_reflected hN _ hbase s hp hc0 hcop hg hchar j hj W lo hi hlo hsupp hW X hX


-- @@ L332-332 verbatim
end


-- @@ L334-334 verbatim
section

-- @@ L335-335 verbatim
open scoped Classical BigOperators MatrixGroups


-- @@ L337-337 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ShortDraftCusp

-- @@ L338-338 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L340-349 verbatim
structure FixedFourierGeometry (c:Eis) (h:Eis⧸Ideal.span {c}) where
  a0 : Eis
  c0 : Eis
  denominator_ne_zero : c0≠0
  denominator_dvd : c0∣c
  coprime : IsCoprime a0 c0
  point : eisEmbedding a0/eisEmbedding c0=thetaFourierTranslation c h
  mode : Bool
  primary : if mode then lambda^2∣a0-1 else lambda^2∣c0-1
  shape : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)


-- @@ L351-362 verbatim
lemma exists_fixedFourierGeometry (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) :
    Nonempty (FixedFourierGeometry c h) := by
  obtain ⟨a0,c0,hc0,hdiv,hcop,hpoint,ha,hcp⟩:=
    ShortDraftCRT.exists_normalized_rational_cusp (-3*Quotient.out h) c hc
  have hp:eisEmbedding a0/eisEmbedding c0=thetaFourierTranslation c h := by
    rw [hpoint,thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
    simp only [map_mul,map_neg,map_ofNat]
  by_cases hl:lambda∣c0
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 true)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,true,ha hl,s⟩⟩
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 false)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,false,hcp hl,s⟩⟩


-- @@ L364-365 verbatim
def fixedFourierGeometry (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) :
    FixedFourierGeometry c h := Classical.choice (exists_fixedFourierGeometry c hc h)


-- @@ L367-367 verbatim
namespace FixedFourierGeometry

-- @@ L368-368 verbatim
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)


-- @@ L370-370 verbatim
abbrev PhaseResidue := Eis⧸Ideal.span {ramifiedTraceLambda^3*G.c0}


-- @@ L372-373 verbatim
instance phaseResidue_finite : Finite G.PhaseResidue :=
  finite_quotient_span (A4_bad_modulus_ne_zero G.c0 G.denominator_ne_zero)


-- @@ L375-375 verbatim
def levelScale : ℝ := fixedCuspLevelScale G.shape.index G.c0


-- @@ L377-378 verbatim
lemma levelScale_pos : 0<G.levelScale :=
  fixedCuspLevelScale_pos G.shape.index G.c0 G.denominator_ne_zero


-- @@ L380-381 verbatim
lemma levelScale_le (hc:c≠0) : G.levelScale≤fixedCuspLevelBound c :=
  fixedCuspLevelScale_le G.shape.index G.c0 c hc G.denominator_dvd


-- @@ L383-385 verbatim
def dualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator G.shape.index (G.shape.upper 0 0)
    (fixedCuspArrayIndex u m I J)


-- @@ L387-388 verbatim
def staticPhase (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  G.shape.reflectionStaticPhase G.c0 G.denominator_ne_zero v (G.dualNumerator u) u m I J


-- @@ L390-392 verbatim
lemma staticPhase_norm_le_one (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖G.staticPhase v u m I J‖≤1 :=
  G.shape.reflectionStaticPhase_norm_le_one G.c0 G.denominator_ne_zero v _ u m I J


-- @@ L394-395 verbatim
def array (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase G.shape.index u (G.staticPhase v u) m I J


-- @@ L397-399 verbatim
lemma array_norm_le_one (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖G.array v u m I J‖≤1 :=
  fixedCuspArrayWithPhase_norm_le_one G.shape.index u _ (G.staticPhase_norm_le_one v u) m I J


-- @@ L401-404 verbatim
lemma array_eq (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    G.array v u m I J=G.shape.amplitude u m I J*
      A4PhaseFromResidue G.c0 G.denominator_ne_zero v (G.dualNumerator u m I J) :=
  G.shape.fixedCuspArrayWithPhase_reflectionStaticPhase G.c0 G.denominator_ne_zero v _ u m I J


-- @@ L406-406 verbatim
end FixedFourierGeometry


-- @@ L408-409 verbatim
def FixedReflectionRay (c:Eis) (hc:c≠0) :=
  Σh:Eis⧸Ideal.span {c},(fixedFourierGeometry c hc h).PhaseResidue×Eisˣ


-- @@ L411-415 verbatim
instance fixedReflectionRay_finite (c:Eis) (hc:c≠0) : Finite (FixedReflectionRay c hc) := by
  let:Finite (Eis⧸Ideal.span {c}):=finite_quotient_span hc
  let:Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  unfold FixedReflectionRay
  infer_instance


-- @@ L417-418 verbatim
noncomputable instance fixedReflectionRay_fintype (c:Eis) (hc:c≠0) :
    Fintype (FixedReflectionRay c hc) := Fintype.ofFinite _


-- @@ L420-420 verbatim
def fixedReflectionRayCount (c:Eis) (hc:c≠0) : ℕ := Fintype.card (FixedReflectionRay c hc)


-- @@ L422-423 verbatim
def fixedReflectionRayEquiv (c:Eis) (hc:c≠0) :
    FixedReflectionRay c hc≃Fin (fixedReflectionRayCount c hc) := Fintype.equivFin _


-- @@ L425-431 verbatim
lemma fixedReflectionRayCount_subpower (c:Eis) (hc:c≠0) (z:ℂ) (κ:ℝ) (hκ:0≤κ) :
    ∃C:ℝ,0≤C ∧ ∀Z:ℝ,1≤Z→
      (fixedReflectionRayCount c hc:ℝ)^2*‖z‖^2≤C*Z^κ := by
  refine ⟨(fixedReflectionRayCount c hc:ℝ)^2*‖z‖^2,by positivity,?_⟩
  intro Z hZ
  have hz:1≤Z^κ:=Real.one_le_rpow hZ hκ
  exact le_mul_of_one_le_right (by positivity) hz


-- @@ L433-433 verbatim
end


-- @@ L435-435 verbatim
open Filter MeasureTheory

-- @@ L436-436 verbatim
open scoped BigOperators Classical Topology ContDiff MatrixGroups


-- @@ L438-438 verbatim
open CompletedGauss ConcreteTraceCRT

-- @@ L439-439 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L441-503 verbatim
theorem completedT_of_finite_cusp_profiles
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    {ι:Type*} [Fintype ι] (d:ι→SourceCuspDatum) (w:ι→ℂ)
    (hFG:∀v:ℝ,0<v→completedBesselProfile Ψ thetaBesselScale v=
      ∑i,w i*cuspBarProfile cubicSourceConjugateFunction (d i).point v)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=∑i,w i*(d i).smoothedKernel W X := by
  let : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let G:ι→ℝ→ℂ:=fun h=>
    cuspBarProfile cubicSourceConjugateFunction (d h).point
  have hG (h:ι) : ∀s:ℂ,MellinConvergent (G h) s:=
    (d h).cuspBarProfile_mellin_entire.1
  have hF:=completedBesselProfile_mellin_entire_of_periodic Ψ Q hperiod c hc hcQ
  have hVs:=Vstar_support W v0 v1 hWs
  have hV:=Vstar_contDiff W v0 v1 hv0 hWs hW
  let J:ι→ℝ→ℂ:=fun h t=>
    besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I)
  have hi (h:ι) : Integrable (J h):=
    besselSmoothingIntegrand_reflected_integrable (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  have hireal (h:ι) : Integrable (fun t:ℝ=>
      besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X (((-1:ℝ):ℂ)+t*Complex.I)):=by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,J] using hi h
  have hleft:=besselSmoothingIntegrand_finite_integrable
    (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X (-1)
    (fun h t=>hG h _) hireal
  have hshift:=completedT_mellin_shift Ψ hΨ thetaBesselScale thetaBesselScale_pos hF.1 hF.2
    W v0 v1 hv0 hWs hW X hX (-1) (by norm_num) hleft
  have hline (h:ι) : (1/(2*Real.pi):ℂ)*(∫t:ℝ,J h t)=(d h).smoothedKernel W X:=by
    exact besselSmoothingIntegral_reflected_kernel (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ thetaBesselScale)
          thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I):=by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hshift
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,∑h,w h*J h t:=by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact besselSmoothingIntegrand_finite_sum
        (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X _
        (fun h=>hG h _)
    _=∑h,w h*((1/(2*Real.pi):ℂ)*∫t:ℝ,J h t):=by
      rw [integral_finsetSum Finset.univ (fun h _=>(hi h).const_mul (w h)),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_const_mul]
      ring
    _=∑h,w h*(d h).smoothedKernel W X:=by simp_rw [hline]


-- @@ L505-505 verbatim
end CubicEisenstein


-- @@ L507-507 verbatim
open scoped BigOperators Classical


-- @@ L509-509 verbatim
namespace CanonicalRowCompletion


-- @@ L511-511 verbatim
section

-- @@ L512-512 verbatim
open ActualEisensteinCubic CompletedGauss

-- @@ L513-513 verbatim
open CubicEisenstein hiding summand

-- @@ L514-514 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L516-517 verbatim
def fixedRowFourierPhase (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) (n:Eis) : ℂ :=
  quotientTrace c hc (h*Ideal.Quotient.mk _ n)


-- @@ L519-521 verbatim
def fixedRowFourierCoeff (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (h:Eis⧸Ideal.span {c}) : ℂ :=
  finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedQuotientValue (Ideal.span {c}) φ) h


-- @@ L523-526 verbatim
lemma fixedRowFourierCoeff_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (h:Eis⧸Ideal.span {c}) :
    ‖fixedRowFourierCoeff c hc φ h‖≤1 :=
  finiteAdditiveFourierCoeff_norm _ _ (fixedQuotientValue_norm _ φ hφ) h


-- @@ L528-535 verbatim
lemma fixedRowFourierCoeff_mass (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) :
    (∑h:Eis⧸Ideal.span {c},‖fixedRowFourierCoeff c hc φ h‖)≤
      (Fintype.card (Eis⧸Ideal.span {c}):ℝ) := by
  calc
    _≤∑_h:Eis⧸Ideal.span {c},(1:ℝ):=
      Finset.sum_le_sum (fun h _=>fixedRowFourierCoeff_norm c hc φ hφ h)
    _=_:=by simp


-- @@ L537-538 verbatim
lemma fixedRowFourierPhase_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})] (h:Eis⧸Ideal.span {c}) (n:Eis) :
    ‖fixedRowFourierPhase c hc h n‖=1 := AddChar.norm_apply _ _


-- @@ L540-543 verbatim
lemma fixedRowFourierPhase_translation (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) (n:Eis) :
    fixedRowFourierPhase c hc h n=
      ShortDraftTrace.breveE (-cuspFrequency n*thetaFourierTranslation c h) :=
  (thetaFourierTranslation_phase c hc h n).symm


-- @@ L545-553 verbatim
lemma fixedRowFourier_inversion (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo (Ideal.span {c}) φ) (n:Eis) :
    (∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*fixedRowFourierPhase c hc h n)=φ n := by
  rw [show (∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*fixedRowFourierPhase c hc h n)=
      fixedQuotientValue (Ideal.span {c}) φ (Ideal.Quotient.mk _ n) from
    finiteAdditiveFourier_inversion (quotientTrace c hc)
      (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc)
      (fixedQuotientValue (Ideal.span {c}) φ) _]
  exact fixedQuotientValue_mk _ φ hφ n


-- @@ L555-563 verbatim
lemma summand_mul_fixed_twist (φ χ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ) (I J:Ideal Eis) :
    summand (φ*χ) W X I J=
      φ (primaryGenerator I*(primaryGenerator J)^3)*summand χ W X I J := by
  have he (η:Eis→*ℂ) : cubeWeight η J=
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
        η (primaryGenerator J)^3/(Ideal.absNorm J:ℂ):=rfl
  rw [summand,summand,he,he]
  simp only [columnWeight,MonoidHom.mul_apply,map_mul,map_pow,mul_pow]
  ring


-- @@ L565-568 verbatim
def completedFixedFrequency (χ:Eis→*ℂ) (c:Eis) (hc:c≠0)
    (h:Eis⧸Ideal.span {c}) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  ∑'p:Ideal Eis×Ideal Eis,summand χ W X p.1 p.2*
    fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)


-- @@ L570-577 verbatim
lemma completedFixedFrequency_summable (χ:Eis→*ℂ) (c:Eis) (hc:c≠0)
    (h:Eis⧸Ideal.span {c}) (W:ℝ→ℂ) (hW:HasCompactSupport W) (X:ℝ) (hX:0<X) :
    Summable (fun p:Ideal Eis×Ideal Eis=>summand χ W X p.1 p.2*
      fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support χ W hW X hX).subset
  intro p hp
  exact left_ne_zero_of_mul hp


-- @@ L579-603 verbatim
theorem completedT_fixed_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo (Ideal.span {c}) φ)
    (W:ℝ→ℂ) (hW:HasCompactSupport W) (X:ℝ) (hX:0<X) :
    completedT (φ*χ) W X=
      ∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*completedFixedFrequency χ c hc h W X := by
  have hp (p:Ideal Eis×Ideal Eis) : summand (φ*χ) W X p.1 p.2=
      ∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*
        (summand χ W X p.1 p.2*
          fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) := by
    rw [summand_mul_fixed_twist,←fixedRowFourier_inversion c hc φ hφ,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  calc
    completedT (φ*χ) W X=∑'p:Ideal Eis×Ideal Eis,summand (φ*χ) W X p.1 p.2 :=
      (completedT_summable (φ*χ) W hW X hX).tsum_prod.symm
    _=∑'p:Ideal Eis×Ideal Eis,∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*
        (summand χ W X p.1 p.2*
          fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) :=
      tsum_congr hp
    _=∑h:Eis⧸Ideal.span {c},∑'p:Ideal Eis×Ideal Eis,fixedRowFourierCoeff c hc φ h*
        (summand χ W X p.1 p.2*
          fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) :=
      Summable.tsum_finsetSum (fun h _=>(completedFixedFrequency_summable χ c hc h W hW X hX).mul_left _)
    _=_:=by simp only [tsum_mul_left,completedFixedFrequency]


-- @@ L605-605 verbatim
end


-- @@ L607-607 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve

-- @@ L608-608 verbatim
open CubicEisenstein hiding summand

-- @@ L609-609 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L611-631 verbatim
theorem actual_completedT_fixed_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hQ:Q≠0)
    (hcQ:Ideal.span {c}≤Q*Ideal.span {(72:Eis)})
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedRowFourierCoeff c hc φ h‖≤1) ∧
      (∀(W:ℝ→ℂ),HasCompactSupport W→∀X:ℝ,0<X→
        completedT (rowTwist Ψ m f z) W X=
          ∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*
            completedFixedFrequency (freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) c hc h W X) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hmod,hperiod,hnorm,hT⟩:=
    exists_actual_coprime_completed_row Ψ Q hQ hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,fixedRowFourierCoeff_norm c hc φ hφn,?_⟩
  intro W hW X hX
  rw [hT W X]
  exact completedT_fixed_fourier c hc φ _ (fun x y hxy=>hφ x y (hcQ hxy)) W hW X hX


-- @@ L633-633 verbatim
end CanonicalRowCompletion


-- @@ L635-635 verbatim
end


-- @@ L637-637 verbatim
end OAI
