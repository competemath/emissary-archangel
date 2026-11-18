import OAI.NumberTheory.DirichletL.RowCompletion.RowAmplitudes


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
open scoped BigOperators Classical ContDiff


-- @@ L78-78 verbatim
namespace CompletedGauss

-- @@ L79-79 verbatim
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets

-- @@ L80-80 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L82-92 verbatim
lemma active_product_admissible_equiv {ι β:Type*} [Fintype ι] [Fintype β]
    (k:Ideal Eis) (hk:Squarefree k) (P:ι→Ideal Eis) (R:β→Ideal Eis)
    (E:PrimeIndex k⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r) :
    (∏i,P i)=k*∏i,R i := by
  rw [←E.prod_comp,Fintype.prod_sum_type]
  simp only [hres,hnonres]
  congr 1
  change (∏r:primeSupport k,r.val)=k
  exact (Finset.prod_coe_sort (primeSupport k) (fun r:Ideal Eis=>r)).trans
    (IdealMobiusDivisorSum.squarefree_support_product_self hk)


-- @@ L94-103 verbatim
theorem residual_bracket_extracted_admissible (k:Ideal Eis) (hk:Admissible k)
    (z:Eis) (A B n b:Ideal Eis) :
    (∏P:PrimeIndex k,
      bracket (actualSextic P.val (admissiblePrimeGood k hk P)) 1
        (Ideal.Quotient.mk P.val (z*primaryGenerator (A*n)*(primaryGenerator (B*b))^3)))=
      residualArgumentPhase k z A B*quadraticRow k (primaryGenerator (n*b)) := by
  rw [residual_bracket_product]
  rw [←quadraticRow_eq_primeIndex k hk,←quadraticRow_eq_primeIndex k hk]
  simp only [primaryGenerator_mul,residualArgumentPhase,canonical_quadraticRow_argument_mul k hk]
  ring


-- @@ L105-126 verbatim
theorem residual_coefficient_eq_canonical_admissible {ι:Type*} [Fintype ι]
    (k:Ideal Eis) (hk:Admissible k)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (residualArgument:ℕ→Eis)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (rowPhase:ℕ→ℂ) (m:ℕ) (n b:Ideal Eis) :
    let A:=reflectionExtractedDivisor P j e 1
    let B:=reflectionExtractedDivisor P j e 2
    (rowPhase m*(∏p:PrimeIndex k,
        bracket (actualSextic p.val (admissiblePrimeGood k hk p)) 1
          (Ideal.Quotient.mk p.val (residualArgument m*primaryGenerator (A*n)*(primaryGenerator (B*b))^3))) *
      η m (A*n) (B*b)*reflectedBranch P hg j e (primaryGenerator (A*n)) (primaryGenerator (B*b)))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (A*n):ℝ)*(Ideal.absNorm (B*b):ℝ):ℝ):ℂ)=
      4*canonicalRawBranchCoefficient P hg j e ρ q
        (fun l a c=>η l (A*a) (B*c))
        (fun l=>rowPhase l*residualArgumentPhase k (residualArgument l) A B) k m n b := by
  dsimp only
  rw [residual_bracket_extracted_admissible k hk]
  unfold canonicalRawBranchCoefficient reflectedDyadicCoefficient
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring


-- @@ L128-162 verbatim
theorem residual_equiv_coefficient_admissible {ι β:Type*} [Fintype ι] [Fintype β]
    (k:Ideal Eis) (hk:Admissible k)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (R:β→Ideal Eis) [∀i,(R i).IsMaximal] (hR:∀i,lambda∉R i)
    (E:PrimeIndex k⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r)
    (j:ι→ℕ) (jβ:β→ℕ) (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=jβ r)
    (e:β→Fin 3) (ρ q:ℝ) (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (m:ℕ) (n b:Ideal Eis) :
    let A:=reflectionExtractedDivisor R jβ e 1
    let B:=reflectionExtractedDivisor R jβ e 2
    unextractedCuspCoefficient P hg j (residualLabelVia E e) ρ q η σ m (A*n) (B*b)=
      4*canonicalRawBranchCoefficient R hR jβ e ρ q
        (fun l a c=>η l (A*a) (B*c))
        (fun l=>σ l*residualArgumentPhase k 1 A B) k m n b := by
  dsimp only
  rw [unextractedCuspCoefficient,reflectedBranch_drop_residual_equiv E P hg j hjres]
  have hchar (r:PrimeIndex k) (z:Eis) :
      bracket (actualSextic (P (E (Sum.inl r))) (hg (E (Sum.inl r)))) 1 (Ideal.Quotient.mk _ z)=
      bracket (actualSextic r.val (admissiblePrimeGood k hk r)) 1 (Ideal.Quotient.mk _ z) :=
    actual_bracket_ideal_congr _ _ _ _ (hres r) 1 z
  have hnbranch (a b:Eis):
      reflectedBranch (fun r=>P (E (Sum.inr r))) (fun r=>hg (E (Sum.inr r)))
        (fun r=>j (E (Sum.inr r))) e a b=reflectedBranch R hR jβ e a b := by
    unfold reflectedBranch
    apply Finset.prod_congr rfl
    intro r hr
    change reflectedLocalPiece (P (E (Sum.inr r))) _ (j (E (Sum.inr r))) (e r) a b=_
    simp only [hnonres r,hjnonres r]
  simp_rw [hchar]
  rw [hnbranch]
  have ht:=residual_coefficient_eq_canonical_admissible k hk R hR jβ e ρ q (fun _=>1) η σ m n b
  simp only [one_mul] at ht
  convert ht using 1 ; ring


-- @@ L164-164 verbatim
end CompletedGauss


-- @@ L166-166 verbatim
namespace CubicEisenstein

-- @@ L167-167 verbatim
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve

-- @@ L168-168 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L169-169 verbatim
namespace FixedFourierGeometry

-- @@ L170-170 verbatim
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)

-- @@ L171-171 verbatim
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}


-- @@ L173-239 verbatim
theorem stratumBranchTerm_tsum_eq_rawValue_at_row
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {I F Q:Ideal Eis} {levelBound K:ℝ} (d:ReflectedBranchData levelBound K I F Q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (E:PrimeIndex k.val⊕d.primes≃ι)
    (hres:∀r,Ideal.span {p (E (Sum.inl r))}=r.val)
    (hnonres:∀r,Ideal.span {p (E (Sum.inr r))}=r.val)
    (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=completedLocalExponent I F r.val)
    (hlevel:d.levelScale=G.levelScale) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    letI : ∀r:d.primes,r.val.IsMaximal:=d.maximal
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      G.stratumBranchTerm D hp hg j u (residualLabelVia E d.label) W X (nonzeroDualDilation A B hA hB x))=
      4*d.rawValue
        (fun m n b=>G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u m (A*n) (B*b))
        (fun m k'=>D.modelRowPhase G.shape hp hg j u m*residualArgumentPhase k'.val 1 A B)
        W X 1 completedRamifiedStep k := by
  let : ∀r:d.primes,r.val.IsMaximal:=d.maximal
  dsimp only
  let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 1
  let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 2
  let η:=G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u
  let σ:=D.modelRowPhase G.shape hp hg j u
  have hfull:Ideal.span {∏i,p i}=k.val*∏r:d.primes,r.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact active_product_admissible_equiv k.val (mem_idealRange.mp k.property).1.2.1 (fun i=>Ideal.span {p i})
      (fun r:d.primes=>r.val) E hres hnonres
  have hk0:k.val≠0:=(mem_idealRange.mp k.property).1.1
  unfold ReflectedBranchData.rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  have hcoef:=residual_equiv_coefficient_admissible k.val (mem_idealRange.mp k.property).1 (fun i=>Ideal.span {p i}) hg
    (fun r:d.primes=>r.val) d.good E hres hnonres j
    (fun r=>completedLocalExponent I F r.val) hjres hjnonres d.label
    1 completedRamifiedStep η σ x.1 x.2.1.val x.2.2.val
  have harg:
      (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm (A*x.2.1.val):ℝ)*
        (Ideal.absNorm (B*x.2.2.val):ℝ)^3=
      ((completedBranchScale K (X/d.levelScale) I F Q (fun r:d.primes=>r.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2)*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
        (Ideal.absNorm x.2.2.val:ℝ)^3 := by
    rw [hlevel,completedBranchScale_raw_argument K X G.levelScale (1*completedRamifiedStep^x.1)
      I F Q (fun r:d.primes=>r.val) d.label k.val x.2.1.val x.2.2.val hK G.levelScale_pos hk0]
    rw [hfull]
    simp only [map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  dsimp only [stratumBranchTerm,nonzeroDualDilation,rawDualKernelTerm]
  change unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j (residualLabelVia E d.label)
      1 completedRamifiedStep η σ x.1 (A*x.2.1.val) (B*x.2.2.val)*_=_
  rw [hcoef,harg]
  exact mul_assoc _ _ _


-- @@ L241-241 verbatim
end FixedFourierGeometry

-- @@ L242-242 verbatim
end CubicEisenstein


-- @@ L244-244 verbatim
namespace CompletedGauss.FreeReflection

-- @@ L245-245 verbatim
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic

-- @@ L246-246 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L248-266 verbatim
theorem sixPhaseFixedCuspBranch_value_eq_rawValue
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound
      e cusp u phaseArray hphase rowPhase hrow
    d.value W X ρ q k=
      d.rawValue (d.extractedFixedCuspArrayWithPhase cusp u phaseArray) rowPhase W X ρ q k := by
  exact (sixReflectedBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase_value cusp u phaseArray hphase rowPhase hrow
      W a b ha hsupp hW X ρ q hX hρ hq hK k hk


-- @@ L268-268 verbatim
end CompletedGauss.FreeReflection

-- @@ L269-269 verbatim
namespace CubicEisenstein.FixedFourierGeometry

-- @@ L270-270 verbatim
open ActualEisensteinCubic CompletedGauss CompletedGauss.FreeReflection CanonicalQuadraticSieve CompletedDyadic

-- @@ L271-271 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L273-294 verbatim
theorem sixPhaseFixedCuspBranch_value_eq_geometric_rawValue
    {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (hbound:G.levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (v:G.PhaseResidue) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound G.levelScale G.levelScale_pos hbound
      e G.shape.index u (G.staticPhase v u) (G.staticPhase_norm_le_one v u) rowPhase hrow
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    d.value W X ρ q k=
      d.rawValue (fun m n b=>G.array v u m (A*n) (B*b)) rowPhase W X ρ q k := by
  exact sixPhaseFixedCuspBranch_value_eq_rawValue I F Q Q0 hI hQ K levelBound
    G.levelScale G.levelScale_pos hbound e G.shape.index u (G.staticPhase v u)
    (G.staticPhase_norm_le_one v u) rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk


-- @@ L296-296 verbatim
end CubicEisenstein.FixedFourierGeometry


-- @@ L298-298 verbatim
open scoped BigOperators Classical


-- @@ L300-300 verbatim
namespace CompletedGauss.FreeReflection

-- @@ L301-301 verbatim
open ActualEisensteinCubic

-- @@ L302-302 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L304-311 verbatim
def supportActivePoolEquiv (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6) :
    reflectionSixSupport e ≃ reflectionActivePool I Q Q0 e where
  toFun b:=⟨b.val.val,(mem_reflectionActivePool I Q Q0 e b.val).mpr
    (Finset.mem_filter.mp b.property).2⟩
  invFun P:=⟨⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_reflectionActivePool I Q Q0 e _).mp P.property⟩⟩
  left_inv _b:=rfl
  right_inv _P:=rfl


-- @@ L313-315 verbatim
lemma supportActivePoolEquiv_val (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6)
    (b:reflectionSixSupport e) :
    (supportActivePoolEquiv I Q Q0 e b).val=b.val.val := rfl


-- @@ L317-319 verbatim
lemma supportActivePoolEquiv_symm_val (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6)
    (P:reflectionActivePool I Q Q0 e) :
    ((supportActivePoolEquiv I Q Q0 e).symm P).val.val=P.val := rfl


-- @@ L321-324 verbatim
lemma supportActivePoolEquiv_label (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6)
    (b:reflectionSixSupport e) :
    reflectionActiveLabel I Q Q0 e (supportActivePoolEquiv I Q Q0 e b)=
      reflectionSixLabel (e b.val) := rfl


-- @@ L326-338 verbatim
def encodedActivePoolEquiv (I Q Q0:Ideal Eis) (B:Finset (pool I Q Q0)) (l:B → Fin 3) :
    B ≃ reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,l⟩) where
  toFun b:=⟨b.val.val,by
    rw [reflectionActivePool_encode]
    exact Finset.mem_image.mpr ⟨b.val,b.property,rfl⟩⟩
  invFun P:=⟨⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩,by
    have hp:P.val∈B.image Subtype.val:=by
      simpa only [reflectionActivePool_encode] using P.property
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hp
    have he':b=⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩:=Subtype.ext he
    exact he' ▸ hb⟩
  left_inv b:=rfl
  right_inv P:=rfl


-- @@ L340-341 verbatim
lemma encodedActivePoolEquiv_val (I Q Q0:Ideal Eis) (B:Finset (pool I Q Q0)) (l:B → Fin 3)
    (b:B) : (encodedActivePoolEquiv I Q Q0 B l b).val=b.val.val := rfl


-- @@ L343-351 verbatim
lemma encodedActivePoolEquiv_label (I Q Q0:Ideal Eis) (B:Finset (pool I Q Q0)) (l:B → Fin 3)
    (b:B) :
    reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,l⟩) (encodedActivePoolEquiv I Q Q0 B l b)=l b := by
  change reflectionSixLabel (encodeReflectionSix ⟨B,l⟩ b.val)=l b
  apply Fin.ext
  simp only [encodeReflectionSix,dite_eq_left b.property,reflectionSixLabel]
  change (3+(l b).val)%3=(l b).val
  have hlt:=(l b).isLt
  omega


-- @@ L353-366 verbatim
lemma encodedActivePoolEquiv_divisor (I F Q Q0:Ideal Eis)
    (B:Finset (pool I Q Q0)) (l:B → Fin 3) (side:Fin 3) :
    reflectionExtractedDivisor
      (fun P:reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,l⟩)=>P.val)
      (fun P=>completedLocalExponent I F P.val)
      (reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,l⟩)) side=
    reflectionExtractedDivisor (fun b:B=>b.val.val)
      (fun b=>completedLocalExponent I F b.val.val) l side := by
  unfold reflectionExtractedDivisor
  symm
  apply Fintype.prod_equiv (encodedActivePoolEquiv I Q Q0 B l)
  intro b
  rw [encodedActivePoolEquiv_label]
  rfl


-- @@ L368-368 verbatim
end CompletedGauss.FreeReflection


-- @@ L370-370 verbatim
namespace CanonicalRowCompletion.ActualFiber

-- @@ L371-371 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein

-- @@ L372-372 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L373-377 verbatim
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F)


-- @@ L379-385 verbatim
noncomputable def activeModelPrimeEquiv :
    PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e ≃
        activeSet q hq m hm rows R F hR hF hrows v e J :=
  (Equiv.sumCongr (Equiv.refl _)
    (FreeReflection.supportActivePoolEquiv R (maskIdeal q m F) (freeConductor q) e).symm).trans
    (selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e))


-- @@ L387-391 verbatim
lemma splitIndex_prime_val
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕ FreeReflection.pool R (maskIdeal q m F) (freeConductor q)) :
    (splitIndex q hq m hm rows R F hR hF hrows v J P).val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl


-- @@ L393-399 verbatim
lemma splitIndex_local_exponent
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕ FreeReflection.pool R (maskIdeal q m F) (freeConductor q)) :
    (UniqueFactorizationMonoid.normalizedFactors (data q m hm rows R F hF hrows v J).movingIdeal).count
      (splitIndex q hq m hm rows R F hR hF hrows v J P).val.val%6=
      Sum.elim (fun _=>1) (fun b=>completedLocalExponent R F b.val) P := by
  unfold splitIndex
  apply GoodMaskRowData.primeFiberEquiv_exponent


-- @@ L401-406 verbatim
lemma activeModelPrimeEquiv_prime_val
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e) :
    (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J P).val.val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl


-- @@ L408-415 verbatim
lemma activeModelPrimeEquiv_span
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e) :
    Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q)
      (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J P).val}=
      Sum.elim Subtype.val Subtype.val P := by
  rw [freePrimaryPrime_span _ _ (data q m hm rows R F hF hrows v J).movingSupported]
  exact activeModelPrimeEquiv_prime_val q hq m hm rows R F hR hF hrows v e J P


-- @@ L417-427 verbatim
lemma activeModelPrimeEquiv_exponent
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e) :
    (UniqueFactorizationMonoid.normalizedFactors (data q m hm rows R F hF hrows v J).movingIdeal).count
      (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J P).val.val.val%6=
      Sum.elim (fun _=>1) (fun b=>completedLocalExponent R F b.val) P := by
  cases P with
  | inl P=>exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inl P)
  | inr P=>
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J
      (Sum.inr ⟨P.val,FreeReflection.reflectionActivePool_subset R (maskIdeal q m F) (freeConductor q) e P.property⟩)


-- @@ L429-429 verbatim
end CanonicalRowCompletion.ActualFiber


-- @@ L431-431 verbatim
namespace CubicEisenstein

-- @@ L432-432 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss LocalReflectionBrackets

-- @@ L433-433 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L435-436 verbatim
noncomputable local instance inactiveField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P

-- @@ L437-438 verbatim
noncomputable local instance inactiveFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _


-- @@ L440-445 verbatim
lemma finiteAdditiveFourierCoeff_zero {R:Type*} [Field R] [Fintype R]
    (ψ:AddChar R ℂ) (χ:MulChar R ℂ) (j:ℕ) :
    finiteAdditiveFourierCoeff ψ (fun x=>(χ^j) x) 0=zeroFourierCoefficient χ j := by
  simp only [finiteAdditiveFourierCoeff,zeroFourierCoefficient,neg_zero,zero_mul,
    AddChar.map_zero_eq_one,mul_one,div_eq_mul_inv]
  ring


-- @@ L447-456 verbatim
lemma prime_zeroFourier_norm_formula (p:Eis) [(Ideal.span {p}).IsMaximal]
    (hp:p≠0) (hg:lambda∉Ideal.span {p}) (hodd:ringChar (Eis⧸Ideal.span {p})≠2)
    (j:ℕ) (hj:j<6) :
    finiteAdditiveFourierCoeff (quotientTrace p hp)
      (fun x=>(actualSextic (Ideal.span {p}) hg^j) x) 0=
      if j=0 then 1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ else 0 := by
  rw [finiteAdditiveFourierCoeff_zero]
  have he:=canonical_zeroFourierCoefficient (Ideal.span {p}) hg hodd j hj
  convert he using 1
  exact congrArg (fun n:ℕ=>(if j=0 then 1-(n:ℂ)⁻¹ else 0)) (by rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card])


-- @@ L458-458 verbatim
end CubicEisenstein


-- @@ L460-460 verbatim
namespace CompletedGauss.FreeReflection

-- @@ L461-461 verbatim
open ActualEisensteinCubic CubicEisenstein LocalReflectionBrackets

-- @@ L462-462 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L463-464 verbatim
local instance inactivePoolMaximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal:=
  pool_maximal I Q Q0 P

-- @@ L465-466 verbatim
noncomputable local instance inactivePoolField (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Field (Eis⧸P.val):=
  Ideal.Quotient.field P.val

-- @@ L467-468 verbatim
noncomputable local instance inactivePoolFintype (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Fintype (Eis⧸P.val):=
  Fintype.ofFinite _


-- @@ L470-481 verbatim
lemma reflectionInactiveStratumWeight_formula (I F Q Q0:Ideal Eis) (A:Finset (pool I Q Q0)) :
    reflectionInactiveStratumWeight I F Q Q0 A=
      ∏P∈(Finset.univ:Finset (pool I Q Q0))\A,
        if completedLocalExponent I F P.val=0 then 1-(Ideal.absNorm P.val:ℂ)⁻¹ else 0 := by
  unfold reflectionInactiveStratumWeight
  apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro P hP
  have he:=canonical_zeroFourierCoefficient P.val (pool_good I Q Q0 P) (pool_odd I Q Q0 P)
    (completedLocalExponent I F P.val) (Nat.mod_lt _ (by decide))
  convert he using 1
  exact congrArg (fun n:ℕ=>(if completedLocalExponent I F P.val=0 then 1-(n:ℂ)⁻¹ else 0))
    (by rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card])


-- @@ L483-483 verbatim
end CompletedGauss.FreeReflection


-- @@ L485-485 verbatim
namespace CanonicalRowCompletion

-- @@ L486-486 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein

-- @@ L487-487 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L488-488 verbatim
namespace GoodMaskRowData

-- @@ L489-489 verbatim
variable {m f z:Eis} (D:GoodMaskRowData m f z)

-- @@ L490-495 verbatim
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (hm:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

-- @@ L496-496 verbatim
include R I F Q0 hR hI hF hm hf hz hbad hcop hA hT


-- @@ L498-559 verbatim
theorem inactive_source_reindex (w:Finset (FreePrimeIndex D.movingIdeal Q0)→ℂ) :
    letI : ∀P:FreePrimeIndex D.movingIdeal Q0,
      (Ideal.span {freePrimaryPrime D.movingIdeal Q0 P}:Ideal Eis).IsMaximal:=
        freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported
    let E:=D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT
    (∑A:Finset (FreePrimeIndex D.movingIdeal Q0),
      primeInactiveFourierWeight (freePrimaryPrime D.movingIdeal Q0)
        (freePrimaryPrime_ne_zero D.movingIdeal Q0 D.movingSupported)
        (freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported)
        (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) A*w A)=
      ∑B:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q0),
        FreeReflection.reflectionInactiveStratumWeight R F (Ideal.span {m}*F) Q0 B*
          w (residualActivePrimes E∪B.image (fun P=>E (Sum.inr P))) := by
  let : ∀P:FreePrimeIndex D.movingIdeal Q0,
      (Ideal.span {freePrimaryPrime D.movingIdeal Q0 P}:Ideal Eis).IsMaximal:=
        freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported
  dsimp only
  let E:=D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT
  let Z:FreePrimeIndex D.movingIdeal Q0→ℂ:=fun P=>
    if (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6=0 then
      1-(Ideal.absNorm P.val.val:ℂ)⁻¹ else 0
  have hzero (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) : Z (E (Sum.inl P))=0:=by
    dsimp only [Z]
    rw [D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inl P)]
    norm_num
  have hnonres (P:FreeReflection.pool R (Ideal.span {m}*F) Q0) :
      Z (E (Sum.inr P))=
        if completedLocalExponent R F P.val=0 then 1-(Ideal.absNorm P.val:ℂ)⁻¹ else 0:=by
    dsimp only [Z]
    rw [D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P),
      D.primeFiberEquiv_val R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P)]
    rfl
  have hw (A:Finset (FreePrimeIndex D.movingIdeal Q0)) :
      primeInactiveFourierWeight (freePrimaryPrime D.movingIdeal Q0)
        (freePrimaryPrime_ne_zero D.movingIdeal Q0 D.movingSupported)
        (freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported)
        (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) A=
      ∏P∈(Finset.univ:Finset (FreePrimeIndex D.movingIdeal Q0))\A,Z P:=by
    unfold primeInactiveFourierWeight
    apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro P hP
    rw [prime_zeroFourier_norm_formula _ _ _ (freePrimaryPrime_odd D.movingIdeal Q0 D.movingSupported P)
      _ (Nat.mod_lt _ (by decide)),freePrimaryPrime_span D.movingIdeal Q0 D.movingSupported P]
  simp only [hw]
  have he:=inactive_weight_nonresidual_subsets E Z hzero w
  refine Eq.trans ?_ (Eq.trans he ?_)
  · apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
    intro A hA
    congr 1
    apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro P hP
    rfl
  apply Finset.sum_congr (by ext B; simp only [Finset.mem_univ])
  intro B hB
  congr 1
  · rw [FreeReflection.reflectionInactiveStratumWeight_formula]
    apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro P hP
    exact hnonres P
  · apply congrArg w
    ext P
    simp only [E,residualActivePrimes,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]


-- @@ L561-561 verbatim
end GoodMaskRowData

-- @@ L562-562 verbatim
end CanonicalRowCompletion


-- @@ L564-564 verbatim
open scoped BigOperators Classical


-- @@ L566-566 verbatim
namespace CubicEisenstein

-- @@ L567-567 verbatim
open ActualEisensteinCubic

-- @@ L568-568 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L569-571 verbatim
noncomputable local instance rayUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _


-- @@ L573-591 verbatim
theorem sum_fixedReflectionRay {M:Type*} [AddCommMonoid M]
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    [∀h:Eis⧸Ideal.span {c},Fintype (fixedFourierGeometry c hc h).PhaseResidue]
    (F:FixedReflectionRay c hc → M) :
    (∑r:FixedReflectionRay c hc,F r)=
      ∑h:Eis⧸Ideal.span {c},∑rho:(fixedFourierGeometry c hc h).PhaseResidue,
        ∑u:Eisˣ,F ⟨h,rho,u⟩ := by
  let e : FixedReflectionRay c hc ≃
      (Σ h : Eis⧸Ideal.span {c}, (fixedFourierGeometry c hc h).PhaseResidue × Eisˣ) :=
    Equiv.refl _
  calc
    _ = ∑ r : (Σ h : Eis⧸Ideal.span {c},
        (fixedFourierGeometry c hc h).PhaseResidue × Eisˣ), F (e.symm r) :=
      Fintype.sum_equiv e _ _ (fun r => congrArg F (e.symm_apply_apply r).symm)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro h hh
      exact Fintype.sum_prod_type _


-- @@ L593-603 verbatim
theorem sum_fixedReflectionRayFin {M:Type*} [AddCommMonoid M]
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    [∀h:Eis⧸Ideal.span {c},Fintype (fixedFourierGeometry c hc h).PhaseResidue]
    (F:Fin (fixedReflectionRayCount c hc) → M) :
    (∑i:Fin (fixedReflectionRayCount c hc),F i)=
      ∑h:Eis⧸Ideal.span {c},∑rho:(fixedFourierGeometry c hc h).PhaseResidue,
        ∑u:Eisˣ,F (fixedReflectionRayEquiv c hc ⟨h,rho,u⟩) := by
  calc
    _=∑r:FixedReflectionRay c hc,F (fixedReflectionRayEquiv c hc r):=
      (Fintype.sum_equiv (fixedReflectionRayEquiv c hc) _ _ (fun _=>rfl)).symm
    _=_:=sum_fixedReflectionRay c hc _


-- @@ L605-605 verbatim
end CubicEisenstein


-- @@ L607-607 verbatim
end


-- @@ L609-609 verbatim
end OAI
