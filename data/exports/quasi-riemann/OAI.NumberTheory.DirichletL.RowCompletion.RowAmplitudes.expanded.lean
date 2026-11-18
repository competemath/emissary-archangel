import OAI.NumberTheory.DirichletL.GaussSum.ResidualEquivalence


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
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein

-- @@ L82-82 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L83-83 verbatim
namespace GoodMaskRowData

-- @@ L84-84 verbatim
variable {m f z:Eis} (D:GoodMaskRowData m f z)

-- @@ L85-88 verbatim
variable (Q:Ideal Eis) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})))


-- @@ L90-91 verbatim
abbrev activeStratum :=
  freePrimaryControlledStratum D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported c hcQ h G A


-- @@ L93-124 verbatim
def sourceRowScalar (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ) : ℂ := by
  letI : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  exact fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
    G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)*
    (D.activeStratum Q c hcQ h G A).modelRowPhase G.shape
      (fun P=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val)
      (fun P=>freePrimaryPrime_good D.movingIdeal _ D.movingSupported P.val)
      (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6) u n

lemma sourceRowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (u:Eisˣ) (n:ℕ) :
    ‖D.sourceRowScalar Q c hc hcQ h G A Ψ u n‖≤1 := by
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  have hp:(G.c0*∏P:A,freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)≠0:=
    mul_ne_zero G.denominator_ne_zero (Finset.prod_ne_zero_iff.mpr
      (fun P _=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val))
  have hs:=G.shape.stratumShapeFactor_norm _ hp
  have hr:=(D.activeStratum Q c hcQ h G A).modelRowPhase_norm
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ
      (fun P:A=>freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)
      (fun P _=>freePrimaryPrime_primary D.movingIdeal _ D.movingSupported P.val))
    G.primary G.shape
    (fun P=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val)
    (fun P=>freePrimaryPrime_good D.movingIdeal _ D.movingSupported P.val)
    (fun P=>freePrimaryPrime_odd D.movingIdeal _ D.movingSupported P.val)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6)
    (fun _=>Nat.mod_lt _ (by decide)) u n
  unfold sourceRowScalar
  rw [norm_mul,norm_mul,hs,hr,mul_one,mul_one]
  exact D.fixedCoefficient_norm Ψ Q hΨ c hc h


-- @@ L126-128 verbatim
def sourceRowResidue : G.PhaseResidue :=
  Ideal.Quotient.mk _ (-((D.activeStratum Q c hcQ h G A).matrix (fun _=>1) 1 1)*
    (D.activeStratum Q c hcQ h G A).U)


-- @@ L130-149 verbatim
def selectedSourceRowScalar (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ)
    (rho:G.PhaseResidue) (k dN dB:Ideal Eis) : ℂ :=
  if rho=D.sourceRowResidue Q c hcQ h G A then
    D.sourceRowScalar Q c hc hcQ h G A Ψ u n*residualArgumentPhase k 1 dN dB else 0

lemma selectedSourceRowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (u:Eisˣ) (n:ℕ)
    (rho:G.PhaseResidue) (k dN dB:Ideal Eis) :
    ‖D.selectedSourceRowScalar Q c hc hcQ h G A Ψ u n rho k dN dB‖≤1 := by
  unfold selectedSourceRowScalar
  split_ifs
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (D.sourceRowScalar_norm Q c hc hcQ h G A Ψ hΨ u n)).trans (residualArgumentPhase_norm_le_one k 1 dN dB)
  · simp

lemma sum_selectedSourceRowScalar [Fintype G.PhaseResidue]
    (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ) (k dN dB:Ideal Eis) :
    (∑rho:G.PhaseResidue,D.selectedSourceRowScalar Q c hc hcQ h G A Ψ u n rho k dN dB)=
      D.sourceRowScalar Q c hc hcQ h G A Ψ u n*residualArgumentPhase k 1 dN dB := by
  simp only [selectedSourceRowScalar,Finset.sum_ite_eq',Finset.mem_univ,ite_true]


-- @@ L151-151 verbatim
end GoodMaskRowData

-- @@ L152-152 verbatim
end

-- @@ L153-153 verbatim
section


-- @@ L155-155 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein

-- @@ L156-156 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L157-157 verbatim
namespace GoodMaskRowData

-- @@ L158-158 verbatim
variable {m f z:Eis} (D:GoodMaskRowData m f z)


-- @@ L160-177 verbatim
theorem completedT_eq_actualControlledSource
    (Q:Ideal Eis) (hQ:Q≠0) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (Ψ:Eis→*ℂ) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ m f z) W X=
      actualControlledSource D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported
        c hc hcQ G (D.fixedFactor Ψ Q) W X := by
  rw [D.completedT_eq_fixedFactor Ψ Q hmLam hm2 W X]
  apply fixedFree_completedT_eq_actualControlledSource D.movingIdeal _ D.movingSupported _
    c hc hcQ G (D.fixedFactor Ψ Q) (D.fixedFactor_periodic Ψ Q hΨ)
    (D.fixedFactor_norm Ψ Q hΨnorm) W lo hi hlo hsupp hW X hX
  apply mul_ne_zero hQ
  apply Ideal.span_singleton_eq_bot.not.mpr
  norm_num


-- @@ L179-179 verbatim
end GoodMaskRowData

-- @@ L180-180 verbatim
end


-- @@ L182-182 verbatim
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]


-- @@ L184-185 verbatim
def residualActivePrimes (e:α⊕β ≃ γ) : Finset γ :=
  Finset.univ.image (fun a:α=>e (Sum.inl a))


-- @@ L187-192 verbatim
omit [Fintype β] [Fintype γ] in
lemma residualActivePrimes_not_inr (e:α⊕β ≃ γ) (b:β) :
    e (Sum.inr b)∉residualActivePrimes e := by
  intro h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h
  cases e.injective ha


-- @@ L194-195 verbatim
def nonresidualComplementMap (e:α⊕β ≃ γ) : β → {g:γ // g∉residualActivePrimes e} :=
  fun b=>⟨e (Sum.inr b),residualActivePrimes_not_inr e b⟩


-- @@ L197-208 verbatim
omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementMap_bijective (e:α⊕β ≃ γ) :
    Function.Bijective (nonresidualComplementMap e) := by
  constructor
  · intro a b hab
    exact Sum.inr.inj (e.injective (congrArg Subtype.val hab))
  · intro g
    obtain ⟨x,hx⟩:=e.surjective g.val
    cases x with
    | inl a=>
      exact (g.property (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,hx⟩)).elim
    | inr b=>exact ⟨b,Subtype.ext hx⟩


-- @@ L210-212 verbatim
noncomputable def nonresidualComplementEquiv (e:α⊕β ≃ γ) :
    β ≃ {g:γ // g∉residualActivePrimes e} :=
  Equiv.ofBijective (nonresidualComplementMap e) (nonresidualComplementMap_bijective e)


-- @@ L214-216 verbatim
omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementEquiv_val (e:α⊕β ≃ γ) (b:β) :
    (nonresidualComplementEquiv e b).val=e (Sum.inr b) := rfl


-- @@ L218-235 verbatim
omit [Fintype β] [Fintype γ] in
lemma complementActive_image (e:α⊕β ≃ γ) (B:Finset β) :
    (B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val=
      B.image (fun b=>e (Sum.inr b)) := by
  simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
    Equiv.toEmbedding_apply,nonresidualComplementEquiv_val]

lemma inactive_product_nonresidual (e:α⊕β ≃ γ) (z:γ → ℂ) (B:Finset β) :
    (∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
      B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)=
      ∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)) := by
  symm
  apply Finset.prod_equiv (nonresidualComplementEquiv e)
  · intro b
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_map_equiv,
      Equiv.symm_apply_apply]
  · intro b hb
    rfl


-- @@ L237-253 verbatim
theorem inactive_weight_nonresidual_subsets (e:α⊕β ≃ γ) (z:γ → ℂ)
    (hz:∀a:α,z (e (Sum.inl a))=0) (F:Finset γ → ℂ) :
    (∑A:Finset γ,(∏g∈(Finset.univ:Finset γ)\A,z g)*F A)=
      ∑B:Finset β,(∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)))*
        F (residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))) := by
  have hres:∀g∈residualActivePrimes e,z g=0:=by
    intro g hg
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hg
    exact hz a
  rw [CompletedGauss.inactive_weight_optional_active (residualActivePrimes e) z hres F]
  symm
  apply Fintype.sum_equiv (nonresidualComplementEquiv e).finsetCongr
  intro B
  change _=(∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
    B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)*
    F (residualActivePrimes e∪(B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val)
  rw [inactive_product_nonresidual,complementActive_image]


-- @@ L255-255 verbatim
end CanonicalRowCompletion


-- @@ L257-257 verbatim
open scoped BigOperators Classical ContDiff


-- @@ L259-259 verbatim
namespace CompletedGauss

-- @@ L260-260 verbatim
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets

-- @@ L261-281 verbatim
local notation "Eis" => ActualEisensteinCubic.O

lemma active_product_residual_equiv {ι β:Type*} [Fintype ι] [Fintype β]
    (I Q:Ideal Eis) (P:ι→Ideal Eis) (R:β→Ideal Eis)
    (E:PrimeIndex (rowResidualPart I Q)⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r) :
    (∏i,P i)=rowResidualPart I Q*∏i,R i := by
  rw [←E.prod_comp,Fintype.prod_sum_type]
  simp only [hres,hnonres]
  congr 1
  change (∏r:primeSupport (rowResidualPart I Q),r.val)=rowResidualPart I Q
  exact (Finset.prod_coe_sort (primeSupport (rowResidualPart I Q))
      (fun r : Ideal Eis => r)).trans
    (IdealMobiusDivisorSum.squarefree_support_product_self (rowResidualPart_squarefree I Q))

lemma actual_bracket_ideal_congr (P Q:Ideal Eis) [P.IsMaximal] [Q.IsMaximal]
    (hP:lambda∉P) (hQ:lambda∉Q) (hPQ:P=Q) (j:ℕ) (z:Eis) :
    bracket (actualSextic P hP) j (Ideal.Quotient.mk P z)=
      bracket (actualSextic Q hQ) j (Ideal.Quotient.mk Q z) := by
  subst Q
  rfl


-- @@ L283-322 verbatim
theorem residual_equiv_coefficient {ι β:Type*} [Fintype ι] [Fintype β]
    (I F Q:Ideal Eis) (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (R:β→Ideal Eis) [∀i,(R i).IsMaximal] (hR:∀i,lambda∉R i)
    (E:PrimeIndex (rowResidualPart I Q)⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r)
    (j:ι→ℕ) (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=completedLocalExponent I F (R r))
    (e:β→Fin 3) (ρ q:ℝ) (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (m:ℕ) (n b:Ideal Eis) :
    let A:=reflectionExtractedDivisor R (fun r=>completedLocalExponent I F (R r)) e 1
    let B:=reflectionExtractedDivisor R (fun r=>completedLocalExponent I F (R r)) e 2
    unextractedCuspCoefficient P hg j (residualLabelVia E e) ρ q η σ m (A*n) (B*b)=
      4*canonicalRawBranchCoefficient R hR (fun r=>completedLocalExponent I F (R r)) e ρ q
        (fun l a c=>η l (A*a) (B*c))
        (fun l=>σ l*residualArgumentPhase (rowResidualPart I Q) 1 A B)
        (rowResidualPart I Q) m n b := by
  dsimp only
  rw [unextractedCuspCoefficient,reflectedBranch_drop_residual_equiv E P hg j hjres]
  have hchar (r:PrimeIndex (rowResidualPart I Q)) (z:Eis) :
      bracket (actualSextic (P (E (Sum.inl r))) (hg (E (Sum.inl r)))) 1 (Ideal.Quotient.mk _ z)=
      bracket (actualSextic r.val (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) r))
        (completedLocalExponent I F r.val) (Ideal.Quotient.mk _ z) := by
    rw [completedLocalExponent_residual I F Q hFQ]
    exact actual_bracket_ideal_congr _ _ _ _ (hres r) 1 z
  have hnbranch (a b:Eis):
      reflectedBranch (fun r=>P (E (Sum.inr r))) (fun r=>hg (E (Sum.inr r)))
        (fun r=>j (E (Sum.inr r))) e a b=
      reflectedBranch R hR (fun r=>completedLocalExponent I F (R r)) e a b := by
    unfold reflectedBranch
    apply Finset.prod_congr rfl
    intro r hr
    change reflectedLocalPiece (P (E (Sum.inr r))) _ (j (E (Sum.inr r))) (e r) a b=_
    simp only [hnonres r,hjnonres r]
  simp_rw [hchar]
  rw [hnbranch]
  have ht:=residual_coefficient_eq_canonical_argument I F Q hFQ hbad R hR
    (fun r=>completedLocalExponent I F (R r)) e ρ q (fun _=>1) η σ m n b
  simp only [one_mul] at ht
  convert ht using 1 ; ring


-- @@ L324-324 verbatim
end CompletedGauss


-- @@ L326-326 verbatim
namespace CubicEisenstein

-- @@ L327-327 verbatim
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve

-- @@ L328-328 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L329-329 verbatim
namespace FixedFourierGeometry

-- @@ L330-330 verbatim
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)

-- @@ L331-331 verbatim
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}


-- @@ L333-398 verbatim
theorem stratumBranchTerm_tsum_eq_rawValue
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {I F Q:Ideal Eis} {levelBound K:ℝ} (d:ReflectedBranchData levelBound K I F Q)
    (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q) (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q)) (hk:k.val=rowResidualPart I Q)
    (E:PrimeIndex (rowResidualPart I Q)⊕d.primes≃ι)
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
    rw [FiniteGaussPhase.span_finset_prod,hk]
    exact active_product_residual_equiv I Q (fun i=>Ideal.span {p i})
      (fun r:d.primes=>r.val) E hres hnonres
  have hk0:k.val≠0:=(mem_idealRange.mp k.property).1.1
  unfold ReflectedBranchData.rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  have hcoef:=residual_equiv_coefficient I F Q hFQ hbad (fun i=>Ideal.span {p i}) hg
    (fun r:d.primes=>r.val) d.good E hres hnonres j hjres hjnonres d.label
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
  rw [hcoef,harg,hk]
  exact mul_assoc _ _ _


-- @@ L400-400 verbatim
end FixedFourierGeometry

-- @@ L401-401 verbatim
end CubicEisenstein


-- @@ L403-403 verbatim
open scoped Classical BigOperators ContDiff


-- @@ L405-405 verbatim
namespace CanonicalRowCompletion

-- @@ L406-406 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass

-- @@ L407-407 verbatim
open ConcretePrimeRowBridge SecondPassArithmetic

-- @@ L408-408 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L410-429 verbatim
def HasFixedShellModels (S:Finset (Ideal Eis)) (base:Eis→*ℂ)
    (rays:ℕ) (scale:ℂ) (ρ q level:ℝ) : Prop :=
  ∀ Ψ:Eis→*ℂ,IsBaseRayTwist base Ψ→∀m:Eis,m≠0→
    ∀ F:ℝ,∀f:idealRange F,∀u:Eisˣ,∀ W:ℝ→ℂ,∀a b:ℝ,
      0<a→Function.support W⊆Set.Icc a b→ContDiff ℝ ∞ W→
      ∀K X:ℝ,0<K→0<X→∀rows:Finset (Ideal Eis),
        (∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)→
        HasExactCompletedModels rays rows K X ρ q level f.val
          (Ideal.span {m*excludedGenerator S}*f.val) W
          (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) scale

lemma normTwistedSource_contDiff (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (t:ℝ) :
    ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W t) := by
  have he:(CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t:ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t:=by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  rw [←he]
  exact (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t).smooth ⊤


-- @@ L431-461 verbatim
theorem hasCanonicalThetaModels_of_fixed_shell_models
    (S:Finset (Ideal Eis)) (base:Eis→*ℂ) (rays:ℕ) (scale:ℂ) (ρ q level:ℝ)
    (hmodels:HasFixedShellModels S base rays scale ρ q level) :
    HasCanonicalThetaModels S base ρ q level := by
  intro A hA W hs hW κ hκ
  refine ⟨(rays:ℝ)^2*‖scale‖^2,by positivity,?_⟩
  intro Z K X F θ hZ hK hX hF hFZ Ψ hΨ m hm
  dsimp only
  intro hmargin
  refine ⟨rays,scale,?_,?_⟩
  · exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hκ.le)
  · intro u f H hH
    have hH0:H≠0:=((mem_shortCubeRange _ H).mp hH).1
    have hHN:(0:ℝ)<(Ideal.absNorm H:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hH0)
    have hXH:0<X/(Ideal.absNorm H:ℝ)^3:=by positivity
    have hsTw:Function.support (CompletedHeight.normTwistedSource W θ)⊆
        Set.Icc (Real.exp (-A)) (Real.exp A):=
      (CompletedHeight.normTwistedSource_support W θ).trans hs
    have hTw:=normTwistedSource_contDiff W (Real.exp (-A)) (Real.exp A)
      (Real.exp_pos _) hs hW θ
    let rows:=((firstFrequencyDisk (2*K)).erase 0).image (fun z:Eis=>Ideal.span {z})
    have hrows:∀I∈rows,I≠0:=by
      intro I hI
      obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
      exact Ideal.span_singleton_eq_bot.not.mpr (Finset.mem_erase.mp hz).1
    intro j hj
    exact hmodels Ψ hΨ m hm F f u (CompletedHeight.normTwistedSource W θ)
      (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) hsTw hTw
      ((2:ℝ)^j) (X/(Ideal.absNorm H:ℝ)^3) (by positivity) hXH
      (completedRowDyad rows j) (completedRowDyad_bounds rows j hrows)


-- @@ L463-463 verbatim
end CanonicalRowCompletion


-- @@ L465-465 verbatim
open scoped Classical BigOperators


-- @@ L467-467 verbatim
namespace CompletedGauss.ReflectedBranchData

-- @@ L468-468 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

-- @@ L469-469 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L470-470 verbatim
variable {levelBound K:ℝ} {I F Q:Ideal Eis}

-- @@ L471-471 verbatim
variable (d:ReflectedBranchData levelBound K I F Q)

-- @@ L472-472 verbatim
variable (η:ℕ→Ideal Eis→Ideal Eis→ℂ)

-- @@ L473-473 verbatim
variable (σ τ:ℕ→idealRange (completedResidualScale K I Q)→ℂ)

-- @@ L474-507 verbatim
variable (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q))

lemma rawValue_congr_phase_at (h:∀m,σ m k=τ m k) :
    d.rawValue η σ W X ρ q k=d.rawValue η τ W X ρ q k := by
  unfold rawValue
  apply tsum_congr
  intro x
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,h]

lemma rawValue_zero_phase : d.rawValue η (fun _ _=>0) W X ρ q k=0 := by
  unfold rawValue
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,zero_mul,tsum_zero]

lemma rawValue_mul_phase_at (a:idealRange (completedResidualScale K I Q)→ℂ) :
    d.rawValue η (fun m l=>a l*σ m l) W X ρ q k=a k*d.rawValue η σ W X ρ q k := by
  unfold rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  unfold rawDualKernelTerm canonicalRawBranchCoefficient
  ring

lemma rawValue_select_phase_at (P:idealRange (completedResidualScale K I Q)→Prop)
    [DecidablePred P] :
    d.rawValue η (fun m l=>if P l then σ m l else 0) W X ρ q k=
      if P k then d.rawValue η σ W X ρ q k else 0 := by
  by_cases hp:P k
  · rw [ite_eq_left hp]
    exact d.rawValue_congr_phase_at η _ σ W X ρ q k (fun m=>ite_eq_left hp)
  · rw [ite_eq_right hp]
    calc
      _=d.rawValue η (fun _ _=>0) W X ρ q k:=
        d.rawValue_congr_phase_at η _ _ W X ρ q k (fun m=>ite_eq_right hp)
      _=0:=d.rawValue_zero_phase η W X ρ q k


-- @@ L509-509 verbatim
end CompletedGauss.ReflectedBranchData


-- @@ L511-511 verbatim
open scoped BigOperators Classical


-- @@ L513-513 verbatim
namespace CanonicalRowCompletion

-- @@ L514-514 verbatim
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]


-- @@ L516-517 verbatim
def completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) : Finset γ :=
  residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))


-- @@ L519-522 verbatim
omit [Fintype β] [Fintype γ] in
lemma completeActiveSet_residual (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    e (Sum.inl a)∈completeActiveSet e B :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)


-- @@ L524-536 verbatim
omit [Fintype γ] in
lemma optionalPrimeActive_completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) :
    optionalPrimeActive e (completeActiveSet e B)=B := by
  ext b
  rw [mem_optionalPrimeActive]
  change e (Sum.inr b)∈residualActivePrimes e∪B.image (fun b=>e (Sum.inr b)) ↔ b∈B
  simp only [Finset.mem_union,residualActivePrimes_not_inr,false_or,Finset.mem_image]
  constructor
  · rintro ⟨b',hb',he⟩
    have hb:b'=b:=Sum.inr.inj (e.injective he)
    exact hb ▸ hb'
  · intro hb
    exact ⟨b,hb,rfl⟩


-- @@ L538-546 verbatim
noncomputable def selectedActiveEquiv (e:α⊕β ≃ γ) (B:Finset β) :
    α⊕B ≃ completeActiveSet e B := by
  let t : B ≃ optionalPrimeActive e (completeActiveSet e B):={
    toFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    invFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (Equiv.sumCongr (Equiv.refl _) t).trans
    (activePrimeUnionEquiv e (completeActiveSet e B) (completeActiveSet_residual e B))


-- @@ L548-550 verbatim
omit [Fintype γ] in
lemma selectedActiveEquiv_inl (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    (selectedActiveEquiv e B (Sum.inl a)).val=e (Sum.inl a) := rfl


-- @@ L552-554 verbatim
omit [Fintype γ] in
lemma selectedActiveEquiv_inr (e:α⊕β ≃ γ) (B:Finset β) (b:B) :
    (selectedActiveEquiv e B (Sum.inr b)).val=e (Sum.inr b.val) := rfl


-- @@ L556-556 verbatim
end CanonicalRowCompletion


-- @@ L558-558 verbatim
open scoped BigOperators Classical


-- @@ L560-560 verbatim
namespace CanonicalRowCompletion.ActualFiber

-- @@ L561-561 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein

-- @@ L562-562 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L564-564 verbatim
def maskElement (q:ℕ) (m:Eis) : Eis := m*excludedGenerator (reflectionExcludedPrimes q)

-- @@ L565-565 verbatim
def maskIdeal (q:ℕ) (m:Eis) (F:Ideal Eis) : Ideal Eis := Ideal.span {maskElement q m}*F

-- @@ L566-566 verbatim
def freeConductor (q:ℕ) : Ideal Eis := CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}

-- @@ L567-575 verbatim
abbrev RowIndex (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis)) (R F:Ideal Eis) :=
  representativeRowFiber rows R (maskIdeal q m F)

lemma maskElement_ne_zero (q:ℕ) (m:Eis) (hm:m≠0) : maskElement q m≠0 :=
  mul_ne_zero hm (reflectionExcludedGenerator_ne_zero q)
lemma maskIdeal_ne_zero (q:ℕ) (m:Eis) (hm:m≠0) (F:Ideal Eis) (hF:F≠0) : maskIdeal q m F≠0 :=
  mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (maskElement_ne_zero q m hm)) hF
lemma mask_bad (q:ℕ) (m:Eis) (F:Ideal Eis) : ∀P∈fixedBadPrimes,P∣maskIdeal q m F :=
  reflection_row_mask_bad q m F


-- @@ L577-579 verbatim
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)


-- @@ L581-584 verbatim
noncomputable def data (J:RowIndex q m rows R F) :
    GoodMaskRowData (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val) :=
  fiberGoodMaskRowData rows R F (maskElement q m) (maskElement_ne_zero q m hm) hF.ne_zero hrows v J


-- @@ L586-596 verbatim
noncomputable def splitIndex (J:RowIndex q m rows R F) :
    PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.pool R (maskIdeal q m F) (freeConductor q) ≃
      FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) := by
  have hJ:J.val≠0:=hrows J.val (Finset.mem_filter.mp J.property).1
  have hz:Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator J.val}=J.val:=by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
  have parts:=representativeFiber_parts rows R (maskIdeal q m F) J
  exact (data q m hm rows R F hF hrows v J).primeFiberEquiv R J.val F (freeConductor q)
    hR hJ hF (maskElement_ne_zero q m hm) (ConcretePrimeRowBridge.span_idealGenerator F) hz
    (mask_bad q m F) (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm


-- @@ L598-601 verbatim
noncomputable def activeSet (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F) :
    Finset (FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q)) :=
  completeActiveSet (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e)


-- @@ L603-608 verbatim
def columnDivisor (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (side:Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor
    (fun P:FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e=>P.val)
    (fun P=>completedLocalExponent R F P.val)
    (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e) side


-- @@ L610-610 verbatim
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]


-- @@ L612-633 verbatim
noncomputable def rowScalar (Ψ:Eis→*ℂ)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) : ℂ :=
  (data q m hm rows R F hF hrows v J).selectedSourceRowScalar
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) Ψ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)

lemma rowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) :
    ‖rowScalar q hq m hm rows R F hR hF hrows v Ψ x n J‖≤1 := by
  exact (data q m hm rows R F hF hrows v J).selectedSourceRowScalar_norm
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) Ψ hΨ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)


-- @@ L635-654 verbatim
noncomputable def reflectedFiber (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      (fixedCuspLevelBound (reflectionConductor q)) K R F (maskIdeal q m F) :=
  FreeReflection.fixedRayFiberFromRows (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    rows R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun a J=>rowScalar q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J)
    (fun a J=>rowScalar_norm q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J)

lemma reflectedFiber_rowPhase (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq))
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6) (i:ℕ×ℕ×ℕ) :
    ((reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)).rowPhase i
        (fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
          (fun I hI=>⟨hrows I hI,hbound I hI⟩) J)=
      rowScalar q hq m hm rows R F hR hF hrows v Ψ (ray,e) i.1 J := by
  exact FreeReflection.fixedRayFiberFromRows_rowPhase _ _ _ _ _ _ _ _ _ _ _ _
    (mask_bad q m F) (fun I hI=>⟨hrows I hI,hbound I hI⟩) J ray e i


-- @@ L656-656 verbatim
end CanonicalRowCompletion.ActualFiber


-- @@ L658-658 verbatim
end


-- @@ L660-660 verbatim
end OAI
