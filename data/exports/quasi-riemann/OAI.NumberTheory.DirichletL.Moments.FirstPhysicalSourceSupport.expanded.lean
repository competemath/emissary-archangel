import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceNormalization
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalSourceSupport

-- @@ L12-12 verbatim
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge

-- @@ L13-13 verbatim
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst

-- @@ L14-14 verbatim
open CenteredMomentFirstPhysicalSource CenteredMomentFirstWholeKernel

-- @@ L15-15 verbatim
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic

-- @@ L16-16 verbatim
open CenteredMomentSourceLowerSupport CenteredMomentExceptionalAmplitudePair

-- @@ L17-17 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L18-18 verbatim
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L20-45 verbatim
theorem nonzero_columns (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    ∃a:columns C C hC.1 S,∃b:columns C D hD.1 S,
      c (C*(a:Ideal O))≠0 ∧ c (D*(b:Ideal O))≠0 ∧
      V 2 (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))≠0 ∧
      V 3 (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀))≠0 := by
  unfold block at hn
  have hs:=right_ne_zero_of_mul hn
  obtain ⟨z,hz,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨a,ha,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨b,hb,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  dsimp only at hs
  split_ifs at hs with hab
  · have hprod:=left_ne_zero_of_mul (left_ne_zero_of_mul hs)
    have hc:=right_ne_zero_of_mul hprod
    have hw:=right_ne_zero_of_mul (left_ne_zero_of_mul hs)
    refine ⟨a,b,?_,?_,?_,?_⟩
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul hc)
    · have hh:=right_ne_zero_of_mul hc
      rw [star_ne_zero] at hh
      exact left_ne_zero_of_mul hh
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul hw)
    · exact right_ne_zero_of_mul hw
  · exact False.elim (hs rfl)


-- @@ L47-58 verbatim
theorem original_column_lower {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(a₁ a₂:ℝ)(ha₁:0≤a₁)(ha₂:0≤a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (hn:CenteredMomentOriginalCommonHarmonic.coefficient s R seed I≠0):
    (∏i,s.lo i)*a₁*a₂*volume s.toData≤(I.absNorm:ℝ) := by
  have hh:=profile_column_lower R s.ν s.W s.P s.lo s.W₁ s.W₂ a₁ a₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos
    (fun i=>(s.lo_pos i).le) ha₁ ha₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product (fun i x hx=>(s.support i hx).1)
    hs₁ hs₂ (Fintype.piFinset s.pools) I (by
      simpa only [CenteredMomentOriginalCommonHarmonic.coefficient] using hn)
  simpa only [map_one,Nat.cast_one,mul_one,div_one,volume,mul_assoc] using hh


-- @@ L60-65 verbatim
lemma log_window_upper (N H M:ℝ)(hN:0<N)(hH:0<H)
    (hlog:|Real.log (N/H)|≤M):N≤Real.exp M*H := by
  have hl:Real.log (N/H)≤M:=(le_abs_self _).trans hlog
  have he:=Real.exp_le_exp.mpr hl
  rw [Real.exp_log (div_pos hN hH)] at he
  exact (div_le_iff₀ hH).mp he


-- @@ L67-93 verbatim
theorem block_reference_lower (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀ a T M:ℝ)
    (hA:0<A₀)(hB:0<B₀)(hsource:∀I,c I≠0→a*T≤(I.absNorm:ℝ))
    (hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    a*T≤(C.absNorm:ℝ)*Real.exp M*A₀ ∧
      a*T≤(D.absNorm:ℝ)*Real.exp M*B₀ := by
  obtain ⟨i,j,hi,hj,hwi,hwj⟩:=nonzero_columns η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀ hn
  have hiN:(0:ℝ)<(i:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C C hC.1 S i).1)
  have hjN:(0:ℝ)<(j:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C D hD.1 S j).1)
  have hni:‖eisEmbedding (element C C hC.1 S i)‖^2=((i:Ideal O).absNorm:ℝ):=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hnj:‖eisEmbedding (element C D hD.1 S j)‖^2=((j:Ideal O).absNorm:ℝ):=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hli:=hwin 2 _ hwi
  have hlj:=hwin 3 _ hwj
  rw [hni] at hli
  rw [hnj] at hlj
  have hsi:=hsource _ hi
  have hsj:=hsource _ hj
  simp only [map_mul,Nat.cast_mul] at hsi hsj
  constructor
  · exact hsi.trans (by nlinarith [log_window_upper _ _ M hiN hA hli])
  · exact hsj.trans (by nlinarith [log_window_upper _ _ M hjN hB hlj])


-- @@ L95-106 verbatim
lemma reference_sqrt_lower (NC ND A₀ B₀ a T M:ℝ)
    (hNC:0≤NC)(hND:0≤ND)(hA:0≤A₀)(_hB:0≤B₀)(ha:0≤a)(hT:0≤T)
    (hl:a*T≤NC*Real.exp M*A₀)(hr:a*T≤ND*Real.exp M*B₀):
    a*T≤Real.exp M*Real.sqrt (NC*ND)*(Real.sqrt A₀*Real.sqrt B₀) := by
  have hh:=mul_le_mul hl hr (mul_nonneg ha hT) (by positivity : 0≤NC*Real.exp M*A₀)
  have hs:(a*T)^2≤(NC*ND)*(Real.exp M)^2*(A₀*B₀):=by nlinarith [hh]
  have hsqrt:=Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq (mul_nonneg ha hT),
    Real.sqrt_mul (mul_nonneg (mul_nonneg hNC hND) (sq_nonneg _)),
    Real.sqrt_mul (mul_nonneg hNC hND),Real.sqrt_sq (Real.exp_pos M).le,
    Real.sqrt_mul hA] at hsqrt
  nlinarith [hsqrt]


-- @@ L108-135 verbatim
theorem scalar_volume_bound (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a T M:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(ha:0≤a)(hT:0≤T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*(a*T)≤
      Real.exp M*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖) := by
  have hs:=reference_sqrt_lower (C.absNorm:ℝ) (D.absNorm:ℝ) A₀ B₀ a T M
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA.le hB.le ha hT hl hr
  have hden:0<Real.sqrt A₀*Real.sqrt B₀:=mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hratio:(a*T)/(Real.sqrt A₀*Real.sqrt B₀)≤Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm):=
    (div_le_iff₀ hden).mpr hs
  have hmu:‖inactiveWeight C D E‖≤1:=QuadraticInitialBound.norm_ideal_moebius_le_one _
  rw [scalar_norm C D hC E K A₀ B₀ hK hA hB]
  calc
    _=(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*((a*T)/(Real.sqrt A₀*Real.sqrt B₀)):=by ring
    _≤(‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)):=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _≤_:=by
      have hh:=mul_le_mul_of_nonneg_right hmu (show 0≤K/(‖eisEmbedding
        (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖)*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)) by positivity)
      convert hh using 1 <;> ring


-- @@ L137-163 verbatim
theorem original_scalar_volume {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀ M:ℝ)
    (hK:0<K)(hA:0<A₀)(hB:0<B₀)(hwin:∀i y,V i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    ‖scalar C D hC E K A₀ B₀‖*volume s.toData≤
      (Real.exp M/((∏i,s.lo i)*a₁*a₂))*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖) := by
  let a:ℝ:=(∏i,s.lo i)*a₁*a₂
  have ha:0<a:=mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  have hV:0<volume s.toData:=volume_pos s.toData
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W V
    K K₀ H₀ A₀ B₀ a (volume s.toData) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  have hh:=scalar_volume_bound C D hC E K A₀ B₀ a (volume s.toData) M hK hA hB ha.le hV.le hl hr
  calc
    _=(‖scalar C D hC E K A₀ B₀‖*(a*volume s.toData))/a:=by field_simp
    _≤(Real.exp M*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖))/a:=div_le_div_of_nonneg_right hh ha.le
    _=_:=by dsimp only [a];ring


-- @@ L165-165 verbatim
end SevenEighths.CenteredMomentFirstPhysicalSourceSupport


-- @@ L167-167 verbatim
end


-- @@ L169-169 verbatim
end OAI
