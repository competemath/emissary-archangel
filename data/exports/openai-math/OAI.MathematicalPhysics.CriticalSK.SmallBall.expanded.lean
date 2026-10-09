import OAI.MathematicalPhysics.CriticalSK.DisorderTransfer
import OAI.MathematicalPhysics.CriticalSK.OrientationLimits


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators Topology NNReal ENNReal


-- @@ L10-10 verbatim
open scoped BigOperators ENNReal NNReal Real Topology


-- @@ L12-12 verbatim
open MeasureTheory ProbabilityTheory Filter


-- @@ L14-14 verbatim
open scoped ENNReal NNReal


-- @@ L16-16 verbatim
open scoped BigOperators NNReal


-- @@ L18-18 verbatim
open scoped BigOperators


-- @@ L20-20 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L22-22 verbatim
open Module


-- @@ L24-24 verbatim
open Matrix Polynomial


-- @@ L26-26 verbatim
open scoped BigOperators Topology


-- @@ L28-28 verbatim
open Filter


-- @@ L30-30 verbatim
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise


-- @@ L32-32 verbatim
open Set Metric MeasureTheory MeasureTheory.Measure


-- @@ L34-34 verbatim
open scoped ENNReal NNReal BigOperators


-- @@ L36-36 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L38-38 verbatim
open scoped ENNReal NNReal Topology


-- @@ L40-40 verbatim
open MeasureTheory MeasureTheory.Measure Set Metric


-- @@ L42-42 verbatim
open scoped NNReal ENNReal BigOperators


-- @@ L44-44 verbatim
open scoped NNReal ENNReal


-- @@ L46-46 verbatim
open ProbabilityTheory


-- @@ L48-48 verbatim
open Metric Set MeasureTheory


-- @@ L50-50 verbatim
open scoped ENNReal Pointwise


-- @@ L52-52 verbatim
open MeasureTheory Filter Set Real


-- @@ L54-54 verbatim
open Finset Real


-- @@ L56-56 verbatim
open scoped BigOperators ENNReal Topology


-- @@ L58-58 verbatim
open Set MeasureTheory


-- @@ L60-60 verbatim
open scoped BigOperators ENNReal


-- @@ L62-62 verbatim
open MeasureTheory


-- @@ L64-64 verbatim
open Finset Real Filter


-- @@ L66-66 verbatim
open scoped Topology


-- @@ L68-68 verbatim
namespace CriticalSK


-- @@ L70-70 verbatim
section


-- @@ L72-84 verbatim
lemma gaussian_inverse_sqrt_bound {s v : ℝ} (hs : 0 < s) (hv : 1/(2*s) ≤ v) :
    (Real.sqrt (2*Real.pi*v))⁻¹ ≤ Real.sqrt s := by
  have hv0 : 0 < v := (by positivity : (0:ℝ) < 1/(2*s)).trans_le hv
  have hp : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hprod : 1 ≤ 2*Real.pi*v*s := by
    have hh := (div_le_iff₀ (by positivity : (0:ℝ) < 2*s)).mp hv
    have hhs : 0 ≤ 2*v*s := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hp hhs]
  have hr : 1 ≤ Real.sqrt (2*Real.pi*v)*Real.sqrt s := by
    rw [← Real.sqrt_mul (by positivity)]
    simpa using Real.sqrt_le_sqrt hprod
  rw [inv_eq_one_div,div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  nlinarith


-- @@ L86-122 verbatim
lemma spectralGood_sphere_smallBall {n : ℕ} {lam : Fin (n+3) → ℝ} {h s b : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost (n+2) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+2) h s)
    (hspace : 32768 ≤ (n+3:ℝ)*s*Real.sqrt s)
    (h0 : |lam 0-2| ≤ s/4) (h1 : |lam 1-2| ≤ s/4) (h2 : |lam 2-2| ≤ s/4)
    (hb : 0 ≤ b) :
    (sphereTilted lam 1 (Real.sqrt (n+3))).real
      {u : unitSphere (Fin (n+3)) | |(Real.sqrt (n+3) • u.val) 2| ≤ b} ≤
      4*b*Real.sqrt s*Real.exp (6*((n+3:ℝ)*s*Real.sqrt s)) := by
  have hv := spectralGood_fixed_variance (n := n+1) hh hs hs1 hcost hlam
    (by norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc]; exact hspace)
  have hd := fixedBulkDeficit_bounds (n := n+1) hh hs hs1 hcost hlam
    (by norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc]; exact hspace)
  norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc] at hv hd
  have hn : (0:ℝ) < n+3 := by positivity
  have hroot : 0 < Real.sqrt (n+3:ℝ) := Real.sqrt_pos.mpr hn
  have hm : 0 < (1:ℝ)/(2*s) := by positivity
  have hz (j) : fixedEdgeVariance lam s j ≠ 0 := fixedEdgeVariance_pos hv.1 j
  have hq (j) : (fixedEdgeVariance lam s j:ℝ)⁻¹ = 2+s-1*lam j := by
    simpa only [one_mul] using fixedEdgeVariance_inverse hv.1 j
  have hb' := sphereTilted_smallBall lam 1 (2+s) (fixedEdgeVariance lam s) hz hq hn hm
    (fixedEdgeVariance_lower hs hv.1 0 h0) (fixedEdgeVariance_lower hs hv.1 1 h1) hd.1
    (div_nonneg hb hroot.le) (by unfold fixedBulkDeficit; push_cast; ring) hd.2.2
  have hset : {u : unitSphere (Fin (n+3)) | |u.val (0 : Fin (n+1)).succ.succ| ≤ b/Real.sqrt (n+3)} =
      {u : unitSphere (Fin (n+3)) | |(Real.sqrt (n+3) • u.val) 2| ≤ b} := by
    ext u
    change |u.val 2| ≤ b/Real.sqrt (n+3) ↔ |Real.sqrt (n+3)*u.val 2| ≤ b
    rw [abs_mul,abs_of_nonneg hroot.le,le_div_iff₀ hroot,mul_comm]
  rw [hset] at hb'
  have hsq := gaussian_inverse_sqrt_bound hs (fixedEdgeVariance_lower hs hv.1 2 h2)
  have he := Real.exp_le_exp.mpr hd.2.1
  have hb'' : (sphereTilted lam 1 (Real.sqrt (n+3))).real
      {u : unitSphere (Fin (n+3)) | |(Real.sqrt (n+3) • u.val) 2| ≤ b} ≤
      4*b*(Real.sqrt (2*Real.pi*(fixedEdgeVariance lam s 2:ℝ)))⁻¹*Real.exp (fixedBulkDeficit lam s/((1:ℝ)/(2*s))) := by
    simpa only [Measure.real,div_mul_cancel₀ _ hroot.ne',show (0:Fin (n+1)).succ.succ = (2:Fin (n+3)) from rfl] using hb'
  exact hb''.trans (mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity)) he
    (Real.exp_pos _).le (by positivity))


-- @@ L124-124 verbatim
open Set MeasureTheory Filter


-- @@ L126-126 verbatim
def naturalSmallBallConstant (L : ℝ) : ℝ := 4*Real.sqrt L*Real.exp (6*(L*Real.sqrt L))


-- @@ L128-186 verbatim
lemma spectralGood_natural_sphere_bounds {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood (n+3) h (naturalEdgeScale (n+3) L),
      (∀ b : ℝ, 0 ≤ b → (sphereTilted lam 1 (Real.sqrt (n+4))).real
        {u : unitSphere (Fin (n+4)) | |(Real.sqrt (n+4) • u.val) 2| ≤ b*(n+4:ℝ)^(1/3:ℝ)} ≤
        naturalSmallBallConstant L*b) ∧
      ((∑ i, (∫ u : unitSphere (Fin (n+4)), ((Real.sqrt (n+4) • u.val) i)^2
        ∂sphereTilted lam 1 (Real.sqrt (n+4)))^2)/(n+4:ℝ)^2 ≤ naturalOverlapRate (n+3) L) := by
  have hLp : 0 < L := by linarith
  have hLa : 1696 ≤ L := by linarith
  have hc := (tendsto_add_atTop_nat 3).eventually (traceCost_natural_eventually hh hLp hcost)
  have hs := (tendsto_add_atTop_nat 3).eventually
    ((naturalEdgeScale_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)))
  have hf := (tendsto_add_atTop_nat 3).eventually edgeLength_tents_eventually
  filter_upwards [hc,hs,hf] with n hnc hns hnf
  intro lam hlam
  let s := naturalEdgeScale (n+3) L
  have hsp : 0 < s := naturalEdgeScale_pos (n+3) hLp
  have hsm : s ≤ 1 := hns.le
  have hspace := naturalEdgeScale_space (n+3) hLp
  norm_num only [Nat.cast_add,Nat.cast_ofNat] at hspace
  rw [show (n:ℝ)+3+1=n+4 by ring] at hspace
  have hsc : 32768 ≤ (n+4:ℝ)*s*Real.sqrt s := by
    have hl := largeL_space hL
    linarith [hspace.1]
  have hclose (i : Fin (n+4)) (hi : i.val < 3) : |lam i-2| ≤ s/4 :=
    spectralGood_top_close hh hLa hsm hnf hnc hlam i hi
  have hexp : Real.exp (6*((n+4:ℝ)*s*Real.sqrt s)) ≤ Real.exp (6*(L*Real.sqrt L)) :=
    Real.exp_le_exp.mpr (by linarith [hspace.2])
  constructor
  · intro b hb
    have hball := spectralGood_sphere_smallBall (n := n+1) hh hsp hsm hnc hlam
      (by norm_num only [Nat.cast_add,Nat.cast_ofNat,add_assoc]; exact hsc)
      (hclose 0 (by simp)) (hclose 1 (by simp)) (hclose 2 (by change 2 < 3; omega))
      (show 0 ≤ b*(n+4:ℝ)^(1/3:ℝ) by positivity)
    norm_num only [Nat.cast_add,Nat.cast_ofNat,add_assoc] at hball
    have hr := natural_smallBall_rate (n+3) hLp.le
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hr
    rw [show (n:ℝ)+3+1=n+4 by ring] at hr
    apply hball.trans
    have hm : 4*(b*(n+4:ℝ)^(1/3:ℝ))*Real.sqrt s ≤ 4*b*Real.sqrt L := by
      simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left hr (show 0 ≤ 4*b by positivity)
    have ht := mul_le_mul hm hexp (Real.exp_pos _).le (show 0 ≤ 4*b*Real.sqrt L by positivity)
    simpa only [naturalSmallBallConstant,mul_assoc,mul_left_comm,mul_comm] using ht
  · have hsphere := spectralGood_sphere_overlap (n := n+2) hh hsp hsm hnc hlam
      (by norm_num only [Nat.cast_add,Nat.cast_ofNat,add_assoc]; exact hsc)
      (hclose 0 (by simp)) (hclose 1 (by simp))
    norm_num only [Nat.cast_add,Nat.cast_ofNat,add_assoc] at hsphere
    rw [sphereTilted_overlap_moment] at hsphere
    have hA : (16*Real.exp (6*((n+4:ℝ)*s*Real.sqrt s)))^2 ≤ (16*Real.exp (6*(L*Real.sqrt L)))^2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hexp (by norm_num)) 2
    have hx := hsphere.trans (mul_le_mul_of_nonneg_right hA (show 0 ≤ 16*(n+4)/Real.sqrt s by positivity))
    have ht := div_le_div_of_nonneg_right hx (sq_nonneg (n+4:ℝ))
    apply ht.trans_eq
    unfold naturalOverlapRate
    norm_num only [Nat.cast_add,Nat.cast_ofNat]
    rw [show (n:ℝ)+3+1=n+4 by ring]
    dsimp only [s]
    field_simp [(Real.sqrt_pos.mpr hsp).ne']


-- @@ L188-213 verbatim
lemma spectralGood_orientation_overlap {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood (n+3) h (naturalEdgeScale (n+3) L),
      (∫ U, rotatedCubePair lam (fun q => q^2) U ∂orthogonalHaar (Fin (n+4))) /
        spherePartition lam 1 (Real.sqrt (n+4))^2 ≤
        (1+ε)*naturalOverlapRate (n+3) L+naturalOrientationTail (n+3) L := by
  have ho := (tendsto_add_atTop_nat 4).eventually (orientation_normalized_overlap_bound ε hε)
  filter_upwards [naturalOrientationInputs hh hL hcost, spectralGood_natural_sphere_bounds hh hL hcost,ho] with n hn hb hv
  intro lam hlam
  have hi := hn lam hlam
  obtain ⟨u,v,hu,hv',huv⟩ := orthogonal_equal_norm_pair (n+2) (Real.sqrt (n+4)) (Real.sqrt_nonneg _)
  have hh := hv lam u v _ _
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hu)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hv') huv hi.bounded hi.Kpos hi.partitionLower hi.scaleNonneg
    hi.topUpper hi.topLower hi.trace hi.traceUniform hi.cutoff hi.saddle
  have hsphere := sphereOverlap_density_weighted_moment n lam (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < n+4)) hu hv' huv
  have hroot : Real.sqrt (n+4:ℝ)^4 = (n+4:ℝ)^2 := by
    rw [show (4:ℕ) = 2*2 by omega,pow_mul,Real.sq_sqrt (by positivity)]
  rw [hroot] at hsphere
  norm_num only [Nat.cast_add,Nat.cast_ofNat] at hh
  rw [hsphere] at hh
  apply hh.trans
  have ht := add_le_add_right (mul_le_mul_of_nonneg_left (hb lam hlam).2
    (show 0 ≤ 1+ε by linarith)) (naturalOrientationTail (n+3) L)
  simpa only [naturalOrientationTail,Nat.cast_add,Nat.cast_ofNat,show (n:ℝ)+3+1=n+4 by ring,
    show (n:ℝ)+3+2=n+4+1 by ring, show n+3+1=n+4 by omega, add_comm] using ht


-- @@ L215-215 verbatim
end


-- @@ L217-217 verbatim
open Set MeasureTheory Filter


-- @@ L219-221 verbatim
instance disorderLaw_probability (n : ℕ) : IsProbabilityMeasure (disorderLaw n) := by
  unfold disorderLaw
  infer_instance


-- @@ L223-236 verbatim
lemma goe_natural_spectral_bad {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) :
    ∀ᶠ n : ℕ in atTop, (goeLaw (Fin (n+1)) (goeScale n)).real
      (matrixOrderedEigenvalues ⁻¹' (spectralGood n h (naturalEdgeScale n L))ᶜ) ≤ 32*Real.exp (-h^2) := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  filter_upwards [traceCost_natural_eventually hh hLp hcost,
    (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hc hs
  apply goe_spectral_bad_probability n hh (naturalEdgeScale_pos n hLp) (naturalEdgeScale_base n hL1)
  have ht := traceCost_small n hh (naturalEdgeScale_pos n hLp) hs.le hc
  have hA : 0 ≤ formA n h*(naturalEdgeScale n L)^(-5/8:ℝ) := by
    exact mul_nonneg (formA_nonneg n hh) (Real.rpow_nonneg (naturalEdgeScale_pos n hLp).le _)
  have hB : 0 ≤ formB n / naturalEdgeScale n L := div_nonneg (formB_nonneg n) (naturalEdgeScale_pos n hLp).le
  nlinarith


-- @@ L238-242 verbatim
lemma disorder_goe_event (n : ℕ) {E : Set (Disorder (n+1))} (hE : MeasurableSet E) :
    (disorderLaw (n+1)).real E = (goeLaw (Fin (n+1)) (goeScale n)).real (gaussianDisorder ⁻¹' E) := by
  rw [← goe_disorder_law n]
  unfold Measure.real
  rw [Measure.map_apply (gaussianDisorder_measurable _) hE]


-- @@ L244-269 verbatim
lemma natural_smallBallObstruction_probability {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) {ε : ℝ} (hε : 0 < ε) {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      (smallBallObstruction (n+4) (b*(n+4:ℝ)^(1/3:ℝ)) δ) ≤
      32*Real.exp (-h^2)+(2*naturalSmallBallConstant L*b+4*(ε+naturalOrientationTail (n+3) L))/δ := by
  have hspectral := (tendsto_add_atTop_nat 3).eventually (goe_natural_spectral_bad hh hL hcost)
  filter_upwards [hspectral,spectralGood_natural_sphere_bounds hh hL hcost,
    spectralGood_orientation_variance hh hL hcost hε] with n hn hball hvar
  rw [disorder_goe_event (n+3) (smallBallObstruction_closed _ _ _).measurableSet]
  let G : Set (GaussianMatrix (Fin (n+4))) := matrixOrderedEigenvalues ⁻¹' spectralGood (n+3) h (naturalEdgeScale (n+3) L)
  have hG : MeasurableSet G := (spectralGood_measurable _ _ _).preimage (matrixOrderedEigenvalues_measurable _)
  have he := goe_event_from_orbit_bound (goeScale (n+3))
    ((smallBallObstruction_closed _ _ _).measurableSet.preimage (gaussianDisorder_measurable _)) hG
    (show 0 ≤ (2*naturalSmallBallConstant L*b+4*(ε+naturalOrientationTail (n+3) L))/δ from by
      unfold naturalSmallBallConstant naturalOrientationTail; positivity)
    (fun A hAG hA => by
      have hbnd := haar_smallBallObstruction_bound (by omega : 0 < n+4) A hA
        (b*(n+4:ℝ)^(1/3:ℝ)) hδ (2 : Fin (n+4))
      apply hbnd.trans
      apply div_le_div_of_nonneg_right _ hδ.le
      have hB := (hball (matrixOrderedEigenvalues A) hAG).1 b hb
      have hV := hvar (matrixOrderedEigenvalues A) hAG
      simpa only [Nat.cast_add,Nat.cast_ofNat,mul_assoc] using
        add_le_add (mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left hV (by norm_num : (0:ℝ) ≤ 4)))
  exact he.trans (add_le_add hn le_rfl)


-- @@ L271-273 verbatim
lemma naturalSmallBallConstant_pos {L : ℝ} (hL : 0 < L) : 0 < naturalSmallBallConstant L := by
  unfold naturalSmallBallConstant
  positivity


-- @@ L275-281 verbatim
lemma exists_spectral_failure_parameter {α : ℝ} (hα : 0 < α) :
    ∃ h : ℝ, 0 ≤ h ∧ 32*Real.exp (-h^2) < α := by
  have hh : Tendsto (fun h : ℝ => -h^2) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have ht : Tendsto (fun h : ℝ => 32*Real.exp (-h^2)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hh).const_mul 32
  exact ((eventually_ge_atTop 0).and (ht.eventually (gt_mem_nhds hα))).exists


-- @@ L283-310 verbatim
lemma natural_smallBall_tight {δ α : ℝ} (hδ : 0 < δ) (hα : 0 < α) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      (smallBallObstruction (n+4) (b*(n+4:ℝ)^(1/3:ℝ)) δ) < α := by
  obtain ⟨h,hh,hfail⟩ := exists_spectral_failure_parameter (show 0 < α/4 by positivity)
  obtain ⟨L,hL,hcost⟩ := ((eventually_ge_atTop (262144:ℝ)).and
    ((edgeFixedCost_tendsto h).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)))).exists
  have hLp : 0 < L := by linarith
  let C := naturalSmallBallConstant L
  have hC : 0 < C := naturalSmallBallConstant_pos hLp
  let b := α*δ/(16*C)
  let ε := α*δ/32
  have hb : 0 < b := by dsimp [b]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨b,hb,?_⟩
  have ht : Tendsto (fun n : ℕ => naturalOrientationTail (n+3) L) atTop (𝓝 0) := by
    have hs := (naturalOrientationTail_scaled_tendsto hLp 0).comp (tendsto_add_atTop_nat 3)
    simpa only [Function.comp_def,Real.rpow_zero,one_mul] using hs
  filter_upwards [natural_smallBallObstruction_probability hh hL hcost hε hb.le hδ,
    ht.eventually (gt_mem_nhds hε)] with n hn htail
  apply lt_of_le_of_lt hn
  have hbc : 2*C*b = α*δ/8 := by dsimp only [b]; field_simp; ring
  change 32*Real.exp (-h^2)+(2*C*b+4*(ε+naturalOrientationTail (n+3) L))/δ < α
  rw [hbc]
  have hfrac : (α*δ/8+4*(ε+naturalOrientationTail (n+3) L))/δ < 3*α/4 := by
    apply (div_lt_iff₀ hδ).mpr
    dsimp only [ε] at htail ⊢
    nlinarith
  linarith


-- @@ L312-312 verbatim
end CriticalSK


-- @@ L314-314 verbatim
end


-- @@ L316-316 verbatim
end OAI
