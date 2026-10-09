import OAI.Analysis.NumericalRange.HolomorphicEvaluation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace CompleteCrouzeix


-- @@ L9-9 verbatim
universe u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72 u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80


-- @@ L11-11 verbatim
open scoped BigOperators Matrix.Norms.L2Operator

-- @@ L12-12 verbatim
open Polynomial Finset


-- @@ L14-14 verbatim
section

-- @@ L15-15 verbatim
open Filter Topology Set Module

-- @@ L16-17 verbatim
variable {V : Type u_65} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]


-- @@ L19-50 verbatim
lemma primaryEval_tendsto_apply {ι : Type u_66} {l : Filter ι}
    (T : Module.End ℂ V) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (h : ∀ β ∈ spectrum ℂ T, ∀ k < finrank ℂ V,
      Tendsto (fun i => iteratedDeriv k (F i) β) l (nhds (iteratedDeriv k f β))) (x : V) :
    Tendsto (fun i => primaryEval T (F i) x) l (nhds (primaryEval T f x)) := by
  have hx : x ∈ ⨆ β, T.maxGenEigenspace β := by rw [T.iSup_maxGenEigenspace_eq_top]; trivial
  refine Submodule.iSup_induction _
    (motive := fun x => Tendsto (fun i => primaryEval T (F i) x) l (nhds (primaryEval T f x))) hx
    ?_ (by simpa using tendsto_const_nhds) ?_
  · intro β x hx
    by_cases hβ : β ∈ spectrum ℂ T
    · have he (g : ℂ → ℂ) : primaryEval T g x =
          ∑ k ∈ Finset.range (finrank ℂ V),
          (iteratedDeriv k g β / (k.factorial : ℂ)) •
            (((primaryNilpotent T β)^k) ⟨x,hx⟩ : V) := by
        rw [primaryEval_coe T g β ⟨x,hx⟩]
        simp only [scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
          Submodule.coe_sum, Submodule.coe_smul]
      simp only [he]
      apply tendsto_finsetSum
      intro k hk
      exact ((h β hβ k (Finset.mem_range.mp hk)).div_const _).smul tendsto_const_nhds
    · have hspace : T.maxGenEigenspace β = ⊥ := by
        by_contra hn
        have he : T.HasGenEigenvalue β (finrank ℂ V) := by
          rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
        exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
      have he : x = 0 := by simpa [hspace] using hx
      simpa only [he, map_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : V)) l (nhds 0))
  · intro x y hx hy
    simpa only [map_add] using hx.add hy


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
section

-- @@ L55-55 verbatim
open Filter Topology Set Module

-- @@ L56-56 verbatim
variable {n : Type u_67} [Fintype n] [DecidableEq n]


-- @@ L58-59 verbatim
noncomputable def matrixAnalyticEval (A : Matrix n n ℂ) (f : ℂ → ℂ) : Matrix n n ℂ :=
  Matrix.toLinAlgEquiv'.symm (primaryEval (Matrix.toLinAlgEquiv' A) f)


-- @@ L61-65 verbatim
lemma matrixAnalyticEval_polynomial (A : Matrix n n ℂ) (p : ℂ[X]) :
    matrixAnalyticEval A (fun z => p.eval z) = Polynomial.aeval A p := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_polynomial,
    Polynomial.aeval_algHom_apply]


-- @@ L67-79 verbatim
lemma matrixAnalyticEval_tendsto {ι : Type u_68} {l : Filter ι}
    (A : Matrix n n ℂ) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (h : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      Tendsto (fun i => iteratedDeriv k (F i) β) l (nhds (iteratedDeriv k f β))) :
    Tendsto (fun i => matrixAnalyticEval A (F i)) l (nhds (matrixAnalyticEval A f)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  have he := primaryEval_tendsto_apply (Matrix.toLinAlgEquiv' A)
    (F := F) (f := f) (fun β hβ k hk => h β (by
      simpa only [AlgEquiv.spectrum_eq] using hβ) k (by simpa using hk)) (Pi.single b 1)
  exact (tendsto_pi_nhds.mp he) a


-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
section

-- @@ L84-84 verbatim
open Filter Topology Set Module


-- @@ L86-98 verbatim
lemma locallyUniform_iteratedDeriv {ι : Type u_69} {l : Filter ι}
    {U : Set ℂ} (hU : IsOpen U) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (ht : TendstoLocallyUniformlyOn F f l U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv k (F i)) (iteratedDeriv k f) l U := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    apply ih.deriv _ hU
    exact Eventually.of_forall fun i => by
      simpa only [iteratedDeriv_eq_iterate] using
        ((hF i).iterated_deriv k).differentiableOn


-- @@ L100-109 verbatim
lemma matrixAnalyticEval_tendsto_locallyUniform
    {n : Type u_70} [Fintype n] [DecidableEq n] {ι : Type u_71} {l : Filter ι}
    (A : Matrix n n ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hAU : spectrum ℂ A ⊆ U) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (ht : TendstoLocallyUniformlyOn F f l U) :
    Tendsto (fun i => matrixAnalyticEval A (F i)) l (nhds (matrixAnalyticEval A f)) := by
  apply matrixAnalyticEval_tendsto
  intro β hβ k _
  exact (locallyUniform_iteratedDeriv hU hF ht k).tendsto_at (hAU hβ)


-- @@ L111-111 verbatim
end


-- @@ L113-113 verbatim
section

-- @@ L114-114 verbatim
open Filter Topology Set Metric

-- @@ L115-115 verbatim
open scoped NNReal ENNReal


-- @@ L117-118 verbatim
noncomputable def seriesPolynomial (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range N, Polynomial.monomial k (p.coeff k)


-- @@ L120-124 verbatim
lemma seriesPolynomial_eval (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) (z : ℂ) :
    (seriesPolynomial p N).eval z = p.partialSum N z := by
  simp only [seriesPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    smul_eq_mul, mul_comm]


-- @@ L126-146 verbatim
lemma analytic_closed_disk_polynomial_approximation {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) :
    ∃ r : ℝ, 1 < r ∧ ∃ p : ℕ → ℂ[X],
      TendstoUniformlyOn (fun N z => (p N).eval z) f atTop (ball 0 r) := by
  obtain ⟨δ, hδ, hinc⟩ := (isCompact_closedBall (0:ℂ) 1).exists_cthickening_subset_open
    (isOpen_analyticAt ℂ f) hf
  rw [cthickening_closedBall hδ.le (by norm_num : (0:ℝ) ≤ 1)] at hinc
  let R : ℝ≥0 := ⟨δ+1, by linarith⟩
  have hR : 0 < R := by change (0:ℝ) < δ+1; linarith
  have hd : DifferentiableOn ℂ f (closedBall 0 R) := by
    intro z hz
    exact (hinc hz).differentiableAt.differentiableWithinAt
  have hs := hd.hasFPowerSeriesOnBall hR
  let r : ℝ≥0 := ⟨δ/2+1, by linarith⟩
  refine ⟨(r : ℝ), by change 1 < δ/2+1; linarith, seriesPolynomial (cauchyPowerSeries f 0 R), ?_⟩
  have hr : (r : ℝ≥0∞) < (R : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe]
    change δ/2+1 < δ+1
    linarith
  have ht := hs.tendstoUniformlyOn hr
  simpa only [seriesPolynomial_eval, zero_add] using ht


-- @@ L148-148 verbatim
end


-- @@ L150-150 verbatim
open Filter Topology

-- @@ L151-151 verbatim
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder


-- @@ L153-153 verbatim
section Stability

-- @@ L154-154 verbatim
variable {A : Type u_72} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]


-- @@ L156-175 verbatim
theorem summable_norm_powers {a : A} (ha : spectralRadius ℂ a < 1) :
    Summable (fun n : ℕ => ‖a ^ n‖) := by
  obtain ⟨r, har, hr1⟩ := exists_between ha
  have hrf : r ≠ ∞ := ne_of_lt (hr1.trans (by simp))
  have hrpos : 0 < r := lt_of_le_of_lt bot_le har
  have hr0 : 0 ≤ r.toReal := ENNReal.toReal_nonneg
  have hrr : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hrf
  have hrt : r.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hrf (by simp : (1 : ℝ≥0∞) ≠ ∞)).mpr hr1
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
    (gt_mem_nhds har)
  have hbound : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ r.toReal ^ n := by
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hroot : ‖a ^ n‖ ^ (1 / (n : ℝ)) < r.toReal := by
      rw [← hrr] at hn
      exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos hrpos.ne' hrf)).mp hn
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hroot.le n
    simpa only [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) (Nat.ne_of_gt hn0)] using hp
  apply (summable_geometric_of_lt_one hr0 hrt).of_norm_bounded_eventually
  simpa only [Nat.cofinite_eq_atTop, norm_norm] using hbound


-- @@ L177-177 verbatim
end Stability


-- @@ L179-179 verbatim
open MeasureTheory

-- @@ L180-180 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- @@ L181-181 verbatim
abbrev circleMeasure := @AddCircle.haarAddCircle 1 inferInstance

-- @@ L182-182 verbatim
variable {n : Type u_73} [instFintypeN : Fintype n] [instDecidableEqN : DecidableEq n]


-- @@ L184-185 verbatim
def diskResolventSeries (D : Matrix n n ℂ) (t : AddCircle (1:ℝ)) : Matrix n n ℂ :=
  ∑' j : ℕ, fourier (-(j:ℤ)) t • D^j


-- @@ L187-188 verbatim
lemma fourier_norm_value (k : ℤ) (t : AddCircle (1:ℝ)) : ‖fourier k t‖ = 1 :=
  Circle.norm_coe _


-- @@ L190-193 verbatim
lemma summable_diskResolvent {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    (t : AddCircle (1:ℝ)) : Summable (fun j : ℕ => fourier (-(j:ℤ)) t • D^j) := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm_value, one_mul] using summable_norm_powers hD


-- @@ L195-202 verbatim
lemma continuous_diskResolvent {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1) :
    Continuous (diskResolventSeries D) := by
  unfold diskResolventSeries
  apply continuous_tsum (fun j : ℕ => (fourier (-(j:ℤ))).continuous.smul (continuous_const (y := D^j)))
    (summable_norm_powers hD)
  intro j t
  change ‖fourier (-(j:ℤ)) t • D^j‖ ≤ ‖D^j‖
  simp only [norm_smul, fourier_norm_value, one_mul, le_refl]


-- @@ L204-212 verbatim
lemma fourier_neg_nat_pow (t : AddCircle (1:ℝ)) (j : ℕ) :
    fourier (-1) t ^ j = fourier (-(j:ℤ)) t := by
  induction j with
  | zero => simp
  | succ j hj =>
    rw [pow_succ,hj,← fourier_add]
    congr 2
    push_cast
    ring


-- @@ L214-223 verbatim
lemma diskResolvent_inverse {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    (t : AddCircle (1:ℝ)) :
    diskResolventSeries D t = (1-fourier (-1) t • D)⁻¹ := by
  have hp (j : ℕ) : (fourier (-1) t • D)^j = fourier (-(j:ℤ)) t • D^j := by
    rw [_root_.smul_pow, fourier_neg_nat_pow]
  have hs : Summable (fun j : ℕ => (fourier (-1) t • D)^j) := by
    simpa only [hp] using summable_diskResolvent hD t
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  simpa only [hp,diskResolventSeries] using hs.tsum_pow_mul_one_sub


-- @@ L225-226 verbatim
def diskDensity (D : Matrix n n ℂ) (t : AddCircle (1:ℝ)) : Matrix n n ℂ :=
  diskResolventSeries D t + (diskResolventSeries D t)ᴴ - 1


-- @@ L228-231 verbatim
lemma continuous_diskDensity {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1) :
    Continuous (diskDensity D) := by
  exact ((continuous_diskResolvent hD).add (continuous_diskResolvent hD).star).sub
    continuous_const


-- @@ L233-264 verbatim
lemma diskDensity_nonneg {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    (hc : Dᴴ*D ≤ 1) (t : AddCircle (1:ℝ)) : 0 ≤ diskDensity D t := by
  let z : ℂ := fourier (-1) t
  let E : Matrix n n ℂ := 1-z • D
  let R : Matrix n n ℂ := diskResolventSeries D t
  have hp (j : ℕ) : (z • D)^j = fourier (-(j:ℤ)) t • D^j := by
    change (fourier (-1) t • D)^j = _
    rw [_root_.smul_pow,fourier_neg_nat_pow]
  have hs : Summable (fun j : ℕ => (z • D)^j) := by
    simpa only [hp] using summable_diskResolvent hD t
  have hER : E*R = 1 := by simpa only [R,E,hp,diskResolventSeries] using hs.one_sub_mul_tsum_pow
  have hz : star z * z = 1 := by
    rw [RCLike.star_def,Complex.conj_mul']
    change (‖fourier (-1) t‖ ^ 2 : ℂ) = 1
    rw [fourier_norm_value]; norm_num
  have hdef : Eᴴ + E - Eᴴ*E = 1-Dᴴ*D := by
    dsimp only [E]
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_smul]
    simp only [sub_mul,mul_sub,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,mul_comm z (star z),hz,one_smul]
    abel
  have hcong : Rᴴ * (1-Dᴴ*D) * R = diskDensity D t := by
    rw [← hdef]
    have hstar := congrArg Matrix.conjTranspose hER
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_one] at hstar
    change Rᴴ * (Eᴴ+E-Eᴴ*E) * R = R+Rᴴ-1
    calc
      _ = (Rᴴ*Eᴴ)*R + Rᴴ*(E*R) - (Rᴴ*Eᴴ)*(E*R) := by noncomm_ring
      _ = _ := by rw [hstar,hER]; simp
  rw [← hcong]
  exact (Matrix.PosSemidef.conjTranspose_mul_mul_same (Matrix.nonneg_iff_posSemidef.mp
    (sub_nonneg.mpr hc)) R).nonneg


-- @@ L266-270 verbatim
lemma integral_fourier (k : ℤ) :
    (∫ t : AddCircle (1:ℝ), fourier k t ∂circleMeasure) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1:ℝ)) k) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply,
    ite_eq_left_iff, eq_comm] using h


-- @@ L272-275 verbatim
lemma integral_fourier_smul (k : ℤ) (A : Matrix n n ℂ) :
    (∫ t : AddCircle (1:ℝ), fourier k t • A ∂circleMeasure) = if k = 0 then A else 0 := by
  rw [integral_smul_const,integral_fourier]
  split_ifs <;> simp


-- @@ L277-297 verbatim
lemma integral_matrix_fourier_series (A : ℕ → Matrix n n ℂ)
    (hA : Summable (fun j => ‖A j‖)) (l : ℕ → ℤ) (k : ℤ) :
    (∫ t : AddCircle (1:ℝ), fourier k t • (∑' j : ℕ, fourier (l j) t • A j) ∂circleMeasure) =
      ∑' j : ℕ, if k + l j = 0 then A j else 0 := by
  have he (t : AddCircle (1:ℝ)) :
      fourier k t • (∑' j : ℕ, fourier (l j) t • A j) =
        ∑' j : ℕ, fourier (k+l j) t • A j := by
    rw [← tsum_const_smul'']
    apply tsum_congr
    intro j
    rw [smul_smul,← fourier_add]
  simp_rw [he]
  rw [← integral_tsum_of_summable_integral_norm]
  · apply tsum_congr
    intro j
    exact integral_fourier_smul _ _
  · intro j
    exact ((fourier (k+l j)).continuous.smul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · simpa only [norm_smul,fourier_norm_value,one_mul,integral_const,measure_univ,
      Measure.real,measure_univ, ENNReal.toReal_one,one_smul] using hA


-- @@ L299-305 verbatim
lemma diskResolvent_moment {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1) (k : ℕ) :
    (∫ t : AddCircle (1:ℝ), fourier (k:ℤ) t • diskResolventSeries D t ∂circleMeasure) = D^k := by
  unfold diskResolventSeries
  rw [integral_matrix_fourier_series _ (summable_norm_powers hD)]
  have he (j : ℕ) : (k:ℤ) + -(j:ℤ) = 0 ↔ j = k := by omega
  simp_rw [he]
  exact tsum_ite_eq k (fun j : ℕ => D^j)


-- @@ L307-322 verbatim
lemma diskResolvent_star_moment {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1) (k : ℕ) :
    (∫ t : AddCircle (1:ℝ), fourier (k:ℤ) t • (diskResolventSeries D t)ᴴ ∂circleMeasure) =
      if k = 0 then 1 else 0 := by
  have he (t : AddCircle (1:ℝ)) : (diskResolventSeries D t)ᴴ =
      ∑' j : ℕ, fourier (j:ℤ) t • (D^j)ᴴ := by
    simp only [diskResolventSeries,Matrix.conjTranspose_tsum,Matrix.conjTranspose_smul,
      RCLike.star_def,fourier_neg,Complex.conj_conj]
  simp_rw [he]
  rw [integral_matrix_fourier_series]
  · have h (j : ℕ) : (k:ℤ) + (j:ℤ) = 0 ↔ k = 0 ∧ j = 0 := by omega
    simp_rw [h]
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  · simpa only [Matrix.l2_opNorm_conjTranspose] using summable_norm_powers hD


-- @@ L324-343 verbatim
theorem diskDensity_moment {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1) (k : ℕ) :
    (∫ t : AddCircle (1:ℝ), fourier (k:ℤ) t • diskDensity D t ∂circleMeasure) = D^k := by
  have h1 : Integrable (fun t : AddCircle (1:ℝ) => fourier (k:ℤ) t • diskResolventSeries D t)
      circleMeasure :=
    ((fourier (k:ℤ)).continuous.smul (continuous_diskResolvent hD)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun t : AddCircle (1:ℝ) => fourier (k:ℤ) t • (diskResolventSeries D t)ᴴ)
      circleMeasure :=
    ((fourier (k:ℤ)).continuous.smul (continuous_diskResolvent hD).star).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h3 : Integrable (fun t : AddCircle (1:ℝ) => fourier (k:ℤ) t • (1 : Matrix n n ℂ))
      circleMeasure :=
    ((fourier (k:ℤ)).continuous.smul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [diskDensity,smul_sub,smul_add]
  have he := integral_sub (h1.add h2) h3
  simp only [Pi.add_apply] at he
  rw [he,integral_add h1 h2,diskResolvent_moment hD,diskResolvent_star_moment hD,
    integral_fourier_smul]
  simp


-- @@ L345-345 verbatim
open scoped Kronecker


-- @@ L347-347 verbatim
variable {m : Type u_74} [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]


-- @@ L349-358 verbatim
lemma contraction_block_iff (C : Matrix m m ℂ) :
    (Matrix.fromBlocks 1 C Cᴴ 1).PosSemidef ↔ ‖C‖ ≤ 1 := by
  let : Invertible (1 : Matrix m m ℂ) := invertibleOne
  rw [Matrix.PosDef.fromBlocks₁₁ C (1 : Matrix m m ℂ) Matrix.PosDef.one]
  simp only [inv_one, Matrix.mul_one]
  change Cᴴ*C ≤ 1 ↔ ‖C‖ ≤ 1
  rw [← CStarAlgebra.norm_le_one_iff_of_nonneg (Cᴴ*C)
    (Matrix.posSemidef_conjTranspose_mul_self C).nonneg,
    Matrix.l2_opNorm_conjTranspose_mul_self]
  constructor <;> intro h <;> nlinarith [norm_nonneg C]


-- @@ L360-373 verbatim
lemma positive_density_block
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m]
    {L : Matrix n n ℂ} (hL : L.PosSemidef)
    {F : Matrix m m ℂ} (hF : ‖F‖ ≤ 1) :
    (Matrix.fromBlocks (L ⊗ₖ 1) (L ⊗ₖ F) (L ⊗ₖ F)ᴴ (L ⊗ₖ 1)).PosSemidef := by
  have h := (hL.kronecker ((contraction_block_iff F).mpr hF)).submatrix
    (Equiv.prodSumDistrib n m m).symm
  have he : Matrix.fromBlocks (L ⊗ₖ 1) (L ⊗ₖ F) (L ⊗ₖ F)ᴴ (L ⊗ₖ 1) =
      (L ⊗ₖ Matrix.fromBlocks 1 F Fᴴ 1).submatrix
        (Equiv.prodSumDistrib n m m).symm (Equiv.prodSumDistrib n m m).symm := by
    rw [Matrix.conjTranspose_kronecker, hL.isHermitian.eq]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  rwa [he]


-- @@ L375-379 verbatim
def entryCLM (i j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  (show Matrix n n ℂ →ₗ[ℂ] ℂ from
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap


-- @@ L381-384 verbatim
lemma matrix_integral_entry {X : Type u_75} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) (i j : n) :
    (∫ t, L t ∂μ) i j = ∫ t, L t i j ∂μ :=
  ((entryCLM i j).integral_comp_comm hL).symm


-- @@ L386-390 verbatim
def kronCLM (B : Matrix m m ℂ) : Matrix n n ℂ →L[ℂ] Matrix (n×m) (n×m) ℂ :=
  (show Matrix n n ℂ →ₗ[ℂ] Matrix (n×m) (n×m) ℂ from
    { toFun := fun A => A ⊗ₖ B
      map_add' := fun A C => Matrix.add_kronecker A C B
      map_smul' := fun c A => Matrix.smul_kronecker c A B }).toContinuousLinearMap


-- @@ L392-395 verbatim
lemma integral_kron_const {X : Type u_76} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) (B : Matrix m m ℂ) :
    (∫ t, L t ⊗ₖ B ∂μ) = (∫ t, L t ∂μ) ⊗ₖ B :=
  (kronCLM B).integral_comp_comm hL


-- @@ L397-417 verbatim
lemma integral_fromBlocks {X : Type u_77} [MeasurableSpace X] {μ : Measure X}
    {A B C D : X → Matrix n n ℂ}
    (hA : Integrable A μ) (hB : Integrable B μ) (hC : Integrable C μ) (hD : Integrable D μ) :
    (∫ t, Matrix.fromBlocks (A t) (B t) (C t) (D t) ∂μ) =
      Matrix.fromBlocks (∫ t, A t ∂μ) (∫ t, B t ∂μ) (∫ t, C t ∂μ) (∫ t, D t ∂μ) := by
  let e : (Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ) →L[ℂ]
      Matrix (n⊕n) (n⊕n) ℂ :=
    (show (Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ) →ₗ[ℂ]
      Matrix (n⊕n) (n⊕n) ℂ from
      { toFun := fun X => Matrix.fromBlocks X.1 X.2.1 X.2.2.1 X.2.2.2
        map_add' := fun X Y => by ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
        map_smul' := fun c X => by ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
      }).toContinuousLinearMap
  have h := e.integral_comp_comm (hA.prodMk (hB.prodMk (hC.prodMk hD)))
  change (∫ t, Matrix.fromBlocks (A t) (B t) (C t) (D t) ∂μ) =
    Matrix.fromBlocks (∫ t, (A t, B t, C t, D t) ∂μ).1
      (∫ t, (A t, B t, C t, D t) ∂μ).2.1
      (∫ t, (A t, B t, C t, D t) ∂μ).2.2.1
      (∫ t, (A t, B t, C t, D t) ∂μ).2.2.2 at h
  simpa only [integral_pair hA (hB.prodMk (hC.prodMk hD)),
    integral_pair hB (hC.prodMk hD), integral_pair hC hD] using h


-- @@ L419-423 verbatim
def conjTransposeRCLM : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (show Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ from
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun c A => by simp }).toContinuousLinearMap


-- @@ L425-428 verbatim
lemma integral_conjTranspose {X : Type u_78} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) :
    (∫ t, (L t)ᴴ ∂μ) = (∫ t, L t ∂μ)ᴴ :=
  conjTransposeRCLM.integral_comp_comm hL


-- @@ L430-445 verbatim
theorem norm_integral_density_kron {X : Type u_79} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} {F : X → Matrix m m ℂ}
    (hL : Integrable L μ) (hLF : Integrable (fun t => L t ⊗ₖ F t) μ)
    (hpos : ∀ t, (L t).PosSemidef) (hmass : ∫ t, L t ∂μ = 1)
    (hF : ∀ t, ‖F t‖ ≤ 1) : ‖∫ t, L t ⊗ₖ F t ∂μ‖ ≤ 1 := by
  have hd (t : X) := positive_density_block (hpos t) (hF t)
  have hnonneg : 0 ≤ ∫ t, Matrix.fromBlocks (L t ⊗ₖ 1) (L t ⊗ₖ F t)
      (L t ⊗ₖ F t)ᴴ (L t ⊗ₖ 1) ∂μ :=
    integral_nonneg (fun t => (hd t).nonneg)
  have hdiag : Integrable (fun t => L t ⊗ₖ (1 : Matrix m m ℂ)) μ :=
    (kronCLM (1 : Matrix m m ℂ)).integrable_comp hL
  have hstar : Integrable (fun t => (L t ⊗ₖ F t)ᴴ) μ :=
    conjTransposeRCLM.integrable_comp hLF
  rw [integral_fromBlocks hdiag hLF hstar hdiag, integral_kron_const hL,
    hmass, Matrix.one_kronecker_one, integral_conjTranspose hLF] at hnonneg
  exact (contraction_block_iff _).mp (Matrix.nonneg_iff_posSemidef.mp hnonneg)


-- @@ L447-455 verbatim
lemma continuous_kron
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m]
    {X : Type u_80} [TopologicalSpace X]
    {L : X → Matrix n n ℂ} {F : X → Matrix m m ℂ}
    (hL : Continuous L) (hF : Continuous F) : Continuous (fun t => L t ⊗ₖ F t) := by
  apply continuous_matrix
  intro i j
  exact ((entryCLM i.1 j.1).continuous.comp hL).mul
    ((entryCLM i.2 j.2).continuous.comp hF)


-- @@ L457-458 verbatim
def circlePolynomial {d : ℕ} (B : Fin (d+1) → Matrix m m ℂ)
    (t : AddCircle (1:ℝ)) : Matrix m m ℂ := ∑ k, fourier (k.val:ℤ) t • B k


-- @@ L460-463 verbatim
lemma continuous_circlePolynomial
    {m : Type u_74} [Fintype m] [DecidableEq m] {d : ℕ} (B : Fin (d+1) → Matrix m m ℂ) :
    Continuous (circlePolynomial B) := by
  exact continuous_finsetSum _ (fun k _ => (fourier (k.val:ℤ)).continuous.smul continuous_const)


-- @@ L465-473 verbatim
lemma integrable_diskDensity_monomial_kron {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (k : ℕ) (B : Matrix m m ℂ) :
    Integrable (fun t : AddCircle (1:ℝ) =>
      (fourier (k:ℤ) t • diskDensity D t) ⊗ₖ B) circleMeasure := by
  have hc : Continuous (fun t : AddCircle (1:ℝ) =>
      (fourier (k:ℤ) t • diskDensity D t) ⊗ₖ B) :=
    continuous_kron ((fourier (k:ℤ)).continuous.smul (continuous_diskDensity hD))
      continuous_const
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)


-- @@ L475-483 verbatim
lemma diskDensity_monomial_kron {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (k : ℕ) (B : Matrix m m ℂ) :
    (∫ t : AddCircle (1:ℝ), (fourier (k:ℤ) t • diskDensity D t) ⊗ₖ B ∂circleMeasure) =
      (D^k) ⊗ₖ B := by
  have hi : Integrable (fun t : AddCircle (1:ℝ) =>
      fourier (k:ℤ) t • diskDensity D t) circleMeasure :=
    ((fourier (k:ℤ)).continuous.smul (continuous_diskDensity hD)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_kron_const hi, diskDensity_moment hD]


-- @@ L485-495 verbatim
lemma kron_circlePolynomial
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m] {d : ℕ}
    (L : Matrix n n ℂ)
    (B : Fin (d+1) → Matrix m m ℂ) (t : AddCircle (1:ℝ)) :
    L ⊗ₖ circlePolynomial B t = ∑ k, (fourier (k.val:ℤ) t • L) ⊗ₖ B k := by
  ext i j
  simp only [circlePolynomial, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring


-- @@ L497-504 verbatim
lemma diskDensity_polynomial_moment {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    {d : ℕ} (B : Fin (d+1) → Matrix m m ℂ) :
    (∫ t : AddCircle (1:ℝ), diskDensity D t ⊗ₖ circlePolynomial B t ∂circleMeasure) =
      ∑ k, (D^k.val) ⊗ₖ B k := by
  simp_rw [kron_circlePolynomial]
  rw [integral_finsetSum Finset.univ (fun k _ =>
    integrable_diskDensity_monomial_kron hD k.val (B k))]
  exact Finset.sum_congr rfl (fun k _ => diskDensity_monomial_kron hD k.val (B k))


-- @@ L506-519 verbatim
theorem stable_complete_disk_bound {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (hDc : Dᴴ*D ≤ 1)
    {d : ℕ} (B : Fin (d+1) → Matrix m m ℂ)
    (hB : ∀ t, ‖circlePolynomial B t‖ ≤ 1) :
    ‖∑ k, (D^k.val) ⊗ₖ B k‖ ≤ 1 := by
  rw [← diskDensity_polynomial_moment hD B]
  apply norm_integral_density_kron
  · exact (continuous_diskDensity hD).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_kron (continuous_diskDensity hD) (continuous_circlePolynomial B)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro t
    exact Matrix.nonneg_iff_posSemidef.mp (diskDensity_nonneg hD hDc t)
  · simpa only [Nat.cast_zero,fourier_zero,one_smul,pow_zero] using diskDensity_moment hD 0
  · exact hB



-- @@ L522-522 verbatim
end CompleteCrouzeix


-- @@ L524-524 verbatim
end


-- @@ L526-526 verbatim
end OAI
