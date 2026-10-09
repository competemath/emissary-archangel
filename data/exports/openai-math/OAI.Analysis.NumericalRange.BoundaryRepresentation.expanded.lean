import OAI.Analysis.NumericalRange.CauchyEvaluation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace CompleteCrouzeix



-- @@ L10-10 verbatim
universe u_116 u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128 u_129 u_130 u_131 u_132 u_133 u_134 u_135 u_136 u_137 u_138 u_139 u_140 u_141 u_142 u_143 u_144 u_145 u_146 u_147 u_148 u_149 u_150 u_151 u_152 u_153


-- @@ L12-12 verbatim
open scoped BigOperators Matrix.Norms.L2Operator

-- @@ L13-13 verbatim
open Polynomial Finset



-- @@ L16-16 verbatim
open Filter Topology

-- @@ L17-17 verbatim
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

-- @@ L18-18 verbatim
section



-- @@ L21-21 verbatim
open MeasureTheory

-- @@ L22-22 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- @@ L23-23 verbatim
variable {n : Type u_121} [Fintype n] [DecidableEq n]


-- @@ L25-25 verbatim
open scoped Kronecker


-- @@ L27-27 verbatim
variable {m : Type u_122} [Fintype m] [DecidableEq m]



-- @@ L30-30 verbatim
open Filter Topology MeasureTheory Set Metric

-- @@ L31-31 verbatim
open scoped ENNReal NNReal Matrix.Norms.L2Operator

-- @@ L32-32 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- @@ L33-33 verbatim
variable {n : Type u_123} [Fintype n] [DecidableEq n]



-- @@ L36-36 verbatim
open Filter Topology MeasureTheory Set Metric

-- @@ L37-37 verbatim
open scoped ENNReal NNReal Matrix.Norms.L2Operator

-- @@ L38-38 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- @@ L39-39 verbatim
variable {n : Type u_124} [Fintype n] [DecidableEq n]



-- @@ L42-42 verbatim
open Filter Topology MeasureTheory Set Metric

-- @@ L43-43 verbatim
open scoped ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder Kronecker

-- @@ L44-44 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- @@ L45-45 verbatim
variable {n : Type u_125} {m : Type u_126} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]


-- @@ L47-47 verbatim
end



-- @@ L50-50 verbatim
open Set Filter Metric Complex

-- @@ L51-51 verbatim
open scoped Topology ComplexConjugate


-- @@ L53-53 verbatim
open MeasureTheory Set Complex

-- @@ L54-54 verbatim
open scoped Topology Real

-- @@ L55-55 verbatim
section

-- @@ L56-56 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
open MeasureTheory Set Complex

-- @@ L61-61 verbatim
open scoped Topology


-- @@ L63-63 verbatim
open MeasureTheory Set Complex Metric

-- @@ L64-64 verbatim
open scoped Topology

-- @@ L65-65 verbatim
section

-- @@ L66-66 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


-- @@ L68-68 verbatim
end


-- @@ L70-70 verbatim
section

-- @@ L71-71 verbatim
open MeasureTheory Set Metric Complex Filter

-- @@ L72-72 verbatim
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder

-- @@ L73-73 verbatim
variable {n : Type u_150} {m : Type u_151} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]


-- @@ L75-80 verbatim
lemma stable_disk_inverse_isUnit {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : IsUnit (1-z • D) := by
  apply spectrum.isUnit_one_sub_smul_of_lt_inv_radius
  have he : (1 : ℝ≥0∞) < (spectralRadius ℂ D)⁻¹ := by
    simpa only [inv_one] using ENNReal.inv_lt_inv.mpr hD
  exact lt_of_le_of_lt (by exact_mod_cast hz) he


-- @@ L82-87 verbatim
lemma stable_star_disk_inverse_isUnit {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    IsUnit (1-z • Dᴴ) := by
  have hu := (stable_disk_inverse_isUnit hD (z := conj z) (by simpa using hz)).star
  simpa only [star_sub, star_one, star_smul, star_star, Matrix.star_eq_conjTranspose,
    starRingEnd_apply] using hu


-- @@ L89-90 verbatim
def boundaryDiskDensity (D : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (1-z⁻¹ • D)⁻¹ + ((1-z⁻¹ • D)⁻¹)ᴴ - 1


-- @@ L92-119 verbatim
lemma boundaryDiskDensity_nonneg {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    (hc : Dᴴ*D ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ boundaryDiskDensity D z := by
  let E : Matrix n n ℂ := 1-z⁻¹ • D
  let R : Matrix n n ℂ := E⁻¹
  have hu : IsUnit E := stable_disk_inverse_isUnit hD (by simp [norm_inv, hz])
  have hER : E*R = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det E).mp hu)
  have hzz : star z⁻¹ * z⁻¹ = 1 := by
    change conj z⁻¹ * z⁻¹ = 1
    rw [RCLike.conj_mul, norm_inv, hz]
    norm_num
  have hdef : Eᴴ+E-Eᴴ*E = 1-Dᴴ*D := by
    dsimp [E]
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_smul]
    simp only [sub_mul,mul_sub,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul,mul_comm z⁻¹ (star z⁻¹),hzz,one_smul]
    abel
  have hcong : Rᴴ*(1-Dᴴ*D)*R = boundaryDiskDensity D z := by
    rw [← hdef]
    have hs := congrArg Matrix.conjTranspose hER
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_one] at hs
    change Rᴴ*(Eᴴ+E-Eᴴ*E)*R = R+Rᴴ-1
    calc
      _ = (Rᴴ*Eᴴ)*R + Rᴴ*(E*R) - (Rᴴ*Eᴴ)*(E*R) := by noncomm_ring
      _ = _ := by rw [hs,hER]; simp
  rw [← hcong]
  exact (Matrix.PosSemidef.conjTranspose_mul_mul_same
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hc)) R).nonneg


-- @@ L121-142 verbatim
lemma boundaryDiskDensity_eq {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    boundaryDiskDensity D z =
      z • (z • (1 : Matrix n n ℂ)-D)⁻¹ + (1-z • Dᴴ)⁻¹ - 1 := by
  have hzn : z ≠ 0 := by intro h; simp [h] at hz
  have he : 1-z⁻¹ • D = z⁻¹ • (z • (1 : Matrix n n ℂ)-D) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hzn, one_smul]
  have hi : star z⁻¹ = z := by
    rw [star_inv₀]
    change (conj z)⁻¹ = z
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, norm_conj, hz]
    simp
  have hu : IsUnit (z • (1 : Matrix n n ℂ)-D) := by
    have hn : z ∉ spectrum ℂ D := by
      intro hs
      have hh := stable_spectrum_norm_lt_one hD hs
      linarith
    simpa only [Algebra.algebraMap_eq_smul_one] using (spectrum.notMem_iff.mp hn)
  let : Invertible z := invertibleOfNonzero hzn
  unfold boundaryDiskDensity
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hi,
    he, Matrix.inv_smul _ _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hu), invOf_eq_inv, inv_inv]


-- @@ L144-162 verbatim
lemma coordinate_circle_cauchy {ψ H : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hH : AnalyticOnNhd ℂ H (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    (∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
      (ψ (t.toCircle : ℂ)-z))*H (ψ (t.toCircle : ℂ))
        ∂AddCircle.haarAddCircle) = H z := by
  apply circle_convex_cauchy (convex_closedBall (0:ℂ) 1) hH hψ
    (fun t ht => by simpa [mem_closedBall] using (hb t ht).le)
    (ball_subset_closedBall hz) _ (hmass z hz)
  intro t ht he
  have hh := hb t ht
  rw [he] at hh
  have hz' : ‖z‖ < 1 := by simpa using hz
  exact (ne_of_lt hz') hh


-- @@ L164-164 verbatim
end


-- @@ L166-166 verbatim
open MeasureTheory Set Metric Complex Filter

-- @@ L167-167 verbatim
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder

-- @@ L168-168 verbatim
variable {n : Type u_152} {m : Type u_153} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]


-- @@ L170-202 verbatim
lemma coordinate_circle_cauchy_matrix {ψ : ℂ → ℂ} {J : ℂ → Matrix n n ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hJ : ∀ i j, AnalyticOnNhd ℂ (fun z => J z i j) (closedBall 0 1))
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle,
      ((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) •
        J (ψ (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = J 0 := by
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by simp [Circle.norm_coe]
  have hc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) := by fun_prop
  have hψc := hψ.continuousOn.comp_continuous hc ht
  have hψd := hψ.deriv.continuousOn.comp_continuous hc ht
  have hjc : Continuous (fun t : UnitAddCircle =>
      (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) :=
    (hc.mul hψd).div hψc (fun t => norm_ne_zero_iff.mp (by rw [hb _ (ht t)]; norm_num))
  have hJc : Continuous (fun t : UnitAddCircle => J (ψ (t.toCircle : ℂ))) := by
    apply continuous_matrix
    intro i j
    exact (hJ i j).continuousOn.comp_continuous hψc
      (fun t => by simpa [mem_closedBall] using (hb _ (ht t)).le)
  have hi := (hjc.smul hJc).integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  ext i j
  erw [matrix_integral_entry hi]
  convert! coordinate_circle_cauchy hψ hb (hJ i j) hmass (z := 0) (by simp) using 1
  apply integral_congr_ae
  filter_upwards [] with t
  change (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ) *
      J (ψ (t.toCircle : ℂ)) i j =
    (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/(ψ (t.toCircle : ℂ)-0) *
      J (ψ (t.toCircle : ℂ)) i j
  rw [sub_zero]


-- @@ L204-293 verbatim
theorem complete_pulled_disk_representation {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1)
    {H : ℂ → Matrix m m ℂ}
    (hH : ∀ i j, AnalyticOnNhd ℂ (fun z => H z i j) (closedBall 0 1)) :
    (∫ t : UnitAddCircle,
      (((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ)) •
        boundaryDiskDensity D (ψ (t.toCircle : ℂ))) ⊗ₖ
          H (ψ (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle) = completeAnalyticEval D H := by
  let c : UnitAddCircle → ℂ := fun t => (t.toCircle : ℂ)
  let s : UnitAddCircle → ℂ := fun t => ψ (c t)
  let v : UnitAddCircle → ℂ := fun t => c t*deriv ψ (c t)
  let j : UnitAddCircle → ℂ := fun t => v t/s t
  have ht (t : UnitAddCircle) : c t ∈ sphere (0:ℂ) 1 := by simp [c, Circle.norm_coe]
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hs : Continuous s := hψ.continuousOn.comp_continuous hc ht
  have hv : Continuous v := hc.mul (hψ.deriv.continuousOn.comp_continuous hc ht)
  have hsn (t : UnitAddCircle) : s t ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [show ‖s t‖ = 1 from hb _ (ht t)]; norm_num)
  have hj : Continuous j := hv.div hs hsn
  have hsb (t : UnitAddCircle) : s t ∈ closedBall (0:ℂ) 1 := by
    simpa [mem_closedBall] using (hb _ (ht t)).le
  have hHc : Continuous (fun t => H (s t)) := by
    apply continuous_matrix
    intro a b
    exact (hH a b).continuousOn.comp_continuous hs hsb
  have hspec : spectrum ℂ D ⊆ ball (0:ℂ) 1 := fun z hz => by
    simpa using stable_spectrum_norm_lt_one hD hz
  have hne (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) (t : UnitAddCircle) : s t ≠ z := by
    intro he
    have hh : ‖s t‖ = 1 := hb _ (ht t)
    rw [he] at hh
    have hz' : ‖z‖ < 1 := by simpa using hz
    exact (ne_of_lt hz') hh
  let K : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => (v t • (s t • (1 : Matrix n n ℂ)-D)⁻¹) ⊗ₖ H (s t)
  let B : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => j t • ((1-s t • Dᴴ)⁻¹ ⊗ₖ H (s t))
  let C : UnitAddCircle → Matrix (n × m) (n × m) ℂ :=
    fun t => j t • ((1 : Matrix n n ℂ) ⊗ₖ H (s t))
  have hKc : Continuous K := continuous_kron
    (hv.smul (matrix_resolvent_continuous D hs (fun t hz => hne _ (hspec hz) t rfl))) hHc
  have hR : AnalyticOnNhd ℂ (fun z : ℂ => (1-z • Dᴴ)⁻¹) (closedBall 0 1) := by
    intro z hz
    exact scalar_matrix_inverse_analytic (stable_star_disk_inverse_isUnit hD (by simpa using hz))
  have hBc : Continuous B := hj.smul (continuous_kron
    (hR.continuousOn.comp_continuous hs hsb) hHc)
  have hCc : Continuous C := hj.smul (continuous_kron continuous_const hHc)
  have hKi := hKc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hBi := hBc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hCi := hCc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hKe : (∫ t, K t ∂AddCircle.haarAddCircle) = completeAnalyticEval D H := by
    rw [← complete_cauchy_integral_evaluation D hs hv hHc isOpen_ball hspec hne]
    apply completeAnalyticEval_eqOn D isOpen_ball hspec
    intro z hz
    ext a b
    have he := coordinate_circle_cauchy hψ hb (hH a b) hmass hz
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [v,s,c]
    ring
  have hBe : (∫ t, B t ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ H 0 := by
    have he := coordinate_circle_cauchy_matrix hψ hb
      (J := fun z => (1-z • Dᴴ)⁻¹ ⊗ₖ H z)
      (fun a b z hz => (matrix_entry_analytic (hR z hz) a.1 b.1).mul (hH a.2 b.2 z hz)) hmass
    simpa only [B,j,v,s,c,zero_smul,sub_zero,inv_one] using he
  have hCe : (∫ t, C t ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ H 0 := by
    exact coordinate_circle_cauchy_matrix hψ hb
      (J := fun z => (1 : Matrix n n ℂ) ⊗ₖ H z)
      (fun a b z hz => analyticAt_const.mul (hH a.2 b.2 z hz)) hmass
  calc
    _ = ∫ t, (K t+B t-C t) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [boundaryDiskDensity_eq hD (hb _ (ht t))]
      change (j t • (s t • (s t • (1 : Matrix n n ℂ)-D)⁻¹ +
        (1-s t • Dᴴ)⁻¹-1)) ⊗ₖ H (s t) = K t+B t-C t
      dsimp [K,B,C,j]
      ext ⟨a₁,a₂⟩ ⟨b₁,b₂⟩
      simp only [Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.add_apply, Matrix.sub_apply]
      field_simp [hsn t]
    _ = completeAnalyticEval D H := by
      erw [integral_sub (hKi.add hBi) hCi, integral_add hKi hBi, hKe,hBe,hCe]
      abel



-- @@ L296-296 verbatim
end CompleteCrouzeix


-- @@ L298-298 verbatim
end


-- @@ L300-300 verbatim
end OAI
