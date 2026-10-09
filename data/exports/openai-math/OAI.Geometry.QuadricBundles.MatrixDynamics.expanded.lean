import OAI.Geometry.QuadricBundles.Gluing


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3 u4


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace QuadricCounterexample

-- @@ L10-10 verbatim
open Matrix

-- @@ L11-12 verbatim
lemma source_A_det : source_A.det = 1 := by
  simp [source_A, Matrix.det_fin_two, source_a_mul_inv]


-- @@ L14-15 verbatim
lemma source_B_det : source_B.det = 1 := by
  simp [source_B, Matrix.det_fin_two, source_s_mul_complement]


-- @@ L17-18 verbatim
lemma source_A_trace : source_A.trace = 1 := by
  simp [source_A, trace_fin_two, source_a_add_inv]


-- @@ L20-21 verbatim
lemma source_B_trace : source_B.trace = 1 := by
  simp [source_B, trace_fin_two]


-- @@ L23-32 verbatim
lemma matrix_sq_of_det_trace_one
    {M : Matrix (Fin 2) (Fin 2) ℂ} (hd : M.det = 1) (ht : M.trace = 1) :
    M ^ 2 = M - 1 := by
  have h := M.aeval_self_charpoly
  rw [Matrix.charpoly_fin_two, ht, hd] at h
  simp only [map_add, map_sub, map_pow, Polynomial.aeval_X,
    map_one, one_mul] at h
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  simpa only [sub_add_eq_add_sub] using h


-- @@ L34-42 verbatim
lemma matrix_cube_of_det_trace_one
    {M : Matrix (Fin 2) (Fin 2) ℂ} (hd : M.det = 1) (ht : M.trace = 1) :
    M ^ 3 = -1 := by
  have hs := matrix_sq_of_det_trace_one hd ht
  calc
    M ^ 3 = M * M ^ 2 := by noncomm_ring
    _ = M * (M - 1) := by rw [hs]
    _ = M ^ 2 - M := by noncomm_ring
    _ = -1 := by rw [hs]; abel


-- @@ L44-45 verbatim
lemma source_A_cube : source_A ^ 3 = -1 :=
  matrix_cube_of_det_trace_one source_A_det source_A_trace

-- @@ L46-47 verbatim
lemma source_B_cube : source_B ^ 3 = -1 :=
  matrix_cube_of_det_trace_one source_B_det source_B_trace


-- @@ L49-51 verbatim
lemma source_A_six : source_A ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, source_A_cube]
  simp

-- @@ L52-54 verbatim
lemma source_B_six : source_B ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, source_B_cube]
  simp


-- @@ L56-60 verbatim
lemma source_A_inv : source_A⁻¹ = !![source_a⁻¹, 0; 0, source_a] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [source_A, Matrix.mul_apply, source_a_ne_zero]


-- @@ L62-72 verbatim
lemma source_relative_trace : (source_A⁻¹ * source_B).trace = -(Real.sqrt 2 : ℂ) := by
  have htrace : (source_A⁻¹ * source_B).trace =
      source_a⁻¹ * source_s + source_a * (1 - source_s) := by
    simp [source_A_inv, source_B, trace_fin_two]
  rw [htrace]
  rw [source_a_inv_eq, source_a_eq]
  unfold source_s
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring


-- @@ L74-81 verbatim
lemma source_product_trace : (source_A * source_B).trace = 1 + (Real.sqrt 2 : ℂ) := by
  have hinv : source_A + source_A⁻¹ = 1 := by
    rw [source_A_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [source_A, source_a_add_inv, add_comm]
  have htrace := congrArg Matrix.trace (congrArg (fun M ↦ M * source_B) hinv)
  rw [add_mul, trace_add, one_mul, source_relative_trace, source_B_trace] at htrace
  linear_combination htrace


-- @@ L83-88 verbatim
lemma source_abs_product_trace_gt_two : 2 < (source_A * source_B).trace.re := by
  rw [source_product_trace]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith


-- @@ L90-90 verbatim
end QuadricCounterexample


-- @@ L92-92 verbatim
namespace QuadricCounterexample

-- @@ L93-93 verbatim
open Matrix Filter Topology OnePoint

-- @@ L94-94 verbatim
open scoped LinearAlgebra.Projectivization


-- @@ L96-97 verbatim
noncomputable def projectiveCoord (v : Fin 2 → ℂ) : OnePoint ℂ :=
  if v 1 = 0 then ∞ else (v 0 / v 1 : ℂ)


-- @@ L99-103 verbatim
lemma projectiveCoord_eq (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    projectiveCoord v = (OnePoint.equivProjectivization ℂ).symm
      (Projectivization.mk ℂ v hv) := by
  simp [projectiveCoord, OnePoint.equivProjectivization_symm_apply_mk,
    div_eq_mul_inv, mul_comm]


-- @@ L105-109 verbatim
lemma projectiveCoord_smul (c : ℂ) (hc : c ≠ 0) (v : Fin 2 → ℂ) :
    projectiveCoord (c • v) = projectiveCoord v := by
  by_cases hv : v 1 = 0
  · simp [projectiveCoord, hv]
  · simp [projectiveCoord, hv, hc, mul_div_mul_left]


-- @@ L111-118 verbatim
lemma projectiveCoord_action (g : GL (Fin 2) ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    projectiveCoord ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) = g • projectiveCoord v := by
  have hgv : g • v ≠ 0 := (smul_ne_zero_iff_ne g).mpr hv
  change projectiveCoord (g • v) = g • projectiveCoord v
  rw [projectiveCoord_eq _ hgv, projectiveCoord_eq _ hv]
  apply (OnePoint.equivProjectivization ℂ).injective
  simp only [OnePoint.equivProjectivization_smul, Equiv.apply_symm_apply,
    Projectivization.smul_mk]


-- @@ L120-131 verbatim
lemma tendsto_projectiveCoord {α : Type u1} {l : Filter α}
    {v : α → Fin 2 → ℂ} {w : Fin 2 → ℂ}
    (hv : Tendsto v l (𝓝 w)) (hw : w 1 ≠ 0) :
    Tendsto (fun k ↦ projectiveCoord (v k)) l (𝓝 (projectiveCoord w)) := by
  have h0 := (tendsto_pi_nhds.mp hv) 0
  have h1 := (tendsto_pi_nhds.mp hv) 1
  have he : ∀ᶠ k in l, v k 1 ≠ 0 := h1.eventually (isOpen_ne.mem_nhds hw)
  have hdiv := OnePoint.continuous_coe.continuousAt.tendsto.comp (h0.div h1 hw)
  rw [projectiveCoord, ite_eq_right hw]
  apply hdiv.congr'
  filter_upwards [he] with k hk
  simp [projectiveCoord, hk]


-- @@ L133-186 verbatim
theorem projective_orbit_converges_in_eigenbasis
    (g p : GL (Fin 2) ℂ) (lam μ : ℂ) (hlam : lam ≠ 0) (hq : ‖μ / lam‖ < 1)
    (hp : p 1 0 ≠ 0)
    (hdiag : (g : Matrix (Fin 2) (Fin 2) ℂ) * (p : Matrix (Fin 2) (Fin 2) ℂ) =
      (p : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![lam, μ])
    (a b : ℂ) (ha : a ≠ 0) :
    Tendsto (fun k : ℕ ↦ (fun x : OnePoint ℂ ↦ g • x)^[k]
      (p • projectiveCoord ![a,b])) atTop (𝓝 (p • (∞ : OnePoint ℂ))) := by
  let v : ℕ → Fin 2 → ℂ := fun k ↦
    (p : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![a, (μ / lam) ^ k * b]
  have hnv (k : ℕ) : v k ≠ 0 := by
    apply (smul_ne_zero_iff_ne p).mpr
    intro h
    have hc := congrFun h 0
    simpa using ha hc
  have hrec (k : ℕ) : (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v k = lam • v (k+1) := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, hdiag, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    congr 1
    ext i
    fin_cases i
    · simp
    · simp [pow_succ]
      field_simp
  have haction (k : ℕ) : g • projectiveCoord (v k) = projectiveCoord (v (k+1)) := by
    rw [← projectiveCoord_action g _ (hnv k), hrec, projectiveCoord_smul _ hlam]
  have hzero : projectiveCoord (v 0) = p • projectiveCoord ![a,b] := by
    dsimp [v]
    simp only [pow_zero, one_mul]
    exact projectiveCoord_action p _ (by intro h; exact ha (congrFun h 0))
  have horbit (k : ℕ) : (fun x : OnePoint ℂ ↦ g • x)^[k]
      (p • projectiveCoord ![a,b]) = projectiveCoord (v k) := by
    induction k with
    | zero => exact hzero.symm
    | succ k ih => rw [Function.iterate_succ_apply', ih, haction]
  have hlim0 : Tendsto (fun k : ℕ ↦ ![a, (μ / lam)^k * b]) atTop (𝓝 ![a,0]) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).mul_const b
  have hc : Continuous (fun w : Fin 2 → ℂ ↦
      (p : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ w) := by fun_prop
  have hlim : Tendsto v atTop (𝓝 ((p : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![a,0])) :=
    hc.continuousAt.tendsto.comp hlim0
  have hlast : ((p : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![a,0]) 1 ≠ 0 := by
    simpa using mul_ne_zero hp ha
  have hfinal : projectiveCoord ((p : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![a,0]) =
      p • (∞ : OnePoint ℂ) := by
    rw [projectiveCoord_action p _ (by intro h; exact ha (congrFun h 0))]
    simp [projectiveCoord]
  have h := tendsto_projectiveCoord hlim hlast
  rw [hfinal] at h
  simpa only [horbit] using h


-- @@ L188-215 verbatim
theorem projective_north_south_of_eigenbasis
    (g p : GL (Fin 2) ℂ) (lam μ : ℂ) (hlam : lam ≠ 0) (hq : ‖μ / lam‖ < 1)
    (hp : p 1 0 ≠ 0)
    (hdiag : (g : Matrix (Fin 2) (Fin 2) ℂ) * (p : Matrix (Fin 2) (Fin 2) ℂ) =
      (p : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![lam, μ]) :
    ∀ x : OnePoint ℂ, x ≠ p • (0 : ℂ) →
      Tendsto (fun k : ℕ ↦ (fun x : OnePoint ℂ ↦ g • x)^[k] x) atTop
        (𝓝 (p • (∞ : OnePoint ℂ))) := by
  intro x hx
  have hy : p⁻¹ • x ≠ ((0 : ℂ) : OnePoint ℂ) := by
    intro h
    apply hx
    simpa using congrArg (fun y : OnePoint ℂ ↦ p • y) h
  have h : ∀ y : OnePoint ℂ, y ≠ ((0 : ℂ) : OnePoint ℂ) →
      Tendsto (fun k : ℕ ↦ (fun z : OnePoint ℂ ↦ g • z)^[k] (p • y)) atTop
        (𝓝 (p • (∞ : OnePoint ℂ))) := by
    intro y
    induction y using OnePoint.rec with
    | infty =>
      intro _
      simpa [projectiveCoord] using
        projective_orbit_converges_in_eigenbasis g p lam μ hlam hq hp hdiag 1 0 one_ne_zero
    | coe z =>
      intro hz
      have hz0 : z ≠ 0 := fun h ↦ hz (by rw [h])
      simpa [projectiveCoord] using
        projective_orbit_converges_in_eigenbasis g p lam μ hlam hq hp hdiag z 1 hz0
  simpa using h (p⁻¹ • x) hy


-- @@ L217-217 verbatim
end QuadricCounterexample


-- @@ L219-219 verbatim
namespace QuadricCounterexample

-- @@ L220-220 verbatim
open Matrix


-- @@ L222-222 verbatim
noncomputable def expandingRoot (t : ℝ) : ℝ := (t + Real.sqrt (t^2 - 4)) / 2

-- @@ L223-223 verbatim
noncomputable def contractingRoot (t : ℝ) : ℝ := (t - Real.sqrt (t^2 - 4)) / 2


-- @@ L225-242 verbatim
lemma hyperbolic_roots {t : ℝ} (ht : 2 < t) :
    1 < expandingRoot t ∧ 0 < contractingRoot t ∧
    contractingRoot t < 1 ∧
    expandingRoot t + contractingRoot t = t ∧
    expandingRoot t * contractingRoot t = 1 := by
  have hs0 : 0 < t ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hs0.le
  have hp := Real.sqrt_pos.mpr hs0
  dsimp [expandingRoot, contractingRoot]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · ring
  · nlinarith


-- @@ L244-249 verbatim
lemma hyperbolic_norm_ratio {t : ℝ} (ht : 2 < t) :
    ‖(contractingRoot t : ℂ) / (expandingRoot t : ℂ)‖ < 1 := by
  obtain ⟨hl, hm, hm1, _, _⟩ := hyperbolic_roots ht
  rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos hm (by linarith)), div_lt_one (by linarith)]
  linarith


-- @@ L251-254 verbatim
noncomputable def hyperbolicBasis (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(expandingRoot t : ℂ) - M 1 1, (contractingRoot t : ℂ) - M 1 1;
    M 1 0, M 1 0]


-- @@ L256-267 verbatim
lemma hyperbolicBasis_det_ne_zero {M : Matrix (Fin 2) (Fin 2) ℂ} {t : ℝ}
    (ht : 2 < t) (hc : M 1 0 ≠ 0) : (hyperbolicBasis M t).det ≠ 0 := by
  have hd : expandingRoot t - contractingRoot t ≠ 0 := by
    obtain ⟨hl, _, hm, _, _⟩ := hyperbolic_roots ht
    linarith
  have hdC : (expandingRoot t : ℂ) - (contractingRoot t : ℂ) ≠ 0 := by exact_mod_cast hd
  have hdet : (hyperbolicBasis M t).det =
      M 1 0 * ((expandingRoot t : ℂ) - (contractingRoot t : ℂ)) := by
    simp [hyperbolicBasis, Matrix.det_fin_two]
    ring
  rw [hdet]
  exact mul_ne_zero hc hdC


-- @@ L269-288 verbatim
lemma hyperbolicBasis_diagonalizes {M : Matrix (Fin 2) (Fin 2) ℂ} {t : ℝ}
    (ht : 2 < t) (htr : M.trace = (t : ℂ)) (hdet : M.det = 1) :
    M * hyperbolicBasis M t = hyperbolicBasis M t *
      Matrix.diagonal ![(expandingRoot t : ℂ), (contractingRoot t : ℂ)] := by
  obtain ⟨_, _, _, hs, hp⟩ := hyperbolic_roots ht
  have hsC : (expandingRoot t : ℂ) + (contractingRoot t : ℂ) = (t : ℂ) := by
    exact_mod_cast hs
  have hpC : (expandingRoot t : ℂ) * (contractingRoot t : ℂ) = 1 := by
    exact_mod_cast hp
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicBasis, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (expandingRoot t : ℂ) * (htr - hsC) -
      hdet + hpC
  · linear_combination (contractingRoot t : ℂ) * (htr - hsC) -
      hdet + hpC
  · ring
  · ring


-- @@ L290-290 verbatim
end QuadricCounterexample


-- @@ L292-292 verbatim
namespace QuadricCounterexample

-- @@ L293-293 verbatim
open Filter Topology Set MeasureTheory


-- @@ L295-311 verbatim
theorem invariant_measure_ae_endpoints
    {X : Type u2} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {T : X → X} {a b : X}
    (hT : MeasurePreserving T μ μ)
    (hconverge : ∀ x, x ≠ b → Tendsto (fun k : ℕ ↦ T^[k] x) atTop (𝓝 a)) :
    ∀ᵐ x ∂μ, x = a ∨ x = b := by
  filter_upwards [hT.conservative.ae_frequently_mem_of_mem_nhds] with x hx
  by_cases hxb : x = b
  · exact Or.inr hxb
  · left
    by_contra hxa
    obtain ⟨U, V, hU, hV, hxU, haV, huv⟩ := t2_separation hxa
    have hf := hx U (hU.mem_nhds hxU)
    have he := (hconverge x hxb).eventually (hV.mem_nhds haV)
    obtain ⟨k, hkU, hkV⟩ := (hf.and_eventually he).exists
    exact Set.disjoint_left.mp huv hkU hkV


-- @@ L313-325 verbatim
lemma fixed_of_period_three_in_pair {X : Type u3} {f : X → X} {p q x : X}
    (hcube : f (f (f x)) = x) (hx : x = p ∨ x = q)
    (h1 : f x = p ∨ f x = q) (h2 : f (f x) = p ∨ f (f x) = q) : f x = x := by
  have hcollision : x = f x ∨ x = f (f x) ∨ f x = f (f x) := by
    rcases hx with hx | hx <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      simp_all
  rcases hcollision with h | h | h
  · exact h.symm
  · simpa only [hcube] using congrArg f h
  · calc
      f x = f (f x) := h
      _ = f (f (f x)) := congrArg f h
      _ = x := hcube


-- @@ L327-348 verbatim
theorem no_invariant_measure_of_period_three_north_south
    {X : Type u4} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {A B : X → X} {a b : X}
    (hA : MeasurePreserving A μ μ) (hB : MeasurePreserving B μ μ)
    (hA3 : ∀ x, A (A (A x)) = x) (hB3 : ∀ x, B (B (B x)) = x)
    (hfix : ∀ x, ¬(A x = x ∧ B x = x))
    (hconverge : ∀ x, x ≠ b →
      Tendsto (fun k : ℕ ↦ (A ∘ B)^[k] x) atTop (𝓝 a)) : μ = 0 := by
  by_contra hμ
  let : NeZero μ := ⟨hμ⟩
  have hs := invariant_measure_ae_endpoints (hA.comp hB) hconverge
  have hA1 := hA.quasiMeasurePreserving.ae hs
  have hA2 := hA.quasiMeasurePreserving.ae hA1
  have hB1 := hB.quasiMeasurePreserving.ae hs
  have hB2 := hB.quasiMeasurePreserving.ae hB1
  have he : ∀ᵐ x ∂μ, A x = x ∧ B x = x := by
    filter_upwards [hs, hA1, hA2, hB1, hB2] with x hx ha1 ha2 hb1 hb2
    exact ⟨fixed_of_period_three_in_pair (hA3 x) hx ha1 ha2,
      fixed_of_period_three_in_pair (hB3 x) hx hb1 hb2⟩
  obtain ⟨x, hx⟩ := he.exists
  exact hfix x hx


-- @@ L350-350 verbatim
end QuadricCounterexample


-- @@ L352-352 verbatim
namespace QuadricCounterexample

-- @@ L353-353 verbatim
open Matrix OnePoint Filter Topology MeasureTheory


-- @@ L355-356 verbatim
noncomputable def source_A_gl : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero source_A (by rw [source_A_det]; exact one_ne_zero)

-- @@ L357-358 verbatim
noncomputable def source_B_gl : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero source_B (by rw [source_B_det]; exact one_ne_zero)


-- @@ L360-360 verbatim
@[simp] lemma source_A_gl_val : (source_A_gl : Matrix (Fin 2) (Fin 2) ℂ) = source_A := rfl

-- @@ L361-361 verbatim
@[simp] lemma source_B_gl_val : (source_B_gl : Matrix (Fin 2) (Fin 2) ℂ) = source_B := rfl


-- @@ L363-374 verbatim
lemma projective_cube_identity {g : GL (Fin 2) ℂ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 = -1) :
    ∀ x : OnePoint ℂ, g • (g • (g • x)) = x := by
  intro x
  have hv : ((g ^ 3 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    simpa using hg
  calc
    g • (g • (g • x)) = (g^3) • x := by simp [pow_succ, mul_smul]
    _ = x := by
      cases x using OnePoint.rec with
      | infty => simp [OnePoint.smul_infty_eq_ite, hv]
      | coe z => simp [OnePoint.smul_some_eq_ite, hv]


-- @@ L376-398 verbatim
lemma source_no_common_fixed_point (x : OnePoint ℂ) :
    ¬ (source_A_gl • x = x ∧ source_B_gl • x = x) := by
  rintro ⟨hA, hB⟩
  cases x using OnePoint.rec with
  | infty =>
    have hc := OnePoint.smul_infty_eq_self_iff.mp hB
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
    simp [source_B_gl, source_B, hn] at hc
  | coe z =>
    have hpoly := Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mpr hA
    have hdiff : source_a - source_a⁻¹ ≠ 0 := by
      rw [source_a_inv_eq, source_a_eq]
      intro h
      have hi := congrArg Complex.im h
      simp at hi
    have haz : (source_a⁻¹ - source_a) * z = 0 := by
      simpa [Matrix.GeneralLinearGroup.fixpointPolynomial, source_A_gl, source_A] using hpoly
    have hz : z = 0 := (mul_eq_zero.mp haz).resolve_left (sub_ne_zero.mpr
      (Ne.symm (sub_ne_zero.mp hdiff)))
    subst z
    have hb := Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mpr hB
    simp [Matrix.GeneralLinearGroup.fixpointPolynomial, source_B_gl, source_B] at hb


-- @@ L400-403 verbatim
lemma source_product_lower_left_ne_zero : (source_A * source_B) 1 0 ≠ 0 := by
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  simp [source_A, source_B, Matrix.mul_apply, source_a_ne_zero, hn]


-- @@ L405-411 verbatim
noncomputable def source_eigenbasis : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (hyperbolicBasis (source_A * source_B) (1 + Real.sqrt 2))
    (hyperbolicBasis_det_ne_zero (by
      have hn := Real.sqrt_nonneg (2 : ℝ)
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith) source_product_lower_left_ne_zero)


-- @@ L413-430 verbatim
lemma source_north_south :
    ∀ x : OnePoint ℂ, x ≠ source_eigenbasis • (0 : ℂ) →
    Tendsto (fun k : ℕ ↦
      (fun z : OnePoint ℂ ↦ (source_A_gl * source_B_gl) • z)^[k] x) atTop
      (𝓝 (source_eigenbasis • (∞ : OnePoint ℂ))) := by
  have ht : 2 < 1 + Real.sqrt 2 := by
    have hn := Real.sqrt_nonneg (2 : ℝ)
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  apply projective_north_south_of_eigenbasis (source_A_gl * source_B_gl)
    source_eigenbasis (expandingRoot (1 + Real.sqrt 2)) (contractingRoot (1 + Real.sqrt 2))
  · exact_mod_cast (ne_of_gt (lt_trans zero_lt_one (hyperbolic_roots ht).1))
  · exact hyperbolic_norm_ratio ht
  · exact source_product_lower_left_ne_zero
  · apply hyperbolicBasis_diagonalizes ht
    · simpa using source_product_trace
    · change (source_A * source_B).det = 1
      rw [Matrix.det_mul, source_A_det, source_B_det, one_mul]


-- @@ L432-432 verbatim
end QuadricCounterexample


-- @@ L434-434 verbatim
namespace QuadricCounterexample

-- @@ L435-435 verbatim
open Matrix OnePoint MeasureTheory


-- @@ L437-439 verbatim
local instance projectiveLineSecondCountable : SecondCountableTopology (OnePoint ℂ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 3) (V := ℂ)
    (by simp [Complex.finrank_real_complex])).secondCountableTopology

-- @@ L440-440 verbatim
noncomputable local instance projectiveLineMeasurable : MeasurableSpace (OnePoint ℂ) := borel _

-- @@ L441-441 verbatim
local instance projectiveLineBorel : BorelSpace (OnePoint ℂ) := ⟨rfl⟩


-- @@ L443-450 verbatim
theorem source_no_invariant_finite_measure
    (μ : Measure (OnePoint ℂ)) [IsFiniteMeasure μ]
    (hA : MeasurePreserving (fun x : OnePoint ℂ ↦ source_A_gl • x) μ μ)
    (hB : MeasurePreserving (fun x : OnePoint ℂ ↦ source_B_gl • x) μ μ) : μ = 0 := by
  apply no_invariant_measure_of_period_three_north_south hA hB
    (projective_cube_identity source_A_cube) (projective_cube_identity source_B_cube)
    source_no_common_fixed_point
  simpa only [Function.comp_def, mul_smul] using source_north_south


-- @@ L452-452 verbatim
end QuadricCounterexample


-- @@ L454-454 verbatim
end


-- @@ L456-456 verbatim
end OAI
