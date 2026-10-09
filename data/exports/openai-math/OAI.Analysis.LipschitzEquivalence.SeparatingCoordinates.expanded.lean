import OAI.Analysis.LipschitzEquivalence.FiniteApproximants


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uIndex uOtherIndex


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators InnerProductSpace Topology ENNReal


-- @@ L10-10 verbatim
namespace LipschitzCounterexample.SeparatingStages


-- @@ L12-12 verbatim
def psi (t : ℝ) : ℝ := expNegInvGlue (1-t^2)


-- @@ L14-14 verbatim
theorem psi_nonneg (t : ℝ) : 0 ≤ psi t := expNegInvGlue.nonneg _


-- @@ L16-29 verbatim
theorem psi_pos_iff {t : ℝ} : 0 < psi t ↔ |t| < 1 := by
  constructor
  · intro h
    have ht : 0 < 1-t^2 := by
      by_contra hh
      have := expNegInvGlue.zero_of_nonpos (le_of_not_gt hh)
      change expNegInvGlue (1-t^2) > 0 at h
      linarith
    rw [abs_lt]
    constructor <;> nlinarith [sq_nonneg (t-1), sq_nonneg (t+1)]
  · intro h
    apply expNegInvGlue.pos_of_pos
    have hh := abs_lt.mp h
    nlinarith [mul_pos (by linarith : 0 < 1-t) (by linarith : 0 < 1+t)]


-- @@ L31-35 verbatim
theorem psi_ne_zero_iff {t : ℝ} : psi t ≠ 0 ↔ |t| < 1 := by
  rw [← psi_pos_iff]
  constructor
  · intro h; exact lt_of_le_of_ne (psi_nonneg t) (Ne.symm h)
  · exact ne_of_gt


-- @@ L37-38 verbatim
theorem psi_contDiff {n : ℕ∞} : ContDiff ℝ n psi :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))


-- @@ L40-40 verbatim
abbrev Label (k : ℕ) := Fin k → {a : ℤ // a ∈ Set.Icc (-(k : ℤ)) k}

-- @@ L41-41 verbatim
abbrev Stage (k : ℕ) := EuclideanSpace ℝ (Label k)

-- @@ L42-42 verbatim
abbrev CubeSpace (k : ℕ) := EuclideanSpace ℝ (Fin k)


-- @@ L44-45 verbatim
def G (k : ℕ) (t : CubeSpace k) : Stage k :=
  WithLp.toLp 2 (fun a => ∏ j, psi ((k : ℝ)*t j - (a j : ℤ)))


-- @@ L47-48 verbatim
@[simp] theorem G_apply (k : ℕ) (t : CubeSpace k) (a : Label k) :
    G k t a = ∏ j, psi ((k : ℝ)*t j - (a j : ℤ)) := rfl


-- @@ L50-70 verbatim
theorem rounding_label {k : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ a : {a : ℤ // a ∈ Set.Icc (-(k : ℤ)) k}, |(k : ℝ)*t - (a : ℤ)| ≤ 1/2 := by
  let a : ℤ := round ((k : ℝ)*t)
  have hround := abs_sub_round ((k : ℝ)*t)
  have hlow : -((k : ℝ)) ≤ (k : ℝ)*t := by nlinarith [Nat.cast_nonneg (α := ℝ) k, ht.1, ht.2]
  have hupp : (k : ℝ)*t ≤ k := by nlinarith [Nat.cast_nonneg (α := ℝ) k, ht.1, ht.2]
  have ha₁ : -(k : ℤ) ≤ a := by
    by_contra h
    have hai : a ≤ -(k : ℤ)-1 := by omega
    have har : (a : ℝ) ≤ -(k : ℝ)-1 := by exact_mod_cast hai
    have := (abs_le.mp hround).2
    change _ ≤ 1/2 at this
    change |(k : ℝ)*t - (a : ℝ)| ≤ 1/2 at hround
    nlinarith [abs_le.mp hround]
  have ha₂ : a ≤ (k : ℤ) := by
    by_contra h
    have hai : (k : ℤ)+1 ≤ a := by omega
    have har : (k : ℝ)+1 ≤ (a : ℝ) := by exact_mod_cast hai
    change |(k : ℝ)*t - (a : ℝ)| ≤ 1/2 at hround
    nlinarith [abs_le.mp hround]
  exact ⟨⟨a, ha₁, ha₂⟩, hround⟩


-- @@ L72-82 verbatim
theorem G_ne_zero {k : ℕ} (t : CubeSpace k) (ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1) :
    G k t ≠ 0 := by
  choose a ha using fun j => rounding_label (ht j)
  have hp : 0 < G k t a := by
    rw [G_apply]
    apply Finset.prod_pos
    intro j hj
    exact psi_pos_iff.mpr (lt_of_le_of_lt (ha j) (by norm_num))
  intro hz
  have hh : G k t a = 0 := by rw [hz]; rfl
  linarith


-- @@ L84-84 verbatim
def normalized (k : ℕ) (t : CubeSpace k) : Stage k := ‖G k t‖⁻¹ • G k t


-- @@ L86-89 verbatim
theorem norm_normalized {k : ℕ} (t : CubeSpace k) (ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1) :
    ‖normalized k t‖ = 1 := by
  rw [normalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (G_ne_zero t ht))


-- @@ L91-99 verbatim
theorem normalized_support {k : ℕ} {t : CubeSpace k} {a : Label k}
    (ha : normalized k t a ≠ 0) (j : Fin k) : |(k : ℝ)*t j - (a j : ℤ)| < 1 := by
  have hG : G k t a ≠ 0 := by
    intro hz
    apply ha
    change ‖G k t‖⁻¹ * G k t a = 0
    rw [hz, mul_zero]
  rw [G_apply, Finset.prod_ne_zero_iff] at hG
  exact psi_ne_zero_iff.mp (hG j (Finset.mem_univ _))


-- @@ L101-115 verbatim
theorem support_disjoint {k : ℕ} (hk : 0 < k) {s t : CubeSpace k} (j : Fin k)
    (hst : 2/(k : ℝ) < |s j-t j|) (a : Label k) :
    normalized k s a = 0 ∨ normalized k t a = 0 := by
  by_contra h
  push Not at h
  have hs := abs_lt.mp (normalized_support h.1 j)
  have ht := abs_lt.mp (normalized_support h.2 j)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hmul : 2 < |s j-t j| *(k : ℝ) := (div_lt_iff₀ hk').mp hst
  rw [abs_sub_comm] at hst
  rcases le_total (s j) (t j) with hj | hj
  · rw [abs_of_nonpos (sub_nonpos.mpr hj)] at hmul
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hj)] at hmul
    nlinarith


-- @@ L117-117 verbatim
def cube (k : ℕ) : Set (CubeSpace k) := {t | ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1}


-- @@ L119-128 verbatim
theorem cube_compact (k : ℕ) : IsCompact (cube k) := by
  have h := (isCompact_pi_infinite (fun _ : Fin k => isCompact_Icc (a := (-1 : ℝ)) (b := 1))).image
    (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ))
  convert h using 1
  ext t
  constructor
  · intro ht
    exact ⟨WithLp.ofLp t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ht


-- @@ L130-136 verbatim
theorem G_contDiff (k : ℕ) {n : ℕ∞} : ContDiff ℝ n (G k) := by
  apply (contDiff_piLp 2).2
  intro a
  change ContDiff ℝ n (fun t : CubeSpace k => ∏ j, psi ((k : ℝ)*t j - (a j : ℤ)))
  apply contDiff_prod
  intro j hj
  exact psi_contDiff.comp ((contDiff_const.mul (contDiff_piLp_apply 2)).sub contDiff_const)


-- @@ L138-141 verbatim
theorem normalized_contDiffAt {k : ℕ} (t : CubeSpace k) (ht : t ∈ cube k) {n : ℕ∞} :
    ContDiffAt ℝ n (normalized k) t := by
  have hG := (G_contDiff k (n := n)).contDiffAt (x := t)
  exact ((hG.norm ℝ (G_ne_zero t ht)).inv (norm_ne_zero_iff.mpr (G_ne_zero t ht))).smul hG


-- @@ L143-149 verbatim
theorem normalized_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ cube k, ‖fderiv ℝ (normalized k) t‖ ≤ C := by
  have hc : ContinuousOn (fderiv ℝ (normalized k)) (cube k) := by
    intro t ht
    exact ((normalized_contDiffAt t ht (n := 1)).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨C, hC⟩ := (cube_compact k).exists_bound_of_continuousOn hc
  exact ⟨max C 0, le_max_right _ _, fun t ht => (hC t ht).trans (le_max_left _ _)⟩


-- @@ L151-151 verbatim
end LipschitzCounterexample.SeparatingStages


-- @@ L153-153 verbatim
namespace LipschitzCounterexample.SeparatingStages

-- @@ L154-154 verbatim
open scoped ENNReal NNReal


-- @@ L156-156 verbatim
abbrev BlockLabel (n : ℕ) := Unit ⊕ (Σ k : Fin (n+1), Label (k.val+1))

-- @@ L157-157 verbatim
abbrev Block (n : ℕ) := EuclideanSpace ℝ (BlockLabel n)

-- @@ L158-158 verbatim
abbrev U := lp Block 2

-- @@ L159-159 verbatim
abbrev V := lp (fun _ : ℕ => ℝ) 2

-- @@ L160-160 verbatim
abbrev M := WithLp 2 (U × V)

-- @@ L161-161 verbatim
abbrev ScalarIndex := (Σ n : ℕ, BlockLabel n) ⊕ ℕ


-- @@ L163-163 verbatim
def enumerate : ℕ ≃ ScalarIndex := nonempty_equiv_of_countable.some


-- @@ L165-169 verbatim
def scalarCoordinate (j : ScalarIndex) : M →L[ℝ] ℝ :=
  match j with
  | .inl ⟨n,a⟩ => (PiLp.proj 2 (fun _ : BlockLabel n => ℝ) a).comp
      ((lp.evalCLM ℝ Block 2 n).comp (WithLp.fstL 2 ℝ U V))
  | .inr n => (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).comp (WithLp.sndL 2 ℝ U V)


-- @@ L171-177 verbatim
theorem scalarCoordinate_norm (j : ScalarIndex) (x : M) : ‖scalarCoordinate j x‖ ≤ ‖x‖ := by
  cases j with
  | inl j =>
    rcases j with ⟨n,a⟩
    exact (PiLp.norm_apply_le (x.fst n) a).trans
      ((lp.norm_apply_le_norm (by norm_num) x.fst n).trans (WithLp.norm_fst_le U x))
  | inr n => exact (lp.norm_apply_le_norm (by norm_num) x.snd n).trans (WithLp.norm_snd_le U x)


-- @@ L179-189 verbatim
theorem scalarCoordinate_separate {x y : M} (h : ∀ j, scalarCoordinate j x = scalarCoordinate j y) : x = y := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply lp.ext
    funext n
    apply PiLp.ext
    intro a
    exact h (.inl ⟨n,a⟩)
  · apply lp.ext
    funext n
    exact h (.inr n)


-- @@ L191-194 verbatim
theorem tanh_contDiff {n : ℕ∞} : ContDiff ℝ n Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')


-- @@ L196-202 verbatim
theorem tanh_hasDerivAt (t : ℝ) : HasDerivAt Real.tanh (1/(Real.cosh t)^2) t := by
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have he : (Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t) / Real.cosh t ^ 2 =
      1 / Real.cosh t ^ 2 := by rw [← sq, ← sq, Real.cosh_sq_sub_sinh_sq]
  rw [he] at h
  rw [show Real.tanh = Real.sinh / Real.cosh from funext Real.tanh_eq_sinh_div_cosh]
  exact h


-- @@ L204-207 verbatim
theorem tanh_deriv_norm (t : ℝ) : ‖1/(Real.cosh t)^2‖ ≤ 1 := by
  have hc := Real.one_le_cosh t
  rw [Real.norm_of_nonneg (by positivity)]
  exact (div_le_one (by positivity : 0 < Real.cosh t ^ 2)).mpr (by nlinarith)


-- @@ L209-209 verbatim
def p (j : ℕ) (x : M) : ℝ := Real.tanh (scalarCoordinate (enumerate j) x)


-- @@ L211-212 verbatim
theorem p_mem (j : ℕ) (x : M) : p j x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨(Real.neg_one_lt_tanh _).le, (Real.tanh_lt_one _).le⟩


-- @@ L214-215 verbatim
theorem p_contDiff (j : ℕ) {n : ℕ∞} : ContDiff ℝ n (p j) :=
  tanh_contDiff.comp (scalarCoordinate (enumerate j)).contDiff


-- @@ L217-221 verbatim
theorem p_separate {x y : M} (h : ∀ j, p j x = p j y) : x = y := by
  apply scalarCoordinate_separate
  intro a
  obtain ⟨j,rfl⟩ := enumerate.surjective a
  exact Real.tanh_injective (h j)


-- @@ L223-231 verbatim
theorem p_fderiv_bound (j : ℕ) (x : M) : ‖fderiv ℝ (p j) x‖ ≤ 1 := by
  have hd := (tanh_hasDerivAt (scalarCoordinate (enumerate j) x)).comp_hasFDerivAt x
    (scalarCoordinate (enumerate j)).hasFDerivAt
  rw [show p j = Real.tanh ∘ scalarCoordinate (enumerate j) from rfl, hd.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖(1 / Real.cosh (scalarCoordinate (enumerate j) x) ^ 2) • scalarCoordinate (enumerate j) z‖ ≤ 1 * ‖z‖
  rw [norm_smul]
  exact mul_le_mul (tanh_deriv_norm _) (scalarCoordinate_norm _ z) (norm_nonneg _) zero_le_one


-- @@ L233-233 verbatim
end LipschitzCounterexample.SeparatingStages


-- @@ L235-235 verbatim
namespace LipschitzCounterexample.SeparatingStages

-- @@ L236-236 verbatim
open scoped ENNReal NNReal


-- @@ L238-240 verbatim
theorem p_lipschitz (j : ℕ) : LipschitzWith 1 (p j) :=
  lipschitzWith_of_nnnorm_fderiv_le ((p_contDiff j (n := 1)).differentiable (by norm_num))
    (p_fderiv_bound j)


-- @@ L242-242 verbatim
def pVector (k : ℕ) (x : M) : CubeSpace k := WithLp.toLp 2 (fun j => p j.val x)


-- @@ L244-244 verbatim
theorem pVector_mem (k : ℕ) (x : M) : pVector k x ∈ cube k := fun j => p_mem j.val x


-- @@ L246-247 verbatim
theorem pVector_contDiff (k : ℕ) {n : ℕ∞} : ContDiff ℝ n (pVector k) :=
  (contDiff_piLp 2).2 (fun j => p_contDiff j.val)


-- @@ L249-249 verbatim
def pVectorBound (k : ℕ) : ℝ≥0 := (Fintype.card (Fin k) : ℝ≥0) ^ (1/(2 : ℝ≥0∞)).toReal


-- @@ L251-257 verbatim
theorem pVector_lipschitz (k : ℕ) : LipschitzWith (pVectorBound k) (pVector k) := by
  have hi : LipschitzWith 1 (fun x : M => fun j : Fin k => p j.val x) := by
    intro x y
    exact edist_pi_le_iff.mpr (fun j => p_lipschitz j.val x y)
  change LipschitzWith ((Fintype.card (Fin k) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal)
    (WithLp.toLp 2 ∘ (fun x : M => fun j : Fin k => p j.val x))
  simpa only [mul_one] using (PiLp.lipschitzWith_toLp 2 (fun _ : Fin k => ℝ)).comp hi


-- @@ L259-259 verbatim
section Embed

-- @@ L260-260 verbatim
variable {ι : Type uIndex} {κ : Type uOtherIndex} [Fintype ι] [Fintype κ]

-- @@ L261-261 verbatim
open Classical


-- @@ L263-273 verbatim
def coordEmbed (e : ι ↪ κ) : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ κ := by
  classical
  let b := EuclideanSpace.basisFun ι ℝ
  let f : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ κ :=
    b.toBasis.constr ℝ (fun a => EuclideanSpace.single (e a) (1 : ℝ))
  have hf : f ∘ b.toBasis = (fun a => EuclideanSpace.single (e a) (1 : ℝ)) := by
    funext a
    exact Module.Basis.constr_basis b.toBasis ℝ _ a
  apply f.isometryOfOrthonormal (v := b.toBasis) b.orthonormal
  rw [hf]
  exact (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := κ)).comp e e.injective


-- @@ L275-282 verbatim
theorem coordEmbed_apply (e : ι ↪ κ) (x : EuclideanSpace ℝ ι) :
    coordEmbed e x = ∑ a, x a • EuclideanSpace.single (e a) (1 : ℝ) := by
  classical
  change ((EuclideanSpace.basisFun ι ℝ).toBasis.constr ℝ
    (fun a => EuclideanSpace.single (e a) (1 : ℝ))) x = _
  rw [Module.Basis.constr_apply, Finsupp.sum_fintype]
  · congr 1
  · intro i; simp


-- @@ L284-290 verbatim
theorem coordEmbed_on (e : ι ↪ κ) (x : EuclideanSpace ℝ ι) (a : ι) :
    coordEmbed e x (e a) = x a := by
  classical
  rw [coordEmbed_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  simp only [e.injective.eq_iff]
  simp


-- @@ L292-299 verbatim
theorem coordEmbed_off (e : ι ↪ κ) (x : EuclideanSpace ℝ ι) (b : κ) (hb : b ∉ Set.range e) :
    coordEmbed e x b = 0 := by
  classical
  rw [coordEmbed_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a ha
  rw [ite_eq_right (fun h => hb ⟨a,h.symm⟩), mul_zero]


-- @@ L301-301 verbatim
end Embed

-- @@ L302-302 verbatim
end LipschitzCounterexample.SeparatingStages


-- @@ L304-304 verbatim
namespace LipschitzCounterexample.SeparatingStages

-- @@ L305-305 verbatim
open scoped ENNReal NNReal


-- @@ L307-309 verbatim
def stageEmbedding (n : ℕ) (k : Fin (n+1)) : Label (k.val+1) ↪ BlockLabel n where
  toFun a := .inr ⟨k,a⟩
  inj' := by intro a b h; cases h; rfl


-- @@ L311-311 verbatim
def Wzero (n : ℕ) : Block n := EuclideanSpace.single (.inl ()) (1 : ℝ)


-- @@ L313-314 verbatim
def W (n : ℕ) (k : Fin (n+1)) (x : M) : Block n :=
  coordEmbed (stageEmbedding n k) (normalized (k.val+1) (pVector (k.val+1) x))


-- @@ L316-316 verbatim
theorem norm_Wzero (n : ℕ) : ‖Wzero n‖ = 1 := by simp [Wzero]


-- @@ L318-320 verbatim
theorem norm_W (n : ℕ) (k : Fin (n+1)) (x : M) : ‖W n k x‖ = 1 := by
  rw [W, LinearIsometry.norm_map]
  exact norm_normalized _ (pVector_mem _ _)


-- @@ L322-327 verbatim
theorem W_contDiff (n : ℕ) (k : Fin (n+1)) {d : ℕ∞} : ContDiff ℝ d (W n k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hg := normalized_contDiffAt (pVector (k.val+1) x) (pVector_mem _ _) (n := d)
  exact (coordEmbed (stageEmbedding n k)).toContinuousLinearMap.contDiff.contDiffAt.comp x
    (hg.comp x (pVector_contDiff _).contDiffAt)


-- @@ L329-329 verbatim
def stageBound (k : ℕ) : ℝ := (normalized_derivative_bound k).choose * (pVectorBound k : ℝ)


-- @@ L331-332 verbatim
theorem stageBound_nonneg (k : ℕ) : 0 ≤ stageBound k :=
  mul_nonneg (normalized_derivative_bound k).choose_spec.1 (pVectorBound k).coe_nonneg


-- @@ L334-351 verbatim
theorem W_fderiv_bound (n : ℕ) (k : Fin (n+1)) (x : M) :
    ‖fderiv ℝ (W n k) x‖ ≤ stageBound (k.val+1) := by
  let E := (coordEmbed (stageEmbedding n k)).toContinuousLinearMap
  have hg := (normalized_contDiffAt (pVector (k.val+1) x) (pVector_mem _ _) (n := 1)).differentiableAt (by norm_num)
  have hp := ((pVector_contDiff (k.val+1) (n := 1)).differentiable (by norm_num)) x
  have hd := E.hasFDerivAt.comp x (hg.hasFDerivAt.comp x hp.hasFDerivAt)
  change ‖fderiv ℝ (E ∘ (normalized (k.val+1) ∘ pVector (k.val+1))) x‖ ≤ _
  rw [hd.fderiv]
  calc
    _ ≤ ‖E‖ * ‖(fderiv ℝ (normalized (k.val+1)) (pVector (k.val+1) x)).comp
        (fderiv ℝ (pVector (k.val+1)) x)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ((normalized_derivative_bound (k.val+1)).choose * (pVectorBound (k.val+1) : ℝ)) := by
      apply mul_le_mul (LinearIsometry.norm_toContinuousLinearMap_le _) _ (norm_nonneg _) zero_le_one
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul ((normalized_derivative_bound (k.val+1)).choose_spec.2 _ (pVector_mem _ _))
          (norm_fderiv_le_of_lipschitz ℝ (pVector_lipschitz _))
          (norm_nonneg _) (normalized_derivative_bound _).choose_spec.1)
    _ = _ := one_mul _


-- @@ L353-355 verbatim
@[simp] theorem W_on (n : ℕ) (k : Fin (n+1)) (x : M) (a : Label (k.val+1)) :
    W n k x (.inr ⟨k,a⟩) = normalized (k.val+1) (pVector (k.val+1) x) a :=
  coordEmbed_on (stageEmbedding n k) _ a


-- @@ L357-359 verbatim
theorem W_off (n : ℕ) (k : Fin (n+1)) (x : M) (a : BlockLabel n)
    (ha : a ∉ Set.range (stageEmbedding n k)) : W n k x a = 0 :=
  coordEmbed_off _ _ _ ha


-- @@ L361-364 verbatim
@[simp] theorem W_at_zero (n : ℕ) (k : Fin (n+1)) (x : M) : W n k x (.inl ()) = 0 := by
  apply W_off
  rintro ⟨a,h⟩
  cases h


-- @@ L366-370 verbatim
@[simp] theorem W_at_other (n : ℕ) (k l : Fin (n+1)) (hkl : k ≠ l) (x : M)
    (a : Label (l.val+1)) : W n k x (.inr ⟨l,a⟩) = 0 := by
  apply W_off
  rintro ⟨b,h⟩
  exact hkl (congrArg Sigma.fst (Sum.inr.inj h))

 
-- @@ L372-380 verbatim
theorem inner_coordEmbed_zero {ι : Type uIndex} {κ : Type uOtherIndex} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ κ)
    (hy : ∀ a, y (e a) = 0) : ⟪coordEmbed e x, y⟫_ℝ = 0 := by
  classical
  rw [coordEmbed_apply, sum_inner]
  apply Finset.sum_eq_zero
  intro a ha
  rw [real_inner_smul_left]
  simp [EuclideanSpace.inner_single_left, hy a]


-- @@ L382-384 verbatim
@[simp] theorem inner_Wzero_W (n : ℕ) (k : Fin (n+1)) (x : M) :
    ⟪Wzero n, W n k x⟫_ℝ = 0 := by
  simp [Wzero, EuclideanSpace.inner_single_left]


-- @@ L386-390 verbatim
theorem inner_W_W (n : ℕ) (k l : Fin (n+1)) (hkl : k ≠ l) (x y : M) :
    ⟪W n k x, W n l y⟫_ℝ = 0 := by
  apply inner_coordEmbed_zero
  intro a
  exact W_at_other n l k hkl.symm y a


-- @@ L392-392 verbatim
end LipschitzCounterexample.SeparatingStages


-- @@ L394-394 verbatim
end


-- @@ L396-396 verbatim
end OAI
