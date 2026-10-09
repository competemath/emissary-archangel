import OAI.Analysis.NumericalRange.FourierExtension


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace CompleteCrouzeix


-- @@ L9-9 verbatim
universe u_48 u_49 u_50 u_51 u_52 u_53


-- @@ L11-11 verbatim
open Set Filter Metric Complex

-- @@ L12-12 verbatim
open scoped Topology ComplexConjugate

-- @@ L13-13 verbatim
open MeasureTheory Set Complex

-- @@ L14-14 verbatim
open scoped Topology Real

-- @@ L15-15 verbatim
open MeasureTheory Set Metric Complex Filter

-- @@ L16-16 verbatim
open scoped Topology

-- @@ L17-17 verbatim
open MeasureTheory Set Filter

-- @@ L18-18 verbatim
open scoped ENNReal NNReal InnerProductSpace

-- @@ L19-19 verbatim
open scoped ComplexConjugate InnerProductSpace

-- @@ L20-20 verbatim
open Set Metric Filter Complex

-- @@ L21-21 verbatim
open scoped Topology

-- @@ L22-22 verbatim
open MeasureTheory Set Complex

-- @@ L23-23 verbatim
open scoped Topology

-- @@ L24-24 verbatim
open MeasureTheory Set Complex Metric

-- @@ L25-25 verbatim
open scoped Topology

-- @@ L26-26 verbatim
open Set Filter Metric Complex

-- @@ L27-27 verbatim
open scoped Topology


-- @@ L29-29 verbatim
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator


-- @@ L31-31 verbatim
section


-- @@ L33-33 verbatim
variable {m : Type u_48} [Fintype m] [instDecidableEqM : DecidableEq m]


-- @@ L35-35 verbatim
def hsSq (A : Matrix m m ℂ) : ℝ := (Matrix.trace (Aᴴ * A)).re


-- @@ L37-43 verbatim
theorem trace_mul_nonneg {A B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have h := (hB.mul_mul_conjTranspose_same C).trace_nonneg
  have hr := (Complex.nonneg_iff.mp h).1
  rw [Matrix.trace_mul_cycle] at hr
  simpa only [Matrix.star_eq_conjTranspose] using hr


-- @@ L45-48 verbatim
private theorem trace_blocks
    {m : Type u_48} [Fintype m] [DecidableEq m] (a b c d : Matrix m m ℂ) :
    (Matrix.fromBlocks a b c d).trace = a.trace + d.trace := by
  simp [Matrix.trace]


-- @@ L50-77 verbatim
theorem block_density_hs {p q r : Matrix m m ℂ}
    (h : (Matrix.fromBlocks p rᴴ r q).PosSemidef) :
    2 * hsSq r ≤ hsSq p + hsSq q := by
  let J : Matrix (m ⊕ m) (m ⊕ m) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  let Δ := Matrix.fromBlocks p rᴴ r q
  have hp : p.IsHermitian := by
    have hh := h.isHermitian
    rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_inj] at hh
    exact hh.1
  have hq : q.IsHermitian := by
    have hh := h.isHermitian
    rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_inj] at hh
    exact hh.2.2.2
  have hJ : Jᴴ = J := by simp [J, Matrix.fromBlocks_conjTranspose]
  have hΔ : Δ.PosSemidef := h
  have hj := hΔ.mul_mul_conjTranspose_same J
  rw [hJ] at hj
  have ht := trace_mul_nonneg hΔ hj
  simp only [Δ, J, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul,
    add_zero, zero_add, neg_neg, trace_blocks, Matrix.trace_add,
    Complex.add_re, Matrix.trace_neg, Complex.neg_re] at ht
  unfold hsSq
  rw [hp, hq]
  rw [Matrix.trace_mul_comm r rᴴ] at ht
  linarith


-- @@ L79-79 verbatim
abbrev HSMatrix (m : Type u_49) [Fintype m] := EuclideanSpace ℂ (m × m)


-- @@ L81-81 verbatim
def toHS (A : Matrix m m ℂ) : HSMatrix m := WithLp.toLp 2 (fun ij => A ij.1 ij.2)

-- @@ L82-82 verbatim
def fromHS (A : HSMatrix m) : Matrix m m ℂ := fun i j => A (i,j)


-- @@ L84-85 verbatim
@[simp] theorem fromHS_toHS
    {m : Type u_48} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) : fromHS (toHS A) = A := rfl

-- @@ L86-87 verbatim
@[simp] theorem toHS_fromHS
    {m : Type u_48} [Fintype m] [DecidableEq m] (A : HSMatrix m) : toHS (fromHS A) = A := rfl


-- @@ L89-101 verbatim
lemma hsSq_eq_sum
    {m : Type u_48} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) :
    hsSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [hsSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.sq_norm]
  rfl


-- @@ L103-105 verbatim
lemma norm_toHS_sq (A : Matrix m m ℂ) : ‖toHS A‖ ^ 2 = hsSq A := by
  rw [hsSq_eq_sum, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl


-- @@ L107-110 verbatim
lemma block_density_norm {p q r : HSMatrix m}
    (h : (Matrix.fromBlocks (fromHS p) (fromHS r)ᴴ (fromHS r) (fromHS q)).PosSemidef) :
    2 * ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  simpa only [← norm_toHS_sq, toHS_fromHS] using block_density_hs h


-- @@ L112-124 verbatim
def hsStar : HSMatrix m ≃ₗᵢ⋆[ℂ] HSMatrix m where
  toFun A := toHS (fromHS A)ᴴ
  invFun A := toHS (fromHS A)ᴴ
  left_inv A := by simp
  right_inv A := by simp
  map_add' A B := by apply PiLp.ext; intro ij; simp [toHS, fromHS, Matrix.conjTranspose_apply]
  map_smul' c A := by apply PiLp.ext; intro ij; simp [toHS, fromHS, Matrix.conjTranspose_apply]
  norm_map' A := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖toHS (fromHS A)ᴴ‖ ^ 2 = ‖A‖ ^ 2
    rw [norm_toHS_sq, hsSq_eq_sum, ← toHS_fromHS A, norm_toHS_sq, hsSq_eq_sum]
    simp only [Matrix.conjTranspose_apply, norm_star, fromHS_toHS]
    rw [Finset.sum_comm]


-- @@ L126-126 verbatim
@[simp] lemma hsStar_apply (A : HSMatrix m) : hsStar A = toHS (fromHS A)ᴴ := rfl


-- @@ L128-129 verbatim
lemma hsStar_involutive : Function.Involutive (hsStar : HSMatrix m → HSMatrix m) := by
  intro A; simp


-- @@ L131-148 verbatim
lemma hs_left_contraction {A : Matrix m m ℂ} (hA : ‖A‖ ≤ 1) (B : Matrix m m ℂ) :
    ‖toHS (A * B)‖ ≤ ‖toHS B‖ := by
  have hnorm : ‖Aᴴ * A‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]
    nlinarith [norm_nonneg A]
  have hle : Aᴴ * A ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg (Aᴴ * A)
      (Matrix.posSemidef_conjTranspose_mul_self A).nonneg).mp hnorm
  have hd : (1 - Aᴴ * A).PosSemidef := hle
  have ht := (hd.conjTranspose_mul_mul_same B).trace_nonneg
  have hr := (Complex.nonneg_iff.mp ht).1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at hr
  have hsq : hsSq (A * B) ≤ hsSq B := by
    unfold hsSq
    rw [Matrix.conjTranspose_mul]
    simpa only [Matrix.mul_assoc] using sub_nonneg.mp hr
  rw [← norm_toHS_sq, ← norm_toHS_sq] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq


-- @@ L150-156 verbatim
lemma hs_right_contraction {A : Matrix m m ℂ} (hA : ‖A‖ ≤ 1) (B : Matrix m m ℂ) :
    ‖toHS (B * A)‖ ≤ ‖toHS B‖ := by
  have h := hs_left_contraction (A := Aᴴ) (by simpa only [Matrix.l2_opNorm_conjTranspose] using hA) Bᴴ
  have hnorm (C : Matrix m m ℂ) : ‖toHS Cᴴ‖ = ‖toHS C‖ := by
    simpa only [hsStar_apply, fromHS_toHS] using hsStar.norm_map (toHS C)
  rw [← Matrix.conjTranspose_mul, hnorm, hnorm] at h
  exact h


-- @@ L158-158 verbatim
open MeasureTheory

-- @@ L159-159 verbatim
variable {α : Type u_50} [MeasurableSpace α] {μ : Measure α}


-- @@ L161-166 verbatim
lemma l2_norm_sq
    {m : Type u_48} [Fintype m] [DecidableEq m] {α : Type u_50} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} (u : Lp (HSMatrix m) 2 μ) :
    ‖u‖ ^ 2 = ∫ t, ‖u t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]


-- @@ L168-172 verbatim
lemma l2_integrable_norm_sq
    {m : Type u_48} [Fintype m] [DecidableEq m] {α : Type u_50} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} (u : Lp (HSMatrix m) 2 μ) :
    Integrable (fun t => ‖u t‖ ^ 2) μ := by
  simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u


-- @@ L174-175 verbatim
def l2StarL : Lp (HSMatrix m) 2 μ →L⋆[ℂ] Lp (HSMatrix m) 2 μ :=
  hsStar.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ


-- @@ L177-179 verbatim
lemma l2StarL_ae (u : Lp (HSMatrix m) 2 μ) :
    l2StarL u =ᵐ[μ] fun t => hsStar (u t) :=
  (hsStar (m := m)).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL u


-- @@ L181-185 verbatim
lemma l2StarL_involutive : Function.Involutive (l2StarL : Lp (HSMatrix m) 2 μ → _) := by
  intro u
  apply Lp.ext
  filter_upwards [l2StarL_ae (l2StarL u), l2StarL_ae u] with t ht hu
  rw [ht, hu, hsStar_involutive]


-- @@ L187-192 verbatim
lemma l2StarL_norm (u : Lp (HSMatrix m) 2 μ) : ‖l2StarL u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq, l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [l2StarL_ae u] with t ht
  rw [ht, hsStar.norm_map]


-- @@ L194-201 verbatim
def l2Star : Lp (HSMatrix m) 2 μ ≃ₗᵢ⋆[ℂ] Lp (HSMatrix m) 2 μ where
  toFun := l2StarL
  invFun := l2StarL
  left_inv := l2StarL_involutive
  right_inv := l2StarL_involutive
  map_add' := map_add l2StarL
  map_smul' := l2StarL.map_smulₛₗ
  norm_map' := l2StarL_norm


-- @@ L203-203 verbatim
@[simp] lemma l2Star_apply (u : Lp (HSMatrix m) 2 μ) : l2Star u = l2StarL u := rfl


-- @@ L205-210 verbatim
lemma hermitian_l2Star {u : Lp (HSMatrix m) 2 μ}
    (hu : ∀ᵐ t ∂μ, (fromHS (u t)).IsHermitian) : l2Star u = u := by
  apply Lp.ext
  filter_upwards [l2StarL_ae u, hu] with t ht hh
  change l2StarL u t = u t
  rw [ht, hsStar_apply, hh, toHS_fromHS]


-- @@ L212-223 verbatim
theorem block_density_l2 {p q r : Lp (HSMatrix m) 2 μ}
    (h : ∀ᵐ t ∂μ,
      (Matrix.fromBlocks (fromHS (p t)) (fromHS (r t))ᴴ
        (fromHS (r t)) (fromHS (q t))).PosSemidef) :
    2 * ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  simp only [l2_norm_sq]
  rw [← integral_const_mul, ← integral_add (l2_integrable_norm_sq p)
    (l2_integrable_norm_sq q)]
  apply integral_mono_ae ((l2_integrable_norm_sq r).const_mul 2)
    ((l2_integrable_norm_sq p).add (l2_integrable_norm_sq q))
  filter_upwards [h] with t ht
  exact block_density_norm ht


-- @@ L225-225 verbatim
end


-- @@ L227-227 verbatim
section

-- @@ L228-228 verbatim
open scoped InnerProductSpace

-- @@ L229-229 verbatim
variable {m : Type u_51} [Fintype m] [instDecidableEqM : DecidableEq m]


-- @@ L231-239 verbatim
def hsLeft (A : Matrix m m ℂ) : HSMatrix m →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun B := toHS (A * fromHS B)
    map_add' B C := by
      apply PiLp.ext; intro ij
      simp [toHS, fromHS, Matrix.mul_apply, Finset.sum_add_distrib, mul_add]
    map_smul' c B := by
      apply PiLp.ext; intro ij
      simp [toHS, fromHS, Matrix.mul_apply, Finset.mul_sum, mul_left_comm] }


-- @@ L241-249 verbatim
def hsRight (A : Matrix m m ℂ) : HSMatrix m →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun B := toHS (fromHS B * A)
    map_add' B C := by
      apply PiLp.ext; intro ij
      simp [toHS, fromHS, Matrix.mul_apply, Finset.sum_add_distrib, add_mul]
    map_smul' c B := by
      apply PiLp.ext; intro ij
      simp [toHS, fromHS, Matrix.mul_apply, Finset.mul_sum, mul_assoc] }


-- @@ L251-253 verbatim
@[simp] lemma hsLeft_apply
    {m : Type u_51} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (B : HSMatrix m) :
    hsLeft A B = toHS (A * fromHS B) := rfl

-- @@ L254-256 verbatim
@[simp] lemma hsRight_apply
    {m : Type u_51} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (B : HSMatrix m) :
    hsRight A B = toHS (fromHS B * A) := rfl


-- @@ L258-261 verbatim
lemma hsLeft_norm {A : Matrix m m ℂ} (h : ‖A‖ ≤ 1) : ‖hsLeft A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  simpa using hs_left_contraction h (fromHS B)

-- @@ L262-265 verbatim
lemma hsRight_norm {A : Matrix m m ℂ} (h : ‖A‖ ≤ 1) : ‖hsRight A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  simpa using hs_right_contraction h (fromHS B)


-- @@ L267-278 verbatim
lemma hs_inner
    {m : Type u_51} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ) :
    inner ℂ (toHS A) (toHS B) = Matrix.trace (Aᴴ * B) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    toHS]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _


-- @@ L280-289 verbatim
lemma hsLeft_adjoint (A : Matrix m m ℂ) : (hsLeft A).adjoint = hsLeft Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (toHS (Aᴴ * fromHS x)) y =
    inner ℂ x (toHS (A * fromHS y))
  conv_lhs => rhs; rw [← toHS_fromHS y]
  conv_rhs => lhs; rw [← toHS_fromHS x]
  rw [hs_inner, hs_inner, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]


-- @@ L291-301 verbatim
lemma hsRight_adjoint (A : Matrix m m ℂ) : (hsRight A).adjoint = hsRight Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (toHS (fromHS x * Aᴴ)) y =
    inner ℂ x (toHS (fromHS y * A))
  conv_lhs => rhs; rw [← toHS_fromHS y]
  conv_rhs => lhs; rw [← toHS_fromHS x]
  rw [hs_inner, hs_inner, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [Matrix.mul_assoc]


-- @@ L303-311 verbatim
def hsLeftL : Matrix m m ℂ →L[ℂ] HSMatrix m →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun := hsLeft
    map_add' A B := by
      ext C ij
      simp [hsLeft, toHS, fromHS, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
    map_smul' c A := by
      ext C ij
      simp [hsLeft, toHS, fromHS, Matrix.mul_apply, Finset.mul_sum, mul_assoc] }


-- @@ L313-321 verbatim
def hsRightL : Matrix m m ℂ →L[ℂ] HSMatrix m →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun := hsRight
    map_add' A B := by
      ext C ij
      simp [hsRight, toHS, fromHS, Matrix.mul_apply, mul_add, Finset.sum_add_distrib]
    map_smul' c A := by
      ext C ij
      simp [hsRight, toHS, fromHS, Matrix.mul_apply, Finset.mul_sum, mul_left_comm] }


-- @@ L323-323 verbatim
end


-- @@ L325-325 verbatim
open MeasureTheory

-- @@ L326-327 verbatim
variable {α : Type u_52} {E : Type u_53} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

-- @@ L328-329 verbatim
variable (B : α → E →L[ℂ] E) (hB : AEStronglyMeasurable B μ)
  (hBn : ∀ᵐ t ∂μ, ‖B t‖ ≤ 1)


-- @@ L331-337 verbatim
include hB hBn in
lemma pointwise_memLp (u : Lp E 2 μ) : MemLp (fun t => B t (u t)) 2 μ := by
  apply (Lp.memLp u).of_le
  · exact (ContinuousLinearMap.id ℂ (E →L[ℂ] E)).aestronglyMeasurable_comp₂
      hB (Lp.aestronglyMeasurable u)
  · filter_upwards [hBn] with t ht
    simpa using (B t).le_of_opNorm_le ht (u t)


-- @@ L339-340 verbatim
def pointwiseL2 (u : Lp E 2 μ) : Lp E 2 μ :=
  (pointwise_memLp B hB hBn u).toLp _


-- @@ L342-344 verbatim
lemma pointwiseL2_ae (u : Lp E 2 μ) :
    pointwiseL2 B hB hBn u =ᵐ[μ] fun t => B t (u t) :=
  MemLp.coeFn_toLp _


-- @@ L346-350 verbatim
lemma pointwiseL2_norm (u : Lp E 2 μ) : ‖pointwiseL2 B hB hBn u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [pointwiseL2_ae B hB hBn u, hBn] with t hu ht
  rw [hu]
  simpa using (B t).le_of_opNorm_le ht (u t)


-- @@ L352-373 verbatim
def pointwiseL2L : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
  { toFun := pointwiseL2 B hB hBn
    map_add' u v := by
      apply Lp.ext
      filter_upwards [pointwiseL2_ae B hB hBn (u + v),
        pointwiseL2_ae B hB hBn u, pointwiseL2_ae B hB hBn v,
        Lp.coeFn_add u v, Lp.coeFn_add (pointwiseL2 B hB hBn u) (pointwiseL2 B hB hBn v)]
        with t huv hu hv hadd hout
      rw [huv, hout, hadd]
      simp only [Pi.add_apply]
      rw [hu, hv, map_add]
    map_smul' c u := by
      apply Lp.ext
      filter_upwards [pointwiseL2_ae B hB hBn (c • u), pointwiseL2_ae B hB hBn u,
        Lp.coeFn_smul c u, Lp.coeFn_smul c (pointwiseL2 B hB hBn u)] with t hcu hu hin hout
      change pointwiseL2 B hB hBn (c • u) t = (c • pointwiseL2 B hB hBn u) t
      rw [hcu, hout, hin]
      simp only [Pi.smul_apply]
      rw [hu]
      exact (B t).map_smul c (u t) }
    1 (by intro u; simpa using pointwiseL2_norm B hB hBn u)


-- @@ L375-378 verbatim
lemma pointwiseL2L_norm : ‖pointwiseL2L B hB hBn‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa [pointwiseL2L] using pointwiseL2_norm B hB hBn u


-- @@ L380-392 verbatim
lemma pointwiseL2L_adjoint (C : α → E →L[ℂ] E) (hC : AEStronglyMeasurable C μ)
    (hCn : ∀ᵐ t ∂μ, ‖C t‖ ≤ 1) (hBC : ∀ᵐ t ∂μ, (B t).adjoint = C t) :
    (pointwiseL2L B hB hBn).adjoint = pointwiseL2L C hC hCn := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pointwiseL2_ae C hC hCn u, pointwiseL2_ae B hB hBn v, hBC]
    with t hu hv ht
  change inner ℂ (pointwiseL2 C hC hCn u t) (v t) =
    inner ℂ (u t) (pointwiseL2 B hB hBn v t)
  rw [hu, hv, ← ht, ContinuousLinearMap.adjoint_inner_left]



-- @@ L395-395 verbatim
end CompleteCrouzeix


-- @@ L397-397 verbatim
end


-- @@ L399-399 verbatim
end OAI
