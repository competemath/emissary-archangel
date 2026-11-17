import TubalTensor.Modules.OrientedMatrix
import TubalTensor.RingStructure.StarRing
import TubalTensor.RingStructure.PartialOrder


-- @@ L5-12 verbatim
/-!
  TubalTensor/Modules/DotProduct.lean
  The ⋆_M-dot product on oriented matrices (Eq. (8), Theorem 20).

  For U, V ∈ K_M^m, the dot product is:
    U ·_M V := ∑ᵢ (U i)* ⋆_M (V i)
  where (U i)* is the ⋆_M-conjugation.
-/


-- @@ L14-14 verbatim
namespace TubalTensor


-- @@ L16-16 verbatim
open BigOperators


-- @@ L18-18 verbatim
variable {n : ℕ} {td : TubalData n} {m : ℕ}


-- @@ L20-23 verbatim
/-- The ⋆_M-dot product on oriented matrices:
    `dotM U V = ∑ᵢ star (U i) * V i`. -/
noncomputable def dotM (U V : OrientedMatrix m n td) : KM n td :=
  ∑ i : Fin m, star (U i) * V i


-- @@ L25-26 verbatim
theorem dotM_apply (U V : OrientedMatrix m n td) :
    dotM U V = ∑ i : Fin m, star (U i) * V i := rfl


-- @@ L28-28 verbatim
/-! ## Theorem 20, Part 1: Conjugate symmetry -/


-- @@ L30-33 verbatim
/-- **Theorem 20 (conjugate symmetry)**: `dotM U V = star (dotM V U)`. -/
theorem dotM_conj_symm (U V : OrientedMatrix m n td) :
    dotM U V = star (dotM V U) := by
  simp only [dotM_apply, star_sum, star_mul, star_star, mul_comm]


-- @@ L35-35 verbatim
/-! ## Theorem 20, Part 2: ⋆_M-linearity in the second argument -/


-- @@ L37-42 verbatim
/-- Helper: dotM is additive in the second argument. -/
theorem dotM_add_right (U V W : OrientedMatrix m n td) :
    dotM U (V + W) = dotM U V + dotM U W := by
  simp only [dotM_apply]
  simp only [show ∀ i, (V + W) i = V i + W i from fun i => rfl, mul_add,
    Finset.sum_add_distrib]


-- @@ L44-50 verbatim
/-- Helper: dotM respects scalar multiplication in the second argument. -/
theorem dotM_smul_right (U : OrientedMatrix m n td) (r : KM n td)
    (V : OrientedMatrix m n td) :
    dotM U (r • V) = r * dotM U V := by
  simp only [dotM_apply, show ∀ i, (r • V) i = r * V i from fun i => rfl]
  conv_rhs => rw [Finset.mul_sum]
  congr 1; ext i; rw [mul_left_comm]


-- @@ L52-56 verbatim
/-- **Theorem 20 (linearity)**: `dotM U (r • V + s • W) = r * dotM U V + s * dotM U W`. -/
theorem dotM_linear_right (U : OrientedMatrix m n td) (r s : KM n td)
    (V W : OrientedMatrix m n td) :
    dotM U (r • V + s • W) = r * dotM U V + s * dotM U W := by
  rw [dotM_add_right, dotM_smul_right, dotM_smul_right]


-- @@ L58-61 verbatim
/-! ## Theorem 20, Part 3: Positive definiteness

  The key identity at tube level: M(u* ⋆_M u) = conj(Mu) • Mu,
  whose j-th entry is |y_j|² where y = Mu. -/


-- @@ L63-63 verbatim
section PositiveDefiniteness


-- @@ L65-65 verbatim
open Complex Matrix


-- @@ L67-74 verbatim
/-- Key identity: M applied to star(u) ⋆_M u (at complex level) equals
    the entrywise product of conj(Mu) and Mu.
    That is, (M(u* ⋆_M u))_j = conj(y_j) * y_j = |y_j|². -/
private theorem applyM_starMC_self (td : TubalData n) (u : Fin n → ℂ) :
    td.applyM (starMC td (starConjC td u) u) =
    vecConj (td.applyM u) ∘ₕ td.applyM u := by
  unfold starMC starConjC
  rw [td.applyM_applyMinv, td.applyM_applyMinv]


-- @@ L76-88 verbatim
/-- At the real level: M applied to toComplex(star u * u) gives
    conj(M·toComplex u) ∘ₕ (M·toComplex u). -/
private theorem applyM_star_mul_self (td : TubalData n) (u : KM n td) :
    td.applyM (toComplex (KM.toFun (star u * u))) =
    vecConj (td.applyM (toComplex (KM.toFun u))) ∘ₕ
      td.applyM (toComplex (KM.toFun u)) := by
  -- star u * u at complex level = starMC (starConjC ..) ..
  have h1 : toComplex (KM.toFun (star u * u)) =
      starMC td (starConjC td (toComplex (KM.toFun u))) (toComplex (KM.toFun u)) := by
    change toComplex (starM td (starConjM td (KM.toFun u)) (KM.toFun u)) = _
    rw [starM_eq_starMC, starConjM_eq_starConjC]
  rw [h1]
  exact applyM_starMC_self td _


-- @@ L90-94 verbatim
/-- The j-th entry of conj(y) ∘ₕ y equals ↑(normSq (y j)), which is real and nonneg. -/
private theorem conj_had_self_eq_normSq {n : ℕ} (y : Fin n → ℂ) (j : Fin n) :
    (vecConj y ∘ₕ y) j = ↑(Complex.normSq (y j)) := by
  show vecConj y j * y j = _
  rw [vecConj_apply, mul_comm, Complex.mul_conj]


-- @@ L96-98 verbatim
private theorem conj_had_self_real {n : ℕ} (y : Fin n → ℂ) (j : Fin n) :
    ((vecConj y ∘ₕ y) j).im = 0 := by
  rw [conj_had_self_eq_normSq, Complex.ofReal_im]


-- @@ L100-103 verbatim
private theorem conj_had_self_nonneg {n : ℕ} (y : Fin n → ℂ) (j : Fin n) :
    0 ≤ ((vecConj y ∘ₕ y) j).re := by
  rw [conj_had_self_eq_normSq, Complex.ofReal_re]
  exact Complex.normSq_nonneg _


-- @@ L105-109 verbatim
/-- The partial order on KM unfolds to: a ≤ b iff M(b - a) real with nonneg entries. -/
private theorem KM.le_def {td : TubalData n} (a b : KM n td) :
    a ≤ b ↔ (∀ i, (td.applyM (toComplex (KM.toFun b - KM.toFun a)) i).im = 0) ∧
             (∀ i, 0 ≤ (td.applyM (toComplex (KM.toFun b - KM.toFun a)) i).re) := by
  rfl


-- @@ L111-118 verbatim
/-- 0 ≤_M (star u * u) for any u : KM n td. -/
theorem KM.star_mul_self_nonneg (u : KM n td) :
    (0 : KM n td) ≤ star u * u := by
  rw [KM.le_def]
  simp only [KM.toFun_zero, sub_zero]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [applyM_star_mul_self]; exact conj_had_self_real _ i
  · rw [applyM_star_mul_self]; exact conj_had_self_nonneg _ i


-- @@ L120-122 verbatim
/-- M applied to 0 is 0. -/
private theorem applyM_zero (td : TubalData n) :
    td.applyM (0 : Fin n → ℂ) = 0 := Matrix.mulVec_zero _


-- @@ L124-127 verbatim
/-- Reducing M(toComplex(toFun(0))) = 0. -/
private theorem applyM_toComplex_KM_zero (td : TubalData n) :
    td.applyM (toComplex (KM.toFun (0 : KM n td))) = 0 := by
  rw [KM.toFun_zero, toComplex_zero]; exact applyM_zero td


-- @@ L129-142 verbatim
/-- star u * u = 0 implies u = 0, at the KM level. -/
theorem KM.star_mul_self_eq_zero {u : KM n td} (h : star u * u = 0) : u = 0 := by
  have hMsq : vecConj (td.applyM (toComplex (KM.toFun u))) ∘ₕ
      td.applyM (toComplex (KM.toFun u)) = 0 := by
    have harg : td.applyM (toComplex (KM.toFun (star u * u))) = 0 := by
      rw [h]; exact applyM_toComplex_KM_zero td
    rwa [applyM_star_mul_self] at harg
  have hMu : td.applyM (toComplex (KM.toFun u)) = 0 := by
    ext j
    have hj := congr_fun hMsq j
    rw [conj_had_self_eq_normSq, Pi.zero_apply, Complex.ofReal_eq_zero] at hj
    exact Complex.normSq_eq_zero.mp hj
  exact KM.ext (fun i => congr_fun (toComplex_injective
    (td.applyM_injective (hMu.trans (applyM_zero td).symm))) i)


-- @@ L144-156 verbatim
/-- The composite M ∘ toComplex applied to a KM sum distributes. -/
private theorem applyM_toComplex_sum (td : TubalData n) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → KM n td) :
    td.applyM (toComplex (KM.toFun (∑ i ∈ s, f i))) =
    ∑ i ∈ s, td.applyM (toComplex (KM.toFun (f i))) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact applyM_toComplex_KM_zero td
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,
      show KM.toFun (f a + ∑ x ∈ s, f x) = KM.toFun (f a) + KM.toFun (∑ x ∈ s, f x) from rfl,
      toComplex_add, td.applyM_add, ih, Finset.sum_insert ha]


-- @@ L158-172 verbatim
/-- **Theorem 20 (positive definiteness, part a)**: `0 ≤_M dotM U U`. -/
theorem dotM_nonneg (U : OrientedMatrix m n td) :
    (0 : KM n td) ≤ dotM U U := by
  rw [dotM_apply, KM.le_def]
  simp only [KM.toFun_zero, sub_zero]
  rw [applyM_toComplex_sum]
  refine ⟨fun j => ?_, fun j => ?_⟩
  · simp only [Finset.sum_apply]
    rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [applyM_star_mul_self]; exact conj_had_self_real _ j
  · simp only [Finset.sum_apply]
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => by
      rw [applyM_star_mul_self]; exact conj_had_self_nonneg _ j


-- @@ L174-217 verbatim
/-- **Theorem 20 (positive definiteness, part b)**: `dotM U U = 0 ↔ U = 0`. -/
theorem dotM_eq_zero_iff (U : OrientedMatrix m n td) :
    dotM U U = 0 ↔ U = 0 := by
  constructor
  · intro h
    rw [dotM_apply] at h
    -- ∑ star(U i) * U i = 0. Apply M ∘ toComplex.
    have h0 : ∀ j, (∑ i : Fin m,
        td.applyM (toComplex (KM.toFun (star (U i) * U i)))) j = 0 := by
      intro j
      have hval : td.applyM (toComplex (KM.toFun (∑ i, star (U i) * U i))) = 0 := by
        rw [h]; exact applyM_toComplex_KM_zero td
      rw [applyM_toComplex_sum] at hval
      exact congr_fun hval j
    -- Each term: M(star(U i) * U i)_j = normSq((MU_i)_j) ≥ 0
    -- Sum of nonneg = 0 ⟹ each = 0
    funext i
    apply KM.star_mul_self_eq_zero
    -- Need star(U i) * U i = 0, i.e., M(star(U i) * U i) = 0
    have hMi : td.applyM (toComplex (KM.toFun (star (U i) * U i))) = 0 := by
      ext j; rw [Pi.zero_apply, applyM_star_mul_self, conj_had_self_eq_normSq]
      -- Sum: ∑_k normSq((MU_k)_j) = 0
      have hsum : ∑ k : Fin m,
          (Complex.normSq (td.applyM (toComplex (KM.toFun (U k))) j) : ℂ) = 0 := by
        have := h0 j
        simp only [Finset.sum_apply] at this
        convert this using 1; congr 1; ext k
        rw [applyM_star_mul_self, conj_had_self_eq_normSq]
      -- Extract real part: ∑ normSq = 0 as real numbers
      have hre : ∑ k : Fin m,
          Complex.normSq (td.applyM (toComplex (KM.toFun (U k))) j) = 0 := by
        have hre_cx := congr_arg Complex.re hsum
        simp only [Complex.zero_re] at hre_cx
        exact_mod_cast hre_cx
      have h_term := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
          Complex.normSq_nonneg _)).mp hre i (Finset.mem_univ _)
      simp only [h_term, Complex.ofReal_zero]
    exact KM.ext (fun k => congr_fun (toComplex_injective
      (td.applyM_injective (hMi.trans (applyM_zero td).symm))) k)
  · intro h; rw [h, dotM_apply]
    apply Finset.sum_eq_zero
    intro i _
    show star ((0 : OrientedMatrix m n td) i) * (0 : OrientedMatrix m n td) i = 0
    simp [show (0 : OrientedMatrix m n td) i = (0 : KM n td) from rfl]


-- @@ L219-219 verbatim
end PositiveDefiniteness


-- @@ L221-229 verbatim
/-- **Theorem 20 (bundled)**: The ⋆_M-dot product satisfies conjugate symmetry,
    ⋆_M-linearity in the second argument, nonnegativity, and definiteness. -/
theorem dotM_properties (U V : OrientedMatrix m n td) (r s : KM n td)
    (W X : OrientedMatrix m n td) :
    dotM U V = star (dotM V U) ∧
    dotM U (r • W + s • X) = r * dotM U W + s * dotM U X ∧
    (0 : KM n td) ≤ dotM U U ∧
    (dotM U U = 0 ↔ U = 0) :=
  ⟨dotM_conj_symm U V, dotM_linear_right U r s W X, dotM_nonneg U, dotM_eq_zero_iff U⟩


-- @@ L231-231 verbatim
end TubalTensor
