import OAI.Analysis.ModularRecovery.Mean


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Exact noncommutative fourth-moment pairings and overlap subtraction. -/


-- @@ L7-7 verbatim
universe u uA uB uι


-- @@ L9-9 verbatim
open Filter MeasureTheory Set

-- @@ L10-10 verbatim
open scoped Topology ComplexConjugate


-- @@ L12-12 verbatim
noncomputable section

-- @@ L13-13 verbatim
open Set Filter

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
namespace BoundedRecovery

-- @@ L16-16 verbatim
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- @@ L17-17 verbatim
namespace StandardModularData

-- @@ L18-18 verbatim
variable {ι : Type uι} [Fintype ι]


-- @@ L20-23 verbatim
lemma modularAverage_add_time (S : StandardModularData H) (p t : ι → ℝ)
    (r : ℝ) (a : H →L[ℂ] H) :
    S.modularAverage p (fun i => r + t i) a = S.sigma r (S.modularAverage p t a) := by
  simp only [modularAverage, S.sigma_sum, S.sigma_real_smul, S.sigma_add_time]


-- @@ L25-29 verbatim
lemma average_square_state_translate (S : StandardModularData H) (p t : ι → ℝ)
    (r : ℝ) (a : H →L[ℂ] H) :
    S.state ((S.modularAverage p (fun i => r+t i) a)^2) =
      S.state ((S.modularAverage p t a)^2) := by
  rw [S.modularAverage_add_time, pow_two, ← S.sigma_mul, S.state_sigma, ← pow_two]


-- @@ L31-38 verbatim
lemma average_sandwich_state_translate (S : StandardModularData H) (p t : ι → ℝ)
    (r : ℝ) (y : H →L[ℂ] H) :
    (∑ i, p i * (S.state (star (S.sigma (r+t i) y) *
      S.modularAverage p (fun j => r+t j) (y*star y) * S.sigma (r+t i) y)).re) =
    (∑ i, p i * (S.state (star (S.sigma (t i) y) *
      S.modularAverage p t (y*star y) * S.sigma (t i) y)).re) := by
  simp only [S.modularAverage_add_time, S.sigma_add_time, ← S.sigma_star,
    ← S.sigma_mul, S.state_sigma]


-- @@ L40-55 verbatim
lemma exists_translate_defect (S : StandardModularData H) (omega : Ultrafilter ℕ)
    (hω : (omega : Filter ℕ) ≤ atTop) (T : H →L[ℂ] H) (y : H →L[ℂ] H)
    (p t : ι → ℝ) (hsum : (∑ i, p i) = 1) {gamma : ℝ}
    (hg : gamma < fixedMean omega (S.D.orbitDefect T (y S.xi))) :
    ∃ r : ℝ, gamma < ∑ i, p i * ‖T (S.sigma (r+t i) y S.xi)‖ ^ 2 := by
  let f := S.D.orbitDefect T (y S.xi)
  let F : BoundedContinuousFunction ℝ ℝ := ∑ i, p i • translateBCF f (t i)
  have hmean : fixedMean omega F = fixedMean omega f := by
    change meanCLM omega (∑ i, p i • translateBCF f (t i)) = fixedMean omega f
    rw [map_sum]
    simp only [map_smul, meanCLM_apply, fixedMean_translate omega hω]
    rw [← Finset.sum_smul, hsum, one_smul]
  obtain ⟨r,hr⟩ := exists_lt_of_lt_fixedMean omega hω F (by rwa [hmean])
  refine ⟨r, ?_⟩
  simpa only [F, BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.smul_apply,
    translateBCF_apply, f, RealSpectralCalculus.orbitDefect_apply, S.sigma_apply_xi, smul_eq_mul] using hr


-- @@ L57-72 verbatim
lemma exists_finite_defect_moment_average (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) (omega : Ultrafilter ℕ)
    (hω : (omega : Filter ℕ) ≤ atTop) (T : H →L[ℂ] H) {y : H →L[ℂ] H}
    (hy : y ∈ S.M) {gamma : ℝ}
    (hg : gamma < fixedMean omega (S.D.orbitDefect T (y S.xi))) :
    ∃ (n : ℕ) (p t : Fin n → ℝ), (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      gamma ≤ ∑ i, p i * ‖T (S.sigma (t i) y S.xi)‖ ^ 2 ∧
      (S.state ((S.modularAverage p t (star y * y)) ^ 2)).re +
      (∑ i, p i * (S.state (star (S.sigma (t i) y) *
        S.modularAverage p t (y * star y) * S.sigma (t i) y)).re) ≤
        (‖y S.xi‖ ^ 2 + 1) ^ 2 + ‖y S.xi‖ ^ 2 * ‖star y S.xi‖ ^ 2 + 1 := by
  obtain ⟨n,p,t,hp,hsum,hA,hB⟩ := S.exists_finite_moment_average hscalar hy
  obtain ⟨r,hr⟩ := S.exists_translate_defect omega hω T y p t hsum hg
  refine ⟨n,p,(fun i => r+t i),hp,hsum,hr.le,?_⟩
  rw [S.average_square_state_translate, S.average_sandwich_state_translate]
  linarith


-- @@ L74-74 verbatim
end StandardModularData

-- @@ L75-75 verbatim
end BoundedRecovery


-- @@ L77-77 verbatim
noncomputable section


-- @@ L79-79 verbatim
namespace BoundedRecovery


-- @@ L81-81 verbatim
section AlgebraicPhases


-- @@ L83-83 verbatim
variable {A : Type uA} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]


-- @@ L85-85 verbatim
def phase (i : Fin 4) : ℂ := ![1, -1, Complex.I, -Complex.I] i


-- @@ L87-87 verbatim
def phaseAverage (f : Fin 4 → A) : A := (1 / 4 : ℂ) • ∑ i, f i


-- @@ L89-98 verbatim
lemma phase_quadratic_step (x y b : A) :
    phaseAverage (fun i => star (x + phase i • y) * b * (x + phase i • y)) =
      star x * b * x + star y * b * y := by
  simp only [phaseAverage, Fin.sum_univ_succ, phase, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    one_smul, neg_smul, star_add, star_smul,
    Complex.star_def, map_neg, map_one, Complex.conj_I,
    mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
  match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]


-- @@ L100-112 verbatim
lemma phase_fourth_step (x y : A) :
    phaseAverage (fun i => (star (x + phase i • y) * (x + phase i • y)) ^ 2) =
      (star x * x) ^ 2 + (star y * y) ^ 2 +
        star x * x * (star y * y) + star y * y * (star x * x) +
        star x * (y * star y) * x + star y * (x * star x) * y := by
  simp only [phaseAverage, Fin.sum_univ_succ, phase, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    one_smul, neg_smul, star_add, star_smul,
    Complex.star_def, map_neg, map_one, Complex.conj_I, pow_two,
    mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
    mul_assoc]
  match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]


-- @@ L114-122 verbatim
lemma phase_reverse_quadratic_step (x y b : A) :
    phaseAverage (fun i => (x + phase i • y) * b * star (x + phase i • y)) =
      x * b * star x + y * b * star y := by
  simp only [phaseAverage, Fin.sum_univ_succ, phase, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_smul, neg_smul, star_add,
    star_smul, Complex.star_def, map_neg, map_one, Complex.conj_I,
    mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
  match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]


-- @@ L124-124 verbatim
end AlgebraicPhases


-- @@ L126-126 verbatim
section PhaseExpectation

-- @@ L127-127 verbatim
variable {A : Type uA} [AddCommMonoid A] [Module ℂ A]


-- @@ L129-132 verbatim
def phaseExpectation : (n : ℕ) → ((Fin n → Fin 4) → A) → A
  | 0, f => f Fin.elim0
  | n + 1, f => phaseExpectation n (fun e =>
      (1 / 4 : ℂ) • ∑ i : Fin 4, f (Fin.cons i e))


-- @@ L134-140 verbatim
lemma phaseExpectation_add (n : ℕ) (f g : (Fin n → Fin 4) → A) :
    phaseExpectation n (fun e => f e + g e) = phaseExpectation n f + phaseExpectation n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, Finset.sum_add_distrib, smul_add]
    exact ih _ _


-- @@ L142-148 verbatim
lemma phaseExpectation_smul (n : ℕ) (f : (Fin n → Fin 4) → A) (c : ℂ) :
    phaseExpectation n (fun e => c • f e) = c • phaseExpectation n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, ← Finset.smul_sum, smul_comm (1 / 4 : ℂ) c]
    exact ih _


-- @@ L150-157 verbatim
lemma phaseExpectation_const (n : ℕ) (a : A) : phaseExpectation n (fun _ => a) = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : (1 / 4 : ℂ) • ∑ _i : Fin 4, a = a := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      module
    simp only [phaseExpectation, h, ih]


-- @@ L159-166 verbatim
lemma phaseExpectation_map {B : Type uB} [AddCommMonoid B] [Module ℂ B]
    (L : A →ₗ[ℂ] B) (n : ℕ) (f : (Fin n → Fin 4) → A) :
    phaseExpectation n (fun e => L (f e)) = L (phaseExpectation n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, ← map_sum, ← map_smul]
    exact ih _


-- @@ L168-168 verbatim
end PhaseExpectation


-- @@ L170-170 verbatim
section RingExpectation

-- @@ L171-171 verbatim
variable {A : Type uA} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]


-- @@ L173-180 verbatim
omit [StarRing A] [StarModule ℂ A] in
lemma phaseExpectation_sub (n : ℕ) (f g : (Fin n → Fin 4) → A) :
    phaseExpectation n (fun e => f e - g e) = phaseExpectation n f - phaseExpectation n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, Finset.sum_sub_distrib, smul_sub]
    exact ih _ _


-- @@ L182-189 verbatim
omit [StarRing A] [StarModule ℂ A] in
lemma phaseExpectation_mul_left (n : ℕ) (f : (Fin n → Fin 4) → A) (a : A) :
    phaseExpectation n (fun e => a * f e) = a * phaseExpectation n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, ← Finset.mul_sum, ← mul_smul_comm]
    exact ih _


-- @@ L191-198 verbatim
omit [StarRing A] [StarModule ℂ A] in
lemma phaseExpectation_mul_right (n : ℕ) (f : (Fin n → Fin 4) → A) (a : A) :
    phaseExpectation n (fun e => f e * a) = phaseExpectation n f * a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseExpectation, ← Finset.sum_mul, ← smul_mul_assoc]
    exact ih _


-- @@ L200-201 verbatim
def phaseSum {n : ℕ} (a : Fin n → A) (e : Fin n → Fin 4) : A :=
  ∑ i, phase (e i) • a i


-- @@ L203-206 verbatim
omit [StarRing A] [StarModule ℂ A] in
lemma phaseSum_succ {n : ℕ} (a : Fin (n + 1) → A) (i : Fin 4) (e : Fin n → Fin 4) :
    phaseSum a (Fin.cons i e) = phaseSum (fun j => a j.succ) e + phase i • a 0 := by
  simp [phaseSum, Fin.sum_univ_succ, add_comm]


-- @@ L208-220 verbatim
lemma phaseExpectation_quadratic (n : ℕ) (a : Fin n → A) (b : A) :
    phaseExpectation n (fun e => star (phaseSum a e) * b * phaseSum a e) =
      ∑ i, star (a i) * b * a i := by
  induction n with
  | zero => simp [phaseExpectation, phaseSum]
  | succ n ih =>
    simp only [phaseExpectation, phaseSum_succ]
    change phaseExpectation n (fun e => phaseAverage
      (fun i => star (phaseSum (fun j => a j.succ) e + phase i • a 0) * b *
        (phaseSum (fun j => a j.succ) e + phase i • a 0))) = _
    simp only [phase_quadratic_step, phaseExpectation_add, phaseExpectation_const, ih,
      Fin.sum_univ_succ]
    exact add_comm _ _


-- @@ L222-234 verbatim
lemma phaseExpectation_reverse_quadratic (n : ℕ) (a : Fin n → A) (b : A) :
    phaseExpectation n (fun e => phaseSum a e * b * star (phaseSum a e)) =
      ∑ i, a i * b * star (a i) := by
  induction n with
  | zero => simp [phaseExpectation, phaseSum]
  | succ n ih =>
    simp only [phaseExpectation, phaseSum_succ]
    change phaseExpectation n (fun e => phaseAverage
      (fun i => (phaseSum (fun j => a j.succ) e + phase i • a 0) * b *
        star (phaseSum (fun j => a j.succ) e + phase i • a 0))) = _
    simp only [phase_reverse_quadratic_step, phaseExpectation_add, phaseExpectation_const, ih,
      Fin.sum_univ_succ]
    exact add_comm _ _


-- @@ L236-239 verbatim
lemma phaseExpectation_square (n : ℕ) (a : Fin n → A) :
    phaseExpectation n (fun e => star (phaseSum a e) * phaseSum a e) =
      ∑ i, star (a i) * a i := by
  simpa using phaseExpectation_quadratic n a 1


-- @@ L241-244 verbatim
lemma phaseExpectation_reverse_square (n : ℕ) (a : Fin n → A) :
    phaseExpectation n (fun e => phaseSum a e * star (phaseSum a e)) =
      ∑ i, a i * star (a i) := by
  simpa using phaseExpectation_reverse_quadratic n a 1


-- @@ L246-262 verbatim
lemma phaseExpectation_fourth (n : ℕ) (a : Fin n → A) :
    phaseExpectation n (fun e => (star (phaseSum a e) * phaseSum a e) ^ 2) =
      (∑ i, star (a i) * a i) ^ 2 +
        (∑ i, star (a i) * (∑ j, a j * star (a j)) * a i) -
        ∑ i, (star (a i) * a i) ^ 2 := by
  induction n with
  | zero => simp [phaseExpectation, phaseSum]
  | succ n ih =>
    simp only [phaseExpectation, phaseSum_succ]
    change phaseExpectation n (fun e => phaseAverage
      (fun i => (star (phaseSum (fun j => a j.succ) e + phase i • a 0) *
        (phaseSum (fun j => a j.succ) e + phase i • a 0)) ^ 2)) = _
    simp only [phase_fourth_step, phaseExpectation_add, phaseExpectation_const,
      phaseExpectation_mul_right, phaseExpectation_mul_left, phaseExpectation_square,
      phaseExpectation_reverse_square, phaseExpectation_quadratic, ih]
    simp only [Fin.sum_univ_succ, mul_add, add_mul, Finset.sum_add_distrib]
    noncomm_ring


-- @@ L264-264 verbatim
end RingExpectation


-- @@ L266-268 verbatim
def phaseMean : (n : ℕ) → ((Fin n → Fin 4) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | n + 1, f => phaseMean n (fun e => (1 / 4 : ℝ) * ∑ i : Fin 4, f (Fin.cons i e))


-- @@ L270-277 verbatim
lemma phaseMean_mono (n : ℕ) {f g : (Fin n → Fin 4) → ℝ} (h : ∀ e, f e ≤ g e) :
    phaseMean n f ≤ phaseMean n g := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    apply ih
    intro e
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h (Fin.cons i e))) (by norm_num)


-- @@ L279-286 verbatim
lemma phaseMean_const (n : ℕ) (c : ℝ) : phaseMean n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hx : (1 / 4 : ℝ) * ∑ _i : Fin 4, c = c := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      ring
    simp only [phaseMean, hx, ih]


-- @@ L288-292 verbatim
lemma phaseMean_add (n : ℕ) (f g : (Fin n → Fin 4) → ℝ) :
    phaseMean n (fun e => f e + g e) = phaseMean n f + phaseMean n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [phaseMean, Finset.sum_add_distrib, mul_add]; exact ih _ _


-- @@ L294-300 verbatim
lemma phaseMean_mul (n : ℕ) (c : ℝ) (f : (Fin n → Fin 4) → ℝ) :
    phaseMean n (fun e => c * f e) = c * phaseMean n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseMean, ← Finset.mul_sum, mul_left_comm (1 / 4 : ℝ) c]
    exact ih _


-- @@ L302-304 verbatim
lemma phaseMean_nonneg (n : ℕ) {f : (Fin n → Fin 4) → ℝ} (hf : ∀ e, 0 ≤ f e) :
    0 ≤ phaseMean n f := by
  simpa only [phaseMean_const] using phaseMean_mono n hf


-- @@ L306-311 verbatim
lemma exists_phaseMean_le (n : ℕ) (f : (Fin n → Fin 4) → ℝ) :
    ∃ e, phaseMean n f ≤ f e := by
  classical
  obtain ⟨e, _, he⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨e, ?_⟩
  simpa only [phaseMean_const] using phaseMean_mono n (fun e' => he e' (Finset.mem_univ _))


-- @@ L313-322 verbatim
lemma phaseMean_re (n : ℕ) (f : (Fin n → Fin 4) → ℂ) :
    phaseMean n (fun e => (f e).re) = (phaseExpectation n f).re := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [phaseMean, phaseExpectation]
    rw [← ih]
    congr 1
    funext e
    simp


-- @@ L324-324 verbatim
end BoundedRecovery


-- @@ L326-326 verbatim
noncomputable section

-- @@ L327-327 verbatim
namespace BoundedRecovery

-- @@ L328-328 verbatim
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- @@ L329-329 verbatim
namespace StandardModularData


-- @@ L331-337 verbatim
lemma state_T_square (S : StandardModularData H) (T z : H →L[ℂ] H) :
    (S.state (star z * (star T * T) * z)).re = ‖T (z S.xi)‖ ^ 2 := by
  have he : star z * (star T * T) * z = star (T * z) * (T * z) := by
    simp only [star_mul]
    noncomm_ring
  rw [he, S.state_star_mul_re]
  rfl


-- @@ L339-342 verbatim
lemma real_sqrt_sandwich {p : ℝ} (hp : 0 ≤ p) (z b : H →L[ℂ] H) :
    star (Real.sqrt p • z) * b * (Real.sqrt p • z) = p • (star z * b * z) := by
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← pow_two, Real.sq_sqrt hp]


-- @@ L344-346 verbatim
lemma real_sqrt_square {p : ℝ} (hp : 0 ≤ p) (z : H →L[ℂ] H) :
    star (Real.sqrt p • z) * (Real.sqrt p • z) = p • (star z * z) := by
  simpa only [mul_one] using real_sqrt_sandwich hp z 1


-- @@ L348-351 verbatim
lemma real_sqrt_reverse_square {p : ℝ} (hp : 0 ≤ p) (z : H →L[ℂ] H) :
    (Real.sqrt p • z) * star (Real.sqrt p • z) = p • (z * star z) := by
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← pow_two, Real.sq_sqrt hp]


-- @@ L353-365 verbatim
lemma phaseMean_defect (S : StandardModularData H) (T : H →L[ℂ] H)
    (n : ℕ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (z : Fin n → H →L[ℂ] H) :
    phaseMean n (fun e => ‖T (phaseSum (fun i => Real.sqrt (p i) • z i) e S.xi)‖ ^ 2) =
      ∑ i, p i * ‖T (z i S.xi)‖ ^ 2 := by
  simp_rw [← S.state_T_square T]
  rw [phaseMean_re]
  change (phaseExpectation n (fun e => vectorStateLM S.xi
    (star (phaseSum (fun i => Real.sqrt (p i) • z i) e) * (star T * T) *
      phaseSum (fun i => Real.sqrt (p i) • z i) e))).re = _
  rw [phaseExpectation_map, phaseExpectation_quadratic]
  simp only [real_sqrt_sandwich (hp _), map_sum, LinearMap.map_smul_of_tower,
    Complex.re_sum, Complex.smul_re, smul_eq_mul]
  rfl


-- @@ L367-396 verbatim
lemma phaseMean_fourth_le (S : StandardModularData H)
    (n : ℕ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (z : Fin n → H →L[ℂ] H) :
    phaseMean n (fun e => (S.state ((star (phaseSum (fun i => Real.sqrt (p i) • z i) e) *
      phaseSum (fun i => Real.sqrt (p i) • z i) e) ^ 2)).re) ≤
      (S.state ((∑ i, p i • (star (z i) * z i)) ^ 2)).re +
      ∑ i, p i * (S.state (star (z i) * (∑ j, p j • (z j * star (z j))) * z i)).re := by
  let a (i : Fin n) := Real.sqrt (p i) • z i
  rw [phaseMean_re]
  change (phaseExpectation n (fun e => vectorStateLM S.xi
    ((star (phaseSum a e) * phaseSum a e) ^ 2))).re ≤ _
  rw [phaseExpectation_map, phaseExpectation_fourth, map_sub, map_add, Complex.sub_re, Complex.add_re]
  have hsum : 0 ≤ (vectorStateLM S.xi (∑ i, (star (a i) * a i)^2)).re := by
    rw [map_sum, Complex.re_sum]
    apply Finset.sum_nonneg
    intro i _
    rw [re_vectorState_sq S.xi (IsSelfAdjoint.star_mul_self _)]
    positivity
  have hA : ∑ i, star (a i) * a i = ∑ i, p i • (star (z i) * z i) := by
    simp only [a, real_sqrt_square (hp _)]
  have hB : ∑ i, a i * star (a i) = ∑ i, p i • (z i * star (z i)) := by
    simp only [a, real_sqrt_reverse_square (hp _)]
  rw [hA, hB]
  have hC : (vectorStateLM S.xi
      (∑ i, star (a i) * (∑ j, p j • (z j * star (z j))) * a i)).re =
      ∑ i, p i * (S.state (star (z i) * (∑ j, p j • (z j * star (z j))) * z i)).re := by
    simp only [a, real_sqrt_sandwich (hp _), map_sum, LinearMap.map_smul_of_tower,
      Complex.re_sum, Complex.smul_re, smul_eq_mul]
    rfl
  rw [hC]
  exact sub_le_self _ hsum


-- @@ L398-398 verbatim
end StandardModularData

-- @@ L399-399 verbatim
end BoundedRecovery


-- @@ L401-401 verbatim
end

-- @@ L402-402 verbatim
end

-- @@ L403-403 verbatim
end


-- @@ L405-405 verbatim
end OAI
