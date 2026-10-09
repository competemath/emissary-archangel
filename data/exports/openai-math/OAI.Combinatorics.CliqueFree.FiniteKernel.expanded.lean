import OAI.Combinatorics.CliqueFree.FiniteEntropy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open Finset


-- @@ L10-10 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L12-12 verbatim
namespace CliqueFreeIndependence


-- @@ L14-14 verbatim
universe u v


-- @@ L16-16 verbatim
namespace FiniteKernel


-- @@ L18-18 verbatim
open FiniteEntropy

-- @@ L19-19 verbatim
variable {I : Type u} [Fintype I]


-- @@ L21-21 verbatim
abbrev Kernel (I : Type u) := Matrix I I ℝ


-- @@ L23-23 verbatim
local instance : DecidableEq I := Classical.decEq I


-- @@ L25-25 verbatim
def Stochastic (P : Kernel I) : Prop := ∀ i, IsProb (P i)

-- @@ L26-26 verbatim
def Stationary (π : I → ℝ) (P : Kernel I) : Prop := ∀ j, ∑ i, π i * P i j = π j

-- @@ L27-27 verbatim
def Reversible (π : I → ℝ) (P : Kernel I) : Prop := ∀ i j, π i * P i j = π j * P j i


-- @@ L29-30 verbatim
noncomputable def lazy (P : Kernel I) : Kernel I := fun i j ↦
  ((if i = j then 1 else 0) + P i j) / 2


-- @@ L32-34 verbatim
noncomputable def smoothed (P : Kernel I) (j : ℕ) : Kernel I := by
  classical
  exact P * lazy P ^ j


-- @@ L36-36 verbatim
def avgEntropy (π w : I → ℝ) (K : Kernel I) : ℝ := ∑ i, π i * entropy w (K i)


-- @@ L38-45 verbatim
lemma stochastic_one : Stochastic (1 : Kernel I) := by
  classical
  intro i
  constructor
  · intro j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  · simp [Matrix.one_apply]


-- @@ L47-50 verbatim
lemma stochastic_mul {P Q : Kernel I} (hP : Stochastic P) (hQ : Stochastic Q) :
    Stochastic (P * Q) := by
  intro i
  exact mix_isProb (hP i) hQ


-- @@ L52-56 verbatim
lemma stochastic_pow {P : Kernel I} (hP : Stochastic P) (n : ℕ) : Stochastic (P ^ n) := by
  classical
  induction n with
  | zero => simpa using (stochastic_one (I := I))
  | succ n ih => simpa only [pow_succ] using stochastic_mul ih hP


-- @@ L58-68 verbatim
lemma stochastic_lazy {P : Kernel I} (hP : Stochastic P) : Stochastic (lazy P) := by
  classical
  intro i
  constructor
  · intro j
    dsimp [lazy]
    have := (hP i).1 j
    split_ifs <;> positivity
  · change (∑ j, ((if i = j then (1 : ℝ) else 0) + P i j) / 2) = 1
    rw [← sum_div, sum_add_distrib]
    simp [(hP i).2]


-- @@ L70-71 verbatim
lemma stochastic_smoothed {P : Kernel I} (hP : Stochastic P) (j : ℕ) :
    Stochastic (smoothed P j) := stochastic_mul hP (stochastic_pow (stochastic_lazy hP) j)


-- @@ L73-78 verbatim
lemma stationary_of_reversible {π : I → ℝ} {P : Kernel I}
    (hP : Stochastic P) (hr : Reversible π P) : Stationary π P := by
  intro j
  calc
    _ = ∑ i, π j * P j i := sum_congr rfl fun i _ ↦ hr i j
    _ = π j := by rw [← mul_sum, (hP j).2, mul_one]


-- @@ L80-89 verbatim
lemma stationary_lazy {π : I → ℝ} {P : Kernel I} (hP : Stationary π P) :
    Stationary π (lazy P) := by
  classical
  intro j
  change (∑ i, π i * (((if i = j then 1 else 0) + P i j) / 2)) = π j
  simp only [← mul_div_assoc, mul_add, ← sum_div, sum_add_distrib,
    mul_ite, mul_one, mul_zero]
  simp only [sum_ite_eq', mem_univ, ite_true]
  rw [hP j]
  ring


-- @@ L91-97 verbatim
omit [Fintype I] in
lemma reversible_one (π : I → ℝ) : Reversible π (1 : Kernel I) := by
  classical
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp [h, Ne.symm h]


-- @@ L99-115 verbatim
lemma reversible_mul {π : I → ℝ} {P Q : Kernel I}
    (hP : Reversible π P) (hQ : Reversible π Q) (hc : Commute P Q) :
    Reversible π (P * Q) := by
  intro i j
  rw [Matrix.mul_apply, mul_sum]
  calc
    _ = ∑ k, π j * (Q j k * P k i) := by
      apply sum_congr rfl
      intro k _
      calc
        _ = (π i * P i k) * Q k j := by ring
        _ = (π k * P k i) * Q k j := by rw [hP]
        _ = (π k * Q k j) * P k i := by ring
        _ = (π j * Q j k) * P k i := by rw [hQ]
        _ = _ := by ring
    _ = π j * (Q * P) j i := by rw [Matrix.mul_apply, mul_sum]
    _ = _ := by rw [hc.eq]


-- @@ L117-124 verbatim
lemma reversible_pow {π : I → ℝ} {P : Kernel I} (hP : Reversible π P) (n : ℕ) :
    Reversible π (P ^ n) := by
  classical
  induction n with
  | zero => simpa using reversible_one π
  | succ n ih =>
    rw [pow_succ]
    exact reversible_mul ih hP ((Commute.refl P).pow_left n)


-- @@ L126-134 verbatim
omit [Fintype I] in
lemma reversible_lazy {π : I → ℝ} {P : Kernel I} (hP : Reversible π P) :
    Reversible π (lazy P) := by
  classical
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp only [lazy, h, Ne.symm h, ite_false, zero_add]
    rw [← mul_div_assoc, ← mul_div_assoc, hP i j]


-- @@ L136-140 verbatim
omit [Fintype I] in
lemma lazy_eq (P : Kernel I) : lazy P = (1 / 2 : ℝ) • (1 + P) := by
  classical
  ext i j
  simp [lazy, Matrix.one_apply, div_eq_mul_inv, mul_comm]


-- @@ L142-146 verbatim
lemma commute_lazy (P : Kernel I) : Commute P (lazy P) := by
  classical
  rw [lazy_eq]
  show P * ((1 / 2 : ℝ) • (1 + P)) = ((1 / 2 : ℝ) • (1 + P)) * P
  simp [mul_add, add_mul]


-- @@ L148-152 verbatim
lemma reversible_smoothed {π : I → ℝ} {P : Kernel I} (hP : Reversible π P) (j : ℕ) :
    Reversible π (smoothed P j) := by
  classical
  exact reversible_mul hP (reversible_pow (reversible_lazy hP) j)
    ((commute_lazy P).pow_right j)


-- @@ L154-156 verbatim
lemma smoothed_zero (P : Kernel I) : smoothed P 0 = P := by
  classical
  simp [smoothed]


-- @@ L158-162 verbatim
lemma smoothed_succ (P : Kernel I) (j : ℕ) :
    smoothed P (j + 1) = lazy P * smoothed P j := by
  classical
  unfold smoothed
  rw [pow_succ', ← mul_assoc, (commute_lazy P).eq, mul_assoc]


-- @@ L164-167 verbatim
lemma smoothed_succ_right (P : Kernel I) (j : ℕ) :
    smoothed P (j + 1) = smoothed P j * lazy P := by
  classical
  simp [smoothed, pow_succ, mul_assoc]


-- @@ L169-179 verbatim
lemma smoothed_density {P : Kernel I} (hP : Stochastic P) {b : I → ℝ}
    (hb : ∀ i j, P i j ≤ b j) (n : ℕ) : ∀ i j, smoothed P n i j ≤ b j := by
  classical
  intro i j
  unfold smoothed
  rw [((commute_lazy P).pow_right n).eq, Matrix.mul_apply]
  have hQ := stochastic_pow (stochastic_lazy hP) n
  calc
    _ ≤ ∑ k, (lazy P ^ n) i k * b j :=
      sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hb k j) ((hQ i).1 k)
    _ = b j := by rw [← sum_mul, (hQ i).2, one_mul]


-- @@ L181-188 verbatim
lemma pair_isProb {π : I → ℝ} (hπ : IsProb π) {Q : Kernel I} (hQ : Stochastic Q) :
    IsProb (fun a : I × I ↦ π a.1 * Q a.1 a.2) := by
  constructor
  · intro a
    exact mul_nonneg (hπ.1 a.1) ((hQ a.1).1 a.2)
  · rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, fun i ↦ (hQ i).2, mul_one]
    exact hπ.2


-- @@ L190-195 verbatim
lemma stationary_average {π : I → ℝ} {Q : Kernel I} (hQ : Stationary π Q) (f : I → ℝ) :
    (∑ i, π i * ∑ j, Q i j * f j) = ∑ j, π j * f j := by
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  simp_rw [← sum_mul]
  exact sum_congr rfl fun j _ ↦ by rw [hQ j]


-- @@ L197-206 verbatim
lemma entropy_increment {π w : I → ℝ} (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    avgEntropy π w (Q * K) - avgEntropy π w K =
      ∑ i, π i * ∑ j, Q i j * divergence (K j) ((Q * K) i) := by
  have he (i : I) := entropy_mix_gap hw (hQ i) hK
  have he' : ∀ i, entropy w ((Q * K) i) - ∑ j, Q i j * entropy w (K j) =
      ∑ j, Q i j * divergence (K j) ((Q * K) i) := he
  simp_rw [← he', mul_sub, sum_sub_distrib]
  rw [stationary_average hs]
  rfl


-- @@ L208-220 verbatim
lemma entropy_increment_nonneg {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    0 ≤ avgEntropy π w (Q * K) - avgEntropy π w K := by
  rw [entropy_increment hw hQ hK hs]
  apply sum_nonneg
  intro i _
  apply mul_nonneg (hπ.1 i)
  apply sum_nonneg
  intro j _
  rcases ((hQ i).1 j).eq_or_lt with hj | hj
  · simp [← hj]
  exact mul_nonneg hj.le (divergence_nonneg (hK j) (stochastic_mul hQ hK i)
    (fun k hk ↦ mix_support (hQ i).1 (fun z ↦ (hK z).1) hj hk))


-- @@ L222-231 verbatim
lemma entropy_increment_tv {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {Q K : Kernel I} (hQ : Stochastic Q) (hK : Stochastic K) (hs : Stationary π Q) :
    (∑ i, π i * ∑ j, Q i j * tv (K j) ((Q * K) i)) ^ 2 ≤
      avgEntropy π w (Q * K) - avgEntropy π w K := by
  rw [entropy_increment hw hQ hK hs]
  have h := average_tv_sq_le_average_divergence (pair_isProb hπ hQ)
    (fun a : I × I ↦ hK a.2) (fun a : I × I ↦ stochastic_mul hQ hK a.1)
    (fun a ha i hi ↦ mix_support (hQ a.1).1 (fun j ↦ (hK j).1)
      (pos_of_mul_pos_right ha (hπ.1 a.1)) hi)
  simpa only [Fintype.sum_prod_type, mul_assoc, ← mul_sum] using h


-- @@ L233-259 verbatim
lemma lazy_triangle_tv {π : I → ℝ} (hπ : IsProb π) {P K : Kernel I}
    (hP : Stochastic P) :
    (∑ i, π i * ∑ j, P i j * tv (K i) (K j)) ≤
      2 * (∑ i, π i * ∑ j, lazy P i j * tv (K j) ((lazy P * K) i)) := by
  classical
  have hi (i : I) : (∑ j, P i j * tv (K i) (K j)) ≤
      2 * ∑ j, lazy P i j * tv (K j) ((lazy P * K) i) := by
    calc
      _ ≤ ∑ j, P i j * (tv (K i) ((lazy P * K) i) + tv (K j) ((lazy P * K) i)) := by
        apply sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ ((hP i).1 j)
        have := tv_triangle (K i) ((lazy P * K) i) (K j)
        simpa only [tv_comm ((lazy P * K) i)] using this
      _ = _ := by
        have he (f : I → ℝ) : (∑ j, lazy P i j * f j) =
            (f i + ∑ j, P i j * f j) / 2 := by
          simp only [lazy, div_mul_eq_mul_div, add_mul, ← sum_div, sum_add_distrib,
            ite_mul, one_mul, zero_mul]
          simp
        rw [he]
        simp only [mul_add, sum_add_distrib, ← sum_mul, (hP i).2, one_mul]
        ring
  calc
    _ ≤ ∑ i, π i * (2 * ∑ j, lazy P i j * tv (K j) ((lazy P * K) i)) :=
      sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hi i) (hπ.1 i)
    _ = _ := by simp_rw [← mul_assoc, mul_comm (π _ ) 2, mul_assoc, ← mul_sum]


-- @@ L261-268 verbatim
lemma smoothed_entropy_mono {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P) :
    Monotone (fun j ↦ avgEntropy π w (smoothed P j)) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [smoothed_succ]
  exact sub_nonneg.1 (entropy_increment_nonneg hπ hw (stochastic_lazy hP)
    (stochastic_smoothed hP j) (stationary_lazy hs))


-- @@ L270-286 verbatim
lemma smoothed_row_distance_sq {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P) (j : ℕ) :
    (∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z)) ^ 2 ≤
      4 * (avgEntropy π w (smoothed P (j + 1)) - avgEntropy π w (smoothed P j)) := by
  have h := entropy_increment_tv hπ hw (stochastic_lazy hP)
    (stochastic_smoothed hP j) (stationary_lazy hs)
  have hc := lazy_triangle_tv (K := smoothed P j) hπ hP
  have ha : 0 ≤ ∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z) :=
    sum_nonneg fun i _ ↦ mul_nonneg (hπ.1 i)
      (sum_nonneg fun z _ ↦ mul_nonneg ((hP i).1 z) (tv_nonneg _ _))
  have hb : 0 ≤ ∑ i, π i * ∑ z, lazy P i z * tv (smoothed P j z)
      ((lazy P * smoothed P j) i) :=
    sum_nonneg fun i _ ↦ mul_nonneg (hπ.1 i)
      (sum_nonneg fun z _ ↦ mul_nonneg ((stochastic_lazy hP i).1 z) (tv_nonneg _ _))
  rw [smoothed_succ]
  have hp := mul_nonneg (sub_nonneg.2 hc) (add_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hb) ha)
  nlinarith


-- @@ L288-310 verbatim
/-- Entropy telescoping gives the averaged triangle-row estimate. -/
lemma exists_smoothed_row_distance {π w : I → ℝ} (hπ : IsProb π) (hw : ∀ i, 0 < w i)
    {P : Kernel I} (hP : Stochastic P) (hs : Stationary π P)
    {R : ℕ} (hR : 0 < R) {D : ℝ}
    (hD : avgEntropy π w (smoothed P R) - avgEntropy π w (smoothed P 0) ≤ D) :
    ∃ j < R, (∑ i, π i * ∑ z, P i z * tv (smoothed P j i) (smoothed P j z)) ^ 2 ≤
      4 * D / R := by
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hR
  have hsum : (∑ j ∈ range R, (avgEntropy π w (smoothed P (j + 1)) -
      avgEntropy π w (smoothed P j))) ≤ ∑ _j ∈ range R, D / (R : ℝ) := by
    rw [sum_range_sub (fun j ↦ avgEntropy π w (smoothed P j)) R]
    have he : (∑ _j ∈ range R, D / (R : ℝ)) = D := by
      rw [sum_const, card_range, nsmul_eq_mul]
      field_simp
    rw [he]
    exact hD
  obtain ⟨j, hj, hle⟩ := exists_le_of_sum_le (nonempty_range_iff.2 (Nat.ne_of_gt hR)) hsum
  refine ⟨j, mem_range.1 hj, ?_⟩
  calc
    _ ≤ 4 * (avgEntropy π w (smoothed P (j + 1)) - avgEntropy π w (smoothed P j)) :=
      smoothed_row_distance_sq hπ hw hP hs j
    _ ≤ 4 * (D / (R : ℝ)) := mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = _ := by ring


-- @@ L312-312 verbatim
variable {J : Type v}


-- @@ L314-315 verbatim
def Preserves (label : I → J) (P : Kernel I) : Prop :=
  ∀ i j, label i ≠ label j → P i j = 0


-- @@ L317-321 verbatim
omit [Fintype I] in
lemma preserves_one (label : I → J) : Preserves label (1 : Kernel I) := by
  intro i j hij
  have h : i ≠ j := fun h ↦ hij (congrArg label h)
  simp [h]


-- @@ L323-332 verbatim
lemma preserves_mul {label : I → J} {P Q : Kernel I}
    (hP : Preserves label P) (hQ : Preserves label Q) : Preserves label (P * Q) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  by_cases hik : label i = label k
  · have hkj : label k ≠ label j := fun h ↦ hij (hik.trans h)
    rw [hQ k j hkj, mul_zero]
  · rw [hP i k hik, zero_mul]


-- @@ L334-338 verbatim
lemma preserves_pow {label : I → J} {P : Kernel I} (hP : Preserves label P) (n : ℕ) :
    Preserves label (P ^ n) := by
  induction n with
  | zero => simpa using preserves_one label
  | succ n ih => simpa only [pow_succ] using preserves_mul ih hP


-- @@ L340-345 verbatim
omit [Fintype I] in
lemma preserves_lazy {label : I → J} {P : Kernel I} (hP : Preserves label P) :
    Preserves label (lazy P) := by
  intro i j hij
  have h : i ≠ j := fun h ↦ hij (congrArg label h)
  simp [lazy, h, hP i j hij]


-- @@ L347-349 verbatim
lemma preserves_smoothed {label : I → J} {P : Kernel I} (hP : Preserves label P) (n : ℕ) :
    Preserves label (smoothed P n) :=
  preserves_mul hP (preserves_pow (preserves_lazy hP) n)


-- @@ L351-351 verbatim
def rowMass (K : Kernel I) (i : I) (A : Finset I) : ℝ := ∑ j ∈ A, K i j


-- @@ L353-356 verbatim
lemma rowMass_le_one {K : Kernel I} (hK : Stochastic K) (i : I) (A : Finset I) :
    rowMass K i A ≤ 1 := by
  rw [← (hK i).2]
  exact sum_le_univ_sum_of_nonneg (hK i).1


-- @@ L358-362 verbatim
lemma rowMass_mul (P Q : Kernel I) (i : I) (A : Finset I) :
    rowMass (P * Q) i A = ∑ j, P i j * rowMass Q j A := by
  unfold rowMass
  simp only [Matrix.mul_apply, mul_sum]
  rw [sum_comm]


-- @@ L364-368 verbatim
lemma rowMass_compl {K : Kernel I} (hK : Stochastic K) (i : I) (A : Finset I) :
    rowMass K i Aᶜ = 1 - rowMass K i A := by
  have h : rowMass K i A + rowMass K i Aᶜ = 1 := by
    rw [rowMass, rowMass, sum_add_sum_compl, (hK i).2]
  linarith


-- @@ L370-386 verbatim
lemma leakage_mul_le {P Q : Kernel I} (hP : Stochastic P) (hQ : Stochastic Q)
    (i : I) (A B : Finset I) :
    rowMass (P * Q) i Bᶜ ≤ rowMass P i Aᶜ + ∑ y ∈ Bᶜ, ∑ z ∈ A, P i z * Q z y := by
  rw [rowMass_mul]
  have hsplit : (∑ j, P i j * rowMass Q j Bᶜ) =
      (∑ j ∈ A, P i j * rowMass Q j Bᶜ) + ∑ j ∈ Aᶜ, P i j * rowMass Q j Bᶜ :=
    (sum_add_sum_compl A _).symm
  rw [hsplit]
  have hle : (∑ j ∈ Aᶜ, P i j * rowMass Q j Bᶜ) ≤ rowMass P i Aᶜ := by
    exact sum_le_sum fun j _ ↦ by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (rowMass_le_one hQ j Bᶜ) ((hP i).1 j)
  have he : (∑ j ∈ A, P i j * rowMass Q j Bᶜ) = ∑ y ∈ Bᶜ, ∑ z ∈ A, P i z * Q z y := by
    simp only [rowMass, mul_sum]
    rw [sum_comm]
  rw [he]
  linarith


-- @@ L388-411 verbatim
lemma reversed_entropy_tail {μ w : I → ℝ} {K : Matrix I I ℝ}
    (hμ : IsProb μ) (hw : ∀ i, 0 < w i) (hK : Stochastic K)
    (hr : Reversible μ K) {x a : ℝ} (hx : 0 < x)
    (hd : ∀ i j, K i j ≤ x * w j) :
    (a + Real.log x) *
        (∑ i, μ i * ∑ j, if K j i < w i * Real.exp (-a) then K i j else 0) ≤
      avgEntropy μ w K + Real.log x := by
  have h := sum_le_sum (s := univ) fun i _ ↦
    mul_le_mul_of_nonneg_left (entropy_tail (a := a) (hK i) hw hx (hd i)) (hμ.1 i)
  have heq : (∑ i, μ i * ∑ j, if K j i < w i * Real.exp (-a) then K i j else 0) =
      ∑ i, μ i * ∑ j, if K i j < w j * Real.exp (-a) then K i j else 0 := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    by_cases hb : K i j < w j * Real.exp (-a)
    · simp only [hb, ↓reduceIte]
      exact hr j i
    · simp only [hb, ↓reduceIte, mul_zero]
  rw [heq]
  simpa only [mul_sum, mul_add, sum_add_distrib, ← sum_mul, hμ.2, one_mul,
    avgEntropy, mul_left_comm] using h


-- @@ L413-413 verbatim
end FiniteKernel


-- @@ L415-415 verbatim
end CliqueFreeIndependence


-- @@ L417-417 verbatim
end


-- @@ L419-419 verbatim
end OAI
