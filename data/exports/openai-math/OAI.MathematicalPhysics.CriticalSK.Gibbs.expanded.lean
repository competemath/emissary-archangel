import OAI.MathematicalPhysics.CriticalSK.SpinModel


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Topology NNReal ENNReal


-- @@ L9-9 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L11-11 verbatim
open scoped ENNReal NNReal


-- @@ L13-13 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L15-15 verbatim
open Module


-- @@ L17-17 verbatim
open scoped BigOperators ENNReal NNReal Real Topology


-- @@ L19-19 verbatim
open MeasureTheory ProbabilityTheory Filter


-- @@ L21-21 verbatim
open scoped BigOperators NNReal


-- @@ L23-23 verbatim
open scoped BigOperators


-- @@ L25-25 verbatim
open Matrix Polynomial


-- @@ L27-27 verbatim
open scoped BigOperators Topology


-- @@ L29-29 verbatim
open Filter


-- @@ L31-31 verbatim
namespace CriticalSK


-- @@ L33-33 verbatim
section FiniteGibbs


-- @@ L35-35 verbatim
variable {n : ℕ} (W : Disorder n)


-- @@ L37-39 verbatim
lemma partition_pos : 0 < partition W := by
  unfold partition
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


-- @@ L41-42 verbatim
lemma gibbs_pos (x : Spin n) : 0 < gibbs W x :=
  div_pos (Real.exp_pos _) (partition_pos W)


-- @@ L44-44 verbatim
lemma gibbs_nonneg (x : Spin n) : 0 ≤ gibbs W x := (gibbs_pos W x).le


-- @@ L46-49 verbatim
lemma gibbs_sum : ∑ x : Spin n, gibbs W x = 1 := by
  unfold gibbs
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos W))


-- @@ L51-53 verbatim
lemma gibbs_le_one (x : Spin n) : gibbs W x ≤ 1 := by
  rw [← gibbs_sum W]
  exact Finset.single_le_sum (fun y _ => gibbs_nonneg W y) (Finset.mem_univ x)


-- @@ L55-55 verbatim
def spinFlip (x : Spin n) : Spin n := fun i => !(x i)


-- @@ L57-57 verbatim
def spinFlipEquiv : Equiv.Perm (Spin n) := Equiv.piCongrRight (fun _ => Equiv.boolNot)


-- @@ L59-59 verbatim
@[simp] lemma spinFlipEquiv_apply (x : Spin n) : spinFlipEquiv x = spinFlip x := rfl


-- @@ L61-63 verbatim
@[simp] lemma spinFlip_spinFlip (x : Spin n) : spinFlip (spinFlip x) = x := by
  funext i
  simp [spinFlip]


-- @@ L65-66 verbatim
@[simp] lemma spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]


-- @@ L68-73 verbatim
@[simp] lemma hamiltonian_spinFlip (x : Spin n) :
    hamiltonian W (spinFlip x) = hamiltonian W x := by
  unfold hamiltonian
  apply Finset.sum_congr rfl
  intro e _
  simp [spinFlip]


-- @@ L75-76 verbatim
@[simp] lemma gibbs_spinFlip (x : Spin n) : gibbs W (spinFlip x) = gibbs W x := by
  simp [gibbs]


-- @@ L78-85 verbatim
lemma mean_odd_eq_zero (f : Spin n → ℝ) (hf : ∀ x, f (spinFlip x) = -f x) :
    mean W f = 0 := by
  have h : mean W f = -mean W f := by
    calc
      mean W f = ∑ x, gibbs W (spinFlip x) * f (spinFlip x) :=
        (Equiv.sum_comp spinFlipEquiv (fun x => gibbs W x * f x)).symm
      _ = -mean W f := by simp [hf, mean, Finset.sum_neg_distrib]
  linarith


-- @@ L87-90 verbatim
@[simp] lemma mean_spin (i : Fin n) : mean W (fun x => spinValue (x i)) = 0 := by
  apply mean_odd_eq_zero
  intro x
  simp [spinFlip]


-- @@ L92-94 verbatim
@[simp] lemma linearObservable_spinFlip (a : Fin n → ℝ) (x : Spin n) :
    linearObservable a (spinFlip x) = -linearObservable a x := by
  simp [linearObservable, spinFlip, Finset.sum_neg_distrib]


-- @@ L96-98 verbatim
@[simp] lemma mean_linearObservable (a : Fin n → ℝ) :
    mean W (linearObservable a) = 0 :=
  mean_odd_eq_zero W _ (linearObservable_spinFlip a)


-- @@ L100-102 verbatim
lemma covariance_eq (i j : Fin n) :
    covariance W i j = mean W (fun x => spinValue (x i) * spinValue (x j)) := by
  simp [covariance]


-- @@ L104-106 verbatim
@[simp] lemma covariance_diag (i : Fin n) : covariance W i i = 1 := by
  rw [covariance_eq]
  simpa [mean, ← sq] using gibbs_sum W


-- @@ L108-110 verbatim
lemma sameExcept_refl (i : Fin n) (x : Spin n) : sameExcept i x x := by
  intro _ _
  rfl


-- @@ L112-115 verbatim
lemma sameExcept_symm {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    sameExcept i y x := by
  intro j hj
  exact (h j hj).symm


-- @@ L117-120 verbatim
lemma sameExcept_trans {i : Fin n} {x y z : Spin n}
    (hxy : sameExcept i x y) (hyz : sameExcept i y z) : sameExcept i x z := by
  intro j hj
  exact (hyz j hj).trans (hxy j hj)


-- @@ L122-124 verbatim
lemma sameExcept_classes {i : Fin n} {x y : Spin n} (h : sameExcept i x y)
    (z : Spin n) : sameExcept i x z ↔ sameExcept i y z :=
  ⟨sameExcept_trans (sameExcept_symm h), sameExcept_trans h⟩


-- @@ L126-127 verbatim
def fiberMass (i : Fin n) (x : Spin n) : ℝ :=
  ∑ z : Spin n, if sameExcept i x z then gibbs W z else 0


-- @@ L129-136 verbatim
lemma fiberMass_pos (i : Fin n) (x : Spin n) : 0 < fiberMass W i x := by
  have h : gibbs W x ≤ fiberMass W i x := by
    unfold fiberMass
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun z => if sameExcept i x z then gibbs W z else 0)
      (fun z _ => by split_ifs; exact gibbs_nonneg W z; exact le_rfl) (Finset.mem_univ x)
    simpa only [sameExcept_refl, ite_true] using hh
  exact lt_of_lt_of_le (gibbs_pos W x) h


-- @@ L138-143 verbatim
lemma fiberMass_eq {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    fiberMass W i x = fiberMass W i y := by
  unfold fiberMass
  apply Finset.sum_congr rfl
  intro z _
  simp only [sameExcept_classes h z]


-- @@ L145-149 verbatim
lemma siteKernel_nonneg (i : Fin n) (x y : Spin n) : 0 ≤ siteKernel W i x y := by
  unfold siteKernel
  split_ifs
  · exact (div_pos (gibbs_pos W y) (fiberMass_pos W i x)).le
  · exact le_rfl


-- @@ L151-159 verbatim
lemma siteKernel_sum (i : Fin n) (x : Spin n) : ∑ y, siteKernel W i x y = 1 := by
  calc
    (∑ y, siteKernel W i x y) = fiberMass W i x / fiberMass W i x := by
      unfold siteKernel fiberMass
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = 1 := div_self (ne_of_gt (fiberMass_pos W i x))


-- @@ L161-170 verbatim
lemma siteKernel_reversible (i : Fin n) (x y : Spin n) :
    gibbs W x * siteKernel W i x y = gibbs W y * siteKernel W i y x := by
  by_cases h : sameExcept i x y
  · have h' := sameExcept_symm h
    change gibbs W x * (if sameExcept i x y then gibbs W y / fiberMass W i x else 0) =
      gibbs W y * (if sameExcept i y x then gibbs W x / fiberMass W i y else 0)
    simp only [h, h', ite_true, fiberMass_eq W h]
    ring
  · have h' : ¬sameExcept i y x := fun hh => h (sameExcept_symm hh)
    simp [siteKernel, h, h']


-- @@ L172-175 verbatim
lemma siteKernel_stationary (i : Fin n) (y : Spin n) :
    ∑ x, gibbs W x * siteKernel W i x y = gibbs W y := by
  simp_rw [siteKernel_reversible W i]
  rw [← Finset.mul_sum, siteKernel_sum, mul_one]


-- @@ L177-182 verbatim
lemma siteKernel_same_row {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    siteKernel W i x = siteKernel W i y := by
  funext z
  change (if sameExcept i x z then gibbs W z / fiberMass W i x else 0) =
    (if sameExcept i y z then gibbs W z / fiberMass W i y else 0)
  simp only [sameExcept_classes h z, fiberMass_eq W h]


-- @@ L184-195 verbatim
lemma siteKernel_projection (i : Fin n) : siteKernel W i * siteKernel W i = siteKernel W i := by
  ext x z
  change (∑ y, siteKernel W i x y * siteKernel W i y z) = siteKernel W i x z
  calc
    (∑ y, siteKernel W i x y * siteKernel W i y z) =
        ∑ y, siteKernel W i x y * siteKernel W i x z := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : sameExcept i x y
      · rw [siteKernel_same_row W h]
      · simp [siteKernel, h]
    _ = siteKernel W i x z := by rw [← Finset.sum_mul, siteKernel_sum, one_mul]


-- @@ L197-197 verbatim
end FiniteGibbs


-- @@ L199-199 verbatim
variable {n : ℕ} (W : Disorder n)


-- @@ L201-202 verbatim
lemma mean_nonneg {f : Spin n → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean W f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (gibbs_nonneg W x) (hf x))


-- @@ L204-205 verbatim
lemma mean_mono {f g : Spin n → ℝ} (h : ∀ x, f x ≤ g x) : mean W f ≤ mean W g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (gibbs_nonneg W x))


-- @@ L207-208 verbatim
@[simp] lemma mean_const (c : ℝ) : mean W (fun _ => c) = c := by
  simp only [mean, ← Finset.sum_mul, gibbs_sum, one_mul]


-- @@ L210-212 verbatim
lemma mean_add (f g : Spin n → ℝ) :
    mean W (fun x => f x + g x) = mean W f + mean W g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]


-- @@ L214-216 verbatim
lemma mean_sub (f g : Spin n → ℝ) :
    mean W (fun x => f x - g x) = mean W f - mean W g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]


-- @@ L218-219 verbatim
lemma mean_neg (f : Spin n → ℝ) : mean W (fun x => -f x) = -mean W f := by
  simp only [mean, mul_neg, Finset.sum_neg_distrib]


-- @@ L221-223 verbatim
lemma mean_mul_const (f : Spin n → ℝ) (c : ℝ) :
    mean W (fun x => f x * c) = mean W f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]


-- @@ L225-227 verbatim
lemma mean_const_mul (f : Spin n → ℝ) (c : ℝ) :
    mean W (fun x => c * f x) = c * mean W f := by
  simpa only [mul_comm c] using mean_mul_const W f c


-- @@ L229-232 verbatim
lemma mean_sum {ι : Type*} (s : Finset ι) (f : ι → Spin n → ℝ) :
    mean W (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, mean W (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm


-- @@ L234-235 verbatim
def siteAverage (i : Fin n) (f : Spin n → ℝ) : Spin n → ℝ :=
  (siteKernel W i).mulVec f


-- @@ L237-238 verbatim
lemma siteAverage_eq (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    siteAverage W i f x = ∑ y, siteKernel W i x y * f y := rfl


-- @@ L240-243 verbatim
lemma siteAverage_add (i : Fin n) (f g : Spin n → ℝ) :
    siteAverage W i (fun x => f x + g x) =
      fun x => siteAverage W i f x + siteAverage W i g x :=
  Matrix.mulVec_add _ _ _


-- @@ L245-249 verbatim
lemma siteAverage_sub (i : Fin n) (f g : Spin n → ℝ) :
    siteAverage W i (fun x => f x - g x) =
      fun x => siteAverage W i f x - siteAverage W i g x := by
  funext x
  simp only [siteAverage_eq, mul_sub, Finset.sum_sub_distrib]


-- @@ L251-254 verbatim
lemma siteAverage_idempotent (i : Fin n) (f : Spin n → ℝ) :
    siteAverage W i (siteAverage W i f) = siteAverage W i f := by
  unfold siteAverage
  rw [Matrix.mulVec_mulVec, siteKernel_projection]


-- @@ L256-259 verbatim
lemma siteAverage_fiber_constant (i : Fin n) (f : Spin n → ℝ)
    {x y : Spin n} (h : sameExcept i x y) :
    siteAverage W i f x = siteAverage W i f y := by
  simp only [siteAverage_eq, siteKernel_same_row W h]


-- @@ L261-271 verbatim
lemma siteAverage_of_fiber_constant (i : Fin n) (f : Spin n → ℝ)
    (hf : ∀ x y, sameExcept i x y → f y = f x) : siteAverage W i f = f := by
  funext x
  calc
    siteAverage W i f x = ∑ y, siteKernel W i x y * f x := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : sameExcept i x y
      · rw [hf x y h]
      · simp [siteKernel, h]
    _ = f x := by rw [← Finset.sum_mul, siteKernel_sum, one_mul]


-- @@ L273-287 verbatim
lemma siteAverage_selfadjoint (i : Fin n) (f g : Spin n → ℝ) :
    mean W (fun x => f x * siteAverage W i g x) =
      mean W (fun x => siteAverage W i f x * g x) := by
  simp only [mean, siteAverage_eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  calc
    gibbs W y * (f y * (siteKernel W i y x * g x)) =
      (gibbs W y * siteKernel W i y x) * (f y * g x) := by ring
    _ = (gibbs W x * siteKernel W i x y) * (f y * g x) := by
      rw [siteKernel_reversible]
    _ = gibbs W x * (siteKernel W i x y * f y * g x) := by ring


-- @@ L289-295 verbatim
lemma siteAverage_orthogonal (i : Fin n) (f g : Spin n → ℝ)
    (hg : siteAverage W i g = g) :
    mean W (fun x => (f x - siteAverage W i f x) * g x) = 0 := by
  have h := siteAverage_selfadjoint W i f g
  rw [hg] at h
  simp only [sub_mul, mean_sub]
  exact sub_eq_zero.mpr h


-- @@ L297-315 verbatim
theorem siteAverage_least_squares (i : Fin n) (f g : Spin n → ℝ)
    (hg : ∀ x y, sameExcept i x y → g y = g x) :
    mean W (fun x => (f x - siteAverage W i f x) ^ 2) ≤
      mean W (fun x => (f x - g x) ^ 2) := by
  have hfixed : siteAverage W i (fun x => siteAverage W i f x - g x) =
      (fun x => siteAverage W i f x - g x) := by
    rw [siteAverage_sub, siteAverage_idempotent, siteAverage_of_fiber_constant W i g hg]
  have horth := siteAverage_orthogonal W i f _ hfixed
  have hexpand : mean W (fun x => (f x - g x) ^ 2) =
      mean W (fun x => (f x - siteAverage W i f x) ^ 2) +
      mean W (fun x => (siteAverage W i f x - g x) ^ 2) +
      2 * mean W (fun x => (f x - siteAverage W i f x) * (siteAverage W i f x - g x)) := by
    rw [← mean_const_mul, ← mean_add, ← mean_add]
    congr 1
    funext x
    ring
  rw [horth, mul_zero, add_zero] at hexpand
  have hnonneg := mean_nonneg W (fun x => sq_nonneg (siteAverage W i f x - g x))
  linarith


-- @@ L317-329 verbatim
lemma siteAverage_form_identity (i : Fin n) (f : Spin n → ℝ) :
    mean W (fun x => (f x - siteAverage W i f x) ^ 2) =
      mean W (fun x => f x * (f x - siteAverage W i f x)) := by
  have hfixed := siteAverage_idempotent W i f
  have horth := siteAverage_orthogonal W i f _ hfixed
  have hexpand : mean W (fun x => f x * (f x - siteAverage W i f x)) =
      mean W (fun x => (f x - siteAverage W i f x) ^ 2) +
      mean W (fun x => (f x - siteAverage W i f x) * siteAverage W i f x) := by
    rw [← mean_add]
    congr 1
    funext x
    ring
  linarith


-- @@ L331-334 verbatim
lemma dirichlet_nonneg (f : Spin n → ℝ) : 0 ≤ dirichlet W f := by
  apply Finset.sum_nonneg
  intro i _
  exact mean_nonneg W (fun _ => sq_nonneg _)


-- @@ L336-348 verbatim
lemma dirichlet_generator (f : Spin n → ℝ) :
    dirichlet W f = -mean W (fun x => f x * (generator W).mulVec f x) := by
  have hgen : (generator W).mulVec f = fun x =>
      ∑ i : Fin n, (siteAverage W i f x - f x) := by
    ext x
    simp [generator, Matrix.sum_mulVec, Matrix.sub_mulVec, siteAverage]
  rw [hgen]
  unfold dirichlet
  simp_rw [← siteAverage_eq, siteAverage_form_identity]
  rw [show (fun x => f x * ∑ i : Fin n, (siteAverage W i f x - f x)) =
      (fun x => ∑ i : Fin n, -(f x * (f x - siteAverage W i f x))) by
    funext x; simp only [Finset.mul_sum]; congr 1; funext i; ring]
  simp only [mean_sum, mean_neg, Finset.sum_neg_distrib, neg_neg]


-- @@ L350-351 verbatim
def linearRest (a : Fin n → ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, a j * spinValue (x j)


-- @@ L353-355 verbatim
lemma linearObservable_split (a : Fin n → ℝ) (i : Fin n) (x : Spin n) :
    linearObservable a x = a i * spinValue (x i) + linearRest a i x := by
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm


-- @@ L357-361 verbatim
lemma linearRest_fiber_constant (a : Fin n → ℝ) (i : Fin n) (x y : Spin n)
    (h : sameExcept i x y) : linearRest a i y = linearRest a i x := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.ne_of_mem_erase hj)]


-- @@ L363-373 verbatim
theorem dirichlet_linear_le (a : Fin n → ℝ) :
    dirichlet W (linearObservable a) ≤ ∑ i : Fin n, a i ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  calc
    mean W (fun x => (linearObservable a x - ∑ y, siteKernel W i x y * linearObservable a y) ^ 2)
        ≤ mean W (fun x => (linearObservable a x - linearRest a i x) ^ 2) :=
      siteAverage_least_squares W i _ _ (linearRest_fiber_constant a i)
    _ = a i ^ 2 := by
      simp_rw [linearObservable_split a i, add_sub_cancel_right, mul_pow, spinValue_sq, mul_one]
      exact mean_const W _


-- @@ L375-375 verbatim
end CriticalSK


-- @@ L377-377 verbatim
end


-- @@ L379-379 verbatim
end OAI
