import OAI.Analysis.FourierLLogL.Thermal.Ginibre
import OAI.Analysis.FourierLLogL.Finite.Quadratic


-- @@ L4-4 verbatim
/-! # Comparisons in form order -/

-- @@ L5-5 verbatim
open Function Set Filter

-- @@ L6-6 verbatim
open scoped Topology BigOperators ComplexConjugate

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-10 verbatim
namespace FourierLLogL.Dyadic.Thermal

-- @@ L11-11 verbatim
open Law Period Real


-- @@ L13-13 verbatim
variable {M : ℕ}


-- @@ L15-18 verbatim
lemma K_add (A D : Form M) (u : Grid M) :
    K (A+D) u = exp (F (A+D)-F A) * (K A u * boltz D u) := by
  simp only [K_eq, boltz, form_add,← exp_add]
  congr 1; ring


-- @@ L20-23 verbatim
lemma ex_tilt (A D : Form M) (f : Grid M → ℝ) :
    (label (A+D)).Ex f =
      exp (F (A+D)-F A) * (label A).Ex (fun y => boltz D y * f y) := by
  simp_rw [label_ex,K_add, expU_ex,mul_assoc,Ex_lmul]


-- @@ L25-27 verbatim
lemma ex_untilt (A D : Form M) (f : Grid M → ℝ) :
    exp (F A-F (A+D)) * (label (A+D)).Ex f = (label A).Ex (fun y => boltz D y * f y) := by
  rw [ex_tilt,← mul_assoc,← exp_add,sub_add_sub_cancel,sub_self,exp_zero,one_mul]


-- @@ L29-31 verbatim
lemma boltz_mean (A D : Form M) :
    (label A).Ex (boltz D) = exp (F A - F (A+D)) := by
  simpa only [Ex_const,mul_one] using (ex_untilt A D fun _ => 1).symm


-- @@ L33-43 verbatim
lemma cred_add_mono {A D : Form M} (hA : 0 ≤ A) (hD : 0 ≤ D) (s : Grid M) :
    cred A s ≤ cred (A+D) s := by
  apply le_of_mul_le_mul_left _ (exp_pos (F A-F (A+D)))
  rw [cred_ex (A+D) s,ex_untilt,← boltz_mean]
  have he (x : Grid M) : boltz D x = ∑ t, q D t * wave t x := (boltz_series _ _).symm
  have hf : boltz D = fun x => ∑ t, q D t * wave t x := funext he
  simp_rw [hf,Finset.sum_mul,mul_assoc, Ex_finset_sum,Ex_lmul]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro x _
  rw [mul_assoc,← cred_ex A x]
  exact mul_le_mul_of_nonneg_left (ginibre hA _ _) (q_nonneg hD _)


-- @@ L45-48 verbatim
lemma cred_mono {A B : Form M} (hA : 0 ≤ A) (h : A ≤ B) (s : Grid M) :
    cred A s ≤ cred B s := by
  have he : B = A+(B-A) := by abel
  simpa only [← he] using cred_add_mono hA (sub_nonneg.mpr h) s


-- @@ L50-58 verbatim
lemma F_increment {A B D : Form M} (hA : 0 ≤ A) (h : A ≤ B) (hD : 0 ≤ D) :
    F (B+D)-F B ≤ F (A+D)-F A := by
  suffices HH : F A-F (A+D) ≤ F B-F (B+D) by linarith
  apply Real.exp_le_exp.mp
  rw [← boltz_mean,← boltz_mean]
  rw [show boltz D = fun x => ∑ t, q D t * wave t x from funext fun x => (boltz_series _ _).symm]
  simp_rw [Ex_finset_sum,Ex_lmul,← cred_ex]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (cred_mono hA h i) (q_nonneg hD _)


-- @@ L60-66 verbatim
lemma mean_energy (A D : Form M) :
    (label (A+D)).Ex (form D) ≤ F (A+D)-F A := by
  apply Real.exp_le_exp.mp
  apply le_trans ((label (A+D)).Ex_exp (form D))
  rw [ex_tilt]
  have H (x : Grid M) : boltz D x * exp (form D x) = 1 := by simp [boltz, ← exp_add]
  simp_rw [H,Ex_const,mul_one]; exact le_rfl


-- @@ L68-70 verbatim
lemma cred_cost (A : Form M) (s : Grid M) : (label A).Ex (cost s) = 1 - cred A s := by
  unfold cost
  simp_rw [Ex_sub,Ex_const,cred_ex]


-- @@ L72-77 verbatim
lemma form_energy_mono {A B D : Form M} (hA : 0 ≤ A) (h : A ≤ B) (hD : 0 ≤ D) :
    (label B).Ex (form D) ≤ (label A).Ex (form D) := by
  unfold form; simp_rw [Ex_finset_sum,Ex_lmul,cred_cost]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hD i)
  rw [sub_le_sub_iff_left]
  exact cred_mono hA h i


-- @@ L79-81 verbatim
lemma q_express (A : Form M) (x : Grid M) : q A x = exp (-F A) * cred A x := by
  rw [cred,F_origin,mul_comm,div_mul_cancel₀]
  exact (q_origin_pos _).ne'


-- @@ L83-87 verbatim
lemma q_compare {A P B : Form M} (hA : 0 ≤ A) (h : A ≤ P) (hh : P ≤ B) (s : Grid M) :
    q P s ≤ exp (-F A) * cred B s := by
  rw [q_express]
  exact mul_le_mul (exp_monotone (neg_le_neg (F_mono h))) (cred_mono (hA.trans h) hh s)
    (cred_nonneg (hA.trans h) s) (exp_nonneg _)


-- @@ L89-89 verbatim
def delta (A : Form M) (s : Grid M) := √((label A).Ex fun i => ‖1-chi s i‖^2)


-- @@ L91-94 verbatim
lemma delta_sq (A : Form M) (s : Grid M) : delta A s ^ 2 = 2*(1-cred A s) := by
  unfold delta
  rw [sq_sqrt ((label A).Ex_nonneg (fun i => sq_nonneg _))]
  simp_rw [norm_phase_sq,Ex_lmul,cred_cost]


-- @@ L96-98 verbatim
lemma delta_zero (A : Form M) : delta A 0 = 0 := by
  simp_rw [delta,chi_zero_left]
  simp [Ex_const]


-- @@ L100-105 verbatim
lemma delta_even (A : Form M) : (delta A).Even := by
  intro x
  have H := delta_sq A x
  have H' := delta_sq A (-x)
  simp_rw [cred,q_even _ _] at H H'
  exact pow_left_inj₀ (sqrt_nonneg _) (sqrt_nonneg _) (by norm_num : 2≠0) |>.mp (H'.trans H.symm)


-- @@ L107-111 verbatim
lemma delta_mono {A B : Form M} (hA : 0 ≤ A) (h : A ≤ B) (s : Grid M) :
    delta B s ≤ delta A s := by
  have h1 := delta_sq A s
  have h2 := delta_sq B s
  nlinarith [cred_mono hA h s,(show 0 ≤ delta A s from sqrt_nonneg _)]


-- @@ L113-120 verbatim
lemma delta_triangle (A : Form M) (s t : Grid M) :
    delta A (s+t) ≤ delta A s + delta A t := by
  let f (s i : Grid M) : ℝ := ‖1-chi s i‖
  refine le_trans ?_ <| quadratic_minkowski (label A) (f s) (f t)
  apply Real.sqrt_le_sqrt ((label A).Ex_mono fun i => ?_)
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  dsimp only [f]; rw [chi_comm,chi_comm s _,chi_comm t _]
  exact norm_phase_add _ _ _


-- @@ L122-128 verbatim
lemma delta_nsmul (A : Form M) (s : Grid M) (k : ℕ) :
    delta A (k•s) ≤ k * delta A s := by
  induction k with
  | zero => simp [delta_zero]
  | succ k ih =>
    rw [add_smul,one_smul]
    exact le_trans (delta_triangle _ _ _) (by push_cast; linarith)


-- @@ L130-139 verbatim
lemma delta_int (A : Form M) (k : ℤ) :
    delta A (k:Grid M) ≤ |(k:ℝ)| * delta A 1 := by
  cases k with
  | ofNat k =>
    simpa [abs_of_nonneg] using delta_nsmul A 1 k
  | negSucc k =>
    have H := delta_even A ((k+1:ℕ):Grid M)
    rw [show ((Int.negSucc k:ℤ):Grid M) = -((k+1:ℕ):Grid M) by simp,H]
    convert delta_nsmul A 1 (k+1) using 1 <;> simp
    left; rw [abs_of_nonpos (by have H := Nat.cast_nonneg (α := ℝ) k; linarith)]; ring


-- @@ L141-141 verbatim
end FourierLLogL.Dyadic.Thermal


-- @@ L143-143 verbatim
end OAI
