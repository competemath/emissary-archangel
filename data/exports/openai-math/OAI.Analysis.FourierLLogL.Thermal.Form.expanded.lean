import OAI.Analysis.FourierLLogL.Dyadic.Discrete

-- @@ L2-2 verbatim
/-! # Thermal forms on the grid -/


-- @@ L4-4 verbatim
open Function Set Filter

-- @@ L5-5 verbatim
open scoped Topology BigOperators ComplexConjugate NNReal

-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-10 verbatim
namespace FourierLLogL.Dyadic.Thermal

-- @@ L11-11 verbatim
open Law Real Period


-- @@ L13-13 verbatim
variable {M : ℕ}


-- @@ L15-16 verbatim
/-- coefficient form. Throughout, nonnegativity of the coefficients means `0 ≤ A`. -/
abbrev Form (M : ℕ) := Grid M → ℝ


-- @@ L18-18 verbatim
def wave (s y : Grid M) : ℝ := (chi s y).re

-- @@ L19-19 verbatim
def cost (s y : Grid M) : ℝ := 1-wave s y

-- @@ L20-20 verbatim
def form (A : Form M) : Grid M → ℝ := fun y => ∑ s, A s * cost s y


-- @@ L22-22 verbatim
lemma wave_even (s : Grid M) : (wave s).Even := by intro x; simp [wave,chi_neg]

-- @@ L23-23 verbatim
lemma wave_comm (s y : Grid M) : wave s y = wave y s := by unfold wave; rw [chi_comm]

-- @@ L24-25 verbatim
lemma wave_abs (s y : Grid M) : |wave s y| ≤ 1 :=
  (Complex.abs_re_le_norm (chi s y)).trans (norm_chi _ _).le

-- @@ L26-26 verbatim
lemma cost_even (s : Grid M) : (cost s).Even := by intro x; unfold cost; rw [wave_even _ x]

-- @@ L27-27 verbatim
lemma cost_symm (s y : Grid M) : cost s y = cost y s := by unfold cost; rw [wave_comm]

-- @@ L28-31 verbatim
lemma cost_bounds (s y : Grid M) : 0 ≤ cost s y ∧ cost s y ≤ 2 := by
  unfold cost
  rcases abs_le.mp (wave_abs s y) with ⟨h1,h2⟩
  constructor <;> linarith


-- @@ L33-39 verbatim
lemma norm_phase_sq (s x : Grid M) : ‖1-chi s x‖^2 = 2*cost s x := by
  unfold cost wave
  have H := Complex.sq_norm (chi s x)
  rw [norm_chi] at H
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re, Complex.one_im] at *
  nlinarith


-- @@ L41-45 verbatim
lemma norm_phase_add (s x y : Grid M) :
    ‖1-chi s (x+y)‖ ≤ ‖1-chi s x‖+‖1-chi s y‖ := by
  rw [chi_add,show 1-chi s x*chi s y = 1-chi s x + chi s x*(1-chi s y) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul,norm_chi,one_mul]


-- @@ L47-52 verbatim
lemma cost_add (s x y : Grid M) : cost s (x+y) ≤ 2*(cost s x+cost s y) := by
  have H1 := norm_phase_sq s x
  have H2 := norm_phase_sq s y
  have H3 := norm_phase_sq s (x+y)
  have H4 := norm_phase_add s x y
  nlinarith [norm_nonneg (1-chi s (x+y)),sq_nonneg (‖1-chi s x‖-‖1-chi s y‖)]


-- @@ L54-54 verbatim
lemma form_zero (x : Grid M) : form 0 x = 0 := by simp [form]


-- @@ L56-57 verbatim
lemma form_at_zero (A : Form M) : form A 0 = 0 := by
  simp [form, cost, wave, chi_zero_right]


-- @@ L59-60 verbatim
lemma form_add (A D : Form M) (x : Grid M) : form (A+D) x = form A x + form D x := by
  simp [form, add_mul, Finset.sum_add_distrib]


-- @@ L62-63 verbatim
lemma form_smul (A : Form M) (t : ℝ) (x : Grid M) : form (t • A) x = t*form A x := by
  simp [form, mul_assoc, Finset.mul_sum]


-- @@ L65-70 verbatim
lemma form_sum {ι : Type*} (s : Finset ι) (f : ι → Form M) (x : Grid M) :
    form (∑ i ∈ s, f i) x = ∑ i ∈ s, form (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,form_add,ih]


-- @@ L72-72 verbatim
lemma form_even (A : Form M) : (form A).Even := by intro x; simp [form, cost_even _ x]


-- @@ L74-76 verbatim
lemma form_mono {A D : Form M} (h : A ≤ D) : form A ≤ form D := by
  intro y
  exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (h s) (cost_bounds _ _).1


-- @@ L78-79 verbatim
lemma form_nonneg {A : Form M} (h : 0 ≤ A) (y : Grid M) : 0 ≤ form A y := by
  simpa only [form_zero] using form_mono h y


-- @@ L81-87 verbatim
lemma form_triangle {A : Form M} (h : 0 ≤ A) (x y : Grid M) :
    form A (x+y) ≤ 2*(form A x+form A y) := by
  unfold form
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i hi
  apply le_trans (mul_le_mul_of_nonneg_left (cost_add _ _ _) (h i))
  exact le_of_eq (by ring)


-- @@ L89-89 verbatim
def boltz (A : Form M) (y : Grid M) : ℝ := exp (-form A y)

-- @@ L90-90 verbatim
def q (A : Form M) (u : Grid M) : ℝ := (fc (fun y => (↑(boltz A y):ℂ)) u).re


-- @@ L92-92 verbatim
lemma boltz_even (A : Form M) : (boltz A).Even := by intro x; simp [boltz,form_even _ x]

-- @@ L93-93 verbatim
lemma boltz_pos (A : Form M) (y : Grid M) : 0 < boltz A y := exp_pos _

-- @@ L94-96 verbatim
lemma boltz_sum (A D : Form M) (y : Grid M) :
    boltz (A+D) y = boltz A y * boltz D y := by
  simp [boltz,form_add, exp_add,mul_comm]


-- @@ L98-99 verbatim
lemma q_even (A : Form M) : (q A).Even := fun x => congrArg Complex.re <|
  fc_neg_even (fun y => (↑(boltz A y):ℂ)) (fun y => by simp [boltz_even _ y]) x


-- @@ L101-102 verbatim
lemma cq (A : Form M) (x : Grid M) :
    (↑(q A x):ℂ) = fc (fun y => (↑(boltz A y):ℂ)) x := real_fc_even _ (boltz_even _) _


-- @@ L104-107 verbatim
lemma q_origin (A : Form M) : q A 0 = expU (boltz A) := by
  apply Complex.ofReal_inj.mp
  rw [cq, ← expU_real,fc]
  simp_rw [neg_zero,chi_zero_left,mul_one]


-- @@ L109-112 verbatim
lemma q_origin_pos (A : Form M) : 0 < q A 0 := by
  rw [q_origin]; unfold expU
  rw [smul_eq_mul]
  exact mul_pos (side_pos _) <| Finset.sum_pos (fun i _ => boltz_pos _ _) Finset.univ_nonempty


-- @@ L114-117 verbatim
lemma q_total (A : Form M) : ∑ x, q A x = 1 := by
  have H := invert_fc (fun y => (↑(boltz A y):ℂ)) 0
  simp_rw [← cq,chi_zero_right,mul_one,← Complex.ofReal_sum] at H
  simpa only [boltz,form_at_zero,neg_zero,Real.exp_zero,Complex.ofReal_inj] using H


-- @@ L119-124 verbatim
lemma q_add (A D : Form M) (u : Grid M) :
    q (A+D) u = ∑ v : Grid M, q A v * q D (u-v) := by
  apply Complex.ofReal_inj.mp
  rw [cq]; push_cast
  simp_rw [cq,boltz_sum,Complex.ofReal_mul]
  exact fc_prod _ _ _


-- @@ L126-130 verbatim
lemma boltz_series (A : Form M) (u : Grid M) :
    ∑ v : Grid M, q A v * wave v u = boltz A u := by
  have H := congrArg Complex.re <| invert_fc (fun y => (↑(boltz A y):ℂ)) u
  simp only [← cq,Complex.re_sum, Complex.re_ofReal_mul,Complex.ofReal_re] at H
  exact H


-- @@ L132-132 verbatim
def F (A : Form M) := -log (q A 0)

-- @@ L133-133 verbatim
def K (A : Form M) (x : Grid M) : ℝ := boltz A x / q A 0


-- @@ L135-135 verbatim
lemma F_origin (A : Form M) : exp (-F A) = q A 0 := by rw [F,neg_neg,exp_log (q_origin_pos A)]

-- @@ L136-139 verbatim
lemma F_zero : F (0:Form M) = 0 := by
  simp_rw [F,q_origin,expU_ex]; unfold boltz
  simp_rw [form_zero]
  simp only [neg_zero, exp_zero, Ex_const, log_one, neg_zero]


-- @@ L141-146 verbatim
lemma F_mono {A B : Form M} (h : A ≤ B) : F A ≤ F B := by
  unfold F
  apply neg_le_neg
  apply Real.log_le_log (q_origin_pos _)
  rw [q_origin,q_origin,expU_ex,expU_ex]
  exact Ex_mono _ fun x => exp_monotone (neg_le_neg (form_mono h x))


-- @@ L148-152 verbatim
lemma K_eq (A : Form M) (x : Grid M) : K A x = exp (F A-form A x) := by
  rw [K,boltz,← F_origin]
  rw [← exp_sub]
  congr 1
  ring


-- @@ L154-154 verbatim
lemma K_even (A : Form M) : (K A).Even := fun y => by simp [K,boltz_even _ y]


-- @@ L156-156 verbatim
lemma K_pos (A : Form M) (x : Grid M) : 0 < K A x := div_pos (boltz_pos _ _) (q_origin_pos _)


-- @@ L158-160 verbatim
lemma K_total (A : Form M) : expU (K A) = 1 := by
  unfold K
  simp_rw [expU_ex,div_eq_mul_inv,Ex_mul,← expU_ex,← q_origin,mul_inv_cancel₀ (q_origin_pos _).ne']


-- @@ L162-166 verbatim
/-- Label noise law centered at zero relative to counting measure. -/
def label (A : Form M) : Law (Grid M) :=
  ⟨fun x => side M * K A x, fun x => mul_nonneg (side_pos _).le (K_pos _ _).le, by
    rw [← Finset.mul_sum]
    exact K_total _⟩


-- @@ L168-168 verbatim
lemma label_apply (A : Form M) (x : Grid M) : label A x = side M * K A x := rfl


-- @@ L170-171 verbatim
lemma label_pos (A : Form M) (x : Grid M) : 0 < label A x :=
  mul_pos (side_pos _) (K_pos _ _)


-- @@ L173-175 verbatim
lemma label_ex (A : Form M) (f : Grid M → ℝ) :
    (label A).Ex f = expU fun x => K A x * f x := by
  simp_rw [expU_ex,Ex,uniform_side,label_apply,mul_assoc]


-- @@ L177-179 verbatim
lemma label_cx (A : Form M) (f : Grid M → ℂ) :
    (label A).Cx f = expU fun x => (K A x:ℂ) * f x := by
  simp_rw [expU_cx,Cx,uniform_side,label_apply,Complex.ofReal_mul,mul_assoc]


-- @@ L181-181 verbatim
def cred (A : Form M) (u : Grid M) := q A u/q A 0


-- @@ L183-186 verbatim
lemma cred_eq (A : Form M) (u : Grid M) : (↑(cred A u):ℂ) = (label A).Cx (chi u) := by
  rw [label_cx]
  simp_rw [K,div_eq_inv_mul,Complex.ofReal_mul,mul_assoc]
  rw [expU_lmul,expU_coeff,cred,div_eq_inv_mul,Complex.ofReal_mul,← cq,q_even _ u]


-- @@ L188-190 verbatim
lemma cred_ex (A : Form M) (u : Grid M) : cred A u = (label A).Ex (wave u) := by
  unfold wave
  simpa only [re_Cx,Complex.ofReal_re,wave] using congrArg Complex.re (cred_eq A u)


-- @@ L192-194 verbatim
lemma cred_norm (A : Form M) (u : Grid M) : |cred A u| ≤ 1 := by
  have H := norm_Cx_unit (label A) (chi u) (fun x => (norm_chi _ _).le)
  rwa [← cred_eq,Complex.norm_real, Real.norm_eq_abs] at H


-- @@ L196-196 verbatim
end FourierLLogL.Dyadic.Thermal


-- @@ L198-198 verbatim
end OAI
