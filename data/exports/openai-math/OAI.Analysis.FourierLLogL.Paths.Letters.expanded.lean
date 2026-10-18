import OAI.Analysis.FourierLLogL.Paths.Trip

-- @@ L2-2 verbatim
/-! # The uniform output path -/


-- @@ L4-4 verbatim
open Function Set Filter

-- @@ L5-5 verbatim
open scoped Topology BigOperators ComplexConjugate

-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-10 verbatim
namespace FourierLLogL.Dyadic.Procedure.Paths

-- @@ L11-11 verbatim
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot

-- @@ L12-12 verbatim
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}

-- @@ L13-13 verbatim
open scoped Classical



-- @@ L16-16 verbatim
abbrev Vector (M : ℕ) := Grid M → ℂ


-- @@ L18-18 verbatim
def dye (s : Scene M) := s.fund.mood

-- @@ L19-19 verbatim
def matter (s : Scene M) := hist s (channel (dye s))

-- @@ L20-20 verbatim
def letter (s : Scene M) (u z : Grid M) := fz s.here s.wage s.norm (dye s) u z


-- @@ L22-22 verbatim
def shell (s : Scene M) := Procedure.diff s (channel (dye s))

-- @@ L23-24 verbatim
def factor (s : Scene M) (u z : Grid M) :=
    (letter (s.smaller false) u z-letter (s.smaller true) u z)/2

-- @@ L25-26 verbatim
def gain (s : Scene M) (u : Grid M) :=
    (scalar (s.smaller false) u-scalar (s.smaller true) u)/2

-- @@ L27-27 verbatim
def fax (s : Scene M) := fisher s (channel (dye s))


-- @@ L29-30 verbatim
lemma matter_nonneg {s : Scene M} (h : Fit s) (z) : 0 ≤ matter s z :=
    nonnegative_hist s h.ready.2 h.pos.le _ _

-- @@ L31-32 verbatim
lemma matter_sum {s : Scene M} (h : Fit s) : ∑ z, matter s z=share s :=
    total_hist _ h.ready.1 _

-- @@ L33-34 verbatim
lemma matter_norm {s : Scene M} (h : Fit s) (u z) : ‖letter s u z‖ ≤ matter s z :=
    fz_norm _ h.ready.2 h.pos.le _ _ _

-- @@ L35-36 verbatim
lemma scalar_label (s : Scene M) (u : Grid M) : scalar s u=∑ z, letter s u z :=
    scalar_series s _ u


-- @@ L38-40 verbatim
lemma scalar_norm {s : Scene M} (h : Fit s) (u) : ‖scalar s u‖ ≤ share s := by
  rw [scalar_label, ← matter_sum h]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => matter_norm h u i)


-- @@ L42-44 verbatim
lemma matter_split {s : Scene M} (h : Climb s) (z : Grid M) :
    matter (s.smaller false) z+matter (s.smaller true) z=2*matter s z :=
    hist_split s h.fit.ready.1.1 h.deep _ _


-- @@ L46-48 verbatim
lemma letter_split {s : Scene M} (h : Climb s) (u z : Grid M) :
    letter (s.smaller false) u z+letter (s.smaller true) u z=2*letter s u z :=
    fz_split s h.fit.ready.1.1 h.deep _ _ _


-- @@ L50-52 verbatim
lemma scalar_split' {s : Scene M} (h : Climb s) (u) :
    scalar (s.smaller false) u+scalar (s.smaller true) u=2*scalar s u := by
  simp_rw [scalar_label,←Finset.sum_add_distrib,Finset.mul_sum,letter_split h]


-- @@ L54-58 verbatim
lemma matter_jump {s : Scene M} (h : Climb s) (b) (z) :
    matter (s.smaller b) z=matter s z+curl b* shell s z := by
  have hi := matter_split h z
  have H : shell s z=(matter (s.smaller false) z-matter (s.smaller true) z)/2 := rfl
  cases b <;> simp [H,curl] <;> linarith


-- @@ L60-65 verbatim
private lemma symmetric_curl (f : Bool → ℂ) (a : ℂ)
    (h : f false+f true=2*a) (b : Bool) :
    f b=a+(curl b:ℂ)*((f false-f true)/2) := by
  rw [show a=(f false+f true)/2 by rw [h]; ring]
  cases b <;> simp only [curl,Bool.false_eq_true,↓reduceIte]
  all_goals push_cast; ring


-- @@ L67-69 verbatim
lemma letter_jump {s : Scene M} (h : Climb s) (b) (u z : Grid M) :
    letter (s.smaller b) u z=letter s u z+(curl b:ℂ)*factor s u z :=
    symmetric_curl (fun b => letter (s.smaller b) u z) _ (letter_split h u z) _

-- @@ L70-72 verbatim
lemma scalar_jump {s : Scene M} (h : Climb s) (b u) :
    scalar (s.smaller b) u=scalar s u+(curl b:ℂ)*gain s u :=
    symmetric_curl (fun b => scalar (s.smaller b) u) _ (scalar_split' h u) _


-- @@ L74-86 verbatim
lemma matter_drain {s q : Scene M} (hh : Ideal s q) (u z : Grid M) :
    ‖letter s u z-letter q u z‖ ≤ matter s z-matter q z := by
  classical
  unfold matter hist letter fz
  unfold omegaObs dye wt
  rw [hh.lower.here,hh.lower.flat,hh.lower.fund,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum; intro i _
  rw [← sub_mul,← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_chi,mul_one]
  refine le_of_eq (abs_of_nonneg (sub_nonneg.mpr ?_))
  apply mul_le_mul_of_nonneg_right _ ((channel _ _).nonneg _)
  apply div_le_div_of_nonneg_right _ hh.fit.pos.le
  apply mul_le_mul_of_nonneg_left (hh.lower.antitone hh.fit.ready.2 i) ((s.here.dice M).nonneg _)


-- @@ L88-92 verbatim
lemma scalar_drain {b : Beat M} (h : Ideal b.pre b.post) (u) :
    ‖scalar b.pre u-scalar b.post u‖ ≤ killed b := by
  simp_rw [scalar_label]
  rw [h.kill_eq,← matter_sum h.fit,← matter_sum h.climb.fit,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => matter_drain h u i)


-- @@ L94-100 verbatim
lemma shell_abs {s : Scene M} (h : Climb s) (z) :
    |shell s z| ≤ matter s z := by
  have H (b) := matter_nonneg (h.child b) z
  simp_rw [matter_jump h] at H
  rw [abs_le]
  constructor <;> linarith [show 0 ≤ matter s z+1*shell s z from H false,
    show 0 ≤ matter s z+-1*shell s z from H true]


-- @@ L102-104 verbatim
lemma norm_halfcomplex (x y : ℂ) :
    ‖(x-y)/2‖ ≤ (‖x‖+‖y‖)/2 := by
  rw [norm_div]; norm_num; gcongr; exact norm_sub_le x y


-- @@ L106-110 verbatim
lemma factor_norm {s : Scene M} (h : Climb s) (u z : Grid M) :
    ‖factor s u z‖ ≤ matter s z := by
  have H (b) := matter_norm (h.child b) u z
  apply (norm_halfcomplex _ _).trans
  linarith [matter_split h z,H true,H false]


-- @@ L112-112 verbatim
def billFax (b : Beat M) := fax b.post

-- @@ L113-113 verbatim
def fullFax (l : Path M) := subtotal billFax l


-- @@ L115-117 verbatim
lemma fax_floor {s : Scene M} (h : Climb s) : 0 ≤ fax s ∧ fax s ≤ 2 :=
    let H := fisher_range s h.fit.ready.1.1 h.deep h.fit.ready.2 h.fit.pos.le (channel (dye s))
    ⟨H.1,H.2.trans h.tight⟩


-- @@ L119-120 verbatim
lemma trip_fax {x : Grid M} {l : Path M} (h : Trip x s l) : 0 ≤ fullFax l :=
    trip_nonneg h (fun _ hh => (fax_floor hh.climb).1)


-- @@ L122-124 verbatim
/-- Normalized scalar transform along part (plateau jumps) on path x. -/
def proceeds (x u : Grid M) (b : Beat M) :=
    (blow x b:ℂ)*gain b.post u

-- @@ L125-126 verbatim
def duties (x u : Grid M) (b : Beat M) (z : Grid M) :=
    (blow x b:ℂ)*factor b.post u z


-- @@ L128-129 verbatim
lemma gain_series (u : Grid M) (s : Scene M) : gain s u = ∑ z, factor s u z := by
  simp_rw [gain,factor, ← Finset.sum_div, Finset.sum_sub_distrib,scalar_label]

-- @@ L130-132 verbatim
lemma gain_norm {s : Scene M} (h : Climb s) (u : Grid M) : ‖gain s u‖ ≤ share s := by
  rw [gain_series,← matter_sum h.fit]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => factor_norm h u i)



-- @@ L135-135 verbatim
end FourierLLogL.Dyadic.Procedure.Paths


-- @@ L137-137 verbatim
end OAI
