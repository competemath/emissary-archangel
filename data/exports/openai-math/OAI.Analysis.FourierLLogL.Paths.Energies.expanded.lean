import OAI.Analysis.FourierLLogL.Paths.Letters

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
def duet (x y : ℂ) : ℝ := (conj x*y).re

-- @@ L17-17 verbatim
lemma duet_zero (x : ℂ) : duet x 0=0 := by simp [duet]

-- @@ L18-19 verbatim
lemma duet_self (x : ℂ) : duet x x=‖x‖^2 := by
  rw [duet,mul_comm,Complex.mul_conj,Complex.sq_norm]; rfl

-- @@ L20-20 verbatim
lemma duet_add (x y z : ℂ) : duet x (y+z)=duet x y+duet x z := by simp [duet,mul_add]

-- @@ L21-21 verbatim
lemma duet_sub (x y z : ℂ) : duet x (y-z)=duet x y-duet x z := by simp [duet,mul_sub]

-- @@ L22-23 verbatim
lemma duet_scale (x y : ℂ) (c : ℝ) : duet x ((c:ℂ)*y)=c* duet x y := by
  rw [duet,duet,mul_left_comm,Complex.re_ofReal_mul]

-- @@ L24-26 verbatim
lemma duet_limit (x y : ℂ) : |duet x y| ≤ ‖x‖* ‖y‖ := by
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul,Complex.norm_conj]

-- @@ L27-29 verbatim
lemma duet_inc (x y : ℂ) : ‖x+y‖^2=‖x‖^2+2*duet x y+‖y‖^2 := by
  rw [Complex.sq_norm,Complex.sq_norm,Complex.sq_norm,duet]
  simp [Complex.normSq_apply]; ring


-- @@ L31-31 verbatim
def meanV (s : Scene M) (u z : Grid M) := letter s u z / (matter s z:ℂ)

-- @@ L32-32 verbatim
def sun (s : Scene M) (u z : Grid M) := matter s z * ‖meanV s u z‖^2

-- @@ L33-33 verbatim
def pierce (s : Scene M) (z : Grid M) := shell s z^2 / matter s z

-- @@ L34-35 verbatim
def nub (s : Scene M) (u z : Grid M) :=
    factor s u z-(shell s z:ℂ)*meanV s u z


-- @@ L37-47 verbatim
lemma mean_hold (s : Scene M) (h : Fit s) (u z : Grid M) :
    (matter s z:ℂ)*meanV s u z=letter s u z ∧ ‖meanV s u z‖ ≤ 1 := by
  have H := matter_norm h u z
  rcases eq_or_lt_of_le (matter_nonneg h z) with ha|ha
  · have hi : letter s u z=0 := norm_le_zero_iff.mp (by linarith)
    simp [meanV,← ha,hi]
  unfold meanV; constructor
  · have hh : (matter s z:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha.le]
  exact (div_le_one ha).mpr H


-- @@ L49-52 verbatim
lemma sun_rays {s : Scene M} (h : Fit s) (u z) :
    0 ≤ sun s u z ∧ sun s u z ≤ matter s z :=
  ⟨mul_nonneg (matter_nonneg h z) (sq_nonneg _),mul_le_of_le_one_right (matter_nonneg h _)
    (pow_le_one₀ (norm_nonneg _) (mean_hold _ h _ _).2)⟩


-- @@ L54-62 verbatim
lemma sun_energy {s : Scene M} (h : Fit s) (u : Grid M) :
    energy s u=∑ z, sun s u z := by
  unfold energy energyZ; refine Finset.sum_congr rfl fun z _ => ?_
  have he := mean_hold _ h u z
  change ‖letter s u z‖^2 / matter s z=_
  rw [← he.1,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (matter_nonneg h z)]
  unfold sun; by_cases h : matter s z=0
  · rw [h]; ring_nf
  field_simp


-- @@ L64-70 verbatim
lemma energy_small {s : Scene M} (h : Fit s) (u) :
    0 ≤ energy s u ∧ energy s u ≤ share s := by
  rw [sun_energy h]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (sun_rays h _ _).1)
  rw [←matter_sum h]
  exact Finset.sum_le_sum fun i _ => (sun_rays h _ _).2


-- @@ L72-73 verbatim
lemma pierce_nonneg {s : Scene M} (h : Fit s) (z) : 0 ≤ pierce s z :=
    div_nonneg (sq_nonneg _) (matter_nonneg h _)


-- @@ L75-80 verbatim
lemma shell_sq {s : Scene M} (h : Climb s) (z) :
    shell s z^2=matter s z*pierce s z := by
  by_cases he : matter s z=0
  · have hx := shell_abs h z; rw [he,abs_nonpos_iff] at hx
    rw [he,hx]; ring
  unfold pierce; field_simp


-- @@ L82-83 verbatim
def mist (u : Grid M) (s t : Scene M) (z : Grid M) :=
    matter t z * ‖meanV t u z-meanV s u z‖^2

-- @@ L84-85 verbatim
def dew (u : Grid M) (s : Scene M) (z : Grid M) :=
    (mist u s (s.smaller false) z+mist u s (s.smaller true) z)/2

-- @@ L86-86 verbatim
def shower (u : Grid M) (s : Scene M) := ∑ z, dew u s z

-- @@ L87-87 verbatim
def gust (s : Scene M) (u : Grid M) := (energy (s.smaller false) u-energy (s.smaller true) u)/2


-- @@ L89-90 verbatim
lemma mist_nonneg (u : Grid M) (s t : Scene M) (h : Fit t) (z) : 0 ≤ mist u s t z :=
    mul_nonneg (matter_nonneg h _) (sq_nonneg _)

-- @@ L91-93 verbatim
lemma mist_low (u : Grid M) {s : Scene M} (h : Climb s) (b z) :
    mist u s (s.smaller b) z ≤ 2*dew u s z := by
  cases b <;> unfold dew <;> linarith [mist_nonneg u s _ (h.child false) z,mist_nonneg u s _ (h.child true) z]

-- @@ L94-96 verbatim
lemma dew_nonneg (u : Grid M) {s : Scene M} (h : Climb s) (z) : 0 ≤ dew u s z :=
    div_nonneg (add_nonneg (mist_nonneg _ _ _ (h.child false) _)
      (mist_nonneg _ _ _ (h.child true) _)) (by norm_num)

-- @@ L97-98 verbatim
lemma shower_nonneg {u : Grid M} {s : Scene M} (h : Climb s) : 0 ≤ shower u s :=
    Finset.sum_nonneg fun _ _ => dew_nonneg _ h _


-- @@ L100-105 verbatim
lemma mean_shift {s : Scene M} (h : Climb s) (b) (u z) :
    (matter (s.smaller b) z:ℂ)*(meanV (s.smaller b) u z-meanV s u z) =
      (curl b:ℂ)*nub s u z := by
  rw [mul_sub,(mean_hold _ (h.child b) _ _).1,matter_jump h b,
    letter_jump h,← (mean_hold _ h.fit _ _).1,nub]
  push_cast; ring



-- @@ L108-121 verbatim
lemma sun_shift {s : Scene M} (h : Climb s) (u b z) :
    sun (s.smaller b) u z = sun s u z+curl b *
      (shell s z*‖meanV s u z‖^2 + 2*duet (meanV s u z) (nub s u z))+
        mist u s (s.smaller b) z := by
  let v := meanV s u z; let w := meanV (s.smaller b) u z-v
  let m := matter (s.smaller b) z
  have he : meanV (s.smaller b) u z=v+w := by unfold w; ring
  have HH : m*duet v w=curl b*duet v (nub s u z) := by rw [←duet_scale,
    show (m:ℂ)*w=_ from mean_shift h _ _ _,duet_scale]
  change m*‖meanV (s.smaller b) u z‖^2=matter s z* ‖v‖^2+curl b*(shell s z*‖v‖^2+_) +m*‖w‖^2
  rw [he,duet_inc]
  change m*_=matter s z*‖v‖^2+curl b* (shell s z*‖v‖^2+2*duet v (nub s u z))+_
  have he' : m=matter s z + curl b * shell s z := matter_jump h b z
  nlinarith [show m*‖v‖^2=(matter s z+curl b*shell s z)*‖v‖^2 by rw [he']]


-- @@ L123-132 verbatim
lemma wet_average (s : Scene M) (h : Climb s) (u) :
    (energy (s.smaller false) u+energy (s.smaller true) u)/2 =
      energy s u+shower u s := by
  rw [sun_energy (h.child false),sun_energy (h.child true),sun_energy h.fit,
    ← Finset.sum_add_distrib, Finset.sum_div,shower,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [sun_shift h,sun_shift h]
  unfold dew; simp [curl]
  ring


-- @@ L134-137 verbatim
lemma wet_walk (s : Scene M) (h : Climb s) (u b) :
    energy (s.smaller b) u=energy s u+shower u s+curl b*gust s u := by
  rw [←wet_average s h u,gust]
  cases b <;> norm_num [curl] <;> ring


-- @@ L139-143 verbatim
lemma matter_max {s : Scene M} (h : Climb s) (b z) :
    matter (s.smaller b) z ≤ 2*matter s z := by
  have hi := matter_nonneg (h.child true) z
  have hj := matter_nonneg (h.child false) z
  cases b <;> linarith [matter_split h z]


-- @@ L145-146 verbatim
lemma norm_scaleC (x : ℝ) (v : ℂ) :
    ‖(x:ℂ)*v‖=|x| * ‖v‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]


-- @@ L148-163 verbatim
lemma nub_innovation (s : Scene M) (h : Climb s) (u z) :
    ‖nub s u z‖^2 ≤ 4*matter s z*dew u s z := by
  let q := s.smaller false
  let x := matter q z
  have hp : 0 ≤ x := matter_nonneg (h.child false) z
  have hi : ‖nub s u z‖^2=x*mist u s q z := by
    have HH := congrArg (fun x : ℂ => ‖x‖) (mean_shift h false u z)
    change ‖(x:ℂ)*(meanV q u z-meanV s u z)‖=‖(curl false:ℂ)*nub s u z‖ at HH
    rw [norm_scaleC,norm_scaleC,curl_unit,one_mul,abs_of_nonneg hp] at HH
    rw [← HH]; unfold mist x; ring
  rw [hi]
  have H : x ≤ 2*matter s z := matter_max h false _
  have he := mul_le_mul H (mist_low u h false z) (mist_nonneg u s _ (h.child false) z)
    (hp.trans H)
  change x*mist u s q z ≤ _ at he
  linarith


-- @@ L165-204 verbatim
/-- Relating mean and energy at removals. -/
lemma drain_changes {s q : Scene M} (h : Ideal s q) (u z) :
    let k := matter s z-matter q z
    mist u s q z ≤ 4*k ∧ |sun s u z-sun q u z| ≤ 8*k := by
  let w := meanV s u z; let v := meanV q u z
  let r := matter s z; let t := matter q z
  intro k
  have hw := mean_hold s h.fit u z; have hv := mean_hold q h.climb.fit u z
  have H := matter_drain h u z
  rw [← hw.1,← hv.1] at H
  have hr : 0 ≤ r := matter_nonneg h.fit z
  have ht : 0 ≤ t := matter_nonneg h.climb.fit z
  change ‖(r:ℂ)*w-(t:ℂ)*v‖ ≤ k at H
  have hk := (norm_nonneg _).trans H
  have hh : k=r-t := rfl
  have H1 : t* ‖w-v‖ ≤ 2*k := by
    rw [show t* ‖w-v‖=‖(t:ℂ)*(w-v)‖ by rw [norm_scaleC,abs_of_nonneg ht]]
    rw [show (t:ℂ)*(w-v)=(r*w-t*v)-(k:ℂ)*w by rw [hh]; push_cast; ring]
    apply le_trans (norm_sub_le _ _)
    rw [norm_scaleC,abs_of_nonneg hk]
    have HH : ‖w‖ ≤ 1 := hw.2
    nlinarith
  have Hw : ‖w‖ ≤ 1 := hw.2
  have Hv : ‖v‖ ≤ 1 := hv.2
  have HE : ‖w-v‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  constructor
  · change t* ‖v-w‖^2 ≤ _
    rw [norm_sub_rev]
    nlinarith [mul_le_mul_of_nonneg_left HE ht,norm_nonneg (w-v),
      mul_le_mul_of_nonneg_left HE (mul_nonneg ht (norm_nonneg (w-v)))]
  · change |r* ‖w‖^2-t* ‖v‖^2| ≤ _
    rw [show r* ‖w‖^2-t* ‖v‖^2=k*‖w‖^2+t*(‖w‖-‖v‖)*(‖w‖+‖v‖) by rw [hh]; ring]
    apply le_trans (abs_add_le _ _)
    have ht' : |‖w‖-‖v‖| ≤ ‖w-v‖ := abs_norm_sub_norm_le w v
    rw [abs_of_nonneg (mul_nonneg hk (sq_nonneg _)), abs_mul,abs_mul,
      abs_of_nonneg ht,abs_of_nonneg (add_nonneg (norm_nonneg w) (norm_nonneg v))]
    have HE' : t*|‖w‖-‖v‖| ≤ 2*k := (mul_le_mul_of_nonneg_left ht' ht).trans H1
    have hW' : k*‖w‖^2 ≤ k := mul_le_of_le_one_right hk
      (pow_le_one₀ (norm_nonneg _) Hw)
    nlinarith [norm_nonneg v,norm_nonneg w]


-- @@ L206-211 verbatim
lemma energy_drain {b : Beat M} (h : Ideal b.pre b.post) (u) :
    |energy b.pre u-energy b.post u| ≤ 8*killed b := by
  rw [sun_energy h.fit,sun_energy h.climb.fit,h.kill_eq,←matter_sum h.fit,←matter_sum h.climb.fit,
    ← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum fun i _ => (drain_changes h u i).2



-- @@ L214-214 verbatim
end FourierLLogL.Dyadic.Procedure.Paths


-- @@ L216-216 verbatim
end OAI
