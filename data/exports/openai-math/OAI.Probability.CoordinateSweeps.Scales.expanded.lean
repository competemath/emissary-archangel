import Mathlib
import OAI.Probability.CoordinateSweeps.Conditioning
import OAI.Probability.CoordinateSweeps.SparseBound


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-11 verbatim
/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

-- @@ L15-15 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L17-19 verbatim
namespace CoordinateSweeps.Grid
/- Any cut retains exactly the ordered bit list; no coordinate permutation is
introduced into the sweep law. -/

-- @@ L20-37 verbatim
lemma exists_concat_of_length (G : Grid) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hb : G.b=n+m) : ∃ A B : Grid, A.b=n ∧ B.b=m ∧ concat A B=G := by
  rcases G with ⟨b,hpos,bits⟩
  dsimp only at hb
  subst b
  let A : Grid := ⟨n,hn,fun i => bits (Fin.castAdd m i)⟩
  let B : Grid := ⟨m,hm,fun i => bits (Fin.natAdd n i)⟩
  refine ⟨A,B,rfl,rfl,?_⟩
  have he : Fin.addCases A.bits B.bits=bits := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [A]
    | right i => simp [B]
  change Grid.mk (n+m) _ (Fin.addCases A.bits B.bits)=Grid.mk (n+m) _ bits
  rw [he]

/- Cutting the coordinate list in half is balanced because every bit count is
between r and 2r. This avoids choosing a cut by logarithmic rounding. -/

-- @@ L38-49 verbatim
lemma exists_half_concat (G : Grid) (hb : 2 ≤ G.b) :
    ∃ A B : Grid, concat A B=G ∧ A.b<G.b ∧ B.b<G.b ∧ A.b≤B.b ∧ B.b≤2*A.b := by
  let n := G.b/2
  let m := G.b-n
  have hn : 0 < n := by dsimp [n]; omega
  have hm : 0 < m := by dsimp [m,n]; omega
  obtain ⟨A,B,hA,hB,hG⟩ := G.exists_concat_of_length n m hn hm (by dsimp [n,m]; omega)
  refine ⟨A,B,hG,?_,?_,?_,?_⟩
  all_goals simp only [hA,hB]
  all_goals (dsimp [n,m] at *; omega)

-- Reused archived grid logarithm support (InductionBase:858--881).


-- @@ L51-73 verbatim
lemma balanced_logs {A B : Grid} {r : ℕ} (hA : A.Allowed r) (hB : B.Allowed r)
    (hAB : A.b≤B.b) (hBA : B.b≤2*A.b) :
    (1/5 : ℝ)*Real.log (concat A B).size ≤ Real.log A.size ∧
    Real.log A.size ≤ (4/5 : ℝ)*Real.log (concat A B).size ∧
    (1/5 : ℝ)*Real.log (concat A B).size ≤ Real.log B.size ∧
    Real.log B.size ≤ (4/5 : ℝ)*Real.log (concat A B).size := by
  rw [concat_size,Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr A.size_pos.ne')
    (Nat.cast_ne_zero.mpr B.size_pos.ne')]
  have ha := A.log_size_lower hA
  have hb := B.log_size_lower hB
  have hau := A.log_size_upper hA
  have hbu := B.log_size_upper hB
  have hab : (A.b : ℝ)≤B.b := by exact_mod_cast hAB
  have hba : (B.b : ℝ)≤2*A.b := by exact_mod_cast hBA
  have hr : 0 ≤ (r : ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hab' := mul_le_mul_of_nonneg_right hab hr
  have hba' := mul_le_mul_of_nonneg_right hba hr
  have hn := Real.log_nonneg (show (1 : ℝ) ≤ B.size by exact_mod_cast B.size_pos)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith


-- @@ L75-92 verbatim
lemma balanced_sizes {A B : Grid} {r : ℕ} (hA : A.Allowed r) (hB : B.Allowed r)
    (hAB : A.b≤B.b) (hBA : B.b≤2*A.b) :
    ((concat A B).size : ℝ)^((1:ℝ)/5) ≤ A.size ∧
    (A.size : ℝ) ≤ ((concat A B).size : ℝ)^((4:ℝ)/5) ∧
    ((concat A B).size : ℝ)^((1:ℝ)/5) ≤ B.size ∧
    (B.size : ℝ) ≤ ((concat A B).size : ℝ)^((4:ℝ)/5) := by
  have hh := balanced_logs hA hB hAB hBA
  have hs : (0:ℝ)<(concat A B).size := Nat.cast_pos.mpr (concat A B).size_pos
  have ha : (0:ℝ)<A.size := Nat.cast_pos.mpr A.size_pos
  have hb : (0:ℝ)<B.size := Nat.cast_pos.mpr B.size_pos
  rw [Real.rpow_def_of_pos hs,Real.rpow_def_of_pos hs]
  constructor
  · simpa only [Real.exp_log ha,mul_comm] using Real.exp_le_exp.mpr hh.1
  constructor
  · simpa only [Real.exp_log ha,mul_comm] using Real.exp_le_exp.mpr hh.2.1
  constructor
  · simpa only [Real.exp_log hb,mul_comm] using Real.exp_le_exp.mpr hh.2.2.1
  · simpa only [Real.exp_log hb,mul_comm] using Real.exp_le_exp.mpr hh.2.2.2

-- @@ L93-93 verbatim
end CoordinateSweeps.Grid

-- @@ L94-94 verbatim
end


-- @@ L96-96 verbatim
noncomputable section

-- @@ L97-97 verbatim
open scoped BigOperators

-- @@ L98-98 verbatim
open Filter Asymptotics

-- @@ L99-100 verbatim
namespace CoordinateSweeps
-- Literal source constants (ConditionalTarget:509--514), not new hypotheses.


-- @@ L102-104 verbatim
namespace ScalarInduction
/- A fixed polynomial logarithmic loss is uniformly negligible compared
with any strictly larger power, the quantitative choice needed in06. -/

-- @@ L105-117 verbatim
lemma eventually_log_power_bound (u v r C : ℝ) (huv : u < v) (hC : 0 < C) :
    ∀ᶠ s : ℝ in atTop, 0 < s ∧ s^u*(Real.log s)^r ≤ C*s^v := by
  have hh := (isLittleO_log_rpow_rpow_atTop r (sub_pos.mpr huv)).bound hC
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with s hs hs1
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  have hl : 0 ≤ Real.log s := Real.log_nonneg hs1.le
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hl r),
    abs_of_nonneg (Real.rpow_nonneg hs0.le (v-u))] at hs
  refine ⟨hs0,?_⟩
  have hm := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hs0.le u)
  calc
    _ ≤ s^u*(C*s^(v-u)) := hm
    _ = C*s^v := by rw [← mul_assoc,mul_comm (s^u) C,mul_assoc,← Real.rpow_add hs0]; congr 2; ring


-- @@ L119-121 verbatim
lemma eventually_constant_le_power (ε C : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, C ≤ s^ε :=
  (tendsto_atTop.1 (tendsto_rpow_atTop hε)) C


-- @@ L123-146 verbatim
lemma eventually_absorb_hook (q : ℕ) :
    ∀ᶠ s : ℝ in atTop, 1 < s ∧
      (((2*q+1 : ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a)*Real.log (s+1) ≤ s^((9:ℝ)/10) := by
  let C : ℝ := (((2*q+1 : ℕ):ℝ)*4+82*c0)*4
  have hC : 0 < C := by dsimp [C,c0,a]; positivity
  have hp := eventually_log_power_bound ((4:ℝ)/5+2*a) ((9:ℝ)/10) 1 (1/C)
    (by norm_num [a]) (by positivity)
  filter_upwards [hp,eventually_ge_atTop (2:ℝ)] with s hs hs2
  refine ⟨by linarith,?_⟩
  have hl : Real.log (s+1) ≤ 2*Real.log s := by
    calc
      Real.log (s+1) ≤ Real.log (s*s) :=
        Real.log_le_log (by linarith) (by nlinarith)
      _ = 2*Real.log s := by rw [Real.log_mul hs.1.ne' hs.1.ne']; ring
  have hm := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ (((2*q+1 : ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a) by
      dsimp [c0,a]; positivity)
  have hh := mul_le_mul_of_nonneg_left hs.2 hC.le
  simp only [Real.rpow_one] at hh
  have hc : C*(1/C)=1 := mul_one_div_cancel hC.ne'
  calc
    _ ≤ (((2*q+1 : ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a)*(2*Real.log s) := hm
    _ = C*(s^((4:ℝ)/5+2*a)*Real.log s) := by dsimp [C]; ring
    _ ≤ s^((9:ℝ)/10) := by simpa only [← mul_assoc,hc,one_mul] using hh


-- @@ L148-174 verbatim
lemma eventually_absorb_removed :
    ∀ᶠ s : ℝ in atTop, 1 < s ∧
      s^((9:ℝ)/10)+s^(1-a/2)*Real.log s ≤ s^(1-a/4)/(20*Real.sqrt (Real.log s)) := by
  have h1 := eventually_log_power_bound ((9:ℝ)/10) (1-a/4) ((1:ℝ)/2) (1/40)
    (by norm_num [a]) (by norm_num)
  have h2 := eventually_log_power_bound (1-a/2) (1-a/4) ((3:ℝ)/2) (1/40)
    (by norm_num [a]) (by norm_num)
  filter_upwards [h1,h2,eventually_gt_atTop (1:ℝ)] with s h₁ h₂ hs
  refine ⟨hs,?_⟩
  have hlog : 0 < Real.log s := Real.log_pos hs
  have hroot : 0 < Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hlog
  have he : Real.log s*Real.sqrt (Real.log s)=(Real.log s)^((3:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow]
    nth_rw 1 [← Real.rpow_one (Real.log s)]
    rw [← Real.rpow_add hlog]
    norm_num
  rw [← Real.sqrt_eq_rpow] at h₁
  apply (le_div_iff₀ (by positivity : 0 < 20*Real.sqrt (Real.log s))).mpr
  have hh : s^((9:ℝ)/10)*Real.sqrt (Real.log s)+
    s^(1-a/2)*Real.log s*Real.sqrt (Real.log s) ≤ (1/20)*s^(1-a/4) := by
    rw [mul_assoc,he]
    linarith [h₁.2,h₂.2]
  nlinarith

/- Scalar endgame after the *actual* induced placement-cycle estimate.
All representation/path data enter only through their already derived
entropies, multiplicity and cost inequalities. -/

-- @@ L175-191 verbatim
theorem removed_endgame (L F Fg Fd k h b C : ℝ) (_ : ℝ) (err : ℝ)
    (hL : 0 < L) (_ : 0 ≤ F) (hh : 0 ≤ h) (_ : 0 ≤ k)
    (hD : F ≤ Fg+k*L) (hroot : 0 < Real.sqrt L)
    (hcost : (c0+e0)*k*L+Real.log 4*k*b-Fd+err ≤ F/(20*Real.sqrt L)) :
    -(c0+1/Real.sqrt L+1/(20*Real.sqrt L))*Fg+
      (e0-1/Real.sqrt L-1/(20*Real.sqrt L))*(h+k)*L+err-C+Real.log 4*k*b-Fd ≤
      -(c0+1/Real.sqrt L)*F+(e0-1/Real.sqrt L)*h*L-C := by
  have hc0 : 0 ≤ c0 := by norm_num [c0,a]
  have hc : 0 ≤ c0+1/Real.sqrt L+1/(20*Real.sqrt L) :=
    add_nonneg (add_nonneg hc0 (one_div_nonneg.mpr hroot.le)) (by positivity)
  have hmain := mul_le_mul_of_nonneg_left hD hc
  have hhole : 0 ≤ (1/(20*Real.sqrt L))*h*L := by positivity
  have hscale : (1/(20*Real.sqrt L))*F=F/(20*Real.sqrt L) := by ring
  rw [← hscale] at hcost
  nlinarith

/- Child coefficient improvement from a balanced nontrivial split. -/

-- @@ L192-199 verbatim
lemma reciprocal_sqrt_gap {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (htL : t ≤ (4/5)*L) :
    (11/10 : ℝ)/Real.sqrt L ≤ 1/Real.sqrt t := by
  have hLr := Real.sqrt_pos.mpr hL
  have htr := Real.sqrt_pos.mpr ht
  have hsqL := Real.sq_sqrt hL.le
  have hsqt := Real.sq_sqrt ht.le
  apply (div_le_div_iff₀ hLr htr).mpr
  nlinarith [sq_nonneg ((11/10 : ℝ)*Real.sqrt t-Real.sqrt L)]


-- @@ L201-211 verbatim
lemma hook_comparison {L F h cStar eStar E : ℝ} (hL : 0 < L) (hF : 0 ≤ F) (hh : 0 ≤ h)
    (hc : c0+1/Real.sqrt L+1/(20*Real.sqrt L) ≤ cStar)
    (he : eStar+cStar/L ≤ e0-1/Real.sqrt L-1/(20*Real.sqrt L)) :
    -cStar*F+eStar*h*L+cStar*h+E ≤
      -(c0+1/Real.sqrt L+1/(20*Real.sqrt L))*F+
        (e0-1/Real.sqrt L-1/(20*Real.sqrt L))*h*L+E := by
  have h1 := mul_le_mul_of_nonneg_right hc hF
  have h2 := mul_le_mul_of_nonneg_right he (mul_nonneg hh hL.le)
  have heq : cStar/L*(h*L)=cStar*h := by field_simp
  rw [add_mul,heq] at h2
  nlinarith

-- @@ L212-212 verbatim
end ScalarInduction

-- @@ L213-213 verbatim
end CoordinateSweeps

-- @@ L214-214 verbatim
end


-- @@ L216-216 verbatim
noncomputable section

-- @@ L217-217 verbatim
open scoped BigOperators

-- @@ L218-218 verbatim
open Filter Asymptotics

-- @@ L219-219 verbatim
namespace CoordinateSweeps.ScalarInduction

-- @@ L220-242 verbatim
lemma hook_error_bound {s : ℝ} (hs : 1 < s) (q A B p : ℕ) (cStar : ℝ)
    (hc : 0 ≤ cStar) (hc' : cStar ≤ 2*c0)
    (hA : (A:ℝ) ≤ s^((4:ℝ)/5)) (hB : (B:ℝ) ≤ s^((4:ℝ)/5))
    (hp : (p:ℝ) ≤ s^a) :
    (((2*q+1:ℕ):ℝ)*((A+B)*((2*p)*(2*p)):ℕ)+cStar*((A+B)*(41*p^2):ℕ))*Real.log (s+1) ≤
    (((2*q+1:ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a)*Real.log (s+1) := by
  have hs0 : 0<s := by linarith
  have hp2 : (p:ℝ)^2 ≤ s^(2*a) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg p : (0:ℝ)≤p) hp 2
    rw [← Real.rpow_natCast (s^a) 2,← Real.rpow_mul hs0.le] at hh
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [mul_comm a 2] using hh
  have hAB : (A:ℝ)+B ≤ 2*s^((4:ℝ)/5) := by linarith
  have hc0 : 0≤c0 := by linarith [hc, hc']
  have h := mul_le_mul hAB hp2 (by positivity : (0:ℝ)≤(p:ℝ)^2)
    (by positivity : (0:ℝ)≤2*s^((4:ℝ)/5))
  rw [mul_assoc,←Real.rpow_add hs0] at h
  have h' := mul_le_mul_of_nonneg_left h (show 0≤((2*q+1:ℕ):ℝ)*4+82*c0 by positivity)
  have hc'' := mul_le_mul_of_nonneg_right hc' (show 0≤((A:ℝ)+B)*41*(p:ℝ)^2 by positivity)
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by linarith : 1≤ s+1))
  push_cast
  push_cast at h'
  nlinarith


-- @@ L244-248 verbatim
structure MainSizeReady (q : ℕ) (s : ℝ) : Prop where
  one : 1 ≤ Real.log s
  sparse : (100004:ℝ)*s^(1-a/4) ≤ s^(1-(1:ℝ)/1600)
  hook : (((2*q+1:ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a)*Real.log (s+1) ≤ s^((9:ℝ)/10)
  removed : s^((9:ℝ)/10)+s^(1-a/2)*Real.log s ≤ s^(1-a/4)/(20*Real.sqrt (Real.log s))

-- @@ L249-256 verbatim
lemma eventually_mainSizeReady (q : ℕ) : ∀ᶠ s : ℝ in atTop, MainSizeReady q s := by
  have hpow := eventually_constant_le_power (a/4-1/1600) 100004 (by norm_num [a])
  filter_upwards [hpow,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_absorb_hook q,eventually_absorb_removed] with s hp hL hh hr
  refine ⟨hL,?_,hh.2,hr.2⟩
  calc
    _ ≤ s^(a/4-1/1600)*s^(1-a/4) := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (by linarith [hh.1]) _)
    _ = _ := by rw [←Real.rpow_add (by linarith [hh.1] : 0<s)]; congr 1; ring


-- @@ L258-262 verbatim
lemma improved_coefficients {L t : ℝ} (hL : 0<L) (ht : 0<t) (htL : t≤(4/5)*L) :
    c0+(11/10:ℝ)/Real.sqrt L ≤ c0+1/Real.sqrt t ∧
    e0-1/Real.sqrt t ≤ e0-(11/10:ℝ)/Real.sqrt L := by
  have hh := reciprocal_sqrt_gap hL ht htL
  constructor <;> linarith

-- @@ L263-284 verbatim
lemma hook_strengthening {L : ℝ} (hL : 0<L) (hroot : 2/e0 ≤ Real.sqrt L)
    (hc : c0+(11/10:ℝ)/Real.sqrt L ≤ 2*c0) :
    c0+1/Real.sqrt L+1/(20*Real.sqrt L) ≤ c0+(11/10:ℝ)/Real.sqrt L ∧
    e0-(11/10:ℝ)/Real.sqrt L+(c0+(11/10:ℝ)/Real.sqrt L)/L ≤
      e0-1/Real.sqrt L-1/(20*Real.sqrt L) := by
  have hR : 0<Real.sqrt L := Real.sqrt_pos.mpr hL
  have hs := Real.sq_sqrt hL.le
  have hsmall : 20*(c0+(11/10:ℝ)/Real.sqrt L) ≤ Real.sqrt L := by
    have hc0 : 40*c0 ≤ 2/e0 := by norm_num [c0,e0,a]
    linarith
  constructor
  · field_simp
    nlinarith
  · have hx : (c0+(11/10:ℝ)/Real.sqrt L)/L ≤ 1/(20*Real.sqrt L) := by
      apply (div_le_div_iff₀ hL (by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_right hsmall hR.le
      nlinarith
    have he : (11/10:ℝ)/Real.sqrt L=1/Real.sqrt L+2/(20*Real.sqrt L) := by field_simp; ring
    rw [he] at hx ⊢
    have hdiv : (2:ℝ)/(20*Real.sqrt L)=2*(1/(20*Real.sqrt L)) := by ring
    rw [hdiv] at hx ⊢
    linarith

-- @@ L285-285 verbatim
end CoordinateSweeps.ScalarInduction


-- @@ L287-287 verbatim
namespace CoordinateSweeps.ScalarInduction

-- @@ L288-314 verbatim
lemma removed_cost_bound {s k b F Fd : ℝ} {q : ℕ}
    (hs : 1<s) (hk : 0≤k) (hb : 0≤b) (hb' : b≤(e0/4)*Real.log s)
    (hF : s^(1-a/4)≤F) (hFd : 0≤Fd) (hS : MainSizeReady q s)
    (hEnt : s^(1-a/2)≤k → (a/4)*k*Real.log s≤Fd) :
    (c0+e0)*k*Real.log s+Real.log 4*k*b-Fd+s^((9:ℝ)/10) ≤ F/(20*Real.sqrt (Real.log s)) := by
  have hL := Real.log_pos hs
  have hroot : 0<Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hL
  have hl4 : Real.log 4≤3 := by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    linarith
  have hc : (c0+e0)*k*Real.log s+Real.log 4*k*b ≤ (a/4)*k*Real.log s := by
    have hh := mul_le_mul_of_nonneg_right hl4 (mul_nonneg hk hb)
    have hbK := mul_le_mul_of_nonneg_left hb' hk
    norm_num [c0,e0,a] at hbK ⊢
    nlinarith
  have hR : s^((9:ℝ)/10)+s^(1-a/2)*Real.log s ≤ F/(20*Real.sqrt (Real.log s)) :=
    hS.removed.trans (div_le_div_of_nonneg_right hF (by positivity))
  by_cases h : s^(1-a/2)≤k
  · have ht := hEnt h
    have hp := Real.rpow_nonneg (by linarith : 0≤ s) (1-a/2)
    nlinarith [mul_nonneg hp hL.le]
  · have ht : k*Real.log s ≤ s^(1-a/2)*Real.log s := mul_le_mul_of_nonneg_right (le_of_not_ge h) hL.le
    have hh : (a/4)*k*Real.log s ≤ k*Real.log s := by
      have hkp:=mul_nonneg hk hL.le
      norm_num [a]
      nlinarith
    linarith

-- @@ L315-315 verbatim
end CoordinateSweeps.ScalarInduction

-- @@ L316-316 verbatim
end

-- @@ L317-317 verbatim
open scoped Matrix.Norms.L2Operator


-- @@ L319-319 verbatim
end OAI
