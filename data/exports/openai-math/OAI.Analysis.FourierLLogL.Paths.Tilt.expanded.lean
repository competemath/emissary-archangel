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
/-! At scalar levels it is convenient to analyze each of the four real projections (± real, ± imaginary). -/


-- @@ L18-18 verbatim
abbrev Face := Bool × Bool

-- @@ L19-19 verbatim
def part (d : Face) (x : ℂ) := curl d.2*(if d.1=true then x.im else x.re)

-- @@ L20-22 verbatim
lemma part_bounded (d : Face) (x : ℂ) : |part d x| ≤ ‖x‖ := by
  rw [part,abs_mul,curl_unit,one_mul]
  split; exact Complex.abs_im_le_norm _; exact Complex.abs_re_le_norm _

-- @@ L23-23 verbatim
lemma part_zero (d : Face) : part d 0=0 := by rcases d with ⟨b,c⟩; cases b <;> simp [part]

-- @@ L24-25 verbatim
lemma part_add (d : Face) (x y : ℂ) : part d (x+y)=part d x+part d y := by
  rcases d with ⟨b,c⟩; cases b <;> simp [part,mul_add]

-- @@ L26-27 verbatim
lemma part_diff (d : Face) (x y : ℂ) : part d (x-y)=part d x-part d y := by
  rcases d with ⟨b,c⟩; cases b <;> simp [part,mul_sub]

-- @@ L28-29 verbatim
lemma part_mul (d : Face) (x : ℂ) (c : ℝ) : part d (c*x)=c*part d x := by
  rcases d with ⟨b,r⟩; cases b <;> simp [part,mul_left_comm]


-- @@ L31-32 verbatim
/-- Local Huber function on a window of length 10 b. -/
private def slide (w x : ℝ) := if x < -w then -w else if w < x then w else x

-- @@ L33-34 verbatim
private def smooth (w x : ℝ) :=
    2*x*slide w x-(slide w x)^2

-- @@ L35-37 verbatim
private lemma slide_range {w x : ℝ} (hw : 0 ≤ w) : |slide w x| ≤ w := by
  rw [abs_le]; unfold slide
  split_ifs <;> constructor <;> linarith


-- @@ L39-41 verbatim
private lemma slide_inner {w x : ℝ} (hx : |x| ≤ w) : slide w x=x := by
  rw [abs_le] at hx; unfold slide
  split_ifs <;> linarith


-- @@ L43-44 verbatim
private lemma smooth_inner {w x : ℝ} (hx : |x| ≤ w) : smooth w x=x^2 := by
  rw [smooth,slide_inner hx]; ring


-- @@ L46-52 verbatim
private lemma slide_pay {w x y : ℝ} (_hw : 0 ≤ w) (hy : |y| ≤ w) :
    2*x*y-y^2 ≤ smooth w x := by
  rw [abs_le] at hy
  unfold smooth slide; split_ifs with h h'
  · nlinarith
  · nlinarith
  nlinarith [sq_nonneg (x-y)]


-- @@ L54-58 verbatim
private lemma smooth_mid {w : ℝ} (x u : ℝ) (hw : 0 ≤ w) :
    smooth w x ≤ (smooth w (x+u)+smooth w (x-u))/2 := by
  have H (t : ℝ) := slide_pay (x:=t) hw (slide_range (x:=x) hw)
  rw [smooth]
  nlinarith [H (x+u), H (x-u)]


-- @@ L60-62 verbatim
private lemma smooth_nonneg {w : ℝ} (x : ℝ) (hw : 0 ≤ w) : 0 ≤ smooth w x := by
  have H := slide_pay (x:=x) hw (by simpa using hw : |(0:ℝ)| ≤ w)
  simpa using H


-- @@ L64-76 verbatim
private lemma smooth_lip {w : ℝ} (x y : ℝ) (hw : 0 ≤ w) :
    |smooth w x-smooth w y| ≤ 2*w * |x-y| := by
  have H (x y : ℝ) : smooth w x-smooth w y ≤ 2*w*|x-y| := by
    have He := slide_range (x:=x) hw
    have hi := slide_pay (x:=y) hw He
    have hh : (x-y)*slide w x ≤ |x-y| *w := by
      apply le_trans (le_abs_self _)
      rw [abs_mul]; gcongr
    conv_lhs => lhs; rw [smooth]
    linarith
  rw [abs_le]
  have hx := H y x; rw [abs_sub_comm] at hx
  constructor <;> linarith [H x y]


-- @@ L78-82 verbatim
private lemma sq_lip (x y : ℝ) (hx : |x| ≤ 4) (hy : |y| ≤ 4) :
    |x^2-y^2| ≤ 8*|x-y| := by
  rw [show x^2-y^2=(x+y)*(x-y) by ring,abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  linarith [abs_add_le x y]


-- @@ L84-84 verbatim
def tilt (b x : ℝ) := smooth (10*b) x+b*x^2

-- @@ L85-94 verbatim
lemma tilt_lip (b : ℝ) (h : 0 ≤ b) (x y : ℝ) (hx : |x| ≤ 4) (hy : |y| ≤ 4) :
    |tilt b x-tilt b y| ≤ 30*b* |x-y| := by
  let w := 10*b
  have he := smooth_lip (w:=w) x y (by unfold w; positivity)
  rw [tilt,tilt,show smooth (10*b) x+b*x^2-(smooth (10*b) y+b*y^2)=smooth w x-smooth w y+b*(x^2-y^2) by unfold w; ring]
  apply le_trans (abs_add_le _ _)
  rw [abs_mul,abs_of_nonneg h]
  have H := mul_le_mul_of_nonneg_left (sq_lip x y hx hy) h
  unfold w at *
  nlinarith [abs_nonneg (x-y),mul_nonneg h (abs_nonneg (x-y))]


-- @@ L96-102 verbatim
lemma tilt_bounds (b : ℝ) (h : 0 ≤ b) (x : ℝ) (hx : |x| ≤ 4) :
    0 ≤ tilt b x ∧ tilt b x ≤ 120*b := by
  have he : 0 ≤ 10*b := by positivity
  have hh : tilt b 0=0 := by rw [tilt,smooth_inner (by simpa using he)]; ring
  refine ⟨add_nonneg (smooth_nonneg x he) (by positivity),?_⟩
  have hi := tilt_lip b h x 0 hx (by norm_num); rw [hh,sub_zero,sub_zero] at hi
  exact ((le_abs_self _).trans hi).trans (by nlinarith)


-- @@ L104-117 verbatim
lemma tilt_rise (b : ℝ) (h : 0 ≤ b) (x u : ℝ) :
    let D := (tilt b (x+u)+tilt b (x-u))/2-tilt b x
    b*u^2 ≤ D ∧ (|x+u| ≤ 10*b → |x-u| ≤ 10*b → u^2 ≤ D) := by
  let w := 10*b
  intro D
  have H1 : D=(smooth w (x+u)+smooth w (x-u))/2-smooth w x+b*u^2 := by
    unfold D w tilt; ring
  rw [H1]
  constructor
  · have HE := smooth_mid x u (by unfold w; positivity : 0 ≤ w); linarith
  intro hx hy
  change _ ≤ w at hx hy
  rw [smooth_inner hx,smooth_inner hy,smooth_inner (x:=x)]; nlinarith [mul_nonneg h (sq_nonneg u)]
  rw [abs_le] at hx hy ⊢; constructor <;> linarith


-- @@ L119-120 verbatim
def guarded (u : Grid M) (b : ℝ) (s : Scene M) : Prop :=
    ∀ i, ‖scalar (s.smaller i) u‖ ≤ 10*b


-- @@ L122-122 verbatim
def prize (u : Grid M) (b : ℝ) (s : Scene M) := if guarded u b s then gain s u else 0

-- @@ L123-124 verbatim
def frosty (x u : Grid M) (b : ℝ) (B : Beat M) :=
    (blow x B:ℂ)*prize u b B.post

-- @@ L125-129 verbatim
lemma prize_norm {b : ℝ} (hb : 0 ≤ b) (u : Grid M) (s : Scene M) :
    ‖prize u b s‖ ≤ 10*b := by
  unfold prize; split_ifs with H
  · apply (norm_halfcomplex _ _).trans; linarith [H false,H true]
  simp; linarith


-- @@ L131-135 verbatim
/-- analyzing scalar path with a chosen signed component -/
structure Lens (M : ℕ) where
  focus : Grid M
  rate : ℝ
  face : Face

-- @@ L136-136 verbatim
namespace Lens

-- @@ L137-137 verbatim
def dot (g : Lens M) (s : Scene M) := part g.face (scalar s g.focus)

-- @@ L138-138 verbatim
def cash (g : Lens M) (s : Scene M) := part g.face (gain s g.focus)

-- @@ L139-139 verbatim
def coin (g : Lens M) (s : Scene M) := part g.face (prize g.focus g.rate s)

-- @@ L140-140 verbatim
def hero (g : Lens M) (s : Scene M) := tilt g.rate (g.dot s)

-- @@ L141-142 verbatim
def flow (g : Lens M) (s : Scene M) :=
    (g.hero (s.smaller false)+g.hero (s.smaller true))/2-g.hero s

-- @@ L143-144 verbatim
def swing (g : Lens M) (s : Scene M) :=
    (g.hero (s.smaller false)-g.hero (s.smaller true))/2


-- @@ L146-149 verbatim
lemma hero_walk (g : Lens M) (s : Scene M) (b : Bool) :
    hero g (s.smaller b)=g.hero s+g.flow s+ curl b*g.swing s := by
  unfold flow swing
  cases b <;> norm_num [curl] <;> ring


-- @@ L151-153 verbatim
lemma dot_walk (g : Lens M) (s : Scene M) (hs : Climb s) (b) :
    g.dot (s.smaller b) = g.dot s+curl b*g.cash s := by
  rw [dot,scalar_jump hs b,part_add,part_mul]; rfl


-- @@ L155-156 verbatim
lemma dot_limit (g : Lens M) (s : Scene M) (hp : Fit s) : |g.dot s| ≤ 4 :=
    (part_bounded g.face _).trans ((scalar_norm hp _).trans hp.lift)


-- @@ L158-160 verbatim
lemma hero_limit (g : Lens M) (hr : 0 ≤ g.rate) (hp : Fit s) :
    0 ≤ g.hero s ∧ g.hero s ≤ 120*g.rate :=
    tilt_bounds g.rate hr _ (dot_limit g s hp)


-- @@ L162-176 verbatim
lemma coin_flow (g : Lens M) (hp : 0 ≤ g.rate) (hs : Climb s) :
    (g.coin s)^2 ≤ g.flow s ∧ g.rate*(g.cash s)^2 ≤ g.flow s := by
  have Hx := g.dot_walk s hs false
  have Hy := g.dot_walk s hs true
  simp only [curl,↓reduceIte,Bool.false_eq_true,one_mul,neg_mul,← sub_eq_add_neg] at Hx Hy
  have HE := tilt_rise _ hp (g.dot s) (g.cash s)
  unfold flow hero
  rw [Hx,Hy]
  refine ⟨?_,HE.1⟩
  unfold coin prize; split_ifs with H
  · have He (b : Bool) : |g.dot (s.smaller b)| ≤ 10*g.rate := (part_bounded _ _).trans (H _)
    apply HE.2 (Hx ▸ He false) (Hy ▸ He true)
  rw [part_zero]
  exact le_trans (by simpa only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] using
    (mul_nonneg hp (sq_nonneg (cash g s)))) HE.1


-- @@ L178-191 verbatim
lemma swing_flow (g : Lens M) (hp : 0 ≤ g.rate) (hs : Climb s) :
    (g.swing s)^2 ≤ 900*g.rate*(g.flow s) := by
  have Hx := g.dot_limit _ (hs.child false); have Hy := g.dot_limit _ (hs.child true)
  have H := tilt_lip _ hp _ _ Hx Hy
  have he : dot g (s.smaller false)-dot g (s.smaller true)=2*cash g s := by
    rw [dot_walk _ _ hs, dot_walk _ _ hs]; norm_num [curl]; ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at H
  change |hero g _-hero g _| ≤ _ at H
  have HH : |swing g s| ≤ 30*g.rate* |g.cash s| := by
    rw [swing,abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith
  have HV := pow_le_pow_left₀ (abs_nonneg _) HH 2
  rw [sq_abs,mul_pow,sq_abs] at HV
  nlinarith [mul_le_mul_of_nonneg_left (coin_flow g hp hs).2 hp]


-- @@ L193-198 verbatim
lemma hero_drain (g : Lens M) (hp : 0 ≤ g.rate) {b : Beat M} (hs : Ideal b.pre b.post) :
    |g.hero b.pre-g.hero b.post| ≤ 30*g.rate*killed b := by
  apply (tilt_lip _ hp _ _ (g.dot_limit _ hs.fit) (g.dot_limit _ hs.climb.fit)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold dot; rw [←part_diff]
  exact (part_bounded _ _).trans (scalar_drain hs _)


-- @@ L200-200 verbatim
end Lens



-- @@ L203-203 verbatim
end FourierLLogL.Dyadic.Procedure.Paths


-- @@ L205-205 verbatim
end OAI
