import OAI.Analysis.FourierLLogL.Paths.Flash
import OAI.Analysis.FourierLLogL.Paths.Wager

-- @@ L3-3 verbatim
/-! # The uniform output path -/


-- @@ L5-5 verbatim
open Function Set Filter

-- @@ L6-6 verbatim
open scoped Topology BigOperators ComplexConjugate

-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace OAI


-- @@ L11-11 verbatim
namespace FourierLLogL.Dyadic.Procedure.Paths

-- @@ L12-12 verbatim
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot

-- @@ L13-13 verbatim
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}

-- @@ L14-14 verbatim
open scoped Classical



-- @@ L17-17 verbatim
namespace Run

-- @@ L18-18 verbatim
open Beam Lamp Desk


-- @@ L20-22 verbatim
structure Streak (M : ℕ) where
  i : ℕ
  u : Grid M


-- @@ L24-24 verbatim
namespace Streak

-- @@ L25-25 verbatim
def b (e : Streak M) := side e.i

-- @@ L26-26 verbatim
def thick (e : Streak M) := Real.sqrt e.b

-- @@ L27-27 verbatim
def rogue (e : Streak M) (s : Scene M) := 0 < e.i ∧ hazard s true (e.i-1)

-- @@ L28-29 verbatim
def every (e : Streak M) (s : Scene M) (L : ℝ) :=
    ∀ i, energy (s.smaller i) e.u ≤ L*e.b^2

-- @@ L30-30 verbatim
def outer (e : Streak M) (s : Scene M) := e.rogue s ∨ e.every s 256

-- @@ L31-31 verbatim
def innerV (e : Streak M) (s : Scene M) := e.rogue s ∨ e.every s 64

-- @@ L32-32 verbatim
def flag (e : Streak M) (s : Scene M) := if e.rogue s then (1:ℝ) else 0

-- @@ L33-33 verbatim
def flagged (e : Streak M) (l : Path M) := subtotal (fun b => flag e b.post) l

-- @@ L34-34 verbatim
def showers (e : Streak M) (l : Path M) := subtotal (fun b => shower e.u b.post) l


-- @@ L36-36 verbatim
lemma rate (e : Streak M) : 0 < e.b ∧ e.b ≤ 1 := ⟨side_pos _,side_le _⟩

-- @@ L37-39 verbatim
lemma thick_rate (e : Streak M) : 0 < e.thick ∧ e.thick ≤ 1 ∧ e.thick^2=e.b :=
    ⟨sqrt_pos.2 e.rate.1,by unfold thick; simpa using Real.sqrt_le_sqrt e.rate.2,
      sq_sqrt e.rate.1.le⟩

-- @@ L40-40 verbatim
lemma flag_nonneg (e : Streak M) (s : Scene M) : 0 ≤ flag e s := by unfold flag; split <;> norm_num

-- @@ L41-42 verbatim
lemma flagged_pos {l : Path M} {x : Grid M} (e : Streak M) (h : Trip x s l) : 0 ≤ flagged e l :=
    trip_nonneg h (fun b _ => flag_nonneg e b.post)

-- @@ L43-44 verbatim
lemma showers_pos {l : Path M} {x : Grid M} (e : Streak M) (h : Trip x s l) : 0 ≤ showers e l :=
    trip_nonneg h (fun _ H => shower_nonneg H.climb)

-- @@ L45-46 verbatim
lemma inner_outer (e : Streak M) (s : Scene M) (h : innerV e s) : outer e s :=
    h.elim Or.inl fun H => Or.inr fun i => by nlinarith [H i]


-- @@ L48-50 verbatim
def rain (e : Streak M) : Desk M Unit where
  stake _ _ s := if e.rogue s then 0 else -gust s e.u/(10^5 * e.b)
  stepAt _ _ := ()


-- @@ L52-88 verbatim
lemma cave (e : Streak M) (b : Beat M) (hp : Ideal b.pre b.post) (hv : e.outer b.post) :
    let u := e.u
    shower u b.post/2 ≤ energy (winds b) u-energy b.pre u+8*killed b+4*flag e b.post+
      e.b*fax b.post+10^5*e.b*((rain e).pay () b) := by
  intro u
  rw [winds,wet_walk _ hp.climb]
  let s := b.post; let x := e.b; let y := gust s u
  let a : ℝ := 10^5*x
  have hx : 0 < x := e.rate.1; have he : x ≤ 1 := e.rate.2
  have hr : 0 < a := by unfold a; positivity
  have hT := (abs_le.mp (energy_drain hp u)).2
  have hJ : 0 ≤ fax s := (fax_floor hp.climb).1
  have hG : 0 ≤ shower u s := shower_nonneg hp.climb
  change shower u s /2 ≤ energy s u+shower u s+curl b.bit*y - energy b.pre u+
    8*killed b+4*flag e s+x*fax s+a*(rain e).pay () b
  by_cases h : e.rogue b.post
  · rw [show flag e s=1 from ite_eq_left h]
    have H : (rain e).pay () b=0 := by simp [rain,pay,h,single]
    have HV (i) : 0 ≤ energy (s.smaller i) u ∧ energy (s.smaller i) u ≤ 4 :=
      let H := energy_small (hp.climb.child i) u
      ⟨H.1,H.2.trans (hp.climb.child i).lift⟩
    have hY : |curl b.bit*y| ≤ 4 := by
      rw [abs_mul,curl_unit,one_mul,abs_le]; unfold y gust
      constructor <;> linarith [(HV false).1,(HV true).1,(HV true).2,(HV false).2]
    rw [H,mul_zero]; unfold s at *; nlinarith [(abs_le.mp hY).1]
  · rw [show flag e s=0 from ite_eq_right h]
    have H : a*(rain e).pay () b= -curl b.bit*y-y^2/(2*a) := by
      have HE : (rain e).stake () b.pre b.post = -y/a := by unfold rain; simp [h]; rfl
      rw [pay,HE,single]; field_simp
    have he₁ : y^2 ≤ 100*(256*x^2)*(fax s+shower u s) :=
      sky_variance s hp.climb u _ (hv.resolve_left h)
    have hx' : y^2/(2*a) ≤ x/2*(fax s+shower u s) := by
      apply (div_le_iff₀ (by positivity)).mpr
      unfold a; nlinarith [mul_nonneg (sq_nonneg x) (add_nonneg hJ hG)]
    rw [H]
    unfold s at *
    nlinarith


-- @@ L90-110 verbatim
lemma cave_whole (e : Streak M) {l : Path M} {x : Grid M} (h : Trip x s l)
    (hh : ∀ b∈l,e.outer b.post) :
    let u := e.u
    showers e l/2 ≤ 4-energy s u + 8*fullKills l+4*flagged e l+e.b*fullFax l+
      10^5*e.b*((rain e).tally () l) := by
  intro u
  induction l generalizing s with
  | nil =>
    have H := trip_head h
    have HH := (energy_small H.1 u).2.trans H.1.lift
    change 0/2 ≤ 4-_+_*0+_*0+_*0+_*0
    linarith
  | cons b l ih =>
    obtain ⟨rfl,ha,hb⟩ := h
    have H := e.cave b ha (hh b (List.mem_cons_self))
    change shower u b.post /2 ≤ _ at H
    have hi := ih hb (fun b hi => hh b (List.mem_cons_of_mem _ hi))
    change (shower u b.post+showers e l)/2 ≤ 4-energy b.pre u+
      8*(killed b+fullKills l)+4*(flag e b.post+flagged e l)+
      _*(fax b.post+fullFax l)+_*((rain e).pay () b+(rain e).tally () l)
    linarith


-- @@ L112-112 verbatim
def aimed (e : Streak M) (W : Paths.Vector M) (s : Scene M) : Lamp M := ⟨e.u,e.thick,W,s⟩

-- @@ L113-133 verbatim
lemma lit_upper (e : Streak M) (W : Paths.Vector M) (t : Scene M) (h : Climb s) (hp : e.outer s) :
    let a := e.thick
    lit (e.aimed W t) s ≤ 300*(a*fax s+flag e s+shower e.u s) := by
  intro a
  let J := fax s; let q := shower e.u s; let g := energy s e.u; let r := e.b
  have hJ : 0 ≤ J ∧ J ≤ 2 := fax_floor h
  have hq : 0 ≤ q := shower_nonneg h
  have hα : 0 < a ∧ a ≤ 1 ∧ a^2=r := e.thick_rate
  have hr : 0 < r ∧ r ≤ 1 := e.rate
  change (g+a^2)*J+q ≤ 300*(a*J+flag e s+q)
  by_cases hh : rogue e s
  · have hg : g ≤ 4 := (energy_small h.fit e.u).2.trans h.fit.lift
    rw [flag,ite_eq_left hh]; nlinarith
  · have HE : g ≤ 256*r^2 := by
      have HV := hp.resolve_left hh
      have H : g+q=(energy (s.smaller false) e.u+energy (s.smaller true) e.u)/2 :=
        (wet_average s h e.u).symm
      unfold r; linarith [HV true,HV false]
    have hx : r^2 ≤ a := by nlinarith
    have Hx : g+a^2 ≤ 257*a := by nlinarith
    rw [flag,ite_eq_right hh]; nlinarith


-- @@ L135-138 verbatim
inductive Tray (M : ℕ) where
| sleep
| bare (W : Paths.Vector M)
| lite (e : Lamp M) (r : Bool)

-- @@ L139-139 verbatim
open Tray


-- @@ L141-149 verbatim
def dealer (e : Streak M) : Desk M (Tray M) where
  stake z _ q := match z with
  | sleep => 0
  | bare W => start (aimed e W q)/e.thick
  | lite s r => delayed s r q/e.thick
  stepAt z b := match z with
  | sleep => bare 0
  | bare W => lite (aimed e W b.post) b.bit
  | lite s r => bare (carry s r b.bit)


-- @@ L151-153 verbatim
def beamRent (e : Streak M) (b : Beat M) :=
    let s := b.post
    10^6*(fax s+(killed b+flag e s+shower e.u s)/e.thick)

-- @@ L154-157 verbatim
lemma rent_nonneg (e : Streak M) (b : Beat M) (hp : Ideal b.pre b.post) :
    0 ≤ beamRent e b := mul_nonneg (by norm_num)
      (add_nonneg (fax_floor hp.climb).1 (div_nonneg
        (add_nonneg (add_nonneg hp.kill_nonneg (flag_nonneg e _)) (shower_nonneg hp.climb)) e.thick_rate.1.le))

-- @@ L158-168 verbatim
lemma rent_total (e : Streak M) (l : Path M) :
    subtotal (beamRent e) l=10^6*(fullFax l+(fullKills l+flagged e l+showers e l)/e.thick) := by
  induction l with
  | nil => change (0:ℝ)=10^6*(0+(0+0+0)/_); ring
  | cons b l ih =>
    rw [subtotal_cons,ih]
    change 10^6*(fax b.post+(killed b+flag e b.post+shower e.u b.post)/e.thick)+
      10^6*(fullFax l+(fullKills l+flagged e l+showers e l)/e.thick)=
      10^6*((fax b.post+fullFax l)+(killed b+fullKills l+(flag e b.post+flagged e l)+
        (shower e.u b.post+showers e l))/e.thick)
    ring


-- @@ L170-220 verbatim
lemma light_bill (e : Streak M) (w : Paths.Vector M)
    (b c : Beat M) (hb : Ideal b.pre b.post) (hc : Ideal c.pre c.post)
    (hh : c.pre=winds b) (hp : e.outer b.post) (he : e.outer c.post) :
    let r := aimed e w b.post
    let v := dealer e
    let a := e.thick
    watt (winds c) e.u (carry r b.bit c.bit) a ≤ watt b.pre e.u w a +
      a*(v.pay (bare w) b+v.pay (v.stepAt (bare w) b) c)+beamRent e b+beamRent e c := by
  intro r v a
  let x := start r; let y := delayed r b.bit c.post
  have ha : 0 < a := e.thick_rate.1
  have hi : a ≤ 1 := e.thick_rate.2.1
  have HE : curl b.bit*x+curl c.bit*y=
      a*(v.pay (bare w) b+v.pay (v.stepAt (bare w) b) c)+(x^2+y^2)/(2*a) := by
    change curl _*_+curl _ *_ = a*(single (x/a) b.bit+single (y/a) c.bit)+_
    unfold single; field_simp; ring
  let J (b : Beat M) := fax b.post; let G (b : Beat M) := shower e.u b.post
  let Q (b : Beat M) := flag e b.post
  have H1 : x^2 ≤ 30000*(a*J b+Q b+G b) := by
    have H : x^2 ≤ 100*lit r b.post := start_cost r hb.climb ha.le
    have H' : lit r b.post ≤ 300*(a*J b+Q b+G b) := lit_upper e w b.post hb.climb hp
    linarith
  have H2 : y^2 ≤ 30000*((a*J b+Q b+G b)+(a*J c+Q c+G c)) := by
    have H : y^2 ≤ 100*(lit r b.post+lit r c.post) := delayed_cost r hb.climb hc.climb ha.le b.bit
    have Hx : lit r b.post ≤ 300*(a*J b+Q b+G b) := lit_upper e w b.post hb.climb hp
    have Hy : lit r c.post ≤ 300*(a*J c+Q c+G c) := lit_upper e w b.post hc.climb he
    linarith
  let K (b : Beat M) := killed b
  let A := J b+J c
  let B := Q b+Q c
  let C := G b+G c
  have HG (b : Beat M) (hb : Ideal b.pre b.post) :
      0 ≤ J b ∧ 0 ≤ Q b ∧ 0 ≤ G b ∧ 0 ≤ K b :=
        ⟨(fax_floor hb.climb).1,flag_nonneg _ _, shower_nonneg hb.climb,hb.kill_nonneg⟩
  obtain ⟨h1,h2,h3,h4⟩ := HG b hb
  obtain ⟨h5,h6,h7,h8⟩ := HG c hc
  have HX : (x^2+y^2)/(2*a) ≤ 10^5*(A+(B+C)/a) := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [show 10^5*(A+(B+C)/a)*(2*a)=200000*(a*A+B+C) by field_simp; ring]
    unfold A B C; nlinarith
  have hH := flash r hb.climb b.bit c hh hc ha hi
  change watt (winds c) e.u (carry r b.bit c.bit) a ≤ watt b.post e.u w a+
    curl b.bit*x+curl c.bit*y+ 2*K c+4*(20*A+400*((K c+G b+G c)/a)) at hH
  have HF : 2*K b+2*K c+4*(20*A+400*((K c+G b+G c)/a))+10^5*(A+(B+C)/a) ≤
      beamRent e b+beamRent e c := by
    change _ ≤ 10^6*(J b+(K b+Q b+G b)/a)+10^6*(J c+(K c+Q c+G c)/a)
    have hz : 1 ≤ a⁻¹ := (one_le_inv₀ ha).mpr hi
    unfold A B C
    simp_rw [div_eq_mul_inv]
    nlinarith
  linarith [watt_slide hb e.u w a ha.le hi]


-- @@ L222-222 verbatim
end Streak

-- @@ L223-223 verbatim
end Run



-- @@ L226-226 verbatim
end FourierLLogL.Dyadic.Procedure.Paths


-- @@ L228-228 verbatim
end OAI
