import OAI.Analysis.FourierLLogL.Edges.Global

-- @@ L2-2 verbatim
/-! # A plateau without its restart markers -/

-- @@ L3-3 verbatim
open Function Set Filter

-- @@ L4-4 verbatim
open scoped Topology BigOperators ComplexConjugate

-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
namespace FourierLLogL.Dyadic.Procedure

-- @@ L9-9 verbatim
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse

-- @@ L10-10 verbatim
variable {M J j : ℕ} {s : Scene M} {f : Grid M → ℝ}

-- @@ L11-11 verbatim
open scoped Classical


-- @@ L13-13 verbatim
def minimumT (j : ℕ) := 1/(12800*Thermal.H j^32)


-- @@ L15-15 verbatim
lemma minimum_pos (j) : 0 < minimumT j := by unfold minimumT; have := H_pos j; positivity


-- @@ L17-22 verbatim
structure Less (s q : Scene M) : Prop where
  here : q.here=s.here
  fund : q.fund=s.fund
  flat : q.norm=s.norm
  mode : q.live=s.live
  coins (x) : q.wage x=s.wage x ∨ q.wage x=0


-- @@ L24-25 verbatim
lemma less_self (s : Scene M) : Less s s :=
    ⟨rfl,rfl,rfl,rfl,fun _ => Or.inl rfl⟩


-- @@ L27-29 verbatim
lemma Less.trans {s b c : Scene M} (h : Less s b) (h' : Less b c) : Less s c :=
  ⟨h'.here.trans h.here,h'.fund.trans h.fund,h'.flat.trans h.flat,h'.mode.trans h.mode,
    fun x => (h'.coins x).elim (fun e => e.symm ▸ h.coins x) Or.inr⟩


-- @@ L31-32 verbatim
lemma less_lost {s : Scene M} (u : Update j M s.here) : Less s (s.lose u) :=
    ⟨rfl,rfl,rfl,rfl,fun x => by rw [lose_eq]; split_ifs <;> simp⟩


-- @@ L34-35 verbatim
lemma Less.antitone {s q : Scene M} (h : Less s q) (hp : 0 ≤ s.wage) : q.wage ≤ s.wage :=
  fun x => (h.coins x).elim (fun e => le_of_eq e) (fun e => e ▸ hp x)

-- @@ L36-39 verbatim
lemma Less.mass_le {s q : Scene M} (h : Less s q) (hp : 0 ≤ s.wage) (hv : s.here.ok M) :
    q.mass ≤ s.mass := by
  unfold mass; rw [h.here,avg_ex hv,avg_ex hv]
  exact Ex_mono _ (h.antitone hp)


-- @@ L41-42 verbatim
def shrink (s q : Scene M) (j : ℕ) :=
    Less s q ∧ (q.mass=s.mass ∨ q.mass ≤ (1-minimumT j)*s.mass)


-- @@ L44-46 verbatim
inductive Thread (M : ℕ) : Scene M → Type
| blank (s : Scene M) : Thread M s
| ran (s q : Scene M) (k : ∀ b : Bool, Thread M (q.smaller b)) : Thread M s


-- @@ L48-48 verbatim
namespace Thread

-- @@ L49-53 verbatim
def Following (j J : ℕ) (f : Grid M → ℝ) {s : Scene M} (t : Thread M s) :=
    match t with
    | blank s => s.Safe j J f
    | ran s q k => s.Safe j J f ∧ shrink s q j ∧ q.Safe j J f ∧ q.work j J f ∧
       q.settled j ∧ ∀ b, Following j J f (k b)


-- @@ L55-58 verbatim
def reattach {s : Scene M} (q : Scene M) (t : Thread M s) : Thread M q :=
    match t with
    | .blank _ => .blank q
    | .ran _ s k => .ran q s k


-- @@ L60-68 verbatim
def project {s : Scene M} (r : Play j M s) : Thread M s :=
    match r with
    | .jump s l r => .ran s s fun b => match b with
      | false => project l
      | true => project r
    | .attempt s _ l r => reattach s (project l)
    | .rest s => .blank s
    | .freeze s _ => .blank s
    | .ticket s _ => .blank s


-- @@ L70-71 verbatim
lemma rooted {s : Scene M} (t : Thread M s) (h : Following j J f t) : s.Safe j J f :=
  match t with | .blank _ => h | .ran _ _ _ => h.1


-- @@ L73-105 verbatim
lemma projected (r : Play j M s) (h : r.Follows J f) : Following j J f (project r) := by
  induction r with
  | rest | ticket | freeze => exact h.1
  | jump s l r il ir =>
    obtain ⟨ha,hb,hc,hd,he⟩ := h
    refine ⟨ha,⟨less_self _,Or.inl rfl⟩,ha,hb,hc,?_⟩
    intro b; cases b; exact il hd; exact ir he
  | attempt s u l r il ir =>
    obtain ⟨ha,hb,hc,hu,hl,hr⟩ := h
    have ht := il hl
    have hp := ha.positive
    change Following j J f (reattach s _)
    cases H : project l with
    | blank => exact ha
    | ran t k =>
      rw [H] at ht
      obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := ht
      refine ⟨ha,⟨(less_lost u).trans h₂.1,?_⟩,h₃,h₄,h₅,h₆⟩
      have hv : (toss s u).TrueLaw :=
        toss_true _ ha.within ha.positive hb.1.2.2
      have he : (s.lose u).mass = (toss s u).probs false * s.mass := toss_mass hv false
      apply Or.inr
      apply le_trans (h₂.1.mass_le h₁.positive h₁.within)
      rw [he]
      apply mul_le_mul_of_nonneg_right _ ha.mass_lower
      have Hx := ((main_bounds _ hu.ix_ok).1)
      have hF := hu.bias
      rw [← success_prob] at hF
      have HT : minimumT j ≤ beta u.ix/2 := by
        unfold minimumT
        apply le_trans (b:=((1/6400)/Thermal.H j^32)/2) ?_ (by linarith)
        exact le_of_eq (by ring)
      have HQ := (toss s u).probs.total; rw [Fintype.sum_bool] at HQ; linarith


-- @@ L107-111 verbatim
/-- Local output paths, excluding terminal removals (unnecessary for transform). -/
structure Beat (M : ℕ) where
  pre : Scene M
  post : Scene M
  bit : Bool


-- @@ L113-117 verbatim
def stream {s : Scene M} (t : Thread M s) (x : Grid M) : List (Beat M) := match t with
| .blank _ => []
| .ran s q k =>
  let b := (step q).bit x
  ⟨s,q,b⟩::(k b).stream x


-- @@ L119-125 verbatim
lemma step_dice_child (p : Node) (hp : p.valid) (hh : p.lev < M) (b : Bool)
    {x : Grid M} (hx : 0 < (p.child b).dice M x) :
    (decide (x∈p.R.block M):Bool)=b := by
  have h1 := (dice_positive (child_ok p hp hh b)).mp hx
  cases b
  · exact decide_eq_false (fun H => Set.disjoint_left.mp (p.block_separate M) h1 H)
  exact decide_eq_true h1


-- @@ L127-147 verbatim
lemma stream_branch {s q : Scene M} (k : ∀ b, Thread M (q.smaller b))
    (h : Following j J f (.ran s q k)) (T : List (Beat M) → Grid M → ℝ) :
    (s.here.dice M).Ex (fun x => T (stream (.ran s q k) x) x) =
      (uniform Bool).Ex (fun b => ((q.smaller b).here.dice M).Ex fun x =>
        T (⟨s,q,b⟩::(k b).stream x) x) := by
  obtain ⟨ha,hb,hc,hd,he,hk⟩ := h
  let p := q.here
  have hh : p.lev < M := (rooted _ (hk false)).within.2
  rw [← hb.1.here,dice_child p hc.within.1 hh]
  let Q (b : Bool) := ((q.smaller b).here.dice M).Ex fun x => T (⟨s,q,b⟩::(k b).stream x) x
  have hi (b : Bool) :
      ((q.smaller b).here.dice M).Ex (fun x => T (stream (.ran s q k) x) x) = Q b := by
    refine Ex_congr_mem _ fun x hx => ?_
    let f (b) := T (⟨s,q,b⟩::(k b).stream x) x
    have h : (step q).bit x = b := step_dice_child p hc.within.1 hh b hx
    change f _=f b
    rw [h]
  change (((q.smaller false).here.dice M).Ex _ + ((q.smaller true).here.dice M).Ex _)/2 =
    (uniform Bool).Ex Q
  rw [hi false,hi true]
  rw [Ex,Fintype.sum_bool]; simp [uniform_apply]; ring


-- @@ L149-150 verbatim
def fee (t : Thread M s) (f : Beat M → ℝ) :=
    (s.here.dice M).Ex fun x => (((t.stream x).map f).sum)


-- @@ L152-158 verbatim
lemma fee_ran {s q : Scene M} (k : ∀ b, Thread M (q.smaller b)) {g : Beat M → ℝ}
    (h : Following j J f (.ran s q k)) :
    fee (.ran s q k) g =
      (uniform Bool).Ex (fun b => g ⟨s,q,b⟩+(k b).fee g) := by
  unfold fee
  rw [stream_branch _ h (fun l _ => (l.map g).sum)]
  simp_rw [List.map_cons,List.sum_cons,Ex_add,Ex_const]


-- @@ L160-160 verbatim
end Thread

-- @@ L161-161 verbatim
end FourierLLogL.Dyadic.Procedure


-- @@ L163-163 verbatim
end OAI
