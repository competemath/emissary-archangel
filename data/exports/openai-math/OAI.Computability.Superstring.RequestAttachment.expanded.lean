import OAI.Computability.Superstring.CountSort


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Superstring.WindowCode

-- @@ L6-6 verbatim
open Hierarchical WalkCode BitCode

-- @@ L7-7 verbatim
variable {α : Type}

-- @@ L8-9 verbatim
def requestAttachment (A : ℤ → α) (p : ℕ) (a e s h : ℤ) : Walk α :=
  join (route A s h (a+p) (e+p)) (route A (a+p) (e+p) (s+p) (h+p))


-- @@ L11-33 verbatim
theorem requestAttachment_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p : ℕ)
    (per : Function.Periodic A (p : ℤ))
    {a e s h : ℤ} (hae : a ≤ e) (hsh : s ≤ h)
    (has : a ≤ s) (hsa : s ≤ a+p) (heh : e ≤ h) (hhe : h ≤ e+p)
    (hR : textWord A a e ∈ V) (hQ : textWord A s h ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A s h) (textWord A s h),
      Path.points P = requestAttachment A p a e s h ∧
      P.cost = p ∧ P.Visits (textWord A a e) := by
  have hER := textWord_translate A p per a e
  have hEQ := textWord_translate A p per s h
  obtain ⟨U,hU,hUc,_,_⟩ := route_realizes closed A letters hsh
    (show a+(p:ℤ) ≤ e+p by omega) hsa hhe hQ (hER.symm ▸ hR)
  obtain ⟨D,hD,hDc,_,_⟩ := route_realizes closed A letters
    (show a+(p:ℤ) ≤ e+p by omega) (show s+(p:ℤ) ≤ h+p by omega)
    (show a+(p:ℤ) ≤ s+p by omega) (show e+(p:ℤ) ≤ h+p by omega)
    (hER.symm ▸ hR) (hEQ.symm ▸ hQ)
  refine ⟨(U.trans D).copy rfl hEQ,?_,?_,?_⟩
  · simp only [points_copy,Path.points,hU,hD,requestAttachment]
  · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hUc,hDc]
    omega
  · rw [← hER]
    exact (Hierarchical.Path.visits_copy ..).mpr (Or.inl (Hierarchical.Path.visits_end U))


-- @@ L35-35 verbatim
variable [Inhabited α] [Coded α]

-- @@ L36-39 verbatim
@[fun_prop] theorem poly_requestAttachment : Poly (fun q : List α × ℕ × ℤ × ℤ × ℤ × ℤ =>
    requestAttachment (PeriodWord.text q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold requestAttachment
  fun_prop

-- @@ L40-40 verbatim
end Superstring.WindowCode



-- @@ L43-43 verbatim
namespace Superstring.WalkCode

-- @@ L44-44 verbatim
open Hierarchical

-- @@ L45-45 verbatim
variable {α : Type}

-- @@ L46-51 verbatim
theorem realizes_spec {V : Set (List α)} {s t : List α} (P : Hierarchical.Path V s t)
    {Q : Walk α} (h : Path.points P = Q) :
    Runs V s t Q ∧ cost Q = P.cost ∧ ∀ w, w ∈ Q ↔ P.Visits w := by
  obtain ⟨hV,hs,ht,hc,hv⟩ := points_spec P
  rw [h] at hV hs ht hc hv
  exact ⟨⟨hV,hs,ht⟩,hc,hv⟩

-- @@ L52-52 verbatim
end Superstring.WalkCode


-- @@ L54-54 verbatim
namespace Superstring.HostCode

-- @@ L55-55 verbatim
open Hierarchical WalkCode WindowCode BitCode

-- @@ L56-56 verbatim
variable {α : Type} [Inhabited α] [DecidableEq α]

-- @@ L57-57 verbatim
abbrev RequestData (α : Type) := List α × Window × Window


-- @@ L59-60 verbatim
def attachment (r : RequestData α) : Walk α :=
  requestAttachment (PeriodWord.text r.1) r.1.length r.2.1.1 r.2.1.2 r.2.2.1 r.2.2.2


-- @@ L62-64 verbatim
def raw (U : List α) (p : ℕ) (a b e : ℤ) (R : List (RequestData α)) : Walk α :=
  rootShort (fill (hostExcursion (PeriodWord.text U) U.length a b e (R.map (·.2.2)))
    (R.map attachment)) p


-- @@ L66-130 verbatim
theorem raw_spec {V : Set (List α)} (closed : SubstringClosed V)
    (U : List α) (letters : ∀ x, [PeriodWord.text U x] ∈ V) (p : ℕ)
    (hp : 0 < p) (a b e : ℤ) (he : a+p < e) (heb : e ≤ b)
    (hR : PeriodWord.window U a b ∈ V) (hshort : b < a+U.length+p)
    (R : List (RequestData α))
    (hc : ∀ r ∈ R, ∀ s ∈ R, ordered r.2.2 s.2.2 ∨ ordered s.2.2 r.2.2)
    (hb : ∀ r ∈ R, a ≤ r.2.2.1 ∧ r.2.2.1 ≤ a+U.length ∧
      r.2.2.1 ≤ r.2.2.2 ∧ b ≤ r.2.2.2 ∧ r.2.2.2 < a+U.length+p)
    (hv : ∀ r ∈ R, PeriodWord.window U r.2.2.1 r.2.2.2 ∈ V)
    (ha : ∀ r ∈ R,
      (∀ x, [PeriodWord.text r.1 x] ∈ V) ∧ r.2.1.1 ≤ r.2.1.2 ∧
      r.2.1.1 ≤ r.2.2.1 ∧ r.2.2.1 ≤ r.2.1.1+r.1.length ∧
      r.2.1.2 ≤ r.2.2.2 ∧ r.2.2.2 ≤ r.2.1.2+r.1.length ∧
      PeriodWord.window r.1 r.2.1.1 r.2.1.2 ∈ V ∧
      PeriodWord.window r.1 r.2.2.1 r.2.2.2 = PeriodWord.window U r.2.2.1 r.2.2.2) :
    Runs V [] [] (raw U p a b e R) ∧
      cost (raw U p a b e R) ≤ U.length + (R.map (fun r => r.1.length)).sum+p ∧
      PeriodWord.window U a b ∈ raw U p a b e R ∧
      (∀ d, e ≤ d → d ≤ b → PeriodWord.window U a d ∈ raw U p a b e R) ∧
      ∀ r ∈ R, PeriodWord.window r.1 r.2.1.1 r.2.1.2 ∈ raw U p a b e R := by
  obtain ⟨P,hP,hPc,hPr,hPv,hPw,x,hx,hxp⟩ := hostExcursion_realizes closed
    (PeriodWord.text U) letters U.length p hp (PeriodWord.periodic U) a b e he heb
    (by simpa only [PeriodWord.window_eq] using hR) hshort (R.map (·.2.2))
    (by intro u hu v hv; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hu
        obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hv; exact hc r hr s hs)
    (by intro v hv; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hv; exact hb r hr)
    (by intro v hv'; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hv'
        simpa only [PeriodWord.window_eq] using hv r hr)
  obtain ⟨hP',hcost,hvis⟩ := realizes_spec P hP
  have hAtt : ∀ r ∈ R, Runs V (PeriodWord.window U r.2.2.1 r.2.2.2)
      (PeriodWord.window U r.2.2.1 r.2.2.2) (attachment r) ∧
      cost (attachment r) = r.1.length ∧
      PeriodWord.window r.1 r.2.1.1 r.2.1.2 ∈ attachment r := by
    intro r hr
    obtain ⟨hl,hle,has,hsa,heh,hhe,hw,heq⟩ := ha r hr
    obtain ⟨Q,hQ,hQc,hQv⟩ := requestAttachment_realizes closed (PeriodWord.text r.1)
      hl r.1.length (PeriodWord.periodic r.1) hle (hb r hr).2.2.1 has hsa heh hhe
      (by simpa only [PeriodWord.window_eq] using hw)
      (by have hh : PeriodWord.window r.1 r.2.2.1 r.2.2.2 ∈ V := heq.symm ▸ hv r hr
          simpa only [PeriodWord.window_eq] using hh)
    obtain ⟨hQ',hcost,hvis⟩ := realizes_spec Q hQ
    rw [← PeriodWord.window_eq,heq] at hQ'
    exact ⟨hQ',hcost.trans hQc,by simpa only [PeriodWord.window_eq,attachment] using (hvis _).mpr hQv⟩
  obtain ⟨hF,hFc,hFv⟩ := fill_spec _ (R.map attachment) hP'
    (by intro Q hQ; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hQ; exact ⟨_,(hAtt r hr).1⟩)
    (by intro Q hQ; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hQ
        exact ⟨_,(hvis _).mpr (hPw _ (List.mem_map.mpr ⟨r,hr,rfl⟩)),
          by simpa only [PeriodWord.window_eq] using List.mem_of_head? (hAtt r hr).1.2.1⟩)
  have hsum : ((R.map attachment).map cost).sum = (R.map (fun r => r.1.length)).sum := by
    rw [List.map_map]
    congr 1
    exact List.map_congr_left (fun r hr => (hAtt r hr).2.1)
  obtain ⟨hQ,hQc,hQv⟩ := rootShort_spec closed hF p
    ⟨x,(hFv x).mpr (Or.inl ((hvis x).mpr hx)),hxp.le⟩
  refine ⟨hQ,?_,?_,?_,?_⟩
  · rw [hFc,hcost,hPc,hsum] at hQc
    exact hQc
  · apply hQv
    simpa only [PeriodWord.window_eq] using (hFv _).mpr (Or.inl ((hvis _).mpr hPr))
  · intro d hd hd'
    apply hQv
    simpa only [PeriodWord.window_eq] using (hFv _).mpr (Or.inl ((hvis _).mpr (hPv d hd hd')))
  · intro r hr
    apply hQv
    exact (hFv _).mpr (Or.inr ⟨_,List.mem_map.mpr ⟨r,hr,rfl⟩,(hAtt r hr).2.2⟩)


-- @@ L132-132 verbatim
variable [Coded α]

-- @@ L133-137 verbatim
omit [DecidableEq α] in
@[fun_prop] theorem poly_attachment : Poly (attachment : RequestData α → Walk α) := by
  unfold attachment
  exact poly_requestAttachment.comp (f := fun r : RequestData α =>
    (r.1,r.1.length,r.2.1.1,r.2.1.2,r.2.2.1,r.2.2.2)) (by fun_prop)

-- @@ L138-148 verbatim
@[fun_prop] theorem poly_raw : Poly (fun t : List α × ℕ × ℤ × ℤ × ℤ × List (RequestData α) =>
    raw t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2) := by
  unfold raw
  have hW : Poly (fun t : List α × ℕ × ℤ × ℤ × ℤ × List (RequestData α) => t.2.2.2.2.2.map (·.2.2)) :=
    (BitCode.Poly.map (show Poly (fun r : RequestData α => r.2.2) from by fun_prop)).comp (by fun_prop)
  have hH := poly_hostExcursion.comp
    (f := fun t : List α × ℕ × ℤ × ℤ × ℤ × List (RequestData α) =>
      (t.1,t.1.length,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2.map (·.2.2)))
    (by fun_prop)
  have hA := (BitCode.Poly.map poly_attachment).comp (f := fun t : List α × ℕ × ℤ × ℤ × ℤ × List (RequestData α) => t.2.2.2.2.2) (by fun_prop)
  fun_prop

-- @@ L149-149 verbatim
end Superstring.HostCode



-- @@ L152-152 verbatim
namespace Superstring.PeriodWord

-- @@ L153-153 verbatim
open Hierarchical BitCode

-- @@ L154-154 verbatim
variable {α : Type} [Inhabited α]

-- @@ L155-155 verbatim
def shift (U : List α) (d : ℤ) : List α := window U (-d) (-d+U.length)

-- @@ L156-158 verbatim
@[simp] theorem length_shift (U : List α) (d : ℤ) : (shift U d).length = U.length := by
  simp only [shift,window_eq,textWord,List.length_ofFn]
  omega

-- @@ L159-168 verbatim
theorem text_shift {U : List α} (hp : 0 < U.length) (d : ℤ) :
    text (shift U d) = fun x => text U (x-d) := by
  apply eq_of_prefix _ _ (by simpa using hp)
  · intro x
    simpa only [length_shift,add_sub_right_comm] using periodic U (x-d)
  · intro i hi
    simp only [length_shift] at hi
    simp only [shift,window_eq,textWord,List.getElem_ofFn]
    congr 1
    omega

-- @@ L169-169 verbatim
variable [Coded α]

-- @@ L170-172 verbatim
@[fun_prop] theorem poly_shift : Poly (fun q : List α × ℤ => shift q.1 q.2) := by
  unfold shift
  fun_prop

-- @@ L173-173 verbatim
end Superstring.PeriodWord


-- @@ L175-175 verbatim
namespace Superstring.HostCode

-- @@ L176-176 verbatim
open Hierarchical WalkCode WindowCode BitCode

-- @@ L177-177 verbatim
variable {α : Type} [Inhabited α] [DecidableEq α]

-- @@ L178-178 verbatim
abbrev Entry (α : Type) := ℕ × List α × ℤ × ℤ × ℤ

-- @@ L179-179 verbatim
namespace Entry

-- @@ L180-180 verbatim
def tag (e : Entry α) := e.1

-- @@ L181-181 verbatim
def word (e : Entry α) := e.2.1

-- @@ L182-182 verbatim
def start (e : Entry α) := e.2.2.1

-- @@ L183-183 verbatim
def stop (e : Entry α) := e.2.2.2.1

-- @@ L184-184 verbatim
def req (e : Entry α) := e.2.2.2.2

-- @@ L185-186 verbatim
def target (q : ℕ) (b e : Entry α) : RequestData α :=
  (e.word,(e.start,e.req),(min (e.start+e.word.length) (b.start+q),max e.req b.stop))

-- @@ L187-188 verbatim
def shift (e : Entry α) (d : ℤ) : Entry α :=
  (e.tag,PeriodWord.shift e.word d,e.start+d,e.stop+d,e.req+d)

-- @@ L189-189 verbatim
end Entry


-- @@ L191-192 verbatim
def later (b : Entry α) (E : List (Entry α)) : List (Entry α) :=
  E.filter (fun e => !(equal e.tag b.tag))

-- @@ L193-194 verbatim
def normalized (U : List α) (b : Entry α) (E : List (Entry α)) : Walk α :=
  raw U b.word.length b.start b.stop b.req ((later b E).map (Entry.target U.length b))


-- @@ L196-196 verbatim
variable [Coded α]

-- @@ L197-198 verbatim
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_tag : Poly (Entry.tag : Entry α → ℕ) := by unfold tag; fun_prop

-- @@ L199-200 verbatim
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_word : Poly (Entry.word : Entry α → List α) := by unfold word; fun_prop

-- @@ L201-202 verbatim
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_start : Poly (Entry.start : Entry α → ℤ) := by unfold start; fun_prop

-- @@ L203-204 verbatim
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_stop : Poly (Entry.stop : Entry α → ℤ) := by unfold stop; fun_prop

-- @@ L205-206 verbatim
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_req : Poly (Entry.req : Entry α → ℤ) := by unfold req; fun_prop

-- @@ L207-210 verbatim
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_target : Poly (fun q : ℕ × Entry α × Entry α => Entry.target q.1 q.2.1 q.2.2) := by
  unfold target
  fun_prop

-- @@ L211-214 verbatim
omit [DecidableEq α] in
@[fun_prop] theorem Entry.poly_shift : Poly (fun q : Entry α × ℤ => Entry.shift q.1 q.2) := by
  unfold shift
  fun_prop

-- @@ L215-219 verbatim
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_later : Poly (fun q : Entry α × List (Entry α) => later q.1 q.2) := by
  unfold later
  exact BitCode.Poly.filterFn (p := fun q : (Entry α × List (Entry α)) × Entry α =>
    !(equal q.2.tag q.1.1.tag)) (by fun_prop) (by fun_prop)

-- @@ L220-231 verbatim
@[fun_prop] theorem poly_normalized : Poly (fun q : List α × Entry α × List (Entry α) => normalized q.1 q.2.1 q.2.2) := by
  have ht : Poly (fun q : List α × Entry α × List (Entry α) =>
      (later q.2.1 q.2.2).map (Entry.target q.1.length q.2.1)) := by
    apply BitCode.Poly.mapFn (f := fun q : (List α × Entry α × List (Entry α)) × Entry α =>
      Entry.target q.1.1.length q.1.2.1 q.2)
    · exact Entry.poly_target.comp (f := fun q : (List α × Entry α × List (Entry α)) × Entry α =>
        (q.1.1.length,q.1.2.1,q.2)) (by fun_prop)
    · fun_prop
  unfold normalized
  exact poly_raw.comp (f := fun q : List α × Entry α × List (Entry α) =>
    (q.1,q.2.1.word.length,q.2.1.start,q.2.1.stop,q.2.1.req,
      (later q.2.1 q.2.2).map (Entry.target q.1.length q.2.1))) (by fun_prop)

-- @@ L232-232 verbatim
end Superstring.HostCode



-- @@ L235-235 verbatim
namespace Superstring.Hierarchical

-- @@ L236-236 verbatim
variable {α ι κ : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}


-- @@ L238-278 verbatim
theorem hosted_targets_chain (D : Layer V A q) (H : ι → HostedGroup D)
    (g : κ → ι) (R : ∀ i, (H (g i)).Request)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (T b : ℤ) (i j : κ) :
    (min ((H (g i)).start+(H (g i)).period) T ≤ min ((H (g j)).start+(H (g j)).period) T ∧
      max (R i).stop b ≤ max (R j).stop b) ∨
    (min ((H (g j)).start+(H (g j)).period) T ≤ min ((H (g i)).start+(H (g i)).period) T ∧
      max (R j).stop b ≤ max (R i).stop b) := by
  have raw (i j : κ) (hij : g i ≠ g j)
      (ha : (H (g i)).start ≤ (H (g j)).start)
      (hb : (H (g i)).stop ≤ (H (g j)).stop) :
      (H (g i)).start + (H (g i)).period ≤ (H (g j)).start + (H (g j)).period ∧
      (R i).stop ≤ (R j).stop := by
    have hd : (H (g i)).text ≠ (H (g j)).text := by
      simpa only [add_zero] using different (g i) (g j) hij 0
    have hov := (H (g i)).overlap_lt (H (g j)) ha hb hd
    have hlong := (R i).long
    have hmargin := (R i).margin
    have hlong' := (R j).long
    constructor <;> omega
  have hc :
      ((H (g i)).start + (H (g i)).period ≤ (H (g j)).start + (H (g j)).period ∧
        (R i).stop ≤ (R j).stop) ∨
      ((H (g j)).start + (H (g j)).period ≤ (H (g i)).start + (H (g i)).period ∧
        (R j).stop ≤ (R i).stop) := by
    by_cases he : g i = g j
    · rcases le_total (R i).stop (R j).stop with hr | hr
      · exact Or.inl ⟨by rw [he], hr⟩
      · exact Or.inr ⟨by rw [he], hr⟩
    · by_cases ha : (H (g i)).start < (H (g j)).start
      · exact Or.inl (raw i j he ha.le
          (D.window_order (H (g i)).le_last (H (g j)).first_le ha))
      · by_cases hb : (H (g j)).start < (H (g i)).start
        · exact Or.inr (raw j i (Ne.symm he) hb.le
            (D.window_order (H (g j)).le_last (H (g i)).first_le hb))
        · rcases le_total (H (g i)).stop (H (g j)).stop with hs | hs
          · exact Or.inl (raw i j he (by omega) hs)
          · exact Or.inr (raw j i (Ne.symm he) (by omega) hs)
  rcases hc with hc | hc
  · exact Or.inl ⟨min_le_min_right _ hc.1, max_le_max_right _ hc.2⟩
  · exact Or.inr ⟨min_le_min_right _ hc.1, max_le_max_right _ hc.2⟩


-- @@ L280-295 verbatim
theorem hosted_target_bounds (D : Layer V A q) (hq : 0 < q)
    (per : Function.Periodic A (q : ℤ)) (H J : HostedGroup D) (R : J.Request)
    (hmin : H.period ≤ J.period)
    (ho : H.start ≤ J.start ∧ J.start ≤ H.start+q ∧ H.stop ≤ J.stop ∧ J.stop ≤ H.stop+q)
    (hd : H.text ≠ J.text) (hd' : J.text ≠ fun x => H.text (x-q)) :
    let s := min (J.start+J.period) (H.start+q)
    let h := max R.stop H.stop
    J.start ≤ s ∧ s ≤ J.start+J.period ∧ s ≤ h ∧ h ≤ J.stop ∧ R.stop ≤ h ∧
      h ≤ R.stop+J.period ∧ H.start ≤ s ∧ s ≤ H.start+q ∧ H.stop ≤ h ∧ h < H.start+q+H.period := by
  have hl := H.overlap_lt J ho.1 ho.2.2.1 hd
  have hr := J.next_overlap_lt H per ho.2.1 ho.2.2.2 hd'
  have hbase : H.stop < H.start+q+H.period := by
    have hh := H.length_lt hq per
    omega
  exact host_target_bounds H.start H.stop J.start J.stop R.stop (H.start+q) H.period J.period
    hmin ho.1 ho.2.1 ho.2.2.1 R.long R.margin hl hr hbase

-- @@ L296-296 verbatim
end Superstring.Hierarchical


-- @@ L298-298 verbatim
end OAI
