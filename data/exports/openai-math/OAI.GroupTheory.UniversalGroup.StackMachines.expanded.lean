import OAI.GroupTheory.UniversalGroup.MarkerMachine


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w x


-- @@ L7-7 verbatim
namespace Higman.IntegerStack

-- @@ L8-8 verbatim
variable {E : Type*}


-- @@ L10-12 verbatim
def code (b : ℤ) (d : E → ℤ) : List E → ℤ
  | [] => 1
  | e :: s => b * code b d s + d e


-- @@ L14-14 verbatim
@[simp] theorem code_nil (b : ℤ) (d : E → ℤ) : code b d [] = 1 := rfl

-- @@ L15-16 verbatim
@[simp] theorem code_cons (b : ℤ) (d : E → ℤ) (e : E) (s : List E) :
    code b d (e :: s) = b * code b d s + d e := rfl


-- @@ L18-19 verbatim
variable (b : ℤ) (d : E → ℤ) (hb : 2 ≤ b)
  (hd : ∀ e, 2 ≤ d e ∧ d e < b)


-- @@ L21-21 verbatim
include hd


-- @@ L23-25 verbatim
lemma push_mod (e : E) (z : ℤ) : (b * z + d e) % b = d e := by
  rw [Int.add_emod,Int.mul_emod_right,zero_add,Int.emod_emod,
    Int.emod_eq_of_lt (by have := (hd e).1; omega) (hd e).2]


-- @@ L27-27 verbatim
include hb


-- @@ L29-34 verbatim
lemma push_ne_empty (e : E) (z : ℤ) : b * z + d e ≠ 1 := by
  intro h
  have he := congrArg (fun x : ℤ ↦ x % b) h
  rw [push_mod b d hd,Int.emod_eq_of_lt (by omega) (by omega)] at he
  have := (hd e).1
  omega


-- @@ L36-44 verbatim
lemma push_injective (hdinj : Function.Injective d) {e f : E} {z w : ℤ}
    (h : b * z + d e = b * w + d f) : e = f ∧ z = w := by
  have he := congrArg (fun x : ℤ ↦ x % b) h
  rw [push_mod b d hd,push_mod b d hd] at he
  have hef := hdinj he
  subst f
  refine ⟨rfl,?_⟩
  have hm : b * z = b * w := by omega
  exact mul_left_cancel₀ (by omega : b ≠ 0) hm


-- @@ L46-58 verbatim
theorem decode_push (hdinj : Function.Injective d) (e : E) (z : ℤ) (s : List E) :
    b * z + d e = code b d s ↔ ∃ t, s = e :: t ∧ z = code b d t := by
  cases s with
  | nil => simp [push_ne_empty b d hb hd e z]
  | cons f t =>
    constructor
    · intro h
      obtain ⟨hef,hzt⟩ := push_injective b d hb hd hdinj h
      subst f
      exact ⟨t,rfl,hzt⟩
    · rintro ⟨u,hu,hz⟩
      cases hu
      simp [hz]


-- @@ L60-71 verbatim
theorem code_injective (hdinj : Function.Injective d) : Function.Injective (code b d) := by
  intro s
  induction s with
  | nil =>
    intro t h
    cases t with
    | nil => rfl
    | cons e t => exact False.elim (push_ne_empty b d hb hd e (code b d t) h.symm)
  | cons e s ih =>
    intro t h
    obtain ⟨u,rfl,hu⟩ := (decode_push b d hb hd hdinj e (code b d s) t).mp h
    exact congrArg (List.cons e) (ih hu)


-- @@ L73-80 verbatim
theorem code_pos (s : List E) : 0 < code b d s := by
  induction s with
  | nil => simp
  | cons e s ih =>
    have hm : 0 < b * code b d s := mul_pos (by omega) ih
    have hh := (hd e).1
    rw [code_cons]
    omega


-- @@ L82-82 verbatim
end Higman.IntegerStack


-- @@ L84-84 verbatim
namespace Higman.HistoryMachine

-- @@ L85-85 verbatim
variable {E : Type*} {C : Type*} {D : E → Type*}


-- @@ L87-90 verbatim
inductive Run (input output : (e : E) → D e → C) (initial : C) : List E → C → Prop
  | start : Run input output initial [] initial
  | step {s : List E} (e : E) (z : D e) :
      Run input output initial s (input e z) → Run input output initial (e :: s) (output e z)


-- @@ L92-92 verbatim
variable (input output : (e : E) → D e → C) (initial : C)


-- @@ L94-100 verbatim
@[simp] theorem run_nil (c : C) : Run input output initial [] c ↔ c = initial := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Run.start


-- @@ L102-110 verbatim
@[simp] theorem run_cons (e : E) (s : List E) (c : C) :
    Run input output initial (e :: s) c ↔
      ∃ z : D e, c = output e z ∧ Run input output initial s (input e z) := by
  constructor
  · intro h
    cases h with
    | step e z h => exact ⟨z,rfl,h⟩
  · rintro ⟨z,rfl,h⟩
    exact Run.step e z h


-- @@ L112-113 verbatim
def Reach (b : ℤ) (digit : E → ℤ) (c : C) (history : ℤ) : Prop :=
  ∃ s, Run input output initial s c ∧ history = IntegerStack.code b digit s


-- @@ L115-116 verbatim
variable (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)
  (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)


-- @@ L118-118 verbatim
lemma reach_start : Reach input output initial b digit initial 1 := ⟨[],Run.start,rfl⟩


-- @@ L120-134 verbatim
include hb hd hinj in

theorem reach_step_iff (hout : ∀ e, Function.Injective (output e)) (e : E) (z : D e)
    (h : ℤ) :
    Reach input output initial b digit (output e z) (b * h + digit e) ↔
      Reach input output initial b digit (input e z) h := by
  constructor
  · rintro ⟨s,hs,he⟩
    obtain ⟨t,rfl,ht⟩ := (IntegerStack.decode_push b digit hb hd hinj e h s).mp he
    obtain ⟨y,hy,hr⟩ := (run_cons input output initial e t (output e z)).mp hs
    have hzy : z = y := hout e hy
    subst y
    exact ⟨t,hr,ht⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨e :: s,Run.step e z hs,rfl⟩


-- @@ L136-136 verbatim
variable {G : Type*} [Group G]


-- @@ L138-140 verbatim
def value (weight : E → G) : List E → G
  | [] => 1
  | e :: s => value weight s * weight e


-- @@ L142-144 verbatim
noncomputable def decoration (weight : E → G) (h : ℤ) : G := by
  classical
  exact if hh : ∃ s, h = IntegerStack.code b digit s then value weight hh.choose else 1


-- @@ L146-155 verbatim
include hb hd hinj in
@[simp] theorem decoration_code (weight : E → G) (s : List E) :
    decoration b digit weight (IntegerStack.code b digit s) = value weight s := by
  classical
  unfold decoration
  split_ifs with h
  · have he : h.choose = s :=
      IntegerStack.code_injective b digit hb hd hinj h.choose_spec.symm
    rw [he]
  · exact False.elim (h ⟨s,rfl⟩)


-- @@ L157-164 verbatim
include hb hd hinj in
lemma decoration_step (weight : E → G) (e : E) (z : D e) (h : ℤ)
    (hr : Reach input output initial b digit (input e z) h) :
    decoration b digit weight (b * h + digit e) = decoration b digit weight h * weight e := by
  obtain ⟨s,_,rfl⟩ := hr
  rw [← IntegerStack.code_cons,decoration_code b digit hb hd hinj,
    decoration_code b digit hb hd hinj]
  rfl


-- @@ L166-166 verbatim
end Higman.HistoryMachine


-- @@ L168-168 verbatim
namespace Higman.RecordedMachine


-- @@ L170-170 verbatim
section

-- @@ L171-171 verbatim
open MarkerMachine

-- @@ L172-172 verbatim
abbrev Counter := Multiplicative ℤ


-- @@ L174-177 verbatim
def scale (b : ℤ) : Counter →* Counter where
  toFun x := Multiplicative.ofAdd (b * x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [mul_add]


-- @@ L179-182 verbatim
lemma scale_injective (b : ℤ) (hb : b ≠ 0) : Function.Injective (scale b) := by
  intro x y h
  change x.toAdd = y.toAdd
  exact mul_left_cancel₀ hb (congrArg Multiplicative.toAdd h)


-- @@ L184-184 verbatim
variable {G T Q : Type u} [Group G]


-- @@ L186-186 verbatim
def augment (c : T × Q) (h : ℤ) : (T × Counter) × Q := ((c.1,Multiplicative.ofAdd h),c.2)

-- @@ L187-187 verbatim
def forget (c : (T × Counter) × Q) : T × Q := (c.1.1,c.2)

-- @@ L188-188 verbatim
def history (c : (T × Counter) × Q) : ℤ := c.1.2.toAdd


-- @@ L190-190 verbatim
@[simp] lemma forget_augment (c : T × Q) (h : ℤ) : forget (augment c h) = c := rfl

-- @@ L191-191 verbatim
@[simp] lemma history_augment (c : T × Q) (h : ℤ) : history (augment c h) = h := rfl

-- @@ L192-192 verbatim
@[simp] lemma augment_forget (c : (T × Counter) × Q) : augment (forget c) (history c) = c := rfl


-- @@ L194-194 verbatim
variable [Group T]


-- @@ L196-211 verbatim
def edge (e : Edge G T Q) (b digit : ℤ) (hb : b ≠ 0) : Edge G (T × Counter) Q where
  Domain := e.Domain × Counter
  inputLinear := e.inputLinear.prodMap (MonoidHom.id Counter)
  outputLinear := e.outputLinear.prodMap (scale b)
  input_injective := by
    intro x y h
    exact Prod.ext (e.input_injective (congrArg Prod.fst h)) (congrArg (fun p : T × Counter ↦ p.2) h)
  output_injective := by
    intro x y h
    exact Prod.ext (e.output_injective (congrArg Prod.fst h))
      (scale_injective b hb (congrArg Prod.snd h))
  inputOffset := (e.inputOffset,1)
  outputOffset := (e.outputOffset,Multiplicative.ofAdd digit)
  inputState := e.inputState
  outputState := e.outputState
  weight := e.weight


-- @@ L213-217 verbatim
@[simp] lemma edge_input (e : Edge G T Q) (b digit : ℤ) (hb : b ≠ 0) (d : e.Domain) (h : Counter) :
    (edge e b digit hb).input (d,h) = augment (e.input d) h.toAdd := by
  change ((e.inputLinear d, h) * (e.inputOffset, 1), e.inputState) = _
  simp only [Prod.mul_def, mul_one]
  rfl

-- @@ L218-220 verbatim
@[simp] lemma edge_output (e : Edge G T Q) (b digit : ℤ) (hb : b ≠ 0) (d : e.Domain) (h : Counter) :
    (edge e b digit hb).output (d,h) =
      augment (e.output d) (b * h.toAdd + digit) := rfl


-- @@ L222-223 verbatim
variable {E : Type u} [Fintype E] (edges : E → Edge G T Q)
  (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)


-- @@ L225-226 verbatim
noncomputable def edgeList : List (Edge G (T × Counter) Q) :=
  Finset.univ.toList.map (fun e ↦ edge (edges e) b (digit e) (by omega))


-- @@ L228-230 verbatim
lemma mem_edgeList (e : E) : edge (edges e) b (digit e) (by omega) ∈ edgeList edges b digit hb := by
  classical
  exact List.mem_map.mpr ⟨e,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩


-- @@ L232-235 verbatim
lemma of_mem_edgeList (a : Edge G (T × Counter) Q) (ha : a ∈ edgeList edges b digit hb) :
    ∃ e, a = edge (edges e) b (digit e) (by omega) := by
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
  exact ⟨e,rfl⟩


-- @@ L237-237 verbatim
variable (seed : T × Q)


-- @@ L239-241 verbatim
def Forward (c : (T × Counter) × Q) : Prop :=
  HistoryMachine.Reach (fun e ↦ (edges e).input) (fun e ↦ (edges e).output) seed b digit
    (forget c) (history c)


-- @@ L243-245 verbatim
omit [Fintype E] in
lemma forward_start : Forward edges b digit seed (augment seed 1) :=
  HistoryMachine.reach_start _ _ _ _ _


-- @@ L247-247 verbatim
variable (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)


-- @@ L249-251 verbatim
lemma output_injective (e : Edge G T Q) : Function.Injective e.output := by
  intro x y h
  exact e.output_injective (mul_right_cancel (congrArg Prod.fst h))


-- @@ L253-259 verbatim
include hb hd hinj in
omit [Fintype E] in
lemma forward_edge (e : E) (d : (edges e).Domain) (h : ℤ) :
    Forward edges b digit seed (augment ((edges e).output d) (b*h + digit e)) ↔
      Forward edges b digit seed (augment ((edges e).input d) h) :=
  HistoryMachine.reach_step_iff _ _ _ b digit hb hd hinj
    (fun e ↦ output_injective (edges e)) e d h


-- @@ L261-280 verbatim
include hd hinj in
lemma reach_implies_forward (c : (T × Counter) × Q)
    (hc : MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c) :
    Forward edges b digit seed c := by
  induction hc with
  | start => exact forward_start edges b digit seed
  | forward a ha d _ ih =>
    obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
    obtain ⟨d,h⟩ := d
    change Counter at h
    simpa only [edge_output] using
      (forward_edge edges b digit hb seed hd hinj e d h.toAdd).mpr
        (by simpa only [edge_input] using ih)
  | backward a ha d _ ih =>
    obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
    obtain ⟨d,h⟩ := d
    change Counter at h
    simpa only [edge_input] using
      (forward_edge edges b digit hb seed hd hinj e d h.toAdd).mp
        (by simpa only [edge_output] using ih)


-- @@ L282-293 verbatim
lemma run_implies_reach {s : List E} {c : T × Q}
    (hc : HistoryMachine.Run (fun e ↦ (edges e).input) (fun e ↦ (edges e).output) seed s c) :
    MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1)
      (augment c (IntegerStack.code b digit s)) := by
  induction hc with
  | start => exact MarkerMachine.Reach.start
  | @step s e d hr ih =>
    have hh := MarkerMachine.Reach.forward (seed := augment seed 1)
      (edge (edges e) b (digit e) (by omega)) (mem_edgeList edges b digit hb e)
      (d,Multiplicative.ofAdd (IntegerStack.code b digit s))
    rw [edge_input,edge_output] at hh
    exact hh ih


-- @@ L295-300 verbatim
lemma forward_implies_reach (c : (T × Counter) × Q) (hc : Forward edges b digit seed c) :
    MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c := by
  obtain ⟨s,hs,hh⟩ := hc
  have hr := run_implies_reach edges b digit hb seed hs
  rw [← hh,augment_forget] at hr
  exact hr


-- @@ L302-308 verbatim
include hd hinj in

theorem reach_iff_forward (c : (T × Counter) × Q) :
    MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c ↔
      Forward edges b digit seed c :=
  ⟨reach_implies_forward edges b digit hb seed hd hinj c,
    forward_implies_reach edges b digit hb seed c⟩


-- @@ L310-310 verbatim
end


-- @@ L312-312 verbatim
open MarkerMachine DecoratedMarker MarkerEmbedding

-- @@ L313-315 verbatim
variable {G T Q E : Type u} [Group G] [Group T] [Fintype E]
  (edges : E → Edge G T Q) (b : ℤ) (digit : E → ℤ) (hb : 2 ≤ b)
  (seed : T × Q) (hd : ∀ e, 2 ≤ digit e ∧ digit e < b) (hinj : Function.Injective digit)


-- @@ L317-318 verbatim
noncomputable def decoration (c : (T × Counter) × Q) : G :=
  HistoryMachine.decoration b digit (fun e ↦ (edges e).weight) (history c)


-- @@ L320-331 verbatim
include hd hinj in
lemma decoration_edge (a : Edge G (T × Counter) Q) (ha : a ∈ edgeList edges b digit hb)
    (d : a.Domain) (hr : MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) (a.input d)) :
    decoration edges b digit (a.output d) = decoration edges b digit (a.input d) * a.weight := by
  obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
  obtain ⟨d,h⟩ := d
  have hf := reach_implies_forward edges b digit hb seed hd hinj _ hr
  rw [edge_input] at hf ⊢
  rw [edge_output]
  exact HistoryMachine.decoration_step (fun e ↦ (edges e).input) (fun e ↦ (edges e).output)
    seed b digit hb hd hinj
    (fun e ↦ (edges e).weight) e d h.toAdd hf


-- @@ L333-348 verbatim
include hb hd hinj in

theorem benign_forward [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T] [Finite Q]
    (hD : ∀ e, Group.IsFinitelyPresented (edges e).Domain) :
    IsBenign (decoratedSubgroup (decoration edges b digit) {c | Forward edges b digit seed c}) := by
  have : Group.IsFinitelyPresented (T × Counter) := finitelyPresented_prod
  have he : {c | MarkerMachine.Reach (edgeList edges b digit hb) (augment seed 1) c} =
      {c | Forward edges b digit seed c} := by
    ext c
    exact reach_iff_forward edges b digit hb seed hd hinj c
  rw [← he]
  apply MarkerMachine.benign _ _ _ _ (decoration_edge edges b digit hb seed hd hinj)
  intro a ha
  obtain ⟨e,rfl⟩ := of_mem_edgeList edges b digit hb a ha
  have := hD e
  exact finitelyPresented_prod


-- @@ L350-350 verbatim
end Higman.RecordedMachine


-- @@ L352-352 verbatim
namespace Higman.MarkerEmbedding

-- @@ L353-353 verbatim
open Monoid Coprod DecoratedMarker

-- @@ L354-354 verbatim
variable {G T : Type u} {Q : Type*} [Group G] [Group T]


-- @@ L356-356 verbatim
def coefficientProjection : Base G T Q →* G := Coprod.lift (MonoidHom.fst G T) 1


-- @@ L358-360 verbatim
@[simp] lemma projection_coefficient (g : G) :
    coefficientProjection (coefficient g : Base G T Q) = g := by
  simp [coefficientProjection,coefficient]

-- @@ L361-363 verbatim
@[simp] lemma projection_translation (t : T) :
    coefficientProjection (translation t : Base G T Q) = 1 := by
  simp [coefficientProjection,translation]

-- @@ L364-366 verbatim
@[simp] lemma projection_marker (t : T) (q : Q) :
    coefficientProjection (marker t q : Base G T Q) = 1 := by
  simp [coefficientProjection,marker,translation]


-- @@ L368-369 verbatim
lemma projection_surjective : Function.Surjective (coefficientProjection : Base G T Q →* G) :=
  fun g ↦ ⟨coefficient g,projection_coefficient g⟩


-- @@ L371-371 verbatim
variable {Q : Type u}


-- @@ L373-407 verbatim
theorem benign_output [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T]
    (v : T × Q → G) (V : Set (T × Q)) (hR : IsBenign (decoratedSubgroup v V)) (q : Q) :
    IsBenign (Subgroup.closure (v '' {c | c ∈ V ∧ c.2 = q})) := by
  have : Group.IsFinitelyPresented (G × T) := finitelyPresented_prod
  let f : Base G T Unit →* Base G T Q := embedding (MonoidHom.id T) (fun _ ↦ 1)
    (fun _ ↦ q) (fun _ ↦ 1)
  have hi : Function.Injective (index (MonoidHom.id T) (fun _ : Unit ↦ 1) (fun _ ↦ q)) :=
    index_injective _ Function.injective_id _ _ (Function.injective_of_subsingleton _)
  have hB := (hR.comap f).map_surjective
    (coefficientProjection : Base G T Unit →* G)
      (projection_surjective (G := G) (T := T) (Q := Unit))
  dsimp only [f] at hB
  rw [comap_decoratedSubgroup _ Function.injective_id _ _ _ hi,
    decoratedSubgroup_eq_closure,MonoidHom.map_closure] at hB
  have he : (coefficientProjection : Base G T Unit →* G) ''
      ((fun x : T × Unit ↦ coefficient
        (pullDecoration (MonoidHom.id T) (fun _ ↦ 1) (fun _ ↦ q) (fun _ ↦ 1) v x) *
          marker x.1 x.2) ''
        (index (MonoidHom.id T) (fun _ : Unit ↦ 1) (fun _ ↦ q) ⁻¹' V)) =
      v '' {c | c ∈ V ∧ c.2 = q} := by
    rw [Set.image_image]
    ext g
    constructor
    · rintro ⟨⟨t,p⟩,ht,rfl⟩
      refine ⟨(t,q),⟨?_,rfl⟩,?_⟩
      · simpa [index] using ht
      · simp [pullDecoration,index]
    · rintro ⟨⟨t,r⟩,⟨hc,hq⟩,rfl⟩
      change r = q at hq
      subst r
      refine ⟨(t,()),?_,?_⟩
      · simpa [index] using hc
      · simp [pullDecoration,index]
  rw [he] at hB
  exact hB


-- @@ L409-409 verbatim
end Higman.MarkerEmbedding


-- @@ L411-411 verbatim
namespace Higman.RecordedMachine

-- @@ L412-412 verbatim
open MarkerMachine

-- @@ L413-414 verbatim
variable {G T Q E : Type u} [Group G] [Group T]
  (edges : E → Edge G T Q) (seed : T × Q) (halt : Q)


-- @@ L416-418 verbatim
def acceptedOutputs : Set G :=
  {g | ∃ s c, HistoryMachine.Run (fun e ↦ (edges e).input) (fun e ↦ (edges e).output)
    seed s c ∧ c.2 = halt ∧ g = HistoryMachine.value (fun e ↦ (edges e).weight) s}


-- @@ L420-420 verbatim
variable [Fintype E] [Finite Q] [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented T]


-- @@ L422-456 verbatim
theorem benign_accepted (hD : ∀ e, Group.IsFinitelyPresented (edges e).Domain) :
    IsBenign (Subgroup.closure (acceptedOutputs edges seed halt)) := by
  classical
  let b : ℤ := Fintype.card E + 2
  let digit : E → ℤ := fun e ↦ ((Fintype.equivFin E e).val : ℤ) + 2
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hd : ∀ e, 2 ≤ digit e ∧ digit e < b := by
    intro e
    have hh := (Fintype.equivFin E e).isLt
    dsimp [digit,b]
    constructor <;> omega
  have hi : Function.Injective digit := by
    intro e f h
    apply (Fintype.equivFin E).injective
    apply Fin.ext
    dsimp [digit] at h
    omega
  have : Group.IsFinitelyPresented (T × Counter) := finitelyPresented_prod
  have hp := MarkerEmbedding.benign_output (decoration edges b digit)
    {c | Forward edges b digit seed c}
    (benign_forward edges b digit hb seed hd hi hD) halt
  have he : decoration edges b digit ''
      {c | c ∈ {c | Forward edges b digit seed c} ∧ c.2 = halt} =
      acceptedOutputs edges seed halt := by
    ext g
    constructor
    · rintro ⟨c,⟨⟨s,hs,hh⟩,hc⟩,rfl⟩
      refine ⟨s,forget c,hs,hc,?_⟩
      dsimp [decoration]
      rw [hh,HistoryMachine.decoration_code b digit hb hd hi]
    · rintro ⟨s,c,hs,hc,rfl⟩
      refine ⟨augment c (IntegerStack.code b digit s),⟨?_,hc⟩,?_⟩
      · exact ⟨s,hs,rfl⟩
      · exact HistoryMachine.decoration_code b digit hb hd hi _ s
  rwa [he] at hp


-- @@ L458-458 verbatim
end Higman.RecordedMachine


-- @@ L460-460 verbatim
namespace Higman


-- @@ L462-474 verbatim
theorem finitelyPresented_pi (I : Type u) [Finite I] (G : Type v) [Group G]
    [Group.IsFinitelyPresented G] : Group.IsFinitelyPresented (I → G) := by
  apply Finite.induction_empty_option _ _ _ I
  · intro A B e ih
    have := ih
    exact Group.IsFinitelyPresented.equiv (MulEquiv.arrowCongr e (MulEquiv.refl G))
  · infer_instance
  · intro A _ ih
    have := ih
    have : Group.IsFinitelyPresented (G × (A → G)) := finitelyPresented_prod
    let e : (Option A → G) ≃* G × (A → G) :=
      { Equiv.piOptionEquivProd with map_mul' := fun _ _ ↦ rfl }
    exact Group.IsFinitelyPresented.equiv e.symm


-- @@ L476-476 verbatim
end Higman


-- @@ L478-478 verbatim
end OAI
