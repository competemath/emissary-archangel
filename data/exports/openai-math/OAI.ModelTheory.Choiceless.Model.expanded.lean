import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe uA uB uC uF uR


-- @@ L9-9 verbatim
namespace CPTSeparation


-- @@ L11-11 verbatim
abbrev Scalar := ZMod 3


-- @@ L13-15 verbatim
inductive Symbol
  | Ed | Cf | EB | VB | I | Z (δ : Scalar)
  deriving DecidableEq, Fintype


-- @@ L17-18 verbatim
structure Input (A : Type) where
  rel : Symbol → A → A → Bool


-- @@ L20-20 verbatim
namespace Input


-- @@ L22-22 verbatim
variable {A B : Type} [Fintype A] [Fintype B]


-- @@ L24-24 verbatim
abbrev Edge (S : Input A) := {y : A // S.rel .Ed y y = true}


-- @@ L26-26 verbatim
abbrev Config (S : Input A) := {a : A // S.rel .Cf a a = true}


-- @@ L28-28 verbatim
instance (S : Input A) : Fintype S.Edge := inferInstanceAs (Fintype (Subtype _))


-- @@ L30-30 verbatim
instance (S : Input A) : Fintype S.Config := inferInstanceAs (Fintype (Subtype _))


-- @@ L32-35 verbatim
def coefficient (S : Input A) (y : S.Edge) (a : S.Config) : Scalar :=
  ∑ x : S.Edge, if S.rel .I a x then
    ∑ δ : Scalar, if S.rel (.Z δ) y x then δ else 0
    else 0


-- @@ L37-39 verbatim
def incident (S : Input A) (t : S.Config) (y : S.Edge) : Prop :=
  ∃ a : S.Config, S.rel .VB t a = true ∧
    ∃ x : S.Edge, S.rel .I a x = true ∧ S.rel .EB y x = true


-- @@ L41-42 verbatim
def normalized (S : Input A) (lambda : S.Config → Scalar) : Prop :=
  ∀ t : S.Config, (∑ a : S.Config, if S.rel .VB t a then lambda a else 0) = 1


-- @@ L44-46 verbatim
def consistent (S : Input A) (lambda : S.Config → Scalar) (mu : S.Edge → Scalar) : Prop :=
  ∀ (t : S.Config) (y : S.Edge), S.incident t y →
    mu y = ∑ a : S.Config, if S.rel .VB t a then lambda a * S.coefficient y a else 0


-- @@ L48-49 verbatim
def query (S : Input A) : Prop :=
  ∃ (lambda : S.Config → Scalar) (mu : S.Edge → Scalar), S.normalized lambda ∧ S.consistent lambda mu


-- @@ L51-52 verbatim
structure Iso (S : Input A) (T : Input B) extends A ≃ B where
  rel_eq : ∀ r x y, T.rel r (toEquiv x) (toEquiv y) = S.rel r x y


-- @@ L54-54 verbatim
end Input


-- @@ L56-56 verbatim
end CPTSeparation


-- @@ L58-58 verbatim
namespace CPTSeparation.Hereditary


-- @@ L60-60 verbatim
section


-- @@ L62-62 verbatim
abbrev HF (A : Type uA) := Quotient (@Lists.instSetoidLists A)


-- @@ L64-64 verbatim
variable {A : Type uA} {B : Type uB}


-- @@ L66-66 verbatim
local instance instDecidableEqHF {A : Type uA} : DecidableEq (HF A) := Classical.decEq _


-- @@ L68-68 verbatim
def mk (l : Lists A) : HF A := Quotient.mk Lists.instSetoidLists l


-- @@ L70-70 verbatim
def atom (a : A) : HF A := mk (Lists.atom a)


-- @@ L72-73 verbatim
@[simp] theorem mk_eq_mk {l r : Lists A} : mk l = mk r ↔ Lists.Equiv l r :=
  Quotient.eq


-- @@ L75-76 verbatim
def isSet (x : HF A) : Bool := Quotient.liftOn x (fun l => l.1)
  (by intro l r h; cases h <;> rfl)


-- @@ L78-80 verbatim
def rawElements (l : Lists A) : Finset (HF A) := by
  classical
  exact l.toList.toFinset.image mk


-- @@ L82-94 verbatim
theorem mem_rawElements (a l : Lists A) : mk a ∈ rawElements l ↔ a ∈ l := by
  classical
  rcases l with ⟨(_ | _), l⟩
  · cases l
    change mk a ∈ (∅ : Finset (HF A)) ↔ False
    simp
  · change mk a ∈ (Lists'.toList l).toFinset.image mk ↔ a ∈ l
    simp only [Finset.mem_image, List.mem_toFinset, Lists'.mem_def, mk_eq_mk]
    constructor
    · rintro ⟨a',ha',heq⟩
      exact ⟨a',ha',heq.symm⟩
    · rintro ⟨a',ha',heq⟩
      exact ⟨a',ha',heq.symm⟩


-- @@ L96-101 verbatim
theorem raw_mem_congr_right {l r : Lists A} (h : Lists.Equiv l r) (a : Lists A) :
    a ∈ l ↔ a ∈ r := by
  cases h with
  | refl => rfl
  | antisymm hl hr =>
    exact ⟨Lists'.mem_of_subset hl, Lists'.mem_of_subset hr⟩


-- @@ L103-110 verbatim
theorem rawElements_congr {l r : Lists A} (h : Lists.Equiv l r) :
    rawElements l = rawElements r := by
  ext x
  induction x using Quotient.inductionOn with
  | _ a =>
    change mk a ∈ rawElements l ↔ mk a ∈ rawElements r
    rw [mem_rawElements, mem_rawElements]
    exact raw_mem_congr_right h a


-- @@ L112-138 verbatim
def elements (x : HF A) : Finset (HF A) := Quotient.liftOn x rawElements (by
  have mem_rawElements (a l : Lists A) : mk a ∈ rawElements l ↔ a ∈ l := by
    classical
    rcases l with ⟨(_ | _), l⟩
    · cases l
      change mk a ∈ (∅ : Finset (HF A)) ↔ False
      simp
    · change mk a ∈ (Lists'.toList l).toFinset.image mk ↔ a ∈ l
      simp only [Finset.mem_image, List.mem_toFinset, Lists'.mem_def, mk, Quotient.eq]
      constructor
      · rintro ⟨a',ha',heq⟩
        exact ⟨a',ha',heq.symm⟩
      · rintro ⟨a',ha',heq⟩
        exact ⟨a',ha',heq.symm⟩
  have raw_mem_congr_right {l r : Lists A} (h : Lists.Equiv l r) (a : Lists A) :
      a ∈ l ↔ a ∈ r := by
    cases h with
    | refl => rfl
    | antisymm hl hr =>
      exact ⟨Lists'.mem_of_subset hl, Lists'.mem_of_subset hr⟩
  intro l r h
  ext z
  induction z using Quotient.inductionOn with
  | _ a =>
    change mk a ∈ rawElements l ↔ mk a ∈ rawElements r
    rw [mem_rawElements, mem_rawElements]
    exact raw_mem_congr_right h a)


-- @@ L140-140 verbatim
instance : Membership (HF A) (HF A) := ⟨fun y x => x ∈ elements y⟩


-- @@ L142-142 verbatim
@[simp] theorem mem_mk (a l : Lists A) : mk a ∈ mk l ↔ a ∈ l := mem_rawElements a l


-- @@ L144-145 verbatim
def ofFinset (s : Finset (HF A)) : HF A :=
  mk (Lists.ofList (s.toList.map Quotient.out))


-- @@ L147-150 verbatim
def rawRank' : {b : Bool} → Lists' A b → ℕ
  | _, .atom _ => 0
  | _, .nil => 0
  | _, .cons' a l => max (rawRank' a + 1) (rawRank' l)


-- @@ L152-152 verbatim
def rawRank (l : Lists A) : ℕ := rawRank' l.2


-- @@ L154-162 verbatim
theorem rawRank_lt_of_mem {b : Bool} (l : Lists' A b) (a : Lists A)
    (ha : a ∈ l.toList) : rawRank a < rawRank' l := by
  induction l with
  | atom => simp at ha
  | nil => simp at ha
  | cons' c l ihc ihl =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ihl ha) (le_max_right _ _)


-- @@ L164-174 verbatim
theorem rawRank_congr {l r : Lists A} (h : Lists.Equiv l r) : rawRank l = rawRank r := by
  induction h using Lists.Equiv.rec
      (motive_2 := fun l r _ => rawRank' l ≤ rawRank' r) with
  | refl => rfl
  | antisymm hl hr ihl ihr => exact Nat.le_antisymm ihl ihr
  | nil => exact Nat.zero_le _
  | @cons a a' l r heq hmem hsub iheq ihsub =>
    change max (rawRank a + 1) (rawRank' l) ≤ rawRank' r
    refine max_le ?_ ihsub
    rw [iheq]
    exact rawRank_lt_of_mem r a' hmem


-- @@ L176-197 verbatim
def rank (x : HF A) : ℕ := Quotient.liftOn x rawRank (by
  have rawRank_lt_of_mem {b : Bool} (l : Lists' A b) (a : Lists A)
      (ha : a ∈ l.toList) : rawRank a < rawRank' l := by
    induction l with
    | atom => simp at ha
    | nil => simp at ha
    | cons' c l ihc ihl =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihl ha) (le_max_right _ _)
  have rawRank_congr {l r : Lists A} (h : Lists.Equiv l r) : rawRank l = rawRank r := by
    induction h using Lists.Equiv.rec
        (motive_2 := fun l r _ => rawRank' l ≤ rawRank' r) with
    | refl => rfl
    | antisymm hl hr ihl ihr => exact Nat.le_antisymm ihl ihr
    | nil => exact Nat.zero_le _
    | @cons a a' l r heq hmem hsub iheq ihsub =>
      change max (rawRank a + 1) (rawRank' l) ≤ rawRank' r
      refine max_le ?_ ihsub
      rw [iheq]
      exact rawRank_lt_of_mem r a' hmem
  exact fun _ _ h => rawRank_congr h)


-- @@ L199-210 verbatim
theorem rank_lt_of_mem {x y : HF A} (h : x ∈ y) : rank x < rank y := by
  induction y using Quotient.inductionOn with
  | _ l =>
    induction x using Quotient.inductionOn with
    | _ a =>
      have h' := (mem_mk a l).mp h
      rcases l with ⟨(_ | _), l⟩
      · exact False.elim h'
      · obtain ⟨a',ha',heq⟩ := h'
        change rawRank a < rawRank' l
        rw [rawRank_congr heq]
        exact rawRank_lt_of_mem l a' ha'


-- @@ L212-212 verbatim
end


-- @@ L214-214 verbatim
open Classical Finset


-- @@ L216-216 verbatim
variable {A : Type uA} {B : Type uB}


-- @@ L218-218 verbatim
def double (a b : HF A) : HF A := ofFinset {a,b}


-- @@ L220-222 verbatim
def ordinal : ℕ → HF A
  | 0 => ofFinset ∅
  | i+1 => ofFinset (insert (ordinal i) (elements (ordinal i)))


-- @@ L224-224 verbatim
end CPTSeparation.Hereditary


-- @@ L226-226 verbatim
namespace CPTSeparation.Operational


-- @@ L228-228 verbatim
open Classical Hereditary Finset


-- @@ L230-230 verbatim
variable {A : Type uA} {B : Type uB} {R : Type uR} {F : Type uF} {arity : F → ℕ}


-- @@ L232-232 verbatim
local instance instDecidableEqHF {C : Type uC} : DecidableEq (HF C) := Classical.decEq _


-- @@ L234-234 verbatim
abbrev empty : HF A := ordinal 0


-- @@ L236-236 verbatim
abbrev truth : HF A := ordinal 1


-- @@ L238-238 verbatim
def boolean (p : Prop) : HF A := if p then truth else empty


-- @@ L240-241 verbatim
def inputRelation (rel : R → A → A → Bool) (r : R) (x y : HF A) : Prop :=
  ∃ a b, x = atom a ∧ y = atom b ∧ rel r a b = true


-- @@ L243-243 verbatim
def allAtoms [Fintype A] : HF A := ofFinset (univ.image atom)


-- @@ L245-245 verbatim
def unionHF (x : HF A) : HF A := ofFinset ((elements x).biUnion elements)


-- @@ L247-248 verbatim
def uniqueHF (x : HF A) : HF A :=
  if h : ∃ a, elements x = {a} then h.choose else empty


-- @@ L250-250 verbatim
def cardinalityHF (x : HF A) : HF A := ordinal (elements x).card


-- @@ L252-252 verbatim
abbrev Location (F : Type uF) (arity : F → ℕ) (A : Type uA) := Σ f : F, Fin (arity f) → HF A


-- @@ L254-256 verbatim
structure State (F : Type uF) (arity : F → ℕ) (A : Type uA) where
  value : Location F arity A → HF A
  finite : Set.Finite {l | value l ≠ empty}


-- @@ L258-258 verbatim
namespace State


-- @@ L260-260 verbatim
def initial : State F arity A := ⟨fun _ => empty, by simp⟩


-- @@ L262-262 verbatim
def support (s : State F arity A) : Finset (Location F arity A) := s.finite.toFinset


-- @@ L264-264 verbatim
end State


-- @@ L266-266 verbatim
abbrev Update (F : Type uF) (arity : F → ℕ) (A : Type uA) := Location F arity A × HF A


-- @@ L268-268 verbatim
namespace State


-- @@ L270-271 verbatim
def Consistent (u : Finset (Update F arity A)) : Prop :=
  ∀ l x y, (l,x) ∈ u → (l,y) ∈ u → x = y


-- @@ L273-275 verbatim
def updatedValue (s : State F arity A) (u : Finset (Update F arity A))
    (l : Location F arity A) : HF A :=
  if h : ∃ x, (l,x) ∈ u then h.choose else s.value l


-- @@ L277-285 verbatim
def applyUpdates (s : State F arity A) (u : Finset (Update F arity A)) : State F arity A where
  value := s.updatedValue u
  finite := by
    apply (s.finite.union (u.image Prod.fst).finite_toSet).subset
    intro l hl
    by_cases h : ∃ x, (l,x) ∈ u
    · obtain ⟨x,hx⟩ := h
      exact Or.inr (mem_image.mpr ⟨(l,x),hx,rfl⟩)
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq,updatedValue,dite_eq_right h] using hl)


-- @@ L287-287 verbatim
end State


-- @@ L289-289 verbatim
inductive Control | halt | accept deriving DecidableEq


-- @@ L291-291 verbatim
end CPTSeparation.Operational


-- @@ L293-293 verbatim
namespace CPTSeparation.Hereditary


-- @@ L295-295 verbatim
open Classical Finset


-- @@ L297-297 verbatim
variable {A : Type uA} {B : Type uB}


-- @@ L299-299 verbatim
local instance instDecidableEqHF_1 {C : Type uC} : DecidableEq (HF C) := Classical.decEq _


-- @@ L301-350 verbatim
def closure (x : HF A) : Finset (HF A) :=
  insert x ((elements x).attach.biUnion (fun y => closure y.val))
termination_by rank x
decreasing_by
  have mem_rawElements (a l : Lists A) : mk a ∈ rawElements l ↔ a ∈ l := by
    classical
    rcases l with ⟨(_ | _), l⟩
    · cases l
      change mk a ∈ (∅ : Finset (HF A)) ↔ False
      simp
    · change mk a ∈ (Lists'.toList l).toFinset.image mk ↔ a ∈ l
      simp only [Finset.mem_image, List.mem_toFinset, Lists'.mem_def, mk, Quotient.eq]
      constructor
      · rintro ⟨a',ha',heq⟩
        exact ⟨a',ha',heq.symm⟩
      · rintro ⟨a',ha',heq⟩
        exact ⟨a',ha',heq.symm⟩
  have rawRank_lt_of_mem {b : Bool} (l : Lists' A b) (a : Lists A)
      (ha : a ∈ l.toList) : rawRank a < rawRank' l := by
    induction l with
    | atom => simp at ha
    | nil => simp at ha
    | cons' c l ihc ihl =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
      · exact lt_of_lt_of_le (ihl ha) (le_max_right _ _)
  have rawRank_congr {l r : Lists A} (h : Lists.Equiv l r) : rawRank l = rawRank r := by
    induction h using Lists.Equiv.rec
        (motive_2 := fun l r _ => rawRank' l ≤ rawRank' r) with
    | refl => rfl
    | antisymm _ _ ihl ihr => exact Nat.le_antisymm ihl ihr
    | nil => exact Nat.zero_le _
    | @cons a a' l r _ hmem _ iheq ihsub =>
      change max (rawRank a + 1) (rawRank' l) ≤ rawRank' r
      refine max_le ?_ ihsub
      rw [iheq]
      exact rawRank_lt_of_mem r a' hmem
  have rank_lt_of_mem {x y : HF A} (h : x ∈ y) : rank x < rank y := by
    induction y using Quotient.inductionOn with
    | _ l =>
      induction x using Quotient.inductionOn with
      | _ a =>
        have h' := (mem_rawElements a l).mp h
        rcases l with ⟨(_ | _), l⟩
        · exact False.elim h'
        · obtain ⟨a',ha',heq⟩ := h'
          change rawRank a < rawRank' l
          rw [rawRank_congr heq]
          exact rawRank_lt_of_mem l a' ha'
  exact rank_lt_of_mem y.property


-- @@ L352-352 verbatim
def familyClosure (f : Finset (HF A)) : Finset (HF A) := f.biUnion closure


-- @@ L354-354 verbatim
end CPTSeparation.Hereditary


-- @@ L356-356 verbatim
namespace CPTSeparation.Operational


-- @@ L358-358 verbatim
open Classical Hereditary Finset


-- @@ L360-360 verbatim
variable {A : Type uA} {R : Type uR} {F : Type uF} {arity : F → ℕ}


-- @@ L362-362 verbatim
local instance instDecidableEqHF_1 {C : Type uC} : DecidableEq (HF C) := Classical.decEq _


-- @@ L364-364 verbatim
namespace State


-- @@ L366-367 verbatim
def critical (s : State F arity A) : Finset (HF A) :=
  s.support.biUnion (fun l => insert (s.value l) (univ.image l.2))


-- @@ L369-370 verbatim
def active [Fintype A] (s : State F arity A) : Finset (HF A) :=
  familyClosure (s.critical ∪ {allAtoms,empty,truth} ∪ univ.image atom)


-- @@ L372-372 verbatim
end State


-- @@ L374-374 verbatim
end CPTSeparation.Operational


-- @@ L376-376 verbatim
namespace CPTSeparation.FullCPT


-- @@ L378-378 verbatim
section


-- @@ L380-380 verbatim
open Classical Hereditary Finset


-- @@ L382-382 verbatim
open Operational (State Control Location Update)


-- @@ L384-384 verbatim
local instance instDecidableEqHF {C : Type} : DecidableEq (HF C) := Classical.decEq _


-- @@ L386-403 verbatim
inductive Term (R F : Type) (arity : F → ℕ) : Type
  | var (name : ℕ)
  | ordinal (n : ℕ)
  | atoms
  | app (f : F) (args : Fin (arity f) → Term R F arity)
  | pair (a b : Term R F arity)
  | union (a : Term R F arity)
  | unique (a : Term R F arity)
  | card (a : Term R F arity)
  | equal (a b : Term R F arity)
  | member (a b : Term R F arity)
  | isAtom (a : Term R F arity)
  | input (r : R) (a b : Term R F arity)
  | not (a : Term R F arity)
  | and (a b : Term R F arity)
  | or (a b : Term R F arity)
  | conditional (c a b : Term R F arity)
  | comprehend (name : ℕ) (bound guard body : Term R F arity)


-- @@ L405-405 verbatim
variable {A R F : Type} {arity : F → ℕ}


-- @@ L407-407 verbatim
namespace Term


-- @@ L409-409 verbatim
variable [Fintype A]


-- @@ L411-432 verbatim
def eval (rel : R → A → A → Bool) (s : State F arity A) :
    Term R F arity → (ℕ → HF A) → HF A
  | .var n, v => v n
  | .ordinal n, _ => Hereditary.ordinal n
  | .atoms, _ => Operational.allAtoms
  | .app f args, v => s.value ⟨f, fun i => eval rel s (args i) v⟩
  | .pair a b, v => double (eval rel s a v) (eval rel s b v)
  | .union a, v => Operational.unionHF (eval rel s a v)
  | .unique a, v => Operational.uniqueHF (eval rel s a v)
  | .card a, v => Operational.cardinalityHF (eval rel s a v)
  | .equal a b, v => Operational.boolean (eval rel s a v = eval rel s b v)
  | .member a b, v => Operational.boolean (eval rel s a v ∈ eval rel s b v)
  | .isAtom a, v => Operational.boolean (isSet (eval rel s a v) = false)
  | .input r a b, v => Operational.boolean (Operational.inputRelation rel r (eval rel s a v) (eval rel s b v))
  | .not a, v => Operational.boolean (eval rel s a v ≠ Operational.truth)
  | .and a b, v => Operational.boolean (eval rel s a v = Operational.truth ∧ eval rel s b v = Operational.truth)
  | .or a b, v => Operational.boolean (eval rel s a v = Operational.truth ∨ eval rel s b v = Operational.truth)
  | .conditional c a b, v => if eval rel s c v = Operational.truth then eval rel s a v else eval rel s b v
  | .comprehend n bound guard body, v =>
      ofFinset (((elements (eval rel s bound v)).filter
        (fun x => eval rel s guard (Function.update v n x) = Operational.truth)).image
        (fun x => eval rel s body (Function.update v n x)))


-- @@ L434-434 verbatim
end Term


-- @@ L436-442 verbatim
inductive Rule (R F : Type) (arity : F → ℕ) : Type
  | skip
  | update (f : F) (args : Fin (arity f) → Term R F arity) (value : Term R F arity)
  | parallel (a b : Rule R F arity)
  | conditional (condition : Term R F arity) (a b : Rule R F arity)
  | forall (name : ℕ) (bound : Term R F arity) (body : Rule R F arity)
  | letValue (name : ℕ) (value : Term R F arity) (body : Rule R F arity)


-- @@ L444-444 verbatim
namespace Rule


-- @@ L446-454 verbatim
def updates [Fintype A] (rel : R → A → A → Bool) (s : State F arity A) :
    Rule R F arity → (ℕ → HF A) → Finset (Update F arity A)
  | .skip, _ => ∅
  | .update f args value, v => {(⟨f, fun i => (args i).eval rel s v⟩, value.eval rel s v)}
  | .parallel a b, v => updates rel s a v ∪ updates rel s b v
  | .conditional c a b, v => if c.eval rel s v = Operational.truth then updates rel s a v else updates rel s b v
  | .forall n bound body, v => (elements (bound.eval rel s v)).biUnion
      (fun x => updates rel s body (Function.update v n x))
  | .letValue n value body, v => updates rel s body (Function.update v n (value.eval rel s v))


-- @@ L456-456 verbatim
end Rule


-- @@ L458-462 verbatim
structure Program (R : Type) where
  Functions : Type
  finiteFunctions : Fintype Functions
  arity : Functions → ℕ
  body : Rule R (Control ⊕ Functions) (Sum.elim (fun _ => 0) arity)


-- @@ L464-464 verbatim
namespace Program


-- @@ L466-466 verbatim
variable (P : Program R) [Fintype A]


-- @@ L468-468 verbatim
abbrev functionArity : Control ⊕ P.Functions → ℕ := Sum.elim (fun _ => 0) P.arity


-- @@ L470-470 verbatim
abbrev Store := State (Control ⊕ P.Functions) P.functionArity A


-- @@ L472-472 verbatim
def flag (s : P.Store (A := A)) (c : Control) : Prop := s.value ⟨.inl c, Fin.elim0⟩ = Operational.truth


-- @@ L474-477 verbatim
def step (rel : R → A → A → Bool) (s : P.Store (A := A)) : Option (P.Store (A := A)) :=
  if P.flag s .halt then some s else
    let u := P.body.updates rel s (fun _ => Operational.empty)
    if State.Consistent u then some (s.applyUpdates u) else none


-- @@ L479-481 verbatim
def run (rel : R → A → A → Bool) : ℕ → Option (P.Store (A := A))
  | 0 => some State.initial
  | j+1 => (run rel j).bind (P.step rel)


-- @@ L483-484 verbatim
def active (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
  (Finset.range (h+1)).biUnion (fun j => ((P.run rel j).toFinset).biUnion State.active)


-- @@ L486-486 verbatim
end Program


-- @@ L488-488 verbatim
end


-- @@ L490-490 verbatim
open Classical Hereditary Finset


-- @@ L492-492 verbatim
open Operational (State Control)


-- @@ L494-494 verbatim
local instance instDecidableEqHF_1 {C : Type} : DecidableEq (HF C) := Classical.decEq _


-- @@ L496-496 verbatim
variable {A R F : Type} {arity : F → ℕ}


-- @@ L498-498 verbatim
namespace Term


-- @@ L500-500 verbatim
variable [Fintype A]


-- @@ L502-518 verbatim
def roots (rel : R → A → A → Bool) (s : State F arity A) :
    Term R F arity → (ℕ → HF A) → Finset (HF A)
  | t@(.var _), v | t@(.ordinal _), v | t@(.atoms), v => {t.eval rel s v}
  | t@(.app _ args), v => insert (t.eval rel s v)
      ((List.ofFn (fun i => roots rel s (args i) v)).foldr (· ∪ ·) ∅)
  | t@(.pair a b), v | t@(.equal a b), v | t@(.member a b), v
  | t@(.input _ a b), v | t@(.and a b), v | t@(.or a b), v =>
      insert (t.eval rel s v) (roots rel s a v ∪ roots rel s b v)
  | t@(.union a), v | t@(.unique a), v | t@(.card a), v
  | t@(.isAtom a), v | t@(.not a), v => insert (t.eval rel s v) (roots rel s a v)
  | .conditional c a b, v => roots rel s c v ∪
      if c.eval rel s v = Operational.truth then roots rel s a v else roots rel s b v
  | t@(.comprehend n bound guard body), v => insert (t.eval rel s v)
      (roots rel s bound v ∪ (elements (bound.eval rel s v)).biUnion (fun x =>
        roots rel s guard (Function.update v n x) ∪
        if guard.eval rel s (Function.update v n x) = Operational.truth then
          roots rel s body (Function.update v n x) else ∅))


-- @@ L520-520 verbatim
end Term


-- @@ L522-522 verbatim
namespace Rule


-- @@ L524-524 verbatim
variable [Fintype A]


-- @@ L526-537 verbatim
def roots (rel : R → A → A → Bool) (s : State F arity A) :
 Rule R F arity → (ℕ → HF A) → Finset (HF A)
 | .skip, _ => ∅
 | .update _ args value, v => value.roots rel s v ∪
     (List.ofFn (fun i => (args i).roots rel s v)).foldr (· ∪ ·) ∅
 | .parallel a b, v => roots rel s a v ∪ roots rel s b v
 | .conditional c a b, v => c.roots rel s v ∪
     if c.eval rel s v = Operational.truth then roots rel s a v else roots rel s b v
 | .forall n bound body, v => bound.roots rel s v ∪
     (elements (bound.eval rel s v)).biUnion (fun x => roots rel s body (Function.update v n x))
 | .letValue n value body, v => value.roots rel s v ∪
     roots rel s body (Function.update v n (value.eval rel s v))


-- @@ L539-539 verbatim
end Rule


-- @@ L541-541 verbatim
namespace Program


-- @@ L543-543 verbatim
variable (P : Program R) [Fintype A]


-- @@ L545-546 verbatim
def stepRoots (rel : R → A → A → Bool) (s : P.Store (A := A)) : Finset (HF A) :=
 if P.flag s .halt then ∅ else P.body.roots rel s (fun _ => Operational.empty)


-- @@ L548-551 verbatim
def occurring (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
 P.active rel h ∪ (range h).biUnion (fun j => match P.run rel j with
   | none => ∅
   | some s => familyClosure (P.stepRoots rel s))


-- @@ L553-555 verbatim
def evaluationAccepts (time space : Polynomial ℕ) (rel : R → A → A → Bool) : Prop :=
 ∃ h st, h ≤ time.eval (Fintype.card A) ∧ P.run rel h = some st ∧ P.flag st .halt ∧ P.flag st .accept ∧
   (P.occurring rel h).card ≤ space.eval (Fintype.card A)


-- @@ L557-557 verbatim
end Program


-- @@ L559-561 verbatim
def EvaluationDefinable (Q : ∀ {A : Type}, [Fintype A] → Input A → Prop) : Prop :=
 ∃ P : Program Symbol, ∃ time space : Polynomial ℕ,
   ∀ (A : Type) [Fintype A] (I : Input A), P.evaluationAccepts time space I.rel ↔ Q I


-- @@ L563-563 verbatim
end CPTSeparation.FullCPT


-- @@ L565-565 verbatim
namespace CPTSeparation.OrderedQuery


-- @@ L567-567 verbatim
section


-- @@ L569-569 verbatim
open Finset


-- @@ L571-571 verbatim
variable {N : ℕ}


-- @@ L573-573 verbatim
abbrev Data (N : ℕ) := Input (Fin N)


-- @@ L575-575 verbatim
end


-- @@ L577-582 verbatim
def indexSymbol (i : Fin 8) : Symbol :=
  if i.val = 0 then .Ed else
  if i.val = 1 then .Cf else
  if i.val = 2 then .EB else
  if i.val = 3 then .VB else
  if i.val = 4 then .I else .Z ((i.val-5 : ℕ) : Scalar)


-- @@ L584-584 verbatim
variable {N : ℕ}


-- @@ L586-589 verbatim
def cellValue (S : Data N) (k : Fin (8*(N*N))) : Bool :=
  let ij := finProdFinEquiv.symm k
  let ab := finProdFinEquiv.symm ij.2
  S.rel (indexSymbol ij.1) ab.1 ab.2


-- @@ L591-591 verbatim
def tableBits (S : Data N) : List Bool := List.ofFn (cellValue S)


-- @@ L593-593 verbatim
abbrev OrderedInput := Σ N, Data N


-- @@ L595-595 verbatim
end CPTSeparation.OrderedQuery


-- @@ L597-597 verbatim
namespace CPTSeparation.GaussMachine


-- @@ L599-599 verbatim
abbrev Letter := Option Scalar


-- @@ L601-601 verbatim
def boolCode (b : Bool) : List Letter := [some (if b then 1 else 0)]


-- @@ L603-603 verbatim
end CPTSeparation.GaussMachine


-- @@ L605-605 verbatim
namespace CPTSeparation.CounterLang


-- @@ L607-607 verbatim
abbrev Letter := Option Scalar


-- @@ L609-609 verbatim
end CPTSeparation.CounterLang


-- @@ L611-611 verbatim
namespace CPTSeparation.TableMachine


-- @@ L613-613 verbatim
open CounterLang


-- @@ L615-615 verbatim
def bitLetter (b : Bool) : Letter := some (if b then 1 else 0)


-- @@ L617-618 verbatim
def tableInput {N} (S : OrderedQuery.Data N) : List Letter :=
 (OrderedQuery.tableBits S).map bitLetter


-- @@ L620-621 verbatim
def code (S : OrderedQuery.OrderedInput) : List Letter :=
 List.replicate S.1 none ++ some 0 :: tableInput S.2


-- @@ L623-623 verbatim
end CPTSeparation.TableMachine


-- @@ L625-625 verbatim
namespace CPTSeparation


-- @@ L627-628 verbatim
def Input.ordered {A : Type} {N : ℕ} (S : Input A) (e : A ≃ Fin N) : OrderedQuery.Data N :=
  ⟨fun r i j => S.rel r (e.symm i) (e.symm j)⟩


-- @@ L630-635 verbatim
def OrdinaryPolynomialTime : Prop :=
  ∃ answer : OrderedQuery.OrderedInput → Bool,
    ∃ machine : Turing.TM2ComputableInPolyTime TableMachine.code GaussMachine.boolCode answer,
      (∀ k, Finite (machine.tm.Γ k)) ∧
      ∀ (A : Type) [Fintype A] (N : ℕ) (e : A ≃ Fin N) (S : Input A),
        answer ⟨N,S.ordered e⟩ = true ↔ S.query


-- @@ L637-637 verbatim
end CPTSeparation


-- @@ L639-639 verbatim
end


-- @@ L641-641 verbatim
end OAI
