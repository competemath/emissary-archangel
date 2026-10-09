import OAI.GroupTheory.UniversalGroup.TuringMachines


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w x


-- @@ L7-7 verbatim
namespace Higman.WordBinary

-- @@ L8-8 verbatim
open Turing.PartrecToTM2

-- @@ L9-9 verbatim
abbrev Letter := Bool × Bool × Bool


-- @@ L11-11 verbatim
def push (a : Letter) (n : ℕ) : ℕ := Nat.bit a.1 (Nat.bit a.2.1 (Nat.bit a.2.2 n))

-- @@ L12-14 verbatim
def code : List Letter → ℕ
  | [] => 1
  | a::w => push a (code w)


-- @@ L16-16 verbatim
def symbol (b : Bool) : Γ' := if b then .bit1 else .bit0


-- @@ L18-20 verbatim
def spelling : List Letter → List Γ'
  | [] => [.bit1]
  | a::w => symbol a.1 :: symbol a.2.1 :: symbol a.2.2 :: spelling w


-- @@ L22-24 verbatim
lemma push_ge (a : Letter) (n : ℕ) : 8*n ≤ push a n := by
  rcases a with ⟨b,c,d⟩
  cases b <;> cases c <;> cases d <;> simp [push,Nat.bit] <;> omega


-- @@ L26-29 verbatim
lemma code_pos (w : List Letter) : 0 < code w := by
  induction w with
  | nil => decide
  | cons a w ih => have := push_ge a (code w); change 0 < push a (code w); omega


-- @@ L31-41 verbatim
lemma push_inj {a b : Letter} {m n : ℕ} (h : push a m = push b n) : a = b ∧ m = n := by
  have h₁ := congrArg Nat.bodd h
  have ht := congrArg Nat.div2 h
  simp only [push,Nat.bodd_bit,Nat.div2_bit] at h₁ ht
  have h₂ := congrArg Nat.bodd ht
  have hu := congrArg Nat.div2 ht
  simp only [Nat.bodd_bit,Nat.div2_bit] at h₂ hu
  have h₃ := congrArg Nat.bodd hu
  have hm := congrArg Nat.div2 hu
  simp only [Nat.bodd_bit,Nat.div2_bit] at h₃ hm
  exact ⟨Prod.ext h₁ (Prod.ext h₂ h₃),hm⟩


-- @@ L43-65 verbatim
lemma code_injective : Function.Injective code := by
  intro v
  induction v with
  | nil =>
    intro w h
    cases w with
    | nil => rfl
    | cons a w =>
      have hp := code_pos w
      have hg := push_ge a (code w)
      change 1 = push a (code w) at h
      omega
  | cons a v ih =>
    intro w h
    cases w with
    | nil =>
      have hp := code_pos v
      have hg := push_ge a (code v)
      change push a (code v) = 1 at h
      omega
    | cons b w =>
      obtain ⟨rfl,he⟩ := push_inj h
      exact congrArg (List.cons a) (ih he)


-- @@ L67-78 verbatim
lemma trNat_bit (b : Bool) (n : ℕ) (hn : 0 < n) :
    trNat (Nat.bit b n) = symbol b :: trNat n := by
  have hcast : (n : Num) ≠ 0 := by
    intro h
    have := congrArg (fun m : Num ↦ (m : ℕ)) h
    simp only [Num.to_of_nat,Num.cast_zero] at this
    omega
  unfold trNat
  rw [← Num.ofNat'_eq,Num.ofNat'_bit,Num.ofNat'_eq]
  cases h : (n : Num) with
  | zero => exact False.elim (hcast h)
  | pos p => cases b <;> rfl


-- @@ L80-88 verbatim
lemma trNat_code (w : List Letter) : trNat (code w) = spelling w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hp := code_pos w
    have hbit (b : Bool) (n : ℕ) (hn : 0 < n) : 0 < Nat.bit b n := by
      cases b <;> simp [Nat.bit]; omega
    simp only [code,push,trNat_bit _ _ (hbit _ _ (hbit _ _ hp)),
      trNat_bit _ _ (hbit _ _ hp),trNat_bit _ _ hp,ih,spelling]


-- @@ L90-97 verbatim
lemma push_primrec : Primrec₂ push := by
  let digit : Letter → ℕ := fun a ↦ push a 0
  have h : Primrec (fun p : Letter × ℕ ↦ 8*p.2+digit p.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.snd)
      ((Primrec.dom_finite digit).comp Primrec.fst)
  apply h.of_eq
  rintro ⟨⟨b,c,d⟩,n⟩
  cases b <;> cases c <;> cases d <;> simp [digit,push,Nat.bit] <;> omega


-- @@ L99-106 verbatim
lemma code_primrec : Primrec code := by
  have h := Primrec.list_foldr (α := List Letter) Primrec.id (Primrec.const 1)
    (push_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro w
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [id_eq,List.foldr_cons,code] using congrArg (push a) ih


-- @@ L108-108 verbatim
end Higman.WordBinary


-- @@ L110-110 verbatim
namespace Higman.RangeRecognizer

-- @@ L111-111 verbatim
open Turing ToPartrec PartrecToTM2


-- @@ L113-114 verbatim
def search (r : ℕ → ℕ) (n : ℕ) : Part ℕ :=
  Nat.rfind (fun k ↦ Part.some (decide (r k = n)))


-- @@ L116-118 verbatim
lemma search_dom (r : ℕ → ℕ) (n : ℕ) : (search r n).Dom ↔ n ∈ Set.range r := by
  exact (Nat.rfind_dom (p := fun k ↦ Part.some (decide (r k = n)))).trans
    (by simp [Set.mem_range])


-- @@ L120-122 verbatim
lemma search_partrec (r : ℕ → ℕ) (hr : Computable r) : Partrec (search r) := by
  apply Partrec.rfind
  exact ((Primrec.eq.decide.to_comp).comp (hr.comp Computable.snd) Computable.fst).partrec.to₂


-- @@ L124-131 verbatim
theorem exists_code (r : ℕ → ℕ) (hr : Computable r) :
    ∃ c : Code, ∀ n, (c.eval [n]).Dom ↔ n ∈ Set.range r := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr (search_partrec r hr))
  refine ⟨c,fun n ↦ ?_⟩
  have he := hc ⟨[n],rfl⟩
  change c.eval [n] = _ at he
  rw [he]
  exact search_dom r n


-- @@ L133-147 verbatim
lemma halt_iff_dom (c : Code) (v : List ℕ) :
    (∃ S x, TM2.Reaches tr (init c v) ⟨none,x,S⟩) ↔ (c.eval v).Dom := by
  constructor
  · rintro ⟨S,x,h⟩
    have hm : (⟨none,x,S⟩ : Cfg') ∈ StateTransition.eval (TM2.step tr) (init c v) :=
      StateTransition.mem_eval.mpr ⟨h,rfl⟩
    rw [tr_eval] at hm
    obtain ⟨w,hw,_⟩ := (Part.mem_map_iff _).mp hm
    exact hw.1
  · intro h
    let w := (c.eval v).get h
    have hw : halt w ∈ StateTransition.eval (TM2.step tr) (init c v) := by
      rw [tr_eval]
      exact (Part.mem_map_iff _).mpr ⟨w,Part.get_mem h,rfl⟩
    exact ⟨(halt w).stk,(halt w).var,(StateTransition.mem_eval.mp hw).1⟩


-- @@ L149-149 verbatim
end Higman.RangeRecognizer


-- @@ L151-151 verbatim
noncomputable section

-- @@ L152-152 verbatim
namespace Higman.RecognizingStack

-- @@ L153-153 verbatim
open Turing ToPartrec PartrecToTM2 WordBinary AffineStack StackProgram Function Relation

-- @@ L154-154 verbatim
variable {G : Type} [Group G]


-- @@ L156-156 verbatim
instance : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩


-- @@ L158-158 verbatim
def support (c : Code) := codeSupp c Cont'.halt

-- @@ L159-159 verbatim
abbrev MState (c : Code) := TM2StackCompiler.State tr (support c)

-- @@ L160-160 verbatim
abbrev MEdge (c : Code) := TM2StackCompiler.Edge tr (support c)

-- @@ L161-163 verbatim
local instance (c : Code) : Fintype (MEdge c) := by
  exact TM2StackCompiler.instFintypeEdge (K := K') (Γ := Γ') (σ := Option Γ')
    tr (support c)

-- @@ L164-165 verbatim
def mprog (c : Code) : MEdge c → Instruction K' Γ' G (MState c) :=
  TM2StackCompiler.compile tr (support c) (tr_supports c Cont'.halt).2


-- @@ L167-169 verbatim
inductive State (c : Code)
  | ready | first (a : Letter) | second (a : Letter) | machine (q : MState c) | done
  deriving Fintype

-- @@ L170-173 verbatim
inductive Edge (c : Code)
  | first (a : Letter) | second (a : Letter) | third (a : Letter) | enter
  | machine (e : MEdge c) | exit (v : Option Γ')
  deriving Fintype


-- @@ L175-180 verbatim
def initialState (c : Code) : MState c := by
  classical
  exact (⟨some (tr (trNormal c Cont'.halt)),by
    apply Finset.some_mem_insertNone.mpr
    apply Finset.mem_biUnion.mpr
    exact ⟨trNormal c Cont'.halt,(tr_supports c Cont'.halt).1,TM2.stmts₁_self⟩⟩,none)


-- @@ L182-183 verbatim
def finalState (c : Code) (v : Option Γ') : MState c :=
  (⟨none,Finset.none_mem_insertNone⟩,v)


-- @@ L185-192 verbatim
def prog (c : Code) (weight : Letter → G) : Edge c → Instruction K' Γ' G (State c)
  | .first a => ⟨.ready,.first a,.onStack .main (.push (symbol a.2.2)),1⟩
  | .second a => ⟨.first a,.second a,.onStack .main (.push (symbol a.2.1)),1⟩
  | .third a => ⟨.second a,.ready,.onStack .main (.push (symbol a.1)),weight a⟩
  | .enter => ⟨.ready,.machine (initialState c),.idle,1⟩
  | .machine e => ⟨.machine (mprog (G := G) c e).source,.machine (mprog (G := G) c e).target,
      (mprog (G := G) c e).action,1⟩
  | .exit v => ⟨.machine (finalState c v),.done,.idle,1⟩


-- @@ L194-194 verbatim
def store (s : List Γ') : K' → List Γ' := K'.elim s [] [] []

-- @@ L195-195 verbatim
def encoded (w : List Letter) := spelling w ++ [.cons]

-- @@ L196-196 verbatim
def seed (c : Code) : (K' → List Γ') × State c := (store (encoded []),.ready)


-- @@ L198-201 verbatim
lemma store_push (s : List Γ') (a : Γ') :
    update (store s) .main (a :: store s .main) = store (a::s) := by
  funext k
  cases k <;> simp [store]


-- @@ L203-207 verbatim
lemma initial_forget (c : Code) (w : List Letter) :
    TM2StackCompiler.forget tr (support c) (store (encoded w),initialState c) =
      MicroTM2.translate tr (init c [code w]) := by
  simp [TM2StackCompiler.forget,initialState,MicroTM2.translate,init,store,encoded,trNat_code]
  rfl


-- @@ L209-217 verbatim
def Correct (c : Code) (weight : Letter → G) (g : G) : ((K' → List Γ') × State c) → Prop
  | (S,.ready) => ∃ w, S = store (encoded w) ∧ g = HistoryMachine.value weight w
  | (S,.first a) => ∃ w, S = store (symbol a.2.2 :: encoded w) ∧ g = HistoryMachine.value weight w
  | (S,.second a) => ∃ w, S = store (symbol a.2.1 :: symbol a.2.2 :: encoded w) ∧
      g = HistoryMachine.value weight w
  | (S,.machine q) => ∃ w, g = HistoryMachine.value weight w ∧
      StateTransition.Reaches (MicroTM2.step tr) (MicroTM2.translate tr (init c [code w]))
        (TM2StackCompiler.forget tr (support c) (S,q))
  | (_,.done) => ∃ w, g = HistoryMachine.value weight w ∧ (c.eval [code w]).Dom


-- @@ L219-220 verbatim
lemma correct_seed (c : Code) (weight : Letter → G) : Correct c weight 1 (seed c) :=
  ⟨[],rfl,rfl⟩


-- @@ L222-258 verbatim
lemma correct_step (c : Code) (weight : Letter → G) (e : Edge c)
    (S T : K' → List Γ') (g : G) (hr : (prog c weight e).action.Rel S T)
    (hc : Correct c weight g (S,(prog c weight e).source)) :
    Correct c weight (g * (prog c weight e).weight) (T,(prog c weight e).target) := by
  cases e with
  | first a =>
    obtain ⟨w,rfl,hg⟩ := hc
    obtain ⟨t,ht,rfl⟩ := hr
    cases ht
    exact ⟨w,store_push _ _,by simpa [prog] using hg⟩
  | second a =>
    obtain ⟨w,rfl,hg⟩ := hc
    obtain ⟨t,ht,rfl⟩ := hr
    cases ht
    exact ⟨w,store_push _ _,by simpa [prog] using hg⟩
  | third a =>
    obtain ⟨w,rfl,rfl⟩ := hc
    obtain ⟨t,ht,rfl⟩ := hr
    cases ht
    refine ⟨a::w,?_,rfl⟩
    exact store_push _ _
  | enter =>
    obtain ⟨w,rfl,hg⟩ := hc
    cases hr
    refine ⟨w,by simpa [prog] using hg,?_⟩
    rw [initial_forget]
    exact .refl
  | machine e =>
    obtain ⟨w,hg,hh⟩ := hc
    refine ⟨w,by simpa [prog] using hg,hh.tail ?_⟩
    exact TM2StackCompiler.compile_sound tr (support c) (tr_supports c Cont'.halt).2 e S T hr
  | exit v =>
    obtain ⟨w,hg,hh⟩ := hc
    cases hr
    refine ⟨w,by simpa [prog] using hg,?_⟩
    apply (RangeRecognizer.halt_iff_dom c [code w]).mp
    exact ⟨S,v,(MicroTM2.reaches_halt_iff tr _ S v).mpr hh⟩


-- @@ L260-265 verbatim
lemma run_correct (c : Code) (weight : Letter → G) {s : List (Edge c)}
    {d : (K' → List Γ') × State c} (h : Run (prog c weight) (seed c) s d) :
    Correct c weight (HistoryMachine.value (fun e ↦ (prog c weight e).weight) s) d := by
  induction h with
  | start => exact correct_seed c weight
  | step e S T hr h ih => exact correct_step c weight e S T _ hr ih


-- @@ L267-282 verbatim
lemma build_word (c : Code) (weight : Letter → G) (w : List Letter) :
    ∃ s, Run (prog c weight) (seed c) s (store (encoded w),.ready) ∧
      HistoryMachine.value (fun e ↦ (prog c weight e).weight) s = HistoryMachine.value weight w := by
  induction w with
  | nil => exact ⟨[],Run.start,rfl⟩
  | cons a w ih =>
    obtain ⟨s,hs,hv⟩ := ih
    refine ⟨.third a :: .second a :: .first a :: s,?_,?_⟩
    · apply Run.step (prog := prog c weight) (Edge.third a) (store (symbol a.2.1 :: symbol a.2.2 :: encoded w)) _
      · exact ⟨_,rfl,(store_push _ _).symm⟩
      apply Run.step (prog := prog c weight) (Edge.second a) (store (symbol a.2.2 :: encoded w)) _
      · exact ⟨_,rfl,(store_push _ _).symm⟩
      apply Run.step (prog := prog c weight) (Edge.first a) (store (encoded w)) _
      · exact ⟨_,rfl,(store_push _ _).symm⟩
      exact hs
    · simpa only [HistoryMachine.value,prog,mul_one] using congrArg (fun g ↦ g * weight a) hv


-- @@ L284-288 verbatim
lemma enter_word (c : Code) (weight : Letter → G) (w : List Letter) :
    ∃ s, Run (prog c weight) (seed c) s (store (encoded w),.machine (initialState c)) ∧
      HistoryMachine.value (fun e ↦ (prog c weight e).weight) s = HistoryMachine.value weight w := by
  obtain ⟨s,hs,hv⟩ := build_word c weight w
  exact ⟨.enter::s,Run.step (prog := prog c weight) Edge.enter _ _ rfl hs,by simpa only [HistoryMachine.value,prog,mul_one] using hv⟩


-- @@ L290-300 verbatim
lemma run_machine (c : Code) (weight : Letter → G) (w : List Letter) {s : List (MEdge c)}
    {d : (K' → List Γ') × MState c}
    (h : Run (mprog (G := G) c) (store (encoded w),initialState c) s d) :
    ∃ t, Run (prog c weight) (seed c) t (d.1,.machine d.2) ∧
      HistoryMachine.value (fun e ↦ (prog c weight e).weight) t = HistoryMachine.value weight w := by
  induction h with
  | start => exact enter_word c weight w
  | step e S T hr h ih =>
    obtain ⟨t,ht,hv⟩ := ih
    exact ⟨.machine e::t,Run.step (prog := prog c weight) (Edge.machine e) S T hr ht,
      by simpa only [HistoryMachine.value,prog,mul_one] using hv⟩


-- @@ L302-318 verbatim
lemma halt_word (c : Code) (weight : Letter → G) (w : List Letter) (h : (c.eval [code w]).Dom) :
    HistoryMachine.value weight w ∈ outputs (prog c weight) (seed c) .done := by
  obtain ⟨S,v,hm⟩ := (RangeRecognizer.halt_iff_dom c [code w]).mpr h
  have hh := (MicroTM2.reaches_halt_iff tr _ S v).mp hm
  rw [← initial_forget c w] at hh
  obtain ⟨s,d,hr,hd⟩ := TM2StackCompiler.reaches_complete (G := G) tr (support c)
    (tr_supports c Cont'.halt).2 hh
  have hq : d.2 = finalState c v := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun x ↦ x.2.1) hd
    · exact congrArg (fun x ↦ x.2.2) hd
  obtain ⟨t,ht,hv⟩ := run_machine c weight w hr
  have ht' : Run (prog c weight) (seed c) t (d.1,.machine (finalState c v)) := by
    simpa only [hq] using ht
  refine ⟨.exit v::t,d.1,Run.step (prog := prog c weight) (Edge.exit v) _ _ rfl ht',?_⟩
  simpa only [HistoryMachine.value,prog,mul_one] using hv.symm


-- @@ L320-329 verbatim
theorem outputs_eq (c : Code) (weight : Letter → G) :
    outputs (prog c weight) (seed c) .done =
      {g | ∃ w, (c.eval [code w]).Dom ∧ g = HistoryMachine.value weight w} := by
  ext g
  constructor
  · rintro ⟨s,S,hs,rfl⟩
    obtain ⟨w,hw,hd⟩ := run_correct c weight hs
    exact ⟨w,hd,hw⟩
  · rintro ⟨w,hd,rfl⟩
    exact halt_word c weight w hd


-- @@ L331-331 verbatim
end Higman.RecognizingStack


-- @@ L333-333 verbatim
namespace Higman

-- @@ L334-334 verbatim
open WordBinary

-- @@ L335-335 verbatim
variable {G : Type} [Group G] [Group.IsFinitelyPresented G]


-- @@ L337-354 verbatim
theorem benign_enumerated_words (enumerate : ℕ → List Letter)
    (he : Computable enumerate) (weight : Letter → G) :
    IsBenign (Subgroup.closure (Set.range (fun n ↦ HistoryMachine.value weight (enumerate n)))) := by
  obtain ⟨c,hc⟩ := RangeRecognizer.exists_code (fun n ↦ code (enumerate n))
    (code_primrec.to_comp.comp he)
  have hh := StackProgram.benign_outputs (RecognizingStack.prog c weight)
    (RecognizingStack.seed c) RecognizingStack.State.done
  rw [RecognizingStack.outputs_eq] at hh
  have hs : {g | ∃ w, (c.eval [code w]).Dom ∧ g = HistoryMachine.value weight w} =
      Set.range (fun n ↦ HistoryMachine.value weight (enumerate n)) := by
    ext g
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨n,hn⟩ := (hc (code w)).mp hw
      exact ⟨n,congrArg (HistoryMachine.value weight) (code_injective hn)⟩
    · rintro ⟨n,rfl⟩
      exact ⟨enumerate n,(hc _).mpr ⟨n,rfl⟩,rfl⟩
  rwa [hs] at hh


-- @@ L356-356 verbatim
end Higman


-- @@ L358-358 verbatim
namespace Higman.HistoryMachine

-- @@ L359-359 verbatim
variable {E G : Type*} [Group G]

-- @@ L360-364 verbatim
lemma value_append (weight : E → G) (v w : List E) :
    value weight (v ++ w) = value weight w * value weight v := by
  induction v with
  | nil => simp [value]
  | cons a v ih => simp only [List.cons_append,value,ih,mul_assoc]

-- @@ L365-365 verbatim
end Higman.HistoryMachine


-- @@ L367-367 verbatim
namespace Higman.NormalWords


-- @@ L369-369 verbatim
section

-- @@ L370-370 verbatim
open WordBinary

-- @@ L371-371 verbatim
abbrev Alphabet := Bool ⊕ Unit

-- @@ L372-372 verbatim
abbrev Raw := List (Alphabet × Bool)


-- @@ L374-376 verbatim
def encodeLetter : Alphabet × Bool → Letter
  | (.inl a,b) => (false,a,b)
  | (.inr _,b) => (true,false,b)


-- @@ L378-378 verbatim
def generator (a : Letter) : Alphabet := if a.1 then .inr () else .inl a.2.1

-- @@ L379-380 verbatim
def weight (a : Letter) : FreeGroup Alphabet :=
  if a.2.2 then FreeGroup.of (generator a) else (FreeGroup.of (generator a))⁻¹


-- @@ L382-382 verbatim
def encodeWord (w : Raw) : List Letter := w.reverse.map encodeLetter


-- @@ L384-392 verbatim
lemma encoded_value (w : Raw) : HistoryMachine.value weight (encodeWord w) = FreeGroup.mk w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [encodeWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      HistoryMachine.value_append,HistoryMachine.value,one_mul] at *
    rw [ih]
    rcases a with ⟨a,b⟩
    cases a <;> cases b <;> rfl


-- @@ L394-395 verbatim
lemma encodeWord_primrec : Primrec encodeWord :=
  Primrec.list_map Primrec.list_reverse ((Primrec.dom_finite encodeLetter).comp Primrec.snd)


-- @@ L397-397 verbatim
def conjugator (n : ℕ) : Raw := (Encodable.decode (α := Raw) n).getD []

-- @@ L398-399 verbatim
def conjugated (r : ℕ → Raw) (n : ℕ) : Raw :=
  conjugator n.unpair.1 ++ r n.unpair.2 ++ FreeGroup.invRev (conjugator n.unpair.1)


-- @@ L401-401 verbatim
def enumerate (r : ℕ → Raw) (n : ℕ) : List Letter := encodeWord (conjugated r n)


-- @@ L403-404 verbatim
lemma conjugator_primrec : Primrec conjugator :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])


-- @@ L406-411 verbatim
lemma invRev_primrec : Primrec (@FreeGroup.invRev Alphabet) := by
  unfold FreeGroup.invRev
  apply Primrec.list_reverse.comp
  apply Primrec.list_map Primrec.id
  exact (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.dom_bool Bool.not).comp (Primrec.snd.comp Primrec.snd))


-- @@ L413-419 verbatim
lemma enumerate_computable (r : ℕ → Raw) (hr : Computable r) : Computable (enumerate r) := by
  apply encodeWord_primrec.to_comp.comp
  have hc : Computable (fun n : ℕ ↦ conjugator n.unpair.1) :=
    conjugator_primrec.to_comp.comp (Primrec.fst.comp Primrec.unpair).to_comp
  exact Primrec.list_append.to_comp.comp
    (Primrec.list_append.to_comp.comp hc (hr.comp (Primrec.snd.comp Primrec.unpair).to_comp))
    (invRev_primrec.to_comp.comp hc)


-- @@ L421-422 verbatim
lemma conjugator_encode (w : Raw) : conjugator (Encodable.encode w) = w := by
  simp only [conjugator,Encodable.encodek,Option.getD_some]


-- @@ L424-427 verbatim
lemma mk_conjugated (r : ℕ → Raw) (n : ℕ) :
    FreeGroup.mk (conjugated r n) = FreeGroup.mk (conjugator n.unpair.1) *
      FreeGroup.mk (r n.unpair.2) * (FreeGroup.mk (conjugator n.unpair.1))⁻¹ := by
  simp only [conjugated,← FreeGroup.mul_mk,← FreeGroup.inv_mk]


-- @@ L429-445 verbatim
theorem range_values (r : ℕ → Raw) :
    Set.range (fun n ↦ HistoryMachine.value weight (enumerate r n)) =
      Group.conjugatesOfSet (Set.range (fun n ↦ FreeGroup.mk (r n))) := by
  ext g
  constructor
  · rintro ⟨n,rfl⟩
    change HistoryMachine.value weight (encodeWord (conjugated r n)) ∈ _
    rw [encoded_value,mk_conjugated]
    exact Group.mem_conjugatesOfSet_iff.mpr
      ⟨_,⟨n.unpair.2,rfl⟩,isConj_iff.mpr ⟨_,rfl⟩⟩
  · intro h
    obtain ⟨x,⟨k,rfl⟩,hx⟩ := Group.mem_conjugatesOfSet_iff.mp h
    obtain ⟨a,ha⟩ := isConj_iff.mp hx
    obtain ⟨w,rfl⟩ := Quot.exists_rep a
    refine ⟨Nat.pair (Encodable.encode w) k,?_⟩
    simp only [enumerate,encoded_value,mk_conjugated,Nat.unpair_pair,conjugator_encode]
    exact ha


-- @@ L447-447 verbatim
end


-- @@ L449-453 verbatim
theorem benign_normalClosure (r : ℕ → Raw) (hr : Computable r) :
    IsBenign (Subgroup.normalClosure (Set.range (fun n ↦ FreeGroup.mk (r n)))) := by
  have h := benign_enumerated_words (enumerate r) (enumerate_computable r hr) weight
  rw [range_values] at h
  exact h


-- @@ L455-465 verbatim
theorem embeds_presentation (r : ℕ → Raw) (hr : Computable r) :
    ∃ (K : Type) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : PresentedGroup (Set.range (fun n ↦ FreeGroup.mk (r n))) →* K),
      Function.Injective i := by
  apply embeds_of_benign_kernel (PresentedGroup.mk _) (PresentedGroup.mk_surjective _)
  have he : (PresentedGroup.mk (Set.range (fun n ↦ FreeGroup.mk (r n)))).ker =
      Subgroup.normalClosure (Set.range (fun n ↦ FreeGroup.mk (r n))) := by
    ext g
    exact PresentedGroup.mk_eq_one_iff
  rw [he]
  exact benign_normalClosure r hr


-- @@ L467-467 verbatim
end Higman.NormalWords


-- @@ L469-469 verbatim
end


-- @@ L471-471 verbatim
end OAI
