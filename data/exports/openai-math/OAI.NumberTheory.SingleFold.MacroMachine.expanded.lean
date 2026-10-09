import OAI.NumberTheory.SingleFold.CounterCompilation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SingleFold.Counter

-- @@ L6-6 verbatim
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]

-- @@ L7-8 verbatim
def step (M : Machine Q J) (c : Cfg Q J) : Option (Cfg Q J) :=
  match M.instr c.state with | .halt=>none | _=>some (next M c)

-- @@ L9-9 verbatim
end SingleFold.Counter


-- @@ L11-11 verbatim
namespace SingleFold.Macro


-- @@ L13-13 verbatim
section

-- @@ L14-14 verbatim
open Counter StateTransition Relation

-- @@ L15-21 verbatim
inductive Instr (Q J : Type)
  | halt
  | goto (p : Q)
  | inc (j : J) (p : Q)
  | test (j : J) (pz pp : Q)
  | muladd (j : J) (e : Fin 5) (p : Q)
  | div (j : J) (binary : Bool) (p : Fin 5 → Q)


-- @@ L23-23 verbatim
def radix (binary : Bool) : ℕ := if binary then 2 else 5

-- @@ L24-26 verbatim
structure Cfg (Q J : Type) where
  label : Option Q
  value : J → ℕ

-- @@ L27-27 verbatim
variable {Q J : Type}

-- @@ L28-35 verbatim
def next [DecidableEq J] (M : Q → Instr Q J) (q : Q) (v : J → ℕ) : Cfg Q J :=
  match M q with
  | .halt => ⟨none,v⟩
  | .goto p => ⟨some p,v⟩
  | .inc j p => ⟨some p,Function.update v j (v j+1)⟩
  | .test j pz pp => ⟨some (if v j=0 then pz else pp),v⟩
  | .muladd j e p => ⟨some p,Function.update v j (5*v j+e)⟩
  | .div j b p => ⟨some (p ⟨v j%radix b,by have h := Nat.mod_lt (v j) (show 0 < radix b by cases b <;> decide); cases b <;> simp_all [radix]; omega⟩),Function.update v j (v j/radix b)⟩

-- @@ L36-37 verbatim
def step [DecidableEq J] (M : Q → Instr Q J) (c : Cfg Q J) : Option (Cfg Q J) :=
  c.label.map (fun q=>next M q c.value)


-- @@ L39-49 verbatim
inductive State (Q : Type)
  | main (q : Q)
  | grow (q : Q) (i : Fin 5)
  | copy (q : Q) (r : Fin 5)
  | copyInc (q : Q) (r : Fin 5)
  | add (q : Q) (i : Fin 5)
  | quotient (q : Q) (r : Fin 5)
  | carry (q : Q)
  | restore (q : Q)
  | halt
  deriving DecidableEq, Fintype

-- @@ L50-50 verbatim
abbrev Reg (J : Type) := J ⊕ Bool

-- @@ L51-51 verbatim
def scratch : Reg J := .inr false

-- @@ L52-52 verbatim
def zeroReg : Reg J := .inr true


-- @@ L54-54 verbatim
def succ5 (i : Fin 5) : Fin 5 := ⟨(i.val+1)%5,Nat.mod_lt _ (by omega)⟩

-- @@ L55-55 verbatim
def go (s : State Q) : Counter.Instr (State Q) (Reg J) := .test zeroReg s s


-- @@ L57-61 verbatim
def finish (M : Q → Instr Q J) (q : Q) (r : Fin 5) : State Q :=
  match M q with
  | .muladd _ _ _ => .add q 0
  | .div _ _ p => .main (p r)
  | _ => .halt


-- @@ L63-87 verbatim
def compileInstr (M : Q → Instr Q J) : State Q → Counter.Instr (State Q) (Reg J)
  | .main q => match M q with
    | .halt => go .halt
    | .goto p => go (.main p)
    | .inc j p => .inc (.inl j) (.main p)
    | .test j pz _ => .test (.inl j) (.main pz) (.restore q)
    | .muladd j _ _ => .test (.inl j) (.copy q 0) (.grow q 0)
    | .div _ _ _ => go (.quotient q 0)
  | .grow q i => .inc scratch (if i.val=4 then .main q else .grow q (succ5 i))
  | .copy q r => .test scratch (finish M q r) (.copyInc q r)
  | .copyInc q r => match M q with
    | .muladd j _ _ | .div j _ _ => .inc (.inl j) (.copy q r)
    | _ => go .halt
  | .add q i => match M q with
    | .muladd j e p => if i.val<e.val then .inc (.inl j) (.add q (succ5 i)) else go (.main p)
    | _ => go .halt
  | .quotient q r => match M q with
    | .div j b _ => .test (.inl j) (.copy q r)
        (if r.val+1=radix b then .carry q else .quotient q (succ5 r))
    | _ => go .halt
  | .carry q => .inc scratch (.quotient q 0)
  | .restore q => match M q with
    | .test j _ p => .inc (.inl j) (.main p)
    | _ => go .halt
  | .halt => .halt


-- @@ L89-103 verbatim
def compile (M : Q → Instr Q J) (start : Q) : Counter.Machine (State Q) (Reg J) where
  instr := compileInstr M
  start := .main start
  halt := .halt
  halt_iff q := by
    cases q with
    | main q => cases h : M q <;> simp [compileInstr, h, go]
    | grow q i => simp [compileInstr]
    | copy q r => simp [compileInstr]
    | copyInc q r => cases h : M q <;> simp [compileInstr, h, go]
    | add q i => cases h : M q <;> simp [compileInstr, h, go]; split <;> simp
    | quotient q r => cases h : M q <;> simp [compileInstr, h, go]
    | carry q => simp [compileInstr]
    | restore q => cases h : M q <;> simp [compileInstr, h, go]
    | halt => simp [compileInstr]


-- @@ L105-105 verbatim
variable [DecidableEq J]

-- @@ L106-107 verbatim
def cfg (s : State Q) (v : J → ℕ) (a : ℕ) : Counter.Cfg (State Q) (Reg J) :=
  ⟨s,Sum.elim v (fun b=>if b then 0 else a)⟩

-- @@ L108-109 verbatim
def encode (c : Cfg Q J) : Counter.Cfg (State Q) (Reg J) :=
  cfg (c.label.elim .halt State.main) c.value 0

-- @@ L110-110 verbatim
variable [DecidableEq Q]


-- @@ L112-120 verbatim
omit [DecidableEq Q] in
lemma inc_reg (M : Q → Instr Q J) (start : Q) (s t : State Q) (v : J → ℕ) (a : ℕ) (j : J)
    (hi : compileInstr M s=.inc (.inl j) t) :
    Counter.step (compile M start) (cfg s v a)=some (cfg t (Function.update v j (v j+1)) a) := by
  simp only [Counter.step,compile,cfg,hi,Counter.next,Sum.elim_inl]
  congr 1
  congr 1
  funext i
  cases i <;> simp [Function.update_apply]

-- @@ L121-131 verbatim
omit [DecidableEq Q] in
lemma inc_scratch (M : Q → Instr Q J) (start : Q) (s t : State Q) (v : J → ℕ) (a : ℕ)
    (hi : compileInstr M s=.inc scratch t) :
    Counter.step (compile M start) (cfg s v a)=some (cfg t v (a+1)) := by
  simp only [Counter.step,compile,cfg,hi,Counter.next,scratch,Sum.elim_inr,Bool.false_eq_true,ite_false]
  congr 1
  congr 1
  funext i
  rcases i with j|b
  · simp
  · cases b <;> simp

-- @@ L132-140 verbatim
omit [DecidableEq Q] in
lemma test_reg (M : Q → Instr Q J) (start : Q) (s t u : State Q) (v : J → ℕ) (a : ℕ) (j : J)
    (hi : compileInstr M s=.test (.inl j) t u) :
    Counter.step (compile M start) (cfg s v a)=
      some (if v j=0 then cfg t v a else cfg u (Function.update v j (v j-1)) a) := by
  simp only [Counter.step,compile,cfg,hi,Counter.next,Sum.elim_inl]
  by_cases h : v j=0
  · simp [h]
  · simp only [h, ite_false]; congr 1; congr 1; funext i; cases i <;> simp [Function.update_apply]

-- @@ L141-152 verbatim
omit [DecidableEq Q] in
lemma test_scratch (M : Q → Instr Q J) (start : Q) (s t u : State Q) (v : J → ℕ) (a : ℕ)
    (hi : compileInstr M s=.test scratch t u) :
    Counter.step (compile M start) (cfg s v a)=
      some (if a=0 then cfg t v a else cfg u v (a-1)) := by
  simp only [Counter.step,compile,cfg,hi,Counter.next,scratch,Sum.elim_inr,Bool.false_eq_true,ite_false]
  split_ifs
  · rfl
  · congr 1; congr 1; funext i
    rcases i with j|b
    · simp
    · cases b <;> simp

-- @@ L153-157 verbatim
omit [DecidableEq Q] in
lemma goto (M : Q → Instr Q J) (start : Q) (s t : State Q) (v : J → ℕ) (a : ℕ)
    (hi : compileInstr M s=go t) :
    Counter.step (compile M start) (cfg s v a)=some (cfg t v a) := by
  simp [Counter.step,compile,cfg,hi,go,Counter.next,zeroReg]

-- @@ L158-158 verbatim
end


-- @@ L160-160 verbatim
section

-- @@ L161-161 verbatim
open Counter StateTransition Relation

-- @@ L162-162 verbatim
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]

-- @@ L163-163 verbatim
variable (M : Q → Instr Q J) (start : Q)

-- @@ L164-164 verbatim
local notation "F" => Counter.step (compile M start)

-- @@ L165-168 verbatim
omit [DecidableEq Q] in
lemma prepend {c d e : Counter.Cfg (State Q) (Reg J)}
    (ht : Reaches₁ F d e) (h : F c=some d) : Reaches₁ F c e :=
  TransGen.head (r:=fun c d=>d∈F c) h ht

-- @@ L169-173 verbatim
omit [DecidableEq Q] in
lemma inc_at (s t : State Q) (v : J → ℕ) (a n : ℕ) (j : J)
    (hi : compileInstr M s=.inc (.inl j) t) :
    F (cfg s (Function.update v j n) a)=some (cfg t (Function.update v j (n+1)) a) := by
  simpa using inc_reg M start s t (Function.update v j n) a j hi

-- @@ L174-178 verbatim
omit [DecidableEq Q] in
lemma test_at_zero (s t u : State Q) (v : J → ℕ) (a : ℕ) (j : J)
    (hi : compileInstr M s=.test (.inl j) t u) :
    F (cfg s (Function.update v j 0) a)=some (cfg t (Function.update v j 0) a) := by
  simpa using test_reg M start s t u (Function.update v j 0) a j hi

-- @@ L179-183 verbatim
omit [DecidableEq Q] in
lemma test_at_succ (s t u : State Q) (v : J → ℕ) (a n : ℕ) (j : J)
    (hi : compileInstr M s=.test (.inl j) t u) :
    F (cfg s (Function.update v j (n+1)) a)=some (cfg u (Function.update v j n) a) := by
  simpa using test_reg M start s t u (Function.update v j (n+1)) a j hi


-- @@ L185-199 verbatim
omit [DecidableEq Q] in
lemma grow_loop (q : Q) (i : Fin 5) (v : J → ℕ) (a : ℕ) :
    Reaches₁ F (cfg (.grow q i) v a) (cfg (.main q) v (a+(5-i.val))) := by
  induction i using Fin.reverseInduction generalizing a with
  | last =>
    exact TransGen.single (by simpa using inc_scratch M start (.grow q 4) (.main q) v a rfl)
  | cast i ih =>
    have hi : i.val < 4 := i.isLt
    have hs : succ5 i.castSucc=i.succ := by ext; simp [succ5]; omega
    have hh : compileInstr M (.grow q i.castSucc)=.inc scratch (.grow q i.succ) := by
      simp only [compileInstr,Fin.val_castSucc]
      rw [ite_eq_right (by omega),hs]
    have he := inc_scratch M start (.grow q i.castSucc) (.grow q i.succ) v a hh
    have ht := prepend M start (ih (a+1)) he
    convert ht using 1 ; congr 1 ; simp only [Fin.val_castSucc,Fin.val_succ] ; omega


-- @@ L201-214 verbatim
omit [DecidableEq Q] in
lemma multiply_loop (q : Q) (j : J) (e : Fin 5) (p : Q) (hm : M q=.muladd j e p)
    (v : J → ℕ) (n a : ℕ) :
    Reaches₁ F (cfg (.main q) (Function.update v j n) a)
      (cfg (.copy q 0) (Function.update v j 0) (a+5*n)) := by
  induction n generalizing a with
  | zero =>
    apply TransGen.single
    simpa using test_at_zero M start (.main q) (.copy q 0) (.grow q 0) v a j (by simp [compileInstr,hm])
  | succ n ih =>
    have h1 := test_at_succ M start (.main q) (.copy q 0) (.grow q 0) v a n j (by simp [compileInstr,hm])
    have h2 := grow_loop M start q 0 (Function.update v j n) a
    have h3 := prepend M start (h2.trans (ih (a+5))) h1
    convert h3 using 1 ; congr 1 ; omega


-- @@ L216-232 verbatim
omit [DecidableEq Q] in
lemma copy_loop (q : Q) (j : J) (r : Fin 5)
    (hm : (∃e p,M q=.muladd j e p) ∨ (∃b p,M q=.div j b p))
    (v : J → ℕ) (n a : ℕ) :
    Reaches₁ F (cfg (.copy q r) (Function.update v j n) a)
      (cfg (finish M q r) (Function.update v j (n+a)) 0) := by
  induction a generalizing n with
  | zero =>
    apply TransGen.single
    simpa using test_scratch M start (.copy q r) (finish M q r) (.copyInc q r) (Function.update v j n) 0 rfl
  | succ a ih =>
    have h1 := test_scratch M start (.copy q r) (finish M q r) (.copyInc q r) (Function.update v j n) (a+1) rfl
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel] at h1
    have hh : compileInstr M (.copyInc q r)=.inc (.inl j) (.copy q r) := by
      rcases hm with ⟨e,p,h⟩|⟨b,p,h⟩ <;> simp [compileInstr,h]
    have h2 := inc_at M start (.copyInc q r) (.copy q r) v a n j hh
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using prepend M start (prepend M start (ih (n+1)) h2) h1


-- @@ L234-254 verbatim
omit [DecidableEq Q] in
lemma add_loop (q : Q) (j : J) (e : Fin 5) (p : Q) (hm : M q=.muladd j e p)
    (i : Fin 5) (hi : i.val ≤ e.val) (v : J → ℕ) (n a : ℕ) :
    Reaches₁ F (cfg (.add q i) (Function.update v j n) a)
      (cfg (.main p) (Function.update v j (n+(e.val-i.val))) a) := by
  induction i using Fin.reverseInduction generalizing n with
  | last =>
    have hh : e.val=4 := by have := e.isLt; simp only [Fin.val_last] at hi; omega
    apply TransGen.single
    simpa [hh] using goto M start (.add q 4) (.main p) (Function.update v j n) a (by simp [compileInstr,hm,hh])
  | cast i ih =>
    simp only [Fin.val_castSucc] at hi
    by_cases he : i.val=e.val
    · apply TransGen.single
      simpa [he] using goto M start (.add q i.castSucc) (.main p) (Function.update v j n) a (by simp [compileInstr,hm,he])
    · have hs : succ5 i.castSucc=i.succ := by ext; simp [succ5]; have := i.isLt; omega
      have h1 := inc_at M start (.add q i.castSucc) (.add q i.succ) v a n j (by
        simp only [compileInstr,hm,Fin.val_castSucc]; rw [ite_eq_left (by omega),hs])
      have h2 := prepend M start (ih (by simp only [Fin.val_succ]; omega) (n+1)) h1
      have har : n+(e.val-i.val)=(n+1)+(e.val-(i.val+1)) := by omega
      simpa only [Fin.val_castSucc,Fin.val_succ,har] using h2

-- @@ L255-255 verbatim
end


-- @@ L257-257 verbatim
open Counter StateTransition Relation

-- @@ L258-258 verbatim
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]

-- @@ L259-259 verbatim
lemma radix_pos (b : Bool) : 0 < radix b := by cases b <;> decide

-- @@ L260-260 verbatim
lemma radix_le (b : Bool) : radix b ≤ 5 := by cases b <;> decide

-- @@ L261-261 verbatim
def mod5 (b : Bool) (n : ℕ) : Fin 5 := ⟨n%radix b,(Nat.mod_lt _ (radix_pos b)).trans_le (radix_le b)⟩

-- @@ L262-262 verbatim
@[simp] lemma mod5_val (b : Bool) (n : ℕ) : (mod5 b n).val=n%radix b := rfl

-- @@ L263-264 verbatim
lemma mod5_self (b : Bool) (r : Fin 5) (hr : r.val<radix b) : mod5 b r.val=r :=
  Fin.ext (Nat.mod_eq_of_lt hr)

-- @@ L265-265 verbatim
variable (M : Q → Instr Q J) (start : Q)

-- @@ L266-266 verbatim
local notation "F" => Counter.step (compile M start)

-- @@ L267-292 verbatim
omit [DecidableEq Q] in
lemma quotient_loop (q : Q) (j : J) (b : Bool) (p : Fin 5 → Q) (hm : M q=.div j b p)
    (v : J → ℕ) (n : ℕ) (r : Fin 5) (hr : r.val<radix b) (a : ℕ) :
    Reaches₁ F (cfg (.quotient q r) (Function.update v j n) a)
      (cfg (.copy q (mod5 b (n+r.val))) (Function.update v j 0) (a+(n+r.val)/radix b)) := by
  induction n generalizing r a with
  | zero =>
    apply TransGen.single
    simpa [mod5_self b r hr, Nat.div_eq_of_lt hr] using test_at_zero M start (.quotient q r) (.copy q r)
      (if r.val+1=radix b then .carry q else .quotient q (succ5 r)) v a j (by simp [compileInstr,hm])
  | succ n ih =>
    have h1 := test_at_succ M start (.quotient q r) (.copy q r)
      (if r.val+1=radix b then .carry q else .quotient q (succ5 r)) v a n j (by simp [compileInstr,hm])
    by_cases he : r.val+1=radix b
    · simp only [he,ite_eq_left] at h1
      have h2 := inc_scratch M start (.carry q) (.quotient q 0) (Function.update v j n) a rfl
      have h3 := prepend M start (prepend M start (ih 0 (radix_pos b) (a+1)) h2) h1
      have har : n+1+r.val=n+radix b := by omega
      simpa [har,mod5,radix_pos b,Nat.add_div_right, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h3
    · have hs : (succ5 r).val=r.val+1 := by
        apply Nat.mod_eq_of_lt
        have := radix_le b
        omega
      simp only [he,ite_false] at h1
      have h3 := prepend M start (ih (succ5 r) (by rw [hs]; omega) a) h1
      simpa only [hs, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h3


-- @@ L294-333 verbatim
omit [DecidableEq Q] in
lemma simulate (q : Q) (v : J → ℕ) :
    Reaches₁ F (cfg (.main q) v 0) (encode (next M q v)) := by
  cases hm : M q with
  | halt =>
    apply TransGen.single
    simpa [next,hm,encode] using goto M start (.main q) .halt v 0 (by simp [compileInstr,hm])
  | goto p =>
    apply TransGen.single
    simpa [next,hm,encode] using goto M start (.main q) (.main p) v 0 (by simp [compileInstr,hm])
  | inc j p =>
    apply TransGen.single
    simpa [next,hm,encode] using inc_reg M start (.main q) (.main p) v 0 j (by simp [compileInstr,hm])
  | test j pz pp =>
    have h1 := test_reg M start (.main q) (.main pz) (.restore q) v 0 j (by simp [compileInstr,hm])
    by_cases hz : v j=0
    · apply TransGen.single
      simpa [next,hm,encode,hz] using h1
    · simp only [hz,ite_false] at h1
      have h2 := inc_at M start (.restore q) (.main pp) v 0 (v j-1) j (by simp [compileInstr,hm])
      have har : v j-1+1=v j := by omega
      have ht : Reaches₁ F (cfg (.restore q) (Function.update v j (v j-1)) 0) (cfg (.main pp) v 0) :=
        TransGen.single (by simpa [har] using h2)
      simpa [next,hm,encode,hz] using prepend M start ht h1
  | muladd j e p =>
    have h1 := multiply_loop M start q j e p hm v (v j) 0
    have h2 := copy_loop M start q j 0 (Or.inl ⟨e,p,hm⟩) v 0 (5*v j)
    have h3 := add_loop M start q j e p hm 0 (Nat.zero_le _) v (5*v j) 0
    simp only [Nat.zero_add] at h1
    simp only [finish,hm,Nat.zero_add] at h2
    simp only [Fin.val_zero,Nat.sub_zero] at h3
    have ht := (h1.trans h2).trans h3
    simpa [next,hm,encode,Reaches₁] using ht
  | div j b p =>
    have h1 := goto M start (.main q) (.quotient q 0) v 0 (by simp [compileInstr,hm])
    have h2 := quotient_loop M start q j b p hm v (v j) 0 (radix_pos b) 0
    have h3 := copy_loop M start q j (mod5 b (v j)) (Or.inr ⟨b,p,hm⟩) v 0 (v j/radix b)
    simp only [Fin.val_zero,Nat.add_zero,Nat.zero_add,Function.update_eq_self] at h2
    simp only [finish,hm,Nat.zero_add] at h3
    simpa [next,hm,encode,mod5] using prepend M start (h2.trans h3) h1


-- @@ L335-342 verbatim
omit [DecidableEq Q] in
lemma respects : Respects (step M) F (fun c d=>encode c=d) := by
  apply fun_respects.mpr
  intro c
  rcases c with ⟨label,v⟩
  cases label with
  | none => simp [step,encode,FRespects,Counter.step,compile,compileInstr,cfg]
  | some q => exact simulate M start q v

-- @@ L343-346 verbatim
omit [DecidableEq Q] in
lemma eval_dom (c : Cfg Q J) :
    (eval F (encode c)).Dom ↔ (eval (step M) c).Dom :=
  tr_eval_dom (respects M start) rfl

-- @@ L347-347 verbatim
end SingleFold.Macro


-- @@ L349-349 verbatim
namespace SingleFold.Counter

-- @@ L350-350 verbatim
open StateTransition Relation

-- @@ L351-351 verbatim
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]

-- @@ L352-355 verbatim
omit [DecidableEq Q] in
lemma step_eq_none (M : Machine Q J) (c : Cfg Q J) : step M c=none ↔ c.state=M.halt := by
  rw [←M.halt_iff c.state]
  cases h : M.instr c.state <;> simp [step,h]

-- @@ L356-369 verbatim
omit [DecidableEq Q] in
lemma reaches_iterate (M : Machine Q J) {c e : Cfg Q J} (h : Reaches (step M) c e) :
    ∃t,(next M)^[t] c=e := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | @tail d e h hd ih =>
    rcases ih with ⟨t,rfl⟩
    refine ⟨t+1,?_⟩
    rw [Function.iterate_succ_apply']
    change step M ((next M)^[t] c)=some e at hd
    unfold step at hd
    split at hd
    · contradiction
    · exact Option.some.inj hd

-- @@ L370-380 verbatim
omit [DecidableEq Q] in
lemma reaches_run (M : Machine Q J) (d : J → ℕ) (t : ℕ) :
    Reaches (step M) ⟨M.start,d⟩ (run M d t) := by
  induction t with
  | zero => exact ReflTransGen.refl
  | succ t ih =>
    rw [run_succ]
    cases h : M.instr (run M d t).state with
    | halt => simpa only [next,h] using ih
    | inc j p => exact ih.tail (by simp [step,h])
    | test j pz pd => exact ih.tail (by simp [step,h])

-- @@ L381-385 verbatim
lemma halts_iff_exists (M : Machine Q J) (d : J → ℕ) : Halts M d ↔ ∃t,(run M d t).state=M.halt := by
  constructor
  · rintro ⟨t,ht,_⟩; exact ⟨t,ht⟩
  · intro h
    exact ⟨Nat.find h,Nat.find_spec h,fun t ht=>Nat.find_min h ht⟩

-- @@ L386-398 verbatim
lemma eval_dom_iff_halts (M : Machine Q J) (d : J → ℕ) :
    (eval (step M) ⟨M.start,d⟩).Dom ↔ Halts M d := by
  rw [halts_iff_exists]
  constructor
  · intro h
    obtain ⟨hr,hh⟩ := mem_eval.mp (Part.get_mem h)
    obtain ⟨t,ht⟩ := reaches_iterate M hr
    refine ⟨t,?_⟩
    have := (step_eq_none M _).mp hh
    simpa only [run,ht] using this
  · rintro ⟨t,ht⟩
    have h := mem_eval.mpr ⟨reaches_run M d t,(step_eq_none M _).mpr ht⟩
    exact Part.dom_iff_mem.mpr ⟨_,h⟩

-- @@ L399-399 verbatim
end SingleFold.Counter


-- @@ L401-401 verbatim
end OAI
