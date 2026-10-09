import OAI.NumberTheory.SingleFold.MacroMachine


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace SingleFold.TM2Macro


-- @@ L9-9 verbatim
section

-- @@ L10-10 verbatim
open Turing Turing.PartrecToTM2 StateTransition Relation

-- @@ L11-11 verbatim
open Macro (mod5)

-- @@ L12-12 verbatim
abbrev Symbol := Γ'

-- @@ L13-13 verbatim
abbrev Store := Option Symbol

-- @@ L14-14 verbatim
abbrev Stack := K'

-- @@ L15-17 verbatim
instance : Fintype K' where
  elems := {.main,.rev,.aux,.stack}
  complete k := by cases k <;> simp

-- @@ L18-18 verbatim
abbrev Stmt (Λ : Type) := TM2.Stmt (fun _ : Stack=>Symbol) Λ Store

-- @@ L19-19 verbatim
abbrev Reg (n : ℕ) := Stack ⊕ Fin n

-- @@ L20-28 verbatim
inductive Label (n : ℕ) (Λ : Type)
  | code (q : Stmt Λ) (v : Store)
  | restore (k : Stack) (d : Fin 5) (q : Stmt Λ) (v : Store)
  | start (i : Fin (n+1))
  | divide (i : Fin n)
  | bit (i : Fin n)
  | pushBit (i : Fin n) (d : Fin 5)
  | reverse (i : Fin n)
  | pushRev (i : Fin n) (d : Fin 5)


-- @@ L30-31 verbatim
def digit : Symbol → Fin 5
  | .consₗ=>1 | .cons=>2 | .bit0=>3 | .bit1=>4

-- @@ L32-33 verbatim
def symbol (d : Fin 5) : Store :=
  if d.val=1 then some .consₗ else if d.val=2 then some .cons else if d.val=3 then some .bit0 else if d.val=4 then some .bit1 else none

-- @@ L34-34 verbatim
@[simp] lemma symbol_zero : symbol 0=none := rfl

-- @@ L35-35 verbatim
@[simp] lemma symbol_digit (s : Symbol) : symbol (digit s)=some s := by cases s <;> rfl

-- @@ L36-36 verbatim
lemma digit_pos (s : Symbol) : 0 < (digit s).val := by cases s <;> decide


-- @@ L38-40 verbatim
def pack : List Symbol → ℕ
  | []=>0
  | s::l=>5*pack l+(digit s).val

-- @@ L41-41 verbatim
@[simp] lemma pack_nil : pack []=0 := rfl

-- @@ L42-42 verbatim
@[simp] lemma pack_cons (s : Symbol) (l : List Symbol) : pack (s::l)=5*pack l+(digit s).val := rfl

-- @@ L43-46 verbatim
lemma pack_div (l : List Symbol) : pack l/5=pack l.tail := by
  cases l with
  | nil => rfl
  | cons s l => simp [Nat.mul_add_div, Nat.div_eq_of_lt (digit s).isLt]

-- @@ L47-50 verbatim
lemma pack_mod (l : List Symbol) : mod5 false (pack l)=l.head?.elim 0 digit := by
  cases l with
  | nil => rfl
  | cons s l => apply Fin.ext; simp [mod5,Macro.radix, Nat.mod_eq_of_lt (digit s).isLt]

-- @@ L51-52 verbatim
lemma pack_symbol (l : List Symbol) : symbol (mod5 false (pack l))=l.head? := by
  rw [pack_mod]; cases l <;> simp

-- @@ L53-57 verbatim
lemma pack_restore (l : List Symbol) :
    (if (mod5 false (pack l)).val=0 then pack l/5 else 5*(pack l/5)+(mod5 false (pack l)).val)=pack l := by
  cases l with
  | nil => rfl
  | cons s l => cases s <;> simp [pack,mod5,Macro.radix,digit,Nat.mul_add_div]


-- @@ L59-59 verbatim
variable {n : ℕ} {Λ : Type}

-- @@ L60-76 verbatim
def program (M : Λ → Stmt Λ) (initial : Λ) : Label n Λ → Macro.Instr (Label n Λ) (Reg n)
  | .code q v => match q with
    | .push k f q => .muladd (.inl k) (digit (f v)) (.code q v)
    | .peek k f q => .div (.inl k) false (fun d=>.restore k d q (f v (symbol d)))
    | .pop k f q => .div (.inl k) false (fun d=>.code q (f v (symbol d)))
    | .load f q => .goto (.code q (f v))
    | .branch f q r => .goto (.code (if f v then q else r) v)
    | .goto f => .goto (.code (M (f v)) v)
    | .halt => .halt
  | .restore k d q v => if d.val=0 then .goto (.code q v) else .muladd (.inl k) d (.code q v)
  | .start i => if hi : i.val=0 then .goto (.code (M initial) none)
      else .muladd (.inl .main) (digit .cons) (.divide ⟨i.val-1,by omega⟩)
  | .divide i => .test (.inr i) (.reverse i) (.bit i)
  | .bit i => .div (.inr i) true (fun d=>.pushBit i d)
  | .pushBit i d => .muladd (.inl .rev) (digit (if d.val=0 then .bit0 else .bit1)) (.divide i)
  | .reverse i => .div (.inl .rev) false (fun d=>if d.val=0 then .start i.castSucc else .pushRev i d)
  | .pushRev i d => .muladd (.inl .main) d (.reverse i)


-- @@ L78-78 verbatim
def values (S : Stack → List Symbol) (x : Fin n → ℕ) : Reg n → ℕ := Sum.elim (fun k=>pack (S k)) x

-- @@ L79-80 verbatim
def encode (M : Λ → Stmt Λ) (c : TM2.Cfg (fun _ : Stack=>Symbol) Λ Store) (x : Fin n → ℕ) : Macro.Cfg (Label n Λ) (Reg n) :=
  ⟨c.l.map (fun l=>.code (M l) c.var),values c.stk x⟩

-- @@ L81-82 verbatim
def codeCfg (q : Stmt Λ) (v : Store) (S : Stack → List Symbol) (x : Fin n → ℕ) : Macro.Cfg (Label n Λ) (Reg n) :=
  ⟨some (.code q v),values S x⟩

-- @@ L83-83 verbatim
@[simp] lemma values_inl (S : Stack → List Symbol) (x : Fin n → ℕ) (k : Stack) : values S x (.inl k)=pack (S k) := rfl

-- @@ L84-84 verbatim
@[simp] lemma values_inr (S : Stack → List Symbol) (x : Fin n → ℕ) (i : Fin n) : values S x (.inr i)=x i := rfl

-- @@ L85-90 verbatim
lemma values_update (S : Stack → List Symbol) (x : Fin n → ℕ) (k : Stack) (l : List Symbol) :
    values (Function.update S k l) x=Function.update (values S x) (.inl k) (pack l) := by
  funext i
  rcases i with j|j
  · by_cases h : j=k <;> simp [values,Function.update_apply,h]
  · simp [values,Function.update_apply]


-- @@ L92-142 verbatim
lemma stepAux_reaches (M : Λ → Stmt Λ) (initial : Λ) (q : Stmt Λ) (v : Store)
    (S : Stack → List Symbol) (x : Fin n → ℕ) :
    Reaches₁ (Macro.step (program M initial)) (codeCfg q v S x) (encode M (TM2.stepAux q v S) x) := by
  induction q generalizing v S with
  | halt => exact TransGen.single rfl
  | goto f => exact TransGen.single rfl
  | load f q ih => exact (ih (f v) S).head (r:=fun c d=>d∈Macro.step (program M initial) c) rfl
  | branch f q r ihq ihr =>
    cases h : f v
    · simpa only [Reaches₁,TM2.stepAux,h,Bool.false_eq_true,ite_false,Bool.cond_false] using
        (ihr v S).head (r:=fun c d=>d∈Macro.step (program M initial) c) (show Macro.step (program M initial) (codeCfg (.branch f q r) v S x)=some (codeCfg r v S x) by simp [Macro.step,Macro.next,program,codeCfg,h])
    · simpa only [Reaches₁,TM2.stepAux,h,ite_true,Bool.cond_true] using
        (ihq v S).head (r:=fun c d=>d∈Macro.step (program M initial) c) (show Macro.step (program M initial) (codeCfg (.branch f q r) v S x)=some (codeCfg q v S x) by simp [Macro.step,Macro.next,program,codeCfg,h])
  | push k f q ih =>
    apply (ih v (Function.update S k (f v::S k))).head (r:=fun c d=>d∈Macro.step (program M initial) c)
    change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.code q v)) (Function.update (values S x) (.inl k) (5*pack (S k)+(digit (f v)).val))) = some _
    rw [codeCfg,values_update,pack_cons]
  | pop k f q ih =>
    apply (ih (f v (S k).head?) (Function.update S k (S k).tail)).head (r:=fun c d=>d∈Macro.step (program M initial) c)
    change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.code q (f v (symbol (mod5 false (pack (S k))))))) (Function.update (values S x) (.inl k) (pack (S k)/5))) = some _
    rw [pack_symbol,pack_div,codeCfg,values_update]
  | peek k f q ih =>
    let d := mod5 false (pack (S k))
    let w := f v (S k).head?
    let V := Function.update (values S x) (.inl k) (pack (S k)/5)
    have h1 : Macro.step (program M initial) (codeCfg (.peek k f q) v S x)=
        some ⟨some (.restore k d q w),V⟩ := by
      change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.restore k d q (f v (symbol (mod5 false (pack (S k))))))) V)=some _
      rw [pack_symbol]
    have h2 : Macro.step (program M initial) ⟨some (.restore k d q w),V⟩=some (codeCfg q w S x) := by
      have hp : (if d.val=0 then pack (S k)/5 else 5*(pack (S k)/5)+d.val)=pack (S k) := pack_restore (S k)
      by_cases hd : d.val=0
      · rw [ite_eq_left hd] at hp
        have hv : V=values S x := by
          dsimp [V]; rw [hp]
          exact Function.update_eq_self _ _
        change some (Macro.next (program M initial) (.restore k d q w) V)=some _
        simp only [Macro.next,program,hd,ite_eq_left]
        rw [hv]; rfl
      · rw [ite_eq_right hd] at hp
        change some (Macro.next (program M initial) (.restore k d q w) V)=some _
        simp only [Macro.next,program,hd,ite_false]
        have hV : V (.inl k)=pack (S k)/5 := Function.update_self _ _ _
        rw [hV]
        dsimp only [V]
        rw [Function.update_idem,hp]
        change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.code q w)) (Function.update (values S x) (.inl k) (values S x (.inl k))))=some _
        rw [Function.update_eq_self]; rfl

    exact ((ih w S).head (r:=fun c d=>d∈Macro.step (program M initial) c) h2).head
      (r:=fun c d=>d∈Macro.step (program M initial) c) h1


-- @@ L144-150 verbatim
lemma respects (M : Λ → Stmt Λ) (initial : Λ) (x : Fin n → ℕ) :
    Respects (TM2.step M) (Macro.step (program M initial)) (fun c d=>encode M c x=d) := by
  apply fun_respects.mpr
  rintro ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => exact stepAux_reaches M initial (M l) v S x

-- @@ L151-153 verbatim
lemma eval_dom (M : Λ → Stmt Λ) (initial : Λ) (c : TM2.Cfg (fun _ : Stack=>Symbol) Λ Store) (x : Fin n → ℕ) :
    (eval (Macro.step (program M initial)) (encode M c x)).Dom ↔ (eval (TM2.step M) c).Dom :=
  tr_eval_dom (respects M initial x) rfl

-- @@ L154-154 verbatim
end


-- @@ L156-156 verbatim
section

-- @@ L157-157 verbatim
open Turing Turing.PartrecToTM2 StateTransition Relation

-- @@ L158-159 verbatim
lemma trNat_posNum (p : PosNum) : trNat (p:ℕ)=trPosNum p := by
  simp [trNat,trNum]

-- @@ L160-177 verbatim
lemma trNat_div (a : ℕ) (ha : a≠0) : trNat a=(if a%2=0 then Γ'.bit0 else Γ'.bit1)::trNat (a/2) := by
  have H (m : Num) (hm : (m:ℕ)≠0) : trNat (m:ℕ)=(if (m:ℕ)%2=0 then Γ'.bit0 else Γ'.bit1)::trNat ((m:ℕ)/2) := by
    cases m with
    | zero => exact (hm rfl).elim
    | pos p =>
      change trNat (p:ℕ)=_
      rw [trNat_posNum]
      cases p with
      | one => simp [trPosNum]
      | bit0 p =>
        have he : ((p:ℕ)+(p:ℕ))%2=0 := by omega
        have hd : ((p:ℕ)+(p:ℕ))/2=(p:ℕ) := by omega
        simp only [Num.cast_pos,PosNum.cast_bit0,he,ite_true,hd,trPosNum,trNat_posNum]
      | bit1 p =>
        have he : ((p:ℕ)+(p:ℕ)+1)%2≠0 := by omega
        have hd : ((p:ℕ)+(p:ℕ)+1)/2=(p:ℕ) := by omega
        simp only [Num.cast_pos,PosNum.cast_bit1,he,ite_false,hd,trPosNum,trNat_posNum]
  simpa only [Num.to_of_nat] using H (a:Num) (by simpa only [Num.to_of_nat] using ha)


-- @@ L179-179 verbatim
open Turing Turing.PartrecToTM2 StateTransition Relation

-- @@ L180-180 verbatim
open Macro (mod5)

-- @@ L181-181 verbatim
variable {n : ℕ} {Λ : Type}

-- @@ L182-182 verbatim
def initValues (L R : List Symbol) (x : Fin n → ℕ) : Reg n → ℕ := values (K'.elim L R [] []) x

-- @@ L183-184 verbatim
def initCfg (q : Label n Λ) (L R : List Symbol) (x : Fin n → ℕ) : Macro.Cfg (Label n Λ) (Reg n) :=
  ⟨some q,initValues L R x⟩

-- @@ L185-185 verbatim
@[simp] lemma initValues_main (L R : List Symbol) (x : Fin n → ℕ) : initValues L R x (.inl .main)=pack L := rfl

-- @@ L186-186 verbatim
@[simp] lemma initValues_rev (L R : List Symbol) (x : Fin n → ℕ) : initValues L R x (.inl .rev)=pack R := rfl

-- @@ L187-187 verbatim
@[simp] lemma initValues_input (L R : List Symbol) (x : Fin n → ℕ) (i : Fin n) : initValues L R x (.inr i)=x i := rfl

-- @@ L188-193 verbatim
lemma initValues_update_main (L R L' : List Symbol) (x : Fin n → ℕ) :
    Function.update (initValues L R x) (.inl .main) (pack L')=initValues L' R x := by
  funext j
  rcases j with k|i
  · cases k <;> simp [initValues,values,K'.elim]
  · simp [initValues,values]

-- @@ L194-199 verbatim
lemma initValues_update_rev (L R R' : List Symbol) (x : Fin n → ℕ) :
    Function.update (initValues L R x) (.inl .rev) (pack R')=initValues L R' x := by
  funext j
  rcases j with k|i
  · cases k <;> simp [initValues,values,K'.elim]
  · simp [initValues,values]

-- @@ L200-203 verbatim
lemma initValues_update_input (L R : List Symbol) (x : Fin n → ℕ) (i : Fin n) (a : ℕ) :
    Function.update (initValues L R x) (.inr i) a=initValues L R (Function.update x i a) := by
  funext j
  rcases j with k|j <;> simp [initValues,values,Function.update_apply]

-- @@ L204-204 verbatim
variable (M : Λ → Stmt Λ) (initial : Λ)

-- @@ L205-205 verbatim
local notation "F" => Macro.step (program M initial)

-- @@ L206-207 verbatim
lemma prepend {c d e : Macro.Cfg (Label n Λ) (Reg n)} (ht : Reaches₁ F d e) (h : F c=some d) : Reaches₁ F c e :=
  TransGen.head (r:=fun c d=>d∈F c) h ht


-- @@ L209-227 verbatim
lemma reverse_loop (i : Fin n) (L R : List Symbol) (x : Fin n → ℕ) :
    Reaches₁ F (initCfg (.reverse i) L R x) (initCfg (.start i.castSucc) (R.reverse++L) [] x) := by
  induction R generalizing L with
  | nil =>
    apply TransGen.single
    have hv : Function.update (initValues L [] x) (.inl .rev) 0=initValues L [] x :=
      initValues_update_rev L [] [] x
    simp [Macro.step,initCfg,Macro.next,program,Macro.radix,hv]
  | cons s R ih =>
    have h1 : F (initCfg (.reverse i) L (s::R) x)=some (initCfg (.pushRev i (digit s)) L R x) := by
      change some (Macro.Cfg.mk (Q:=Label n Λ) (some (if (mod5 false (pack (s::R))).val=0 then .start i.castSucc else .pushRev i (mod5 false (pack (s::R))))) (Function.update (initValues L (s::R) x) (.inl .rev) (pack (s::R)/5)))=some _
      rw [show mod5 false (pack (s::R))=digit s from pack_mod _,
        show pack (s::R)/5=pack R from pack_div _, initValues_update_rev,
        ite_eq_right (Nat.ne_of_gt (digit_pos s))]
      rfl
    have h2 : F (initCfg (.pushRev i (digit s)) L R x)=some (initCfg (.reverse i) (s::L) R x) := by
      change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.reverse i)) (Function.update (initValues L R x) (.inl .main) (pack (s::L))))=some _
      rw [initValues_update_main]; rfl
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using prepend M initial (prepend M initial (ih (s::L)) h2) h1


-- @@ L229-252 verbatim
lemma divide_loop (i : Fin n) (L R : List Symbol) (x : Fin n → ℕ) (a : ℕ) :
    Reaches₁ F (initCfg (.divide i) L R (Function.update x i a))
      (initCfg (.reverse i) L ((trNat a).reverse++R) (Function.update x i 0)) := by
  induction a using Nat.strong_induction_on generalizing R with
  | h a ih =>
    have hx : Function.update x i a i=a := Function.update_self _ _ _
    by_cases ha : a=0
    · subst a
      apply TransGen.single
      change some (Macro.Cfg.mk (Q:=Label n Λ) (some (if Function.update x i 0 i=0 then .reverse i else .bit i)) (initValues L R (Function.update x i 0)))=some _
      rw [Function.update_self,ite_eq_left rfl]
      simp only [trNat_zero,List.reverse_nil,List.nil_append,initCfg]
    · let s : Symbol := if a%2=0 then .bit0 else .bit1
      have h1 : F (initCfg (.divide i) L R (Function.update x i a))=some (initCfg (.bit i) L R (Function.update x i a)) := by
        change some (Macro.Cfg.mk (Q:=Label n Λ) (some (if Function.update x i a i=0 then .reverse i else .bit i)) (initValues L R (Function.update x i a)))=some _
        rw [hx,ite_eq_right ha]; rfl
      have h2 : F (initCfg (.bit i) L R (Function.update x i a))=some (initCfg (.pushBit i (mod5 true a)) L R (Function.update x i (a/2))) := by
        change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.pushBit i (mod5 true (Function.update x i a i)))) (Function.update (initValues L R (Function.update x i a)) (.inr i) (Function.update x i a i/2)))=some _
        rw [hx,initValues_update_input,Function.update_idem]; rfl
      have h3 : F (initCfg (.pushBit i (mod5 true a)) L R (Function.update x i (a/2)))=some (initCfg (.divide i) L (s::R) (Function.update x i (a/2))) := by
        change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.divide i)) (Function.update (initValues L R (Function.update x i (a/2))) (.inl .rev) (pack (s::R))))=some _
        rw [initValues_update_rev]; rfl
      have ht := prepend M initial (prepend M initial (prepend M initial (ih (a/2) (Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)) (s::R)) h3) h2) h1
      simpa only [trNat_div a ha,List.reverse_cons,List.append_assoc,List.singleton_append] using ht


-- @@ L254-266 verbatim
lemma one_input (i : Fin n) (L : List Symbol) (x : Fin n → ℕ) :
    Reaches₁ F (initCfg (.start i.succ) L [] x)
      (initCfg (.start i.castSucc) (trNat (x i)++Γ'.cons::L) [] (Function.update x i 0)) := by
  have h1 : F (initCfg (.start i.succ) L [] x)=some (initCfg (.divide i) (Γ'.cons::L) [] x) := by
    simp only [Macro.step,initCfg,Macro.next,program,Option.map_some,Fin.val_succ,
      Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,dite_false,Nat.add_sub_cancel,initValues_main]
    change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.divide i)) (Function.update (initValues L [] x) (.inl .main) (pack (Γ'.cons::L))))=some _
    rw [initValues_update_main]
  have h2 := divide_loop M initial i (Γ'.cons::L) [] x (x i)
  simp only [Function.update_eq_self,List.append_nil] at h2
  have h3 := reverse_loop M initial i (Γ'.cons::L) (trNat (x i)).reverse (Function.update x i 0)
  simp only [List.reverse_reverse] at h3
  exact prepend M initial (h2.trans h3) h1

-- @@ L267-267 verbatim
end


-- @@ L269-269 verbatim
open Turing Turing.PartrecToTM2 StateTransition Relation

-- @@ L270-270 verbatim
variable {n : ℕ} {Λ : Type}

-- @@ L271-272 verbatim
def inputPrefix (x : Fin n → ℕ) (k : ℕ) (hk : k≤n) : List ℕ :=
  List.ofFn (fun j : Fin k=>x ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)

-- @@ L273-273 verbatim
def clearPrefix (x : Fin n → ℕ) (k : ℕ) : Fin n → ℕ := fun j=>if j.val<k then 0 else x j

-- @@ L274-278 verbatim
lemma prefix_succ (x : Fin n → ℕ) (k : ℕ) (hk : k+1≤n) :
    inputPrefix x (k+1) hk=inputPrefix x k (by omega)++[x ⟨k,by omega⟩] := by
  unfold inputPrefix
  rw [List.ofFn_succ',List.concat_eq_append]
  rfl

-- @@ L279-283 verbatim
lemma prefix_update (x : Fin n → ℕ) (k : ℕ) (hk : k<n) :
    inputPrefix (Function.update x ⟨k,hk⟩ 0) k (by omega)=inputPrefix x k (by omega) := by
  apply congrArg List.ofFn
  funext j
  exact Function.update_of_ne (by intro he; have hh:=congrArg Fin.val he; exact Nat.ne_of_lt j.isLt hh) _ _

-- @@ L284-293 verbatim
lemma clearPrefix_update (x : Fin n → ℕ) (k : ℕ) (hk : k<n) :
    clearPrefix (Function.update x ⟨k,hk⟩ 0) k=clearPrefix x (k+1) := by
  funext j
  by_cases h : j.val<k
  · simp [clearPrefix,h,show j.val<k+1 by omega]
  · by_cases he : j.val=k
    · have hej : j=⟨k,hk⟩ := Fin.ext he
      simp [clearPrefix,hej]
    · have hej : j≠⟨k,hk⟩ := fun hh=>he (congrArg Fin.val hh)
      simp [clearPrefix,h,show ¬j.val<k+1 by omega,Function.update_of_ne hej]

-- @@ L294-297 verbatim
lemma trList_append (L R : List ℕ) : trList (L++R)=trList L++trList R := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.cons_append,trList,ih,List.append_assoc,List.cons_append]

-- @@ L298-298 verbatim
variable (M : Λ → Stmt Λ) (initial : Λ)

-- @@ L299-299 verbatim
local notation "F" => Macro.step (program M initial)

-- @@ L300-315 verbatim
lemma init_loop (k : ℕ) (hk : k≤n) (L : List Symbol) (x : Fin n → ℕ) :
    Reaches F (initCfg (.start ⟨k,by omega⟩) L [] x)
      (initCfg (.start 0) (trList (inputPrefix x k hk)++L) [] (clearPrefix x k)) := by
  induction k generalizing L x with
  | zero =>
    have hc : clearPrefix x 0=x := by funext j; simp [clearPrefix]
    rw [hc]
    exact ReflTransGen.refl
  | succ k ih =>
    have ht := (one_input M initial (⟨k,by omega⟩:Fin n) L x).to_reflTransGen
    have hs := ih (by omega) (trNat (x ⟨k,by omega⟩)++Γ'.cons::L) (Function.update x ⟨k,by omega⟩ 0)
    rw [prefix_update,clearPrefix_update] at hs
    have hh := ht.trans hs
    change ReflTransGen (fun c d=>d∈F c) _ _
    simp only [prefix_succ,trList_append,trList,List.append_assoc,List.cons_append,List.nil_append]
    exact hh


-- @@ L317-327 verbatim
lemma initialize_reaches (x : Fin n → ℕ) :
    Reaches₁ F (initCfg (.start (Fin.last n)) [] [] x)
      (codeCfg (M initial) none (K'.elim (trList (List.ofFn x)) [] [] []) (fun _=>0)) := by
  have ht := init_loop M initial n le_rfl [] x
  have hp : inputPrefix x n le_rfl=List.ofFn x := rfl
  have hc : clearPrefix x n=(fun _=>0) := by funext j; simp [clearPrefix,j.isLt]
  rw [hp,hc,List.append_nil] at ht
  apply TransGen.tail' ht
  change some (Macro.next (program M initial) (.start 0) _)=some _
  simp only [Macro.next,program,Fin.val_zero]
  rfl

-- @@ L328-328 verbatim
end SingleFold.TM2Macro


-- @@ L330-330 verbatim
namespace SingleFold.Macro

-- @@ L331-331 verbatim
open StateTransition Relation

-- @@ L332-332 verbatim
open scoped Classical

-- @@ L333-333 verbatim
variable {Q Q' J : Type} [DecidableEq J]

-- @@ L334-337 verbatim
def Instr.map (f : Q → Q') : Instr Q J → Instr Q' J
  | .halt=>.halt | .goto q=>.goto (f q) | .inc j q=>.inc j (f q)
  | .test j q r=>.test j (f q) (f r) | .muladd j d q=>.muladd j d (f q)
  | .div j b q=>.div j b (f ∘ q)

-- @@ L338-340 verbatim
def Instr.Within (p : Q → Prop) : Instr Q J → Prop
  | .halt=>True | .goto q=>p q | .inc _ q=>p q
  | .test _ q r=>p q ∧ p r | .muladd _ _ q=>p q | .div _ _ q=>∀ d,p (q d)

-- @@ L341-341 verbatim
def Cfg.map (f : Q → Q') (c : Cfg Q J) : Cfg Q' J := ⟨c.label.map f,c.value⟩

-- @@ L342-343 verbatim
def retract (p : Q → Prop) (q₀ : {q // p q}) (q : Q) : {q // p q} :=
  if h : p q then ⟨q,h⟩ else q₀

-- @@ L344-345 verbatim
def restrict (M : Q → Instr Q J) (p : Q → Prop) (q₀ : {q // p q}) : {q // p q} → Instr {q // p q} J :=
  fun q=>Instr.map (retract p q₀) (M q.val)

-- @@ L346-347 verbatim
lemma retract_val (p : Q → Prop) (q₀ : {q // p q}) (q : Q) (hq : p q) : (retract p q₀ q).val=q := by
  simp [retract,hq]

-- @@ L348-351 verbatim
omit [DecidableEq J] in
lemma instr_retract (p : Q → Prop) (q₀ : {q // p q}) (i : Instr Q J) (hi : i.Within p) :
    Instr.map Subtype.val (Instr.map (retract p q₀) i)=i := by
  cases i <;> simp_all [Instr.map,Instr.Within,retract,Function.comp_def]

-- @@ L352-356 verbatim
lemma cfg_next_map (f : Q → Q') (M : Q → Instr Q J) (q : Q) (v : J → ℕ) :
    Cfg.map f (next M q v)=next (fun _=>Instr.map f (M q)) (f q) v := by
  cases h : M q <;> simp only [next,h,Instr.map,Cfg.map]
  case test j p r => split <;> rfl
  all_goals rfl

-- @@ L357-363 verbatim
lemma restrict_next (M : Q → Instr Q J) (p : Q → Prop) (q₀ : {q // p q})
    (hM : ∀ q,p q → (M q).Within p) (q : {q // p q}) (v : J → ℕ) :
    Cfg.map Subtype.val (next (restrict M p q₀) q v)=next M q.val v := by
  rw [cfg_next_map]
  have he : Instr.map Subtype.val (restrict M p q₀ q)=M q.val := instr_retract p q₀ _ (hM q q.property)
  rw [he]
  rfl

-- @@ L364-374 verbatim
lemma restrict_respects (M : Q → Instr Q J) (p : Q → Prop) (q₀ : {q // p q})
    (hM : ∀ q,p q → (M q).Within p) :
    Respects (step (restrict M p q₀)) (step M) (fun c d=>Cfg.map Subtype.val c=d) := by
  apply fun_respects.mpr
  rintro ⟨l,v⟩
  cases l with
  | none => rfl
  | some q =>
    apply TransGen.single
    change some (next M q.val v)=some (Cfg.map Subtype.val (next (restrict M p q₀) q v))
    rw [restrict_next M p q₀ hM]

-- @@ L375-378 verbatim
lemma restrict_eval_dom (M : Q → Instr Q J) (p : Q → Prop) (q₀ : {q // p q})
    (hM : ∀ q,p q → (M q).Within p) (c : Cfg {q // p q} J) :
    (eval (step (restrict M p q₀)) c).Dom ↔ (eval (step M) (Cfg.map Subtype.val c)).Dom :=
  (tr_eval_dom (restrict_respects M p q₀ hM) rfl).symm

-- @@ L379-379 verbatim
end SingleFold.Macro


-- @@ L381-381 verbatim
end


-- @@ L383-383 verbatim
end OAI
