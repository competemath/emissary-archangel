import OAI.Computability.RationalHitting.DenseDeterminant


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace RationalHitting.StackLanguage

-- @@ L6-6 verbatim
open Function


-- @@ L8-13 verbatim
lemma unaryMulStep_iterate (a : Unary×Unary) (n : ℕ) :
    (fun a : Unary×Unary => (a.1,Unary.mk (a.2.val+a.1.val)))^[n] a=
      (a.1,Unary.mk (a.2.val+n*a.1.val)) := by
  induction n with
  | zero => cases a; cases ‹Unary› ; simp
  | succ n ih => simp only [iterate_succ_apply',ih];congr 2;simp [Nat.succ_mul,Nat.add_assoc]


-- @@ L15-15 verbatim
namespace Poly

-- @@ L16-29 verbatim
@[fun_prop] theorem unaryMul : Poly (fun a : Unary×Unary => Unary.mk (a.1.val*a.2.val)) := by
  have hs : Poly (fun a : Unary×Unary => (a.1,Unary.mk (a.2.val+a.1.val))) :=
    (show Poly (Prod.fst : Unary×Unary → Unary) from fst).pair
      (unaryAdd.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop))
  have ht := hs.iterate (10*(TimeBound.variable+1)^2) (by
    intro n a i hi
    simp only [unaryMulStep_iterate,prod_code_length,unary_code_length,TimeBound.eval_mul,
      TimeBound.eval_numeral,TimeBound.eval_pow,TimeBound.eval_add,TimeBound.eval_variable,
      pairCode_length,unaryCode_length]
    have hin := Nat.mul_le_mul_right a.1.val hi
    nlinarith only [hin,Nat.zero_le (a.1.val^2),Nat.zero_le (a.2.val^2),Nat.zero_le (n^2)])
  have hm := (show Poly (Prod.snd : Unary×Unary → Unary) from snd).comp
    (ht.comp (show Poly (fun a : Unary×Unary => (a.2,(a.1,(⟨0⟩:Unary)))) by fun_prop))
  exact hm.of_eq (by intro a;simp [unaryMulStep_iterate,Nat.mul_comm])


-- @@ L31-36 verbatim
theorem unaryPow (k : ℕ) : Poly (fun a : Unary => Unary.mk (a.val^k)) := by
  induction k with
  | zero => simpa using (const (A:=Unary) (Unary.mk 1))
  | succ k ih =>
    exact (unaryMul.comp (ih.pair (show Poly (fun a : Unary => a) from id))).of_eq
      (by intro a;simp [pow_succ])


-- @@ L38-38 verbatim
end Poly

-- @@ L39-39 verbatim
end RationalHitting.StackLanguage



-- @@ L42-42 verbatim
namespace RationalHitting.StackLanguage

-- @@ L43-43 verbatim
open Function


-- @@ L45-45 verbatim
abbrev DivState := Unary×(Unary×Unary)

-- @@ L46-48 verbatim
def divStep (a : DivState) : DivState :=
  (a.1,if 0<a.1.val ∧ a.1.val≤a.2.2.val+1 then
    (⟨a.2.1.val+1⟩,⟨a.2.2.val+1-a.1.val⟩) else (a.2.1,⟨a.2.2.val+1⟩))


-- @@ L50-52 verbatim
lemma divStep_size (a : DivState) : (code (divStep a)).length≤(code a).length+3 := by
  unfold divStep
  split_ifs <;> simp only [prod_code_length,unary_code_length] <;> omega


-- @@ L54-61 verbatim
lemma divStep_iterate_size (a : DivState) (n : ℕ) :
    (code (divStep^[n] a)).length≤(code a).length+3*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']
    have hh:=divStep_size (divStep^[n] a)
    omega


-- @@ L63-82 verbatim
lemma divStep_expected (d n : ℕ) :
    divStep (⟨d⟩,(⟨n/d⟩,⟨n%d⟩))=(⟨d⟩,(⟨(n+1)/d⟩,⟨(n+1)%d⟩)) := by
  by_cases hd : d=0
  · subst d;simp [divStep]
  have hp : 0<d := by omega
  have hr := Nat.mod_lt n hp
  have he := Nat.div_add_mod n d
  by_cases h : d≤n%d+1
  · have hb : n%d+1=d := by omega
    have hn : n+1=d*(n/d+1) := by nlinarith only [he,hb]
    have hq : (n+1)/d=n/d+1 := Nat.div_eq_of_eq_mul_right hp hn
    have hm : (n+1)%d=0 := by rw [hn,Nat.mul_mod_right]
    simp [divStep,hp,hq,hm,hb]
  · have hb : n%d+1<d := by omega
    have hq : (n+1)/d=n/d := Nat.div_eq_of_lt_le (by simpa [Nat.mul_comm] using (show d*(n/d)≤n+1 by omega)) (by nlinarith only [he,hb])
    have hm : (n+1)%d=n%d+1 := by
      have hh := Nat.div_add_mod (n+1) d
      rw [hq] at hh
      omega
    simp [divStep,h,hq,hm]


-- @@ L84-90 verbatim
lemma divStep_iterate (d : Unary) (n : ℕ) :
    divStep^[n] (d,(⟨0⟩,⟨0⟩))=(d,(⟨n/d.val⟩,⟨n%d.val⟩)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply',ih]
    exact divStep_expected d.val n


-- @@ L92-92 verbatim
namespace Poly

-- @@ L93-107 verbatim
@[fun_prop] theorem divStep_poly : Poly divStep := by
  have hc : Poly (fun a : DivState => decide (0<a.1.val ∧ a.1.val≤a.2.2.val+1)) := by
    have hz := boolNot.comp (unaryZero.comp (show Poly (Prod.fst : DivState → Unary) from fst))
    have hle := unaryLe.comp ((show Poly (Prod.fst : DivState → Unary) from fst).pair
      (unarySucc.comp (show Poly (fun a : DivState => a.2.2) by fun_prop)))
    exact (boolAnd.comp (hz.pair hle)).of_eq (by intro a;simp [Nat.pos_iff_ne_zero])
  have hy : Poly (fun a : DivState => ((⟨a.2.1.val+1⟩:Unary),(⟨a.2.2.val+1-a.1.val⟩:Unary))) :=
    (unarySucc.comp (show Poly (fun a : DivState => a.2.1) by fun_prop)).pair
      (unarySub.comp ((unarySucc.comp (show Poly (fun a : DivState => a.2.2) by fun_prop)).pair
        (show Poly (Prod.fst : DivState → Unary) from fst)))
  have hn : Poly (fun a : DivState => (a.2.1,(⟨a.2.2.val+1⟩:Unary))) :=
    (show Poly (fun a : DivState => a.2.1) by fun_prop).pair
      (unarySucc.comp (show Poly (fun a : DivState => a.2.2) by fun_prop))
  exact ((show Poly (Prod.fst : DivState → Unary) from fst).pair (hc.cond hy hn)).of_eq
    (by intro a;simp [divStep])


-- @@ L109-117 verbatim
@[fun_prop] theorem unaryDivMod : Poly (fun a : Unary×Unary => ((⟨a.1.val/a.2.val⟩:Unary),(⟨a.1.val%a.2.val⟩:Unary))) := by
  have hh := divStep_poly.iterate (4*TimeBound.variable) (by
    intro n a i hi
    have h:=divStep_iterate_size a i
    simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable,pairCode_length,unaryCode_length]
    omega)
  have ho := (show Poly (Prod.snd : DivState → Unary×Unary) from snd).comp
    (hh.comp (show Poly (fun a : Unary×Unary => (a.1,(a.2,((⟨0⟩:Unary),(⟨0⟩:Unary))))) by fun_prop))
  exact ho.of_eq (by intro a;simp [divStep_iterate])


-- @@ L119-119 verbatim
@[fun_prop] theorem unaryDiv : Poly (fun a : Unary×Unary => Unary.mk (a.1.val/a.2.val)) := fst.comp unaryDivMod

-- @@ L120-120 verbatim
@[fun_prop] theorem unaryMod : Poly (fun a : Unary×Unary => Unary.mk (a.1.val%a.2.val)) := snd.comp unaryDivMod

-- @@ L121-121 verbatim
end Poly

-- @@ L122-122 verbatim
end RationalHitting.StackLanguage



-- @@ L125-125 verbatim
namespace RationalHitting.StackLanguage


-- @@ L127-127 verbatim
namespace Procedure


-- @@ L129-141 verbatim
def wordLength : Procedure _root_.id unaryCode List.length where
  Registers := Fin 2
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 1
  program := unaryLength 0 1
  bound := 4*TimeBound.variable+1
  correct a := by
    refine ⟨4*a.length+1,by simp,?_⟩
    have hh := eval_unaryLength (a:=(0:Fin 2)) (b:=1) (by decide) (single 0 a)
    simpa [single,unaryCode] using hh
  size a := by simp [unaryCode];omega


-- @@ L143-143 verbatim
end Procedure

-- @@ L144-144 verbatim
namespace Poly

-- @@ L145-147 verbatim
@[fun_prop] theorem bitLength : Poly (fun a : BitWord => Unary.mk a.val.length) :=
  (show Feasible _root_.id unaryCode List.length from ⟨Procedure.wordLength⟩).recode
    _ _ _ BitWord.val (by intro a;rfl) (by intro a;rfl)


-- @@ L149-151 verbatim
@[fun_prop] theorem natBitLength : Poly (fun a : ℕ => Unary.mk a.bits.length) :=
  (show Feasible _root_.id unaryCode List.length from ⟨Procedure.wordLength⟩).recode
    _ _ _ Nat.bits (by intro a;rfl) (by intro a;rfl)


-- @@ L153-154 verbatim
@[fun_prop] theorem natSize : Poly (fun a : ℕ => Unary.mk a.size) :=
  natBitLength.of_eq (fun a => congrArg Unary.mk (Nat.size_eq_bits_len a))

-- @@ L155-155 verbatim
end Poly

-- @@ L156-156 verbatim
end RationalHitting.StackLanguage



-- @@ L159-159 verbatim
namespace RationalHitting.StackLanguage

-- @@ L160-160 verbatim
open Function


-- @@ L162-162 verbatim
def doubleBelow (t v : ℕ) : ℕ := if v≤t then v+v else v


-- @@ L164-164 verbatim
def doubleState (a : Unary×Unary) : Unary×Unary := (a.1,⟨doubleBelow a.1.val a.2.val⟩)


-- @@ L166-175 verbatim
lemma doubleBelow_iterate_bound (t v k : ℕ) : (doubleBelow t)^[k] v≤ max v (2*t) := by
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    rw [iterate_succ_apply']
    change (if (doubleBelow t)^[k] v≤t then (doubleBelow t)^[k] v+(doubleBelow t)^[k] v
      else (doubleBelow t)^[k] v)≤ max v (2*t)
    split_ifs with h
    · exact (show (doubleBelow t)^[k] v+(doubleBelow t)^[k] v≤2*t by omega).trans (le_max_right _ _)
    · exact ih


-- @@ L177-181 verbatim
lemma doubleState_iterate (a : Unary×Unary) (k : ℕ) :
    doubleState^[k] a=(a.1,⟨(doubleBelow a.1.val)^[k] a.2.val⟩) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate_succ_apply',ih,doubleState]


-- @@ L183-193 verbatim
lemma doubleBelow_iterate_pow (t k : ℕ) (hk : k≤t.size) :
    (doubleBelow t)^[k] 1=2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply',ih (by omega)]
    have h : 2^k≤t := by
      by_contra hh
      have hs := Nat.size_le.mpr (show t<2^k by omega)
      omega
    simp [doubleBelow,h,pow_succ,Nat.mul_two]


-- @@ L195-202 verbatim
lemma nat_size_log {t : ℕ} (ht : 0<t) : t.size=Nat.log 2 t+1 := by
  have hle := Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1<2) t)
  have hpow := Nat.pow_log_le_self 2 ht.ne'
  have hlo : Nat.log 2 t<t.size := by
    by_contra hh
    have h := Nat.size_le.mp (show t.size≤Nat.log 2 t by omega)
    omega
  omega


-- @@ L204-204 verbatim
namespace Poly

-- @@ L205-210 verbatim
@[fun_prop] theorem doubleState_poly : Poly doubleState := by
  have hc := unaryLe.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop)
  have hs := unaryAdd.comp (show Poly (fun a : Unary×Unary => (a.2,a.2)) by fun_prop)
  exact ((show Poly (Prod.fst : Unary×Unary → Unary) from fst).pair
    (hc.cond hs (show Poly (Prod.snd : Unary×Unary → Unary) from snd))).of_eq
      (by intro a;simp [doubleState,doubleBelow];split_ifs <;> rfl)


-- @@ L212-223 verbatim
@[fun_prop] theorem unaryNextPower : Poly (fun a : Unary => Unary.mk (2^a.val.size)) := by
  have hh := doubleState_poly.iterate (2*TimeBound.variable) (by
    intro n a i hi
    rw [doubleState_iterate]
    have hb := doubleBelow_iterate_bound a.1.val a.2.val i
    simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable,
      pairCode_length,unaryCode_length,prod_code_length,unary_code_length]
    omega)
  have hn := natSize.comp unaryToNat
  have hout := (show Poly (Prod.snd : Unary×Unary → Unary) from snd).comp
    (hh.comp (hn.pair (show Poly (fun a : Unary => (a,(⟨1⟩:Unary))) by fun_prop)))
  exact hout.of_eq (by intro a;simp [doubleState_iterate,doubleBelow_iterate_pow])


-- @@ L225-231 verbatim
@[fun_prop] theorem unaryLogTwo : Poly (fun a : Unary => Unary.mk (Nat.log 2 a.val)) := by
  have hh := unaryPred.comp (natSize.comp unaryToNat)
  refine hh.of_eq ?_
  intro a
  by_cases h : a.val=0
  · simp [h]
  · simp [nat_size_log (show 0<a.val by omega)]


-- @@ L233-233 verbatim
end Poly

-- @@ L234-234 verbatim
end RationalHitting.StackLanguage


-- @@ L236-236 verbatim
end OAI
