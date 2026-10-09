import OAI.Computability.RationalHitting.UnaryArithmetic


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace RationalHitting.StackLanguage

-- @@ L6-6 verbatim
open Function


-- @@ L8-8 verbatim
def chooseClean : Program (Fin 18) := .seq Binomial.choose (.seq (clear 14) (clear 15))


-- @@ L10-29 verbatim
lemma eval_chooseClean (n k : ℕ) : ∃ t≤4000000*(n+k+1)^10,
    Eval chooseClean (both (14 : Fin 18) 15 (unaryCode n) (unaryCode k))
      (single 0 (n.choose k).bits) t := by
  obtain ⟨t,ht,he⟩ := Binomial.eval_choose_polynomial n k
  have hin : Binomial.input n k=both (14:Fin 18) 15 (unaryCode n) (unaryCode k) := rfl
  let s := update (Binomial.input n k) 0 (n.choose k).bits
  have e1 := eval_clear (14:Fin 18) s
  have e2 := eval_clear (15:Fin 18) (update s 14 [])
  have hout : update (update s 14 []) 15 []=single 0 (n.choose k).bits := by
    funext j;fin_cases j <;> simp [s,Binomial.input,single]
  rw [hout] at e2
  have hcat := Eval.seq he (Eval.seq e1 e2)
  have hn : (s 14).length=n := by simp [s,Binomial.input]
  have hk : ((update s 14 []) 15).length=k := by simp [s,Binomial.input]
  rw [hn] at e1
  rw [hk] at e2
  refine ⟨1+t+(1+(2*n+1)+(2*k+1)),?_,?_⟩
  · have hp : n+k+1≤(n+k+1)^10 := Nat.le_self_pow (by omega) _
    omega
  · simpa only [chooseClean,hin,hn,hk] using hcat


-- @@ L31-31 verbatim
namespace Procedure


-- @@ L33-43 verbatim
def choose : Procedure (pairCode unaryCode unaryCode) Nat.bits (fun a => a.1.choose a.2) :=
  fromBinary chooseClean 14 15 0 (by decide) (4000000*TimeBound.variable^10)
    (by intro a b;simpa using eval_chooseClean a b)
    (by
      intro n k
      have h := nat_bits_mono (Nat.choose_le_two_pow n k)
      simp only [Nat.size_eq_bits_len,Nat.size_pow] at h
      have hp : n+k+1≤(n+k+1)^10 := Nat.le_self_pow (by omega) _
      simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_pow,
        TimeBound.eval_variable,unaryCode_length,Nat.size_eq_bits_len]
      omega)


-- @@ L45-45 verbatim
end Procedure

-- @@ L46-46 verbatim
namespace Poly

-- @@ L47-50 verbatim
@[fun_prop] theorem choose : Poly (fun a : Unary×Unary => a.1.val.choose a.2.val) :=
  (show Feasible (pairCode unaryCode unaryCode) Nat.bits (fun a : ℕ×ℕ => a.1.choose a.2) from
    ⟨Procedure.choose⟩).recode _ _ _ (fun a => (a.1.val,a.2.val))
      (by intro a;rfl) (by intro a;rfl)

-- @@ L51-51 verbatim
end Poly

-- @@ L52-52 verbatim
end RationalHitting.StackLanguage



-- @@ L55-55 verbatim
namespace RationalHitting.StackLanguage

-- @@ L56-56 verbatim
open Function


-- @@ L58-58 verbatim
variable {K : Type} [DecidableEq K]


-- @@ L60-60 verbatim
def unpackInt (a sg : K) : Program K := .seq (.drop a) (.seq (.transfer a sg) (.drop a))


-- @@ L62-75 verbatim
lemma eval_unpackInt {a sg : K} (has : a≠sg) (s : Store K) (z : ℤ) (hz : s a=intCode z) :
    Eval (unpackInt a sg) s (update (update s a z.natAbs.bits) sg (decide (z<0)::s sg)) 5 := by
  have h : s a=false::decide (z<0)::true::z.natAbs.bits := hz
  let u := update s a (decide (z<0)::true::z.natAbs.bits)
  let v := update (update s a (true::z.natAbs.bits)) sg (decide (z<0)::s sg)
  have e1 : Eval (.drop a) s u 1 := by simpa [u,h] using Eval.drop a s
  have e2 : Eval (.transfer a sg) u v 1 := by
    simpa [transfer_cons has u (decide (z<0)) (true::z.natAbs.bits) (by simp [u]),u,v,has.symm] using
      Eval.transfer a sg u
  have e3 : Eval (.drop a) v (update (update s a z.natAbs.bits) sg (decide (z<0)::s sg)) 1 := by
    have he := Eval.drop a v
    convert he using 1
    funext k;by_cases ha : k=a <;> by_cases hs : k=sg <;> simp_all [v]
  exact Eval.seq e1 (Eval.seq e2 e3)


-- @@ L77-78 verbatim
def rationalClean : Program (Fin 16) := .seq (unpackInt 0 12) (.seq (unpackInt 5 13)
  (.seq rationalEncode (.seq (clear 12) (clear 13))))


-- @@ L80-80 verbatim
abbrev NZInt := {z : ℤ // z≠0}


-- @@ L82-114 verbatim
lemma eval_rationalClean (a : ℤ) (b : NZInt) : ∃ t≤4000*(a.natAbs.bits.length+b.val.natAbs.bits.length+8)^3,
    Eval rationalClean (both (0:Fin 16) 5 (intCode a) (intCode b.val))
      (single 14 (encodeRat (Rat.divInt a b.val))) t := by
  let s := both (0:Fin 16) 5 (intCode a) (intCode b.val)
  let u := update (update s 0 a.natAbs.bits) 12 [decide (a<0)]
  let v := update (update u 5 b.val.natAbs.bits) 13 [decide (b.val<0)]
  have e1 : Eval (unpackInt 0 12) s u 5 := by
    simpa [s,u,both,single] using eval_unpackInt (a:=(0:Fin 16)) (sg:=12) (by decide) s a (by simp [s,both,single])
  have e2 : Eval (unpackInt 5 13) u v 5 := by
    simpa [v,u,s,both,single] using eval_unpackInt (a:=(5:Fin 16)) (sg:=13) (by decide) u b.val
      (by simp [u,s,both,single])
  obtain ⟨t,ht,he⟩ := eval_rationalEncode v a b.val b.property
    (by simp [v,u,s,both,single]) (by simp [v]) (by simp [v,u]) (by simp [v])
    (by simp [v,u,s,both,single])
    (by intro i hi h0 h5;simp [v,u,s,both,single,h0,h5,show i≠12 by omega,show i≠13 by omega])
    (a.natAbs.bits.length+b.val.natAbs.bits.length+1) (by omega) (by omega)
  let w := update (update (update v 0 []) 5 []) 14 (encodeRat (Rat.divInt a b.val))
  have e3 : Eval rationalEncode v w t := by simpa [w,v,u,s,both,single] using he
  have e4 : Eval (clear 12) w (update w 12 []) 3 := by simpa [w,v,u] using eval_clear (12:Fin 16) w
  have ho : update (update w 12 []) 13 []=single 14 (encodeRat (Rat.divInt a b.val)) := by
    funext k;fin_cases k <;> simp [w,v,u,s,both,single]
  have e5 : Eval (clear 13) (update w 12 []) (single 14 (encodeRat (Rat.divInt a b.val))) 3 := by
    have hh := eval_clear (13:Fin 16) (update w 12 [])
    rw [ho] at hh
    simpa [w,v] using hh
  refine ⟨1+5+(1+5+(1+t+(1+3+3))),?_,Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))⟩
  have hp : (a.natAbs.bits.length+b.val.natAbs.bits.length+2)^3≤
      (a.natAbs.bits.length+b.val.natAbs.bits.length+8)^3 := by gcongr ; omega
  have hp0 : 1≤(a.natAbs.bits.length+b.val.natAbs.bits.length+8)^3 := by
    have hpos : 0<(a.natAbs.bits.length+b.val.natAbs.bits.length+8)^3 := by positivity
    omega
  simp only [Nat.add_assoc,Nat.reduceAdd] at ht hp hp0 ⊢
  omega


-- @@ L116-116 verbatim
namespace Procedure


-- @@ L118-134 verbatim
def rationalEncode : Procedure (pairCode intCode (fun b : NZInt => intCode b.val)) _root_.id
    (fun a => encodeRat (Rat.divInt a.1 a.2.val)) :=
  fromBinary rationalClean 0 5 14 (by decide) (4000*(TimeBound.variable+1)^3)
    (by intro a b;simpa only [intCode_length,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_pow,TimeBound.eval_add,TimeBound.eval_variable,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.reduceAdd,id_eq] using eval_rationalClean a b)
    (by
      intro a b
      let L := a.natAbs.bits.length+b.val.natAbs.bits.length+1
      have ha : a.natAbs.size≤L := by rw [←Nat.size_eq_bits_len];dsimp [L];omega
      have hb : b.val.natAbs.size≤L := by rw [←Nat.size_eq_bits_len];dsimp [L];omega
      have hh := EncodingBounds.encodeRat_ratio_le a b.val b.property L (Nat.size_le.mp ha) (Nat.size_le.mp hb)
      have hp : L+7≤(L+7)^3 := Nat.le_self_pow (by decide) _
      simp only [intCode_length,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_pow,
        TimeBound.eval_add,TimeBound.eval_variable,id_eq]
      dsimp [L] at hh hp
      simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.reduceAdd] at hp ⊢
      omega)

-- @@ L135-135 verbatim
end Procedure

-- @@ L136-136 verbatim
namespace Poly

-- @@ L137-140 verbatim
@[fun_prop] theorem rationalEncodeNZ : Poly (fun a : ℤ×NZInt => BitWord.mk (encodeRat (Rat.divInt a.1 a.2.val))) :=
  (show Feasible (pairCode intCode (fun b : NZInt => intCode b.val)) _root_.id
    (fun a : ℤ×NZInt => encodeRat (Rat.divInt a.1 a.2.val)) from
      ⟨Procedure.rationalEncode⟩).recode _ _ _ _root_.id (by intro a;rfl) (by intro a;rfl)


-- @@ L142-145 verbatim
@[fun_prop] theorem safeDen : Poly (fun b : ℤ => (⟨if b=0 then 1 else b,by split_ifs with h <;> simp_all⟩ : NZInt)) := by
  have hh := intZero.cond (const (1:ℤ)) (show Poly (fun b : ℤ => b) from id)
  have hh' : Poly (fun b : ℤ => if b=0 then 1 else b) := hh.of_eq (by intro b;simp)
  exact hh'.subtypeMk _


-- @@ L147-155 verbatim
@[fun_prop] theorem rationalEncode : Poly (fun a : ℤ×ℤ => BitWord.mk (encodeRat (Rat.divInt a.1 a.2))) := by
  have hz := intZero.comp (show Poly (Prod.snd : ℤ×ℤ → ℤ) from snd)
  have hn := rationalEncodeNZ.comp ((show Poly (Prod.fst : ℤ×ℤ → ℤ) from fst).pair
    (safeDen.comp (show Poly (Prod.snd : ℤ×ℤ → ℤ) from snd)))
  exact (hz.cond (const (BitWord.mk (encodeRat 0))) hn).of_eq (by
    intro a
    by_cases h : a.2=0
    · simp [h,Rat.divInt_eq_div]
    · simp [h])

-- @@ L156-156 verbatim
end Poly

-- @@ L157-157 verbatim
end RationalHitting.StackLanguage



-- @@ L160-160 verbatim
namespace RationalHitting.StackLanguage

-- @@ L161-161 verbatim
namespace Poly

-- @@ L162-162 verbatim
variable {A B : Type} [Coding A] [Coding B]


-- @@ L164-165 verbatim
theorem unaryEta {f : A → Unary} (hf : Poly f) :
    Poly (fun a => Unary.mk (f a).val) := hf


-- @@ L167-169 verbatim
theorem unaryAddFun {f g : A → ℕ}
    (hf : Poly (fun a => Unary.mk (f a))) (hg : Poly (fun a => Unary.mk (g a))) :
    Poly (fun a => Unary.mk (f a+g a)) := unaryAdd.comp (hf.pair hg)

-- @@ L170-172 verbatim
theorem unarySubFun {f g : A → ℕ}
    (hf : Poly (fun a => Unary.mk (f a))) (hg : Poly (fun a => Unary.mk (g a))) :
    Poly (fun a => Unary.mk (f a-g a)) := unarySub.comp (hf.pair hg)

-- @@ L173-175 verbatim
theorem unaryMulFun {f g : A → ℕ}
    (hf : Poly (fun a => Unary.mk (f a))) (hg : Poly (fun a => Unary.mk (g a))) :
    Poly (fun a => Unary.mk (f a*g a)) := unaryMul.comp (hf.pair hg)

-- @@ L176-178 verbatim
theorem unaryDivFun {f g : A → ℕ}
    (hf : Poly (fun a => Unary.mk (f a))) (hg : Poly (fun a => Unary.mk (g a))) :
    Poly (fun a => Unary.mk (f a/g a)) := unaryDiv.comp (hf.pair hg)

-- @@ L179-181 verbatim
theorem unaryModFun {f g : A → ℕ}
    (hf : Poly (fun a => Unary.mk (f a))) (hg : Poly (fun a => Unary.mk (g a))) :
    Poly (fun a => Unary.mk (f a%g a)) := unaryMod.comp (hf.pair hg)

-- @@ L182-184 verbatim
theorem unaryPowFun {f : A → ℕ} (k : ℕ)
    (hf : Poly (fun a => Unary.mk (f a))) : Poly (fun a => Unary.mk (f a^k)) :=
  (unaryPow k).comp hf

-- @@ L185-186 verbatim
@[fun_prop] theorem unaryCastInt : Poly (fun a : Unary => (a.val : ℤ)) :=
  natCastInt.comp unaryToNat


-- @@ L188-189 verbatim
theorem unaryCastIntFun {f : A → ℕ}
    (hf : Poly (fun a => Unary.mk (f a))) : Poly (fun a => (f a : ℤ)) := unaryCastInt.comp hf

-- @@ L190-192 verbatim
theorem unaryEqFun {f g : A → ℕ}
    (hf : Poly (fun a => Unary.mk (f a))) (hg : Poly (fun a => Unary.mk (g a))) :
    Poly (fun a => decide (f a=g a)) := unaryEq.comp (hf.pair hg)

-- @@ L193-195 verbatim
theorem unaryLtFun {f g : A → ℕ}
    (hf : Poly (fun a => Unary.mk (f a))) (hg : Poly (fun a => Unary.mk (g a))) :
    Poly (fun a => decide (f a<g a)) := unaryLt.comp (hf.pair hg)

-- @@ L196-198 verbatim
theorem chooseFun {f g : A → ℕ}
    (hf : Poly (fun a => Unary.mk (f a))) (hg : Poly (fun a => Unary.mk (g a))) :
    Poly (fun a => (f a).choose (g a)) := choose.comp (hf.pair hg)

-- @@ L199-201 verbatim
theorem intPowFun {f : A → ℤ} {g : A → ℕ}
    (hf : Poly f) (hg : Poly (fun a => Unary.mk (g a))) :
    Poly (fun a => f a ^ g a) := intPow.comp (hf.pair hg)

 
-- @@ L203-206 verbatim
theorem ite {c : A → Prop} [DecidablePred c] {f g : A → B}
    (hc : Poly (fun a => decide (c a))) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => if c a then f a else g a) :=
  (hc.cond hf hg).of_eq (by intro a;simp)

 
-- @@ L208-211 verbatim
theorem sumUp {n : A → ℕ} {f : A×Unary → ℤ}
    (hn : Poly (fun a => Unary.mk (n a))) (hf : Poly f) :
    Poly (fun a => ((List.range (n a)).map (fun i => f (a,⟨i⟩))).sum) :=
  hf.sumRange.comp (hn.pair (show Poly (fun a : A => a) from id))


-- @@ L213-213 verbatim
end Poly


-- @@ L215-215 verbatim
namespace Unary

-- @@ L216-216 verbatim
instance (n : ℕ) : OfNat Unary n := ⟨⟨n⟩⟩

-- @@ L217-217 verbatim
instance : Add Unary := ⟨fun a b => ⟨a.val+b.val⟩⟩

-- @@ L218-218 verbatim
instance : Sub Unary := ⟨fun a b => ⟨a.val-b.val⟩⟩

-- @@ L219-219 verbatim
instance : Mul Unary := ⟨fun a b => ⟨a.val*b.val⟩⟩

-- @@ L220-220 verbatim
instance : Div Unary := ⟨fun a b => ⟨a.val/b.val⟩⟩

-- @@ L221-221 verbatim
instance : Mod Unary := ⟨fun a b => ⟨a.val%b.val⟩⟩

-- @@ L222-222 verbatim
instance : Pow Unary ℕ := ⟨fun a b => ⟨a.val^b⟩⟩

-- @@ L223-223 verbatim
def toInt (a : Unary) : ℤ := a.val

-- @@ L224-224 verbatim
def choose (a b : Unary) : ℤ := a.val.choose b.val

-- @@ L225-225 verbatim
def powInt (a : ℤ) (b : Unary) : ℤ := a^b.val

-- @@ L226-226 verbatim
def eqb (a b : Unary) : Bool := decide (a.val=b.val)

-- @@ L227-227 verbatim
def ltb (a b : Unary) : Bool := decide (a.val<b.val)

-- @@ L228-228 verbatim
end Unary


-- @@ L230-230 verbatim
namespace Poly

-- @@ L231-231 verbatim
@[fun_prop] theorem uAdd : Poly (fun a : Unary×Unary => a.1+a.2) := unaryAdd

-- @@ L232-232 verbatim
@[fun_prop] theorem uSub : Poly (fun a : Unary×Unary => a.1-a.2) := unarySub

-- @@ L233-233 verbatim
@[fun_prop] theorem uMul : Poly (fun a : Unary×Unary => a.1*a.2) := unaryMul

-- @@ L234-234 verbatim
@[fun_prop] theorem uDiv : Poly (fun a : Unary×Unary => a.1/a.2) := unaryDiv

-- @@ L235-235 verbatim
@[fun_prop] theorem uMod : Poly (fun a : Unary×Unary => a.1%a.2) := unaryMod

-- @@ L236-236 verbatim
@[fun_prop] theorem uPow (k : ℕ) : Poly (fun a : Unary => a^k) := unaryPow k

-- @@ L237-237 verbatim
@[fun_prop] theorem uInt : Poly Unary.toInt := unaryCastInt

-- @@ L238-239 verbatim
@[fun_prop] theorem uChoose : Poly (fun a : Unary×Unary => Unary.choose a.1 a.2) :=
  natCastInt.comp choose

-- @@ L240-240 verbatim
@[fun_prop] theorem uPowInt : Poly (fun a : ℤ×Unary => Unary.powInt a.1 a.2) := intPow

-- @@ L241-241 verbatim
@[fun_prop] theorem uEq : Poly (fun a : Unary×Unary => Unary.eqb a.1 a.2) := unaryEq

-- @@ L242-242 verbatim
@[fun_prop] theorem uLt : Poly (fun a : Unary×Unary => Unary.ltb a.1 a.2) := unaryLt


-- @@ L244-246 verbatim
example : Poly (fun a : Unary×Unary => Unary.mk (2*(a.1.val+1)^3*(2*a.2.val+1))) := by
  change Poly (fun a : Unary×Unary => 2*(a.1+1)^3*(2*a.2+1))
  fun_prop

-- @@ L247-249 verbatim
example : Poly (fun a : Unary×Unary => (a.1.val : ℤ)^a.2.val) := by
  change Poly (fun a : Unary×Unary => Unary.powInt a.1.toInt a.2)
  fun_prop

-- @@ L250-250 verbatim
end Poly

-- @@ L251-251 verbatim
end RationalHitting.StackLanguage


-- @@ L253-253 verbatim
end OAI
