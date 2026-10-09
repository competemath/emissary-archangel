import OAI.Computability.RationalHitting.RationalArithmetic


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace RationalHitting.StackLanguage

-- @@ L6-6 verbatim
open scoped BigOperators


-- @@ L8-10 verbatim
lemma range_sum_fin {A : Type} [AddCommMonoid A] (n : ℕ) (f : ℕ → A) :
    ((List.range n).map f).sum=∑ i : Fin n, f i.val := by
  rw [range_map_to_finRange,←List.ofFn_eq_map,List.sum_ofFn]


-- @@ L12-16 verbatim
lemma finEquiv_val {m : ℕ} [NeZero m] (i : Fin m) :
    ((ZMod.finEquiv m) i).val=i.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl


-- @@ L18-21 verbatim
lemma finEquiv_symm_val {m : ℕ} [NeZero m] (i : ZMod m) :
    ((ZMod.finEquiv m).symm i).val=i.val := by
  exact (finEquiv_val ((ZMod.finEquiv m).symm i)).symm.trans
    (congrArg ZMod.val ((ZMod.finEquiv m).apply_symm_apply i))


-- @@ L23-26 verbatim
lemma finEquiv_cast {m : ℕ} [NeZero m] (i : Fin m) :
    (ZMod.finEquiv m) i=(i.val : ZMod m) := by
  apply ZMod.val_injective
  rw [finEquiv_val,ZMod.val_cast_of_lt i.isLt]


-- @@ L28-36 verbatim
lemma range_sum_zmod {A : Type} [AddCommMonoid A] (m : ℕ) [NeZero m] (f : ZMod m → A) :
    ((List.range m).map (fun (k : ℕ) => f (k : ZMod m))).sum = ∑ k : ZMod m, f k := by
  calc
    _ = ∑ i : Fin m, f (i.val : ZMod m) := by
      simpa only [List.map_map,Function.comp_def] using
        range_sum_fin m (fun k => f (k : ZMod m))
    _ = _ := Fintype.sum_equiv (ZMod.finEquiv m).toEquiv _ _ (fun i => by
      change f (i.val : ZMod m)=f ((ZMod.finEquiv m) i)
      rw [finEquiv_cast])


-- @@ L38-40 verbatim
lemma zmod_val_sub {m : ℕ} [NeZero m] (a b : ZMod m) :
    (a-b).val=(a.val+(m-b.val)%m)%m := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val']


-- @@ L42-48 verbatim
lemma coordinate_vals (e : ℕ) (i : Fin (Generator.D e)) :
    (((Generator.coordinate e).symm i).1.val,((Generator.coordinate e).symm i).2.val)=
      (i.val/CyclotomicRing.degree e,i.val % CyclotomicRing.degree e) := by
  change (((ZMod.finEquiv (CyclotomicRing.dimension e))
    (finProdFinEquiv.symm i).1).val,(finProdFinEquiv.symm i).2.val)=_
  rw [finEquiv_val]
  rfl

-- @@ L49-49 verbatim
end RationalHitting.StackLanguage



-- @@ L52-52 verbatim
namespace RationalHitting.StackLanguage

-- @@ L53-53 verbatim
open scoped BigOperators


-- @@ L55-55 verbatim
namespace Runtime


-- @@ L57-59 verbatim
def taylorTerm (m : ℕ) (a t : ℤ) (i j r : ℕ) : ℤ :=
  ((-a)^(m-1-r-i)*((m-1-r).choose i : ℤ)) *
    (a^(j-r)*(j.choose r : ℤ))*t^r


-- @@ L61-62 verbatim
def taylor (m : ℕ) (a t : ℤ) (i j : ℕ) : ℤ :=
  ((List.range m).map (fun r => taylorTerm m a t i j r)).sum


-- @@ L64-65 verbatim
def padded (m N : ℕ) (a t : ℤ) (i j : ℕ) : ℤ :=
  if j<N then taylor m a t i j else 0


-- @@ L67-73 verbatim
lemma taylor_eq (m : ℕ) (a t : ℤ) (i j : Fin m) :
    taylor m a t i.val j.val=IntegralTest.full m a t i j := by
  unfold taylor IntegralTest.full
  rw [range_sum_fin]
  apply Finset.sum_congr rfl
  intro r _
  simp [taylorTerm,Fin.val_rev,Nat.sub_sub,Nat.add_comm]


-- @@ L75-77 verbatim
lemma padded_eq (m N : ℕ) (a t : ℤ) (i j : Fin m) :
    padded m N a t i.val j.val=IntegralTest.padded m N a t i j := by
  simp [padded,IntegralTest.padded,taylor_eq]


-- @@ L79-79 verbatim
abbrev TaylorArgs := Unary×ℤ×ℤ×Unary×Unary


-- @@ L81-88 verbatim
@[fun_prop] theorem taylorTerm_poly : Poly (fun a : TaylorArgs×Unary =>
    taylorTerm a.1.1.val a.1.2.1 a.1.2.2.1 a.1.2.2.2.1.val a.1.2.2.2.2.val a.2.val) := by
  change Poly (fun a : TaylorArgs×Unary =>
    (Unary.powInt (-a.1.2.1) (a.1.1-1-a.2-a.1.2.2.2.1)*
      Unary.choose (a.1.1-1-a.2) a.1.2.2.2.1)*
    (Unary.powInt a.1.2.1 (a.1.2.2.2.2-a.2)*Unary.choose a.1.2.2.2.2 a.2)*
    Unary.powInt a.1.2.2.1 a.2)
  fun_prop


-- @@ L90-92 verbatim
@[fun_prop] theorem taylor_poly : Poly (fun a : TaylorArgs =>
    taylor a.1.val a.2.1 a.2.2.1 a.2.2.2.1.val a.2.2.2.2.val) := by
  exact Poly.sumUp (show Poly (fun a : TaylorArgs => a.1) by fun_prop) taylorTerm_poly


-- @@ L94-100 verbatim
@[fun_prop] theorem padded_poly : Poly (fun a : Unary×TaylorArgs =>
    padded a.2.1.val a.1.val a.2.2.1 a.2.2.2.1 a.2.2.2.2.1.val a.2.2.2.2.2.val) := by
  have hc : Poly (fun a : Unary×TaylorArgs => Unary.ltb a.2.2.2.2.2 a.1) := by fun_prop
  have hf : Poly (fun a : Unary×TaylorArgs =>
    taylor a.2.1.val a.2.2.1 a.2.2.2.1 a.2.2.2.2.1.val a.2.2.2.2.2.val) :=
    taylor_poly.comp (show Poly (Prod.snd : Unary×TaylorArgs → TaylorArgs) from Poly.snd)
  exact (hc.cond hf (Poly.const 0)).of_eq (by intro a;simp [padded,Unary.ltb])


-- @@ L102-102 verbatim
end Runtime

-- @@ L103-103 verbatim
end RationalHitting.StackLanguage



-- @@ L106-106 verbatim
namespace RationalHitting.StackLanguage


-- @@ L108-108 verbatim
abbrev Params := Unary×Unary×Unary×Unary×Unary

-- @@ L109-109 verbatim
namespace Params

-- @@ L110-110 verbatim
abbrev n (p : Params) : ℕ := p.1.val

-- @@ L111-111 verbatim
abbrev N (p : Params) : ℕ := p.2.1.val

-- @@ L112-112 verbatim
abbrev m (p : Params) : ℕ := p.2.2.1.val

-- @@ L113-113 verbatim
abbrev q (p : Params) : ℕ := p.2.2.2.1.val

-- @@ L114-114 verbatim
abbrev H (p : Params) : ℕ := p.2.2.2.2.val


-- @@ L116-118 verbatim
def of (n s : ℕ) : Params :=
  (⟨n⟩,⟨Parameters.N n s⟩,⟨Parameters.M n s⟩,
    ⟨CyclotomicRing.degree (Parameters.exponent n s)⟩,⟨Parameters.H n s⟩)

-- @@ L119-119 verbatim
end Params


-- @@ L121-121 verbatim
namespace Params

-- @@ L122-122 verbatim
def BB (a : Unary) : Unary := ⟨Parameters.B a.val⟩

-- @@ L123-123 verbatim
def DD (a : Unary×Unary) : Unary := ⟨Parameters.delta a.1.val a.2.val⟩

-- @@ L124-124 verbatim
def threshold (a : Unary×Unary) : Unary := BB a.2 * DD a

-- @@ L125-125 verbatim
def EE (a : Unary×Unary) : Unary := ⟨Parameters.exponent a.1.val a.2.val⟩

-- @@ L126-126 verbatim
def MM (a : Unary×Unary) : Unary := ⟨Parameters.M a.1.val a.2.val⟩

-- @@ L127-127 verbatim
def NN (a : Unary×Unary) : Unary := ⟨Parameters.N a.1.val a.2.val⟩

-- @@ L128-128 verbatim
def HH (a : Unary×Unary) : Unary := ⟨Parameters.H a.1.val a.2.val⟩

-- @@ L129-129 verbatim
def QQ (a : Unary×Unary) : Unary := ⟨CyclotomicRing.degree (Parameters.exponent a.1.val a.2.val)⟩

-- @@ L130-130 verbatim
end Params

-- @@ L131-131 verbatim
namespace Poly

-- @@ L132-134 verbatim
@[fun_prop] theorem paramB : Poly Params.BB := by
  change Poly (fun a : Unary => 2*a+1)
  fun_prop

-- @@ L135-137 verbatim
@[fun_prop] theorem paramDelta : Poly Params.DD := by
  change Poly (fun a : Unary×Unary => 2*(a.1+1)^3*(2*a.2+1))
  fun_prop

-- @@ L138-140 verbatim
@[fun_prop] theorem paramThreshold : Poly Params.threshold := by
  unfold Params.threshold
  fun_prop

-- @@ L141-141 verbatim
@[fun_prop] theorem paramExponent : Poly Params.EE := unaryLogTwo.comp paramThreshold

-- @@ L142-147 verbatim
@[fun_prop] theorem paramM : Poly Params.MM := by
  exact (unaryNextPower.comp paramThreshold).of_eq (by
    intro a
    change Unary.mk (2^(Parameters.B a.2.val*Parameters.delta a.1.val a.2.val).size)=_
    simp only [Params.MM,Parameters.M,Parameters.exponent,
      nat_size_log (Parameters.threshold_pos a.1.val a.2.val)])

-- @@ L148-150 verbatim
@[fun_prop] theorem paramN : Poly Params.NN := by
  change Poly (fun a : Unary×Unary => Params.MM a-Params.DD a)
  fun_prop

-- @@ L151-153 verbatim
@[fun_prop] theorem paramH : Poly Params.HH := by
  change Poly (fun a : Unary×Unary => 1+3*(a.2+2)*Params.BB a.2*(Params.MM a)^3)
  fun_prop

-- @@ L154-159 verbatim
@[fun_prop] theorem paramDegree : Poly Params.QQ := by
  have hh : Poly (fun a : Unary×Unary => Params.MM a/2) := by fun_prop
  exact hh.of_eq (by
    intro a
    change Unary.mk (Parameters.M a.1.val a.2.val/2)=_
    simp [Params.QQ,Parameters.M,CyclotomicRing.degree,pow_succ])

-- @@ L160-162 verbatim
@[fun_prop] theorem params : Poly (fun a : Unary×Unary => Params.of a.1.val a.2.val) := by
  change Poly (fun a : Unary×Unary => (a.1,Params.NN a,Params.MM a,Params.QQ a,Params.HH a))
  fun_prop

-- @@ L163-163 verbatim
end Poly

-- @@ L164-164 verbatim
end RationalHitting.StackLanguage


-- @@ L166-166 verbatim
end OAI
