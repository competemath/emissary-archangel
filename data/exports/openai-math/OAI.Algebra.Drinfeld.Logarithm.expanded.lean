import OAI.Algebra.Drinfeld.KZTransport


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace DeligneDrinfeld


-- @@ L9-9 verbatim
namespace OperatorLog


-- @@ L11-11 verbatim
section

-- @@ L12-12 verbatim
open Polynomial


-- @@ L14-14 verbatim
def binom (k : ℕ) : ℚ[X] := (k.factorial : ℚ)⁻¹ • descPochhammer ℚ k


-- @@ L16-16 verbatim
@[simp] theorem binom_zero : binom 0=1 := by simp [binom]

-- @@ L17-19 verbatim
@[simp] theorem binom_eval_nat (k n : ℕ) : (binom k).eval (n : ℚ)=(n.choose k : ℚ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp [binom,div_eq_mul_inv,mul_comm]


-- @@ L21-26 verbatim
@[simp] theorem binom_coeff_zero (k : ℕ) : (binom k).coeff 0=if k=0 then 1 else 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [binom,eval_smul,smul_eq_mul,descPochhammer_eval_zero]
  split_ifs with h
  · simp [h]
  · simp


-- @@ L28-38 verbatim
theorem desc_coeff_one (k : ℕ) : (descPochhammer ℚ (k+1)).coeff 1=(-1:ℚ)^k*(k.factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right,mul_sub,coeff_sub,coeff_mul_X]
    have h0 : (descPochhammer ℚ (k+1)).coeff 0=0 := by
      rw [coeff_zero_eq_eval_zero]
      simp
    simp only [h0,zero_sub]
    rw [←C_eq_natCast,coeff_mul_C,ih,Nat.factorial_succ,Nat.cast_mul,pow_succ]
    ring


-- @@ L40-45 verbatim
theorem binom_coeff_one_succ (k : ℕ) : (binom (k+1)).coeff 1=(-1:ℚ)^k/(k+1) := by
  rw [binom,coeff_smul,smul_eq_mul,desc_coeff_one,Nat.factorial_succ,Nat.cast_mul]
  have hf : (k.factorial : ℚ)≠0 := by exact_mod_cast k.factorial_ne_zero
  have hk : ((k+1 : ℕ):ℚ)≠0 := by positivity
  push_cast
  field_simp


-- @@ L47-47 verbatim
variable {V : Type*} [AddCommGroup V] [Module ℚ V]


-- @@ L49-50 verbatim
def interpolate (N : ℕ) (T : Module.End ℚ V) (s : ℚ) : Module.End ℚ V :=
  ∑ k∈Finset.range (N+1),(binom k).eval s • T^k


-- @@ L52-53 verbatim
def logarithm (N : ℕ) (T : Module.End ℚ V) : Module.End ℚ V :=
  ∑ k∈Finset.range (N+1),(binom k).coeff 1 • T^k


-- @@ L55-60 verbatim
theorem sum_range_extend {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n m : ℕ} (h : n ≤ m)
    (hz : ∀ k,n ≤ k → k < m → f k=0) :
    ∑ k∈Finset.range n,f k=∑ k∈Finset.range m,f k := by
  apply Finset.sum_subset (Finset.range_mono h)
  intro k hkm hkn
  exact hz k (Nat.le_of_not_lt (by simpa using hkn)) (Finset.mem_range.mp hkm)


-- @@ L62-80 verbatim
theorem interpolate_nat (N : ℕ) (T : Module.End ℚ V) (hT : T^(N+1)=0) (m : ℕ) :
    interpolate N T m=(1+T)^m := by
  have hpow : ∀ k,N+1 ≤ k → T^k=0 := fun k hk => by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add,hT,zero_mul]
  have hsmall : ∀ k,m+1 ≤ k → (m.choose k : ℚ) • T^k=0 := by
    intro k hk
    rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_smul]
  unfold interpolate
  simp only [binom_eval_nat]
  rw [sum_range_extend (fun k => (m.choose k : ℚ) • T^k) (m:=N+m+2) (by omega)
    (fun k hk _ => by rw [hpow k hk,smul_zero])]
  rw [←sum_range_extend (fun k => (m.choose k : ℚ) • T^k) (n:=m+1) (m:=N+m+2) (by omega)
    (fun k hk _ => hsmall k hk)]
  rw [add_comm (1:Module.End ℚ V) T,(Commute.one_right T).add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow,mul_one,Algebra.smul_def,map_natCast]
  exact Nat.cast_comm _ _


-- @@ L82-86 verbatim
theorem logarithm_eq (N : ℕ) (T : Module.End ℚ V) :
    logarithm N T=∑ k∈Finset.range N,((-1:ℚ)^k/(k+1)) • T^(k+1) := by
  unfold logarithm
  rw [Finset.sum_range_succ']
  simp only [binom_coeff_one_succ,binom_zero,coeff_one,one_ne_zero,ite_false,zero_smul,add_zero]


-- @@ L88-89 verbatim
def valuePolynomial (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ k∈Finset.range (N+1),binom k*C (l ((T^k) a))


-- @@ L91-93 verbatim
theorem value_eval (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) (s : ℚ) :
    (valuePolynomial N T a l).eval s=l (interpolate N T s a) := by
  simp [valuePolynomial,interpolate,LinearMap.sum_apply,LinearMap.smul_apply,Polynomial.eval_finsetSum]


-- @@ L95-97 verbatim
theorem value_one (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) :
    (valuePolynomial N T a l).coeff 1=l (logarithm N T a) := by
  simp [valuePolynomial,logarithm,LinearMap.sum_apply,LinearMap.smul_apply]


-- @@ L99-103 verbatim
theorem polynomial_ext_nat {p q : ℚ[X]} (h : ∀ n : ℕ,p.eval (n:ℚ)=q.eval (n:ℚ)) : p=q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R:=ℚ))).mono
  rintro _ ⟨n,rfl⟩
  exact h n


-- @@ L105-105 verbatim
variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]


-- @@ L107-110 verbatim
def pairPolynomial (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
    (binom i*binom j)*C (l (B ((T^i) a) ((S^j) b)))


-- @@ L112-122 verbatim
theorem pair_eval (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) (s : ℚ) :
    (pairPolynomial N T S B a b l).eval s=
      l (B (interpolate N T s a) (interpolate N S s b)) := by
  simp only [pairPolynomial,Polynomial.eval_finsetSum,eval_mul,eval_C,interpolate,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring


-- @@ L124-129 verbatim
theorem pair_one (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) :
    (pairPolynomial N T S B a b l).coeff 1=
      l (B (logarithm N T a) b+B a (logarithm N S b)) := by
  simp [pairPolynomial,logarithm,LinearMap.sum_apply,LinearMap.smul_apply,mul_coeff_one,
    binom_coeff_zero,add_mul,Finset.sum_add_distrib,ite_mul,mul_ite,add_comm]


-- @@ L131-137 verbatim
theorem powers_bilinear (A : Module.End ℚ V) (C : Module.End ℚ W) (D : Module.End ℚ U)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (h : ∀ a b,D (B a b)=B (A a) (C b)) (m : ℕ) (a : V) (b : W) :
    (D^m) (B a b)=B ((A^m) a) ((C^m) b) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [pow_succ',Module.End.mul_apply,ih,h]


-- @@ L139-155 verbatim
theorem logarithm_bilinear (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (R : Module.End ℚ U) (hT : T^(N+1)=0) (hS : S^(N+1)=0) (hR : R^(N+1)=0)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U)
    (h : ∀ a b,(1+R) (B a b)=B ((1+T) a) ((1+S) b)) (a : V) (b : W) :
    logarithm N R (B a b)=B (logarithm N T a) b+B a (logarithm N S b) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ
    (logarithm N R (B a b)-(B (logarithm N T a) b+B a (logarithm N S b)))).mp
  intro l
  have hp : valuePolynomial N R (B a b) l=pairPolynomial N T S B a b l := by
    apply polynomial_ext_nat
    intro m
    rw [value_eval,pair_eval,interpolate_nat N R hR,interpolate_nat N T hT,interpolate_nat N S hS]
    exact congrArg l (powers_bilinear _ _ _ B h m a b)
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hp
  rw [value_one,pair_one] at hc
  simpa only [map_sub,sub_eq_zero] using hc


-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]


-- @@ L161-165 verbatim
theorem powers_natural (T : Module.End ℚ V) (S : Module.End ℚ W) (f : V →ₗ[ℚ] W)
    (h : ∀ v,f (T v)=S (f v)) (n : ℕ) (v : V) : f ((T^n) v)=(S^n) (f v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Module.End.mul_apply,h,ih]


-- @@ L167-171 verbatim
theorem logarithm_natural (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (f : V →ₗ[ℚ] W) (h : ∀ v,f (T v)=S (f v)) (v : V) :
    f (logarithm N T v)=logarithm N S (f v) := by
  simp only [logarithm,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    powers_natural T S f h]


-- @@ L173-179 verbatim
theorem logarithm_fixed (N : ℕ) (T : Module.End ℚ V) {v : V} (h : T v=0) :
    logarithm N T v=0 := by
  rw [logarithm_eq]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [pow_succ,Module.End.mul_apply,h,map_zero,smul_zero]


-- @@ L181-191 verbatim
theorem nilpotent_of_raises (T : Module.End ℚ V) (F : ℕ → Submodule ℚ V) (N : ℕ)
    (hzero : F 0=⊤) (hterminal : F (N+1)=⊥)
    (hraise : ∀ n v,v∈F n → T v∈F (n+1)) : T^(N+1)=0 := by
  have hpow : ∀ n v,(T^n) v∈F n := by
    intro n v
    induction n with
    | zero => simpa only [pow_zero,Module.End.one_apply,hzero] using Submodule.mem_top
    | succ n ih => simpa only [pow_succ',Module.End.mul_apply] using hraise n _ ih
  apply LinearMap.ext
  intro v
  simpa only [hterminal,Submodule.mem_bot,LinearMap.zero_apply] using hpow (N+1) v


-- @@ L193-193 verbatim
end OperatorLog


-- @@ L195-195 verbatim
namespace LogCategory

-- @@ L196-196 verbatim
open OperatorLog

-- @@ L197-197 verbatim
variable {A O : Type*} [Ring A] [Algebra ℚ A]


-- @@ L199-204 verbatim
structure Data (A O : Type*) [Ring A] [Algebra ℚ A] where
  S : O → O → Module.End ℚ A
  N : ℕ
  nilpotent : ∀ p q,(S p q-1)^(N+1)=0
  comp : ∀ p q r (a b : A),S p r (b*a)=S q r b*S p q a
  one : ∀ p,S p p 1=1


-- @@ L206-206 verbatim
def delta (g : Data A O) (p q : O) : Module.End ℚ A := logarithm g.N (g.S p q-1)


-- @@ L208-214 verbatim
theorem delta_comp (g : Data A O) (p q r : O) (a b : A) :
    delta g p r (b*a)=delta g q r b*a+b*delta g p q a := by
  apply logarithm_bilinear g.N (g.S q r-1) (g.S p q-1) (g.S p r-1)
    (g.nilpotent q r) (g.nilpotent p q) (g.nilpotent p r) (LinearMap.mul ℚ A)
  intro b a
  have he : ∀ p q,(1+(g.S p q-1))=g.S p q := by intros; abel
  simpa only [he,LinearMap.mul_apply'] using g.comp p q r a b


-- @@ L216-218 verbatim
@[simp] theorem delta_one_loop (g : Data A O) (p : O) : delta g p p 1=0 := by
  apply logarithm_fixed
  simp only [LinearMap.sub_apply,Module.End.one_apply,g.one,sub_self]


-- @@ L220-220 verbatim
attribute [local instance] LieRing.ofAssociativeRing


-- @@ L222-228 verbatim
def derivation (g : Data A O) (p : O) : LieDerivation ℚ A A where
  toLinearMap := delta g p p
  leibniz' a b := by
    change delta g p p (a*b-b*a)=(a*delta g p p b-delta g p p b*a)-
      (b*delta g p p a-delta g p p a*b)
    rw [map_sub,delta_comp,delta_comp]
    abel


-- @@ L230-232 verbatim
theorem unit_cocycle (g : Data A O) (p q r : O) :
    delta g p r 1=delta g q r 1+delta g p q 1 := by
  simpa only [one_mul,mul_one] using delta_comp g p q r 1 1


-- @@ L234-240 verbatim
theorem delta_formula (g : Data A O) (o p q : O) (u : A) :
    delta g p q u=delta g o o u+delta g o q 1*u-u*delta g o p 1 := by
  have h₁ := delta_comp g o p q 1 u
  have h₂ := delta_comp g o o q u 1
  simp only [mul_one,one_mul] at h₁ h₂
  rw [h₂] at h₁
  exact eq_sub_of_add_eq (by simpa only [add_comm] using h₁.symm)


-- @@ L242-242 verbatim
end LogCategory


-- @@ L244-244 verbatim
namespace GaugeAutomorphism

-- @@ L245-245 verbatim
variable {A O : Type*} [Ring A] [Algebra ℚ A]

 
-- @@ L247-248 verbatim
def map (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (p q : O) : Module.End ℚ A :=
  ((LinearMap.mulLeft ℚ (H q:A)).comp (LinearMap.mulRight ℚ ((H p)⁻¹:Aˣ))).comp θ.toLinearMap

 
-- @@ L250-253 verbatim
@[simp] theorem map_apply (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (p q : O) (a : A) :
    map θ H p q a=(H q:A)*θ a*((H p)⁻¹:Aˣ) := by
  simp only [map,LinearMap.comp_apply,LinearMap.mulLeft_apply,LinearMap.mulRight_apply,mul_assoc]
  rfl

 
-- @@ L255-258 verbatim
theorem composition (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (p q r : O) (a b : A) :
    map θ H p r (b*a)=map θ H q r b*map θ H p q a := by
  simp only [map_apply,map_mul,mul_assoc]
  rw [←mul_assoc (((H q)⁻¹:Aˣ):A) (H q:A),Units.inv_mul,one_mul]

 
-- @@ L260-261 verbatim
@[simp] theorem map_one_loop (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (p : O) :
    map θ H p p 1=1 := by simp only [map_apply,map_one,mul_one,Units.mul_inv]

 
-- @@ L263-286 verbatim
theorem raises (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (F : ℕ → Submodule ℚ A)
    (hF : Antitone F) (h0 : F 0=⊤)
    (hmul : ∀ i j {u v : A},u∈F i → v∈F j → u*v∈F (i+j))
    (hθ : ∀ n u,u∈F n → θ u-u∈F (n+1)) (hH : ∀ p,(H p:A)-1∈F 1)
    (p q : O) (n : ℕ) (u : A) (hu : u∈F n) : map θ H p q u-u∈F (n+1) := by
  have hθu : θ u∈F n := by
    simpa only [sub_add_cancel] using (F n).add_mem (hF (Nat.le_succ n) (hθ n u hu)) hu
  have hall : ∀ v : A,v∈F 0 := by intro v; rw [h0]; trivial
  have hinv : (((H p)⁻¹:Aˣ):A)-1∈F 1 := by
    have hh := hmul 0 1 (hall (((H p)⁻¹:Aˣ):A)) (hH p)
    have he : (((H p)⁻¹:Aˣ):A)*((H p:A)-1)= -((((H p)⁻¹:Aˣ):A)-1) := by
      rw [mul_sub,Units.inv_mul,mul_one,neg_sub]
    rw [he] at hh
    exact (F 1).neg_mem_iff.mp hh
  have hh₁ := hmul (n+1) 0
    (show ((H q:A)-1)*θ u∈F (n+1) from by simpa only [Nat.add_comm 1 n] using hmul 1 n (hH q) hθu)
    (hall (((H p)⁻¹:Aˣ):A))
  have hh₂ := hmul n 1 hθu hinv
  have he : map θ H p q u-u=
      ((H q:A)-1)*θ u*((H p)⁻¹:Aˣ)+θ u*((((H p)⁻¹:Aˣ):A)-1)+(θ u-u) := by
    rw [map_apply]
    noncomm_ring
  rw [he]
  exact (F (n+1)).add_mem ((F (n+1)).add_mem hh₁ hh₂) (hθ n u hu)

 
-- @@ L288-297 verbatim
def data (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (F : ℕ → Submodule ℚ A) (N : ℕ)
    (hF : Antitone F) (h0 : F 0=⊤) (ht : F (N+1)=⊥)
    (hmul : ∀ i j {u v : A},u∈F i → v∈F j → u*v∈F (i+j))
    (hθ : ∀ n u,u∈F n → θ u-u∈F (n+1)) (hH : ∀ p,(H p:A)-1∈F 1) :
    LogCategory.Data A O where
  S := map θ H
  N := N
  nilpotent p q := OperatorLog.nilpotent_of_raises _ F N h0 ht (raises θ H F hF h0 hmul hθ hH p q)
  comp := composition θ H
  one := map_one_loop θ H


-- @@ L299-299 verbatim
end GaugeAutomorphism


-- @@ L301-301 verbatim
namespace OperatorLog

-- @@ L302-302 verbatim
variable {A : Type*} [Ring A] [Algebra ℚ A]


-- @@ L304-319 verbatim
theorem logarithm_depth_one (F : ℕ → Submodule ℚ A) (hF : Antitone F)
    (T : Module.End ℚ A) (hT : ∀ n u,u∈F n → T u∈F (n+1))
    (h1 : (1:A)∈F 0) (N : ℕ) :
    logarithm (N+1) T 1-T 1∈F 2 := by
  have hp : ∀ k,(T^k) 1∈F k := by
    intro k
    induction k with
    | zero => exact h1
    | succ k ih => simpa only [pow_succ',Module.End.mul_apply] using hT k _ ih
  rw [logarithm_eq]
  rw [Finset.sum_range_succ']
  simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    pow_zero,Nat.cast_zero,zero_add,div_one,one_smul,pow_one,add_sub_cancel_right]
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (hF (by omega : 2≤k+1+1) (hp _))


-- @@ L321-335 verbatim
theorem comparison_depth_one (F : ℕ → Submodule ℚ A) (hF : Antitone F)
    (hmul : ∀ i j {u v : A},u∈F i → v∈F j → u*v∈F (i+j))
    (θ : A →ₐ[ℚ] A) (hθ : ∀ n u,u∈F n → θ u-u∈F (n+1))
    {U Φ Ψ : A} (hU : U-1∈F 1) (hΦ : Φ-1∈F 1) (h : U*θ Φ=Ψ) :
    Ψ-Φ-(U-1)∈F 2 := by
  have hd : θ Φ-Φ∈F 2 := by
    simpa only [map_sub,map_one,sub_sub_sub_cancel_right] using hθ 1 (Φ-1) hΦ
  have hθΦ : θ Φ-1∈F 1 := by
    simpa only [sub_add_sub_cancel] using (F 1).add_mem (hF (by omega : 1≤2) hd) hΦ
  have hh := hmul 1 1 hU hθΦ
  have he : Ψ-Φ-(U-1)=(U-1)*(θ Φ-1)+(θ Φ-Φ) := by
    rw [←h]
    noncomm_ring
  rw [he]
  exact (F 2).add_mem hh hd


-- @@ L337-337 verbatim
end OperatorLog


-- @@ L339-339 verbatim
namespace KZComparison

-- @@ L340-340 verbatim
open CutoffDepth CutoffKZ FinitePicard KZCollar

 
-- @@ L342-343 verbatim
def positive (N : ℕ) : (Q ℝ N)ˣ :=
  (associator_isUnit (weight N) (gen_weight N false) (gen_weight N true)).unit

 
-- @@ L345-346 verbatim
@[simp] theorem positive_val (N : ℕ) : (positive N:Q ℝ N)=associator (weight N) (X N) (Y N) :=
  (associator_isUnit (weight N) (gen_weight N false) (gen_weight N true)).unit_spec

 
-- @@ L348-348 verbatim
def negative (N : ℕ) : (Q ℝ N)ˣ := Units.map (CutoffScaling.map N (-1:ℝ)).toMonoidHom (positive N)

 
-- @@ L350-355 verbatim
theorem negative_val (N : ℕ) : (negative N:Q ℝ N)=associator (weight N) (-X N) (-Y N) := by
  change CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N)=_
  rw [positive_val,map_associator _ (weight N) (weight N) rfl (gen_weight N false) (gen_weight N true)]
  have h (b : Bool) : CutoffScaling.map N (-1:ℝ) (gen N b)= -gen N b := by
    simpa only [neg_smul,one_smul,gen,TruncatedSubstitution.gen] using CutoffScaling.map_gen N (-1:ℝ) b
  rw [h false,h true]

 
-- @@ L357-360 verbatim
theorem positive_weight (N : ℕ) : (positive N:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  rw [positive_val]
  exact associator_sub_one_mem (weight N) (TruncatedSubstitution.filtration_initial N)
    (gen_weight N false) (gen_weight N true)

 
-- @@ L362-368 verbatim
theorem negative_weight (N : ℕ) : (negative N:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  have hh := TruncatedSubstitution.subst_preserves N (fun b => (-1:ℝ) • TruncatedSubstitution.gen N b)
    (fun b => (TruncatedWords.filtration ∅ N 1).smul_mem _ (TruncatedSubstitution.gen_mem N b))
    1 ((positive N:Q ℝ N)-1) (positive_weight N)
  change CutoffScaling.map N (-1:ℝ) ((positive N:Q ℝ N)-1)∈_ at hh
  change CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N)-1∈_
  simpa only [map_sub,map_one] using hh

 
-- @@ L370-371 verbatim
theorem positive_depth (N : ℕ) : (positive N:Q ℝ N)-1∈depthSpace N 1 := by
  rw [positive_val]; exact associator_depth_one N

 
-- @@ L373-376 verbatim
theorem negative_depth (N : ℕ) : (negative N:Q ℝ N)-1∈depthSpace N 1 := by
  have hh := CutoffScaling.preserves_depth N (-1:ℝ) 1 ((positive N:Q ℝ N)-1) (positive_depth N)
  change CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N)-1∈_
  simpa only [map_sub,map_one] using hh

 
-- @@ L378-379 verbatim
def theta (N : ℕ) : Q ℝ N ≃ₐ[ℝ] Q ℝ N :=
  ConjugateComparison.theta N (positive N) (negative N) (positive_weight N) (negative_weight N)

 
-- @@ L381-382 verbatim
def arrow (N : ℕ) : (Q ℝ N)ˣ :=
  ConjugateComparison.unitArrow N (positive N) (negative N) (positive_weight N) (negative_weight N)

 
-- @@ L384-385 verbatim
theorem exact_comparison (N : ℕ) : (arrow N:Q ℝ N)*theta N (positive N:Q ℝ N)=(negative N:Q ℝ N) :=
  ConjugateComparison.exact_comparison N _ _ _ _

 
-- @@ L387-387 verbatim
theorem theta_x (N : ℕ) : theta N (X N)=X N := ConjugateComparison.theta_x N _ _ _ _
 
-- @@ L388-389 verbatim
theorem theta_y (N : ℕ) : theta N (Y N)=((arrow N)⁻¹:(Q ℝ N)ˣ)*Y N*(arrow N:Q ℝ N) :=
  ConjugateComparison.theta_y N _ _ _ _

 
-- @@ L391-393 verbatim
theorem theta_depth (N n : ℕ) (u : Q ℝ N) (hu : u∈depthSpace N n) :
    theta N u-u∈depthSpace N (n+1) :=
  ConjugateComparison.theta_depth_raises N _ _ _ _ (positive_depth N) (negative_depth N) n u hu

 
-- @@ L395-396 verbatim
theorem arrow_depth (N : ℕ) : (arrow N:Q ℝ N)-1∈depthSpace N 1 :=
  ConjugateComparison.unitArrow_depth N _ _ _ _ (positive_depth N) (negative_depth N)

 
-- @@ L398-398 verbatim
def frames (N : ℕ) : Bool → (Q ℝ N)ˣ | false => 1 | true => arrow N

 
-- @@ L400-403 verbatim
theorem frames_depth (N : ℕ) (b : Bool) : (frames N b:Q ℝ N)-1∈depthSpace N 1 := by
  cases b
  · simp only [frames,Units.val_one,sub_self,Submodule.zero_mem]
  · exact arrow_depth N

 
-- @@ L405-405 verbatim
def rationalDepth (N n : ℕ) : Submodule ℚ (Q ℝ N) := (depthSpace N n).restrictScalars ℚ

 
-- @@ L407-411 verbatim
theorem rationalDepth_initial (N : ℕ) : rationalDepth N 0=⊤ := by
  apply Submodule.ext
  intro u
  change u∈depthSpace N 0 ↔ True
  simp only [CutoffKZ.depth_initial,Submodule.mem_top]

 
-- @@ L413-417 verbatim
theorem rationalDepth_terminal (N : ℕ) : rationalDepth N (N+2)=⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  have hh := depth_antitone N (show N+1≤N+2 by omega) hu
  simpa only [depth_terminal,Submodule.mem_bot] using hh

 
-- @@ L419-422 verbatim
def category (N : ℕ) : LogCategory.Data (Q ℝ N) Bool :=
  GaugeAutomorphism.data ((theta N).restrictScalars ℚ) (frames N) (rationalDepth N) (N+1)
    (depth_antitone N) (rationalDepth_initial N) (rationalDepth_terminal N)
    (depth_mul N) (theta_depth N) (frames_depth N)

 
-- @@ L424-424 verbatim
def value (N : ℕ) : Q ℝ N := LogCategory.delta (category N) false true 1

 
-- @@ L426-433 verbatim
theorem arrow_log_congruence (N : ℕ) : value N-((arrow N:Q ℝ N)-1)∈depthSpace N 2 := by
  have hh := OperatorLog.logarithm_depth_one (A:=Q ℝ N) (rationalDepth N) (depth_antitone N)
    ((category N).S false true-(1 : Module.End ℚ (Q ℝ N)))
    (GaugeAutomorphism.raises ((theta N).restrictScalars ℚ) (frames N) (rationalDepth N)
      (depth_antitone N) (rationalDepth_initial N) (depth_mul N) (theta_depth N) (frames_depth N) false true)
    (depth_one N) N
  simpa only [rationalDepth,Submodule.restrictScalars_mem,value,LogCategory.delta,category,GaugeAutomorphism.data,LinearMap.sub_apply,
    Module.End.one_apply,GaugeAutomorphism.map_apply,frames,inv_one,Units.val_one,map_one,mul_one] using hh

 
-- @@ L435-441 verbatim
theorem comparison_congruence (N : ℕ) :
    (negative N:Q ℝ N)-(positive N:Q ℝ N)-value N∈depthSpace N 2 := by
  have hh := OperatorLog.comparison_depth_one (rationalDepth N) (depth_antitone N)
    (depth_mul N) ((theta N).restrictScalars ℚ).toAlgHom (theta_depth N)
    (arrow_depth N) (positive_depth N) (exact_comparison N)
  have hd := (depthSpace N 2).sub_mem hh (arrow_log_congruence N)
  simpa only [sub_sub_sub_cancel_right] using hd

 
-- @@ L443-455 verbatim
theorem value_coefficient (N m : ℕ) :
    c N m (value N)=((-1:ℝ)^(m+1)-1)*c N m (positive N:Q ℝ N) := by
  have hh := coeff_zero_of_depth N 2 (comparison_congruence N)
    (w:=GenericIhara.depthOneWord m) (by simp [GenericIhara.depthOneWord,GenericIhara.depth])
  change c N m ((negative N:Q ℝ N)-(positive N:Q ℝ N)-value N)=0 at hh
  rw [map_sub,map_sub] at hh
  have hn : c N m (negative N:Q ℝ N)=(-1:ℝ)^(m+1)*c N m (positive N:Q ℝ N) := by
    change TruncatedFree.coefficient N (GenericIhara.depthOneWord m)
      (CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N))=_
    simpa only [length_depthOne,c] using CutoffScaling.coefficient N (-1:ℝ)
      (GenericIhara.depthOneWord m) (positive N:Q ℝ N)
  rw [hn] at hh
  linear_combination -hh

 
-- @@ L457-463 verbatim
theorem odd_value_nonzero (k : ℕ) : c (2*k+3) (2*k+2) (value (2*k+3))≠0 := by
  rw [value_coefficient]
  have hp : (-1:ℝ)^(2*k+2+1)= -1 := Odd.neg_one_pow ⟨k+1,by omega⟩
  rw [hp]
  apply mul_ne_zero (by norm_num)
  rw [positive_val]
  exact associator_coefficient_ne_zero _ _ (by omega) (by omega)


-- @@ L465-465 verbatim
end KZComparison


-- @@ L467-467 verbatim
namespace KZGroupLike

-- @@ L468-468 verbatim
open scoped TensorProduct

-- @@ L469-469 verbatim
open CutoffDepth CutoffKZ CutoffDiagonal KZCollar

-- @@ L470-470 verbatim
local instance (N : ℕ) : NormedRing (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedRing _

-- @@ L471-471 verbatim
local instance (N : ℕ) : NormedAlgebra ℝ (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedAlgebra _
 
-- @@ L472-484 verbatim
theorem associator_diagonal (N : ℕ) :
    diagonal N (associator (weight (N+N)) (X (N+N)) (Y (N+N)))=
    associator (weight N) (X N) (Y N)⊗ₜ[ℝ]associator (weight N) (X N) (Y N) := by
  rw [map_associator_general (diagonal N) (weight (N+N)) (tensorWeight N)
    (gen_weight (N+N) false) (gen_weight (N+N) true)
    (diagonal_mem N 1 _ (gen_weight (N+N) false)) (diagonal_mem N 1 _ (gen_weight (N+N) true)),
    diagonal_gen,diagonal_gen]
  rw [KZProduct.associator_product (left N) (right N) (commute N) (weight N) (weight N) (tensorWeight N)
    (gen_weight N false) (gen_weight N true) (gen_weight N false) (gen_weight N true)
    (left_mem N 1 _ (gen_weight N false)) (left_mem N 1 _ (gen_weight N true))
    (right_mem N 1 _ (gen_weight N false)) (right_mem N 1 _ (gen_weight N true))]
  change (_⊗ₜ[ℝ](1:Q ℝ N))*((1:Q ℝ N)⊗ₜ[ℝ]_)=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
 
-- @@ L485-488 verbatim
theorem positive_diagonal (N : ℕ) :
    diagonal N (KZComparison.positive (N+N):Q ℝ (N+N))=
      (KZComparison.positive N:Q ℝ N)⊗ₜ[ℝ](KZComparison.positive N:Q ℝ N) := by
  simp only [KZComparison.positive_val,associator_diagonal]
 
-- @@ L489-508 verbatim
theorem negative_diagonal (N : ℕ) :
    diagonal N (KZComparison.negative (N+N):Q ℝ (N+N))=
      (KZComparison.negative N:Q ℝ N)⊗ₜ[ℝ](KZComparison.negative N:Q ℝ N) := by
  simp only [KZComparison.negative_val]
  rw [map_associator_general (diagonal N) (weight (N+N)) (tensorWeight N)
    ((weight (N+N)).space 1|>.neg_mem (gen_weight (N+N) false))
    ((weight (N+N)).space 1|>.neg_mem (gen_weight (N+N) true))
    (by rw [map_neg]; exact ((tensorWeight N).space 1).neg_mem (diagonal_mem N 1 _ (gen_weight (N+N) false)))
    (by rw [map_neg]; exact ((tensorWeight N).space 1).neg_mem (diagonal_mem N 1 _ (gen_weight (N+N) true)))]
  simp only [map_neg,diagonal_gen,neg_add]
  rw [←map_neg (left N),←map_neg (right N),←map_neg (left N),←map_neg (right N)]
  rw [KZProduct.associator_product (left N) (right N) (commute N) (weight N) (weight N) (tensorWeight N)
    ((weight N).space 1|>.neg_mem (gen_weight N false)) ((weight N).space 1|>.neg_mem (gen_weight N true))
    ((weight N).space 1|>.neg_mem (gen_weight N false)) ((weight N).space 1|>.neg_mem (gen_weight N true))
    (by simpa only [map_neg] using ((tensorWeight N).space 1).neg_mem (left_mem N 1 _ (gen_weight N false)))
    (by simpa only [map_neg] using ((tensorWeight N).space 1).neg_mem (left_mem N 1 _ (gen_weight N true)))
    (by simpa only [map_neg] using ((tensorWeight N).space 1).neg_mem (right_mem N 1 _ (gen_weight N false)))
    (by simpa only [map_neg] using ((tensorWeight N).space 1).neg_mem (right_mem N 1 _ (gen_weight N true)))]
  change (_⊗ₜ[ℝ](1:Q ℝ N))*((1:Q ℝ N)⊗ₜ[ℝ]_)=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

-- @@ L509-509 verbatim
end KZGroupLike


-- @@ L511-511 verbatim
namespace TruncatedSubstitution

-- @@ L512-512 verbatim
open AssociativeElimination TruncatedWords

-- @@ L513-513 verbatim
variable {R α B : Type*} [CommRing R] [Ring B] [Algebra R B]
 
-- @@ L514-522 verbatim
theorem hom_ext (N : ℕ) (f g : Q (∅ : Set (A R α)) N →ₐ[R] B)
    (h : ∀ a,f (gen N a)=g (gen N a)) : f=g := by
  have he : f.comp (quotient ∅ N)=g.comp (quotient ∅ N) := by
    apply AssociativeElimination.hom_ext
    exact h
  apply AlgHom.ext
  intro u
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R α)) N) u
  exact AlgHom.congr_fun he p

-- @@ L523-523 verbatim
end TruncatedSubstitution


-- @@ L525-525 verbatim
namespace ConjugateCoalgebra

-- @@ L526-526 verbatim
open scoped TensorProduct

-- @@ L527-527 verbatim
open CutoffDepth CutoffKZ CutoffDiagonal ConjugateComparison


-- @@ L529-533 verbatim
def tensorUnit {A : Type*} [Ring A] [Algebra ℝ A] (P : Aˣ) : (A⊗[ℝ]A)ˣ where
  val := (P:A)⊗ₜ[ℝ](P:A)
  inv := ((P⁻¹:Aˣ):A)⊗ₜ[ℝ]((P⁻¹:Aˣ):A)
  val_inv := by rw [Algebra.TensorProduct.tmul_mul_tmul,Units.mul_inv,Algebra.TensorProduct.one_def]
  inv_val := by rw [Algebra.TensorProduct.tmul_mul_tmul,Units.inv_mul,Algebra.TensorProduct.one_def]


-- @@ L535-541 verbatim
theorem inverse_diagonal (N : ℕ) (P : (Q ℝ (N+N))ˣ) (p : (Q ℝ N)ˣ)
    (h : diagonal N (P:Q ℝ (N+N))=(p:Q ℝ N)⊗ₜ[ℝ](p:Q ℝ N)) :
    diagonal N ((P⁻¹:(Q ℝ (N+N))ˣ):Q ℝ (N+N))=
      ((p⁻¹:(Q ℝ N)ˣ):Q ℝ N)⊗ₜ[ℝ]((p⁻¹:(Q ℝ N)ˣ):Q ℝ N) := by
  have hu : Units.map (diagonal N).toMonoidHom P=tensorUnit p := Units.ext h
  have hh := congrArg (fun u => ((u⁻¹:(Q ℝ N⊗[ℝ]Q ℝ N)ˣ):Q ℝ N⊗[ℝ]Q ℝ N)) hu
  exact hh


-- @@ L543-545 verbatim
theorem transport_cutoff_gen (N : ℕ) (P : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1) (b : Bool) :
    transport N P hP (gen N b)=family N P b := transport_gen N P hP b


-- @@ L547-548 verbatim
theorem congr_tmul {A : Type*} [Ring A] [Algebra ℝ A] (e : A ≃ₐ[ℝ] A) (a b : A) :
    Algebra.TensorProduct.congr e e (a⊗ₜ[ℝ]b)=e a⊗ₜ[ℝ]e b := rfl


-- @@ L550-576 verbatim
theorem transport_diagonal (N : ℕ) (P : (Q ℝ (N+N))ˣ) (p : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : diagonal N (P:Q ℝ (N+N))=(p:Q ℝ N)⊗ₜ[ℝ](p:Q ℝ N)) (u : Q ℝ (N+N)) :
    diagonal N (transport (N+N) P hP u)=
      Algebra.TensorProduct.congr (transport N p hp) (transport N p hp) (diagonal N u) := by
  have he : (diagonal N).comp (transport (N+N) P hP).toAlgHom=
      (Algebra.TensorProduct.congr (transport N p hp) (transport N p hp)).toAlgHom.comp (diagonal N) := by
    apply TruncatedSubstitution.hom_ext (N+N)
    intro b
    change diagonal N (transport (N+N) P hP (gen (N+N) b))=
      Algebra.TensorProduct.congr (transport N p hp) (transport N p hp) (diagonal N (gen (N+N) b))
    rw [transport_cutoff_gen,diagonal_gen]
    cases b
    · simp only [family,left,right,Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply,map_add,congr_tmul,map_one,
        transport_cutoff_gen,ConjugateComparison.family]
      exact diagonal_gen N false
    · change diagonal N (((P⁻¹:(Q ℝ (N+N))ˣ):Q ℝ (N+N))*gen (N+N) true*(P:Q ℝ (N+N)))=_
      rw [map_mul,map_mul,inverse_diagonal N P p h,h,diagonal_gen]
      change (_⊗ₜ[ℝ]_)*(gen N true⊗ₜ[ℝ]1+1⊗ₜ[ℝ]gen N true)*(_⊗ₜ[ℝ]_)=_
      simp only [mul_add,add_mul,Algebra.TensorProduct.tmul_mul_tmul,mul_one,
        Units.inv_mul,map_add,left,right,Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply,congr_tmul,map_one,
        transport_cutoff_gen,family]
      rfl
  exact AlgHom.congr_fun he u


-- @@ L578-582 verbatim
theorem natural_inverse {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    (f : A →ₐ[ℝ] B) (e : A ≃ₐ[ℝ] A) (d : B ≃ₐ[ℝ] B)
    (he : ∀ u,f (e u)=d (f u)) (u : A) : f (e.symm u)=d.symm (f u) := by
  apply d.injective
  rw [d.apply_symm_apply,←he,e.apply_symm_apply]


-- @@ L584-601 verbatim
theorem theta_diagonal (N : ℕ) (P V : (Q ℝ (N+N))ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hV : (V:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hΔP : diagonal N (P:Q ℝ (N+N))=(p:Q ℝ N)⊗ₜ[ℝ](p:Q ℝ N))
    (hΔV : diagonal N (V:Q ℝ (N+N))=(v:Q ℝ N)⊗ₜ[ℝ](v:Q ℝ N)) (u : Q ℝ (N+N)) :
    diagonal N (theta (N+N) P V hP hV u)=
      Algebra.TensorProduct.congr (theta N p v hp hv) (theta N p v hp hv) (diagonal N u) := by
  rw [theta,AlgEquiv.trans_apply,transport_diagonal N V v hV hv hΔV,
    natural_inverse (diagonal N) (transport (N+N) P hP)
      (Algebra.TensorProduct.congr (transport N p hp) (transport N p hp))
      (transport_diagonal N P p hP hp hΔP)]
  generalize diagonal N u=z
  induction z using TensorProduct.inductionOn with

  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul a b => rfl


-- @@ L603-619 verbatim
theorem arrow_diagonal (N : ℕ) (P V : (Q ℝ (N+N))ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hV : (V:Q ℝ (N+N))-1∈TruncatedWords.filtration ∅ (N+N) 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hΔP : diagonal N (P:Q ℝ (N+N))=(p:Q ℝ N)⊗ₜ[ℝ](p:Q ℝ N))
    (hΔV : diagonal N (V:Q ℝ (N+N))=(v:Q ℝ N)⊗ₜ[ℝ](v:Q ℝ N)) :
    diagonal N (unitArrow (N+N) P V hP hV:Q ℝ (N+N))=
      (unitArrow N p v hp hv:Q ℝ N)⊗ₜ[ℝ](unitArrow N p v hp hv:Q ℝ N) := by
  have ht : diagonal N (Units.map (theta (N+N) P V hP hV).toMonoidHom P:Q ℝ (N+N))=
      (Units.map (theta N p v hp hv).toMonoidHom p:Q ℝ N)⊗ₜ[ℝ]
        (Units.map (theta N p v hp hv).toMonoidHom p:Q ℝ N) := by
    change diagonal N (theta (N+N) P V hP hV (P:Q ℝ (N+N)))=_
    rw [theta_diagonal N P V p v hP hV hp hv hΔP hΔV,hΔP]
    rfl
  simp only [unitArrow,Units.val_mul,map_mul,hΔV,inverse_diagonal N _ _ ht,
    Algebra.TensorProduct.tmul_mul_tmul]

-- @@ L620-620 verbatim
end ConjugateCoalgebra


-- @@ L622-622 verbatim
namespace OperatorLog


-- @@ L624-624 verbatim
section

-- @@ L625-625 verbatim
open scoped TensorProduct

-- @@ L626-626 verbatim
variable {V : Type*} [AddCommGroup V] [Module ℚ V]


-- @@ L628-633 verbatim
theorem logarithm_stable (T : Module.End ℚ V) {N M : ℕ} (hT : T^(N+1)=0) (hNM : N≤M) :
    logarithm N T=logarithm M T := by
  unfold logarithm
  apply sum_range_extend _ (by omega : N+1≤M+1)
  intro k hk hkm
  rw [pow_eq_zero_of_le hk hT,smul_zero]


-- @@ L635-636 verbatim
def tensorDifference (T : Module.End ℚ V) : Module.End ℚ (V ⊗[ℚ] V) :=
  TensorProduct.map (1+T) (1+T)-1


-- @@ L638-655 verbatim
theorem tensorDifference_nilpotent (T : Module.End ℚ V) (N : ℕ) (hT : T^(N+1)=0) :
    tensorDifference T^(2*N+1)=0 := by
  let a := TensorProduct.map T (1+T)
  let b := TensorProduct.map (1:Module.End ℚ V) T
  have he : tensorDifference T=a+b := by
    simp only [tensorDifference,TensorProduct.map_add_left,TensorProduct.map_add_right,
      TensorProduct.map_one,a,b]
    abel
  have hc : Commute a b := by
    change a*b=b*a
    dsimp only [a,b]
    rw [←TensorProduct.map_mul,←TensorProduct.map_mul,mul_one,one_mul]
    congr 1
    noncomm_ring
  have ha : a^(N+1)=0 := by simp only [a,TensorProduct.map_pow,hT,TensorProduct.map_zero_left]
  have hb : b^(N+1)=0 := by simp only [b,TensorProduct.map_pow,hT,TensorProduct.map_zero_right]
  rw [he]
  exact hc.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero ha hb (by omega)


-- @@ L657-671 verbatim
theorem logarithm_tensor_tmul (T : Module.End ℚ V) (N : ℕ) (hT : T^(N+1)=0) (u v : V) :
    logarithm (2*N) (tensorDifference T) (u ⊗ₜ[ℚ] v)=
      logarithm N T u ⊗ₜ[ℚ] v+u ⊗ₜ[ℚ] logarithm N T v := by
  have hp : T^(2*N+1)=0 := pow_eq_zero_of_le (by omega) hT
  have h := logarithm_bilinear (2*N) T T (tensorDifference T) hp hp
    (tensorDifference_nilpotent T N hT) (TensorProduct.mk ℚ V V)
    (by
      intro a b
      have he : 1+tensorDifference T=TensorProduct.map (1+T) (1+T) := by
        unfold tensorDifference
        abel
      rw [he]
      rfl) u v
  rw [←logarithm_stable T hT (by omega : N≤2*N)] at h
  exact h


-- @@ L673-680 verbatim
theorem logarithm_tensor (T : Module.End ℚ V) (N : ℕ) (hT : T^(N+1)=0) (z : V ⊗[ℚ] V) :
    logarithm (2*N) (tensorDifference T) z=
      TensorProduct.map (logarithm N T) LinearMap.id z+
        TensorProduct.map LinearMap.id (logarithm N T) z := by
  induction z using TensorProduct.inductionOn with

  | add z w hz hw => simp only [map_add,hz,hw]; abel
  | tmul u v => exact logarithm_tensor_tmul T N hT u v


-- @@ L682-695 verbatim
theorem logarithm_coderivation (T : Module.End ℚ V) (N : ℕ) (hT : T^(N+1)=0)
    (Δ : V →ₗ[ℚ] V ⊗[ℚ] V)
    (hΔ : ∀ v,Δ ((1+T) v)=TensorProduct.map (1+T) (1+T) (Δ v)) (v : V) :
    Δ (logarithm N T v)=TensorProduct.map (logarithm N T) LinearMap.id (Δ v)+
      TensorProduct.map LinearMap.id (logarithm N T) (Δ v) := by
  have hn : ∀ v,Δ (T v)=tensorDifference T (Δ v) := by
    intro v
    have h := hΔ v
    simp only [LinearMap.add_apply,Module.End.one_apply,map_add] at h
    change Δ (T v)=TensorProduct.map (1+T) (1+T) (Δ v)-Δ v
    exact eq_sub_of_add_eq' h
  rw [logarithm_stable T hT (by omega : N≤2*N),
    logarithm_natural (2*N) T (tensorDifference T) Δ hn,logarithm_tensor T N hT]
  rw [←logarithm_stable T hT (by omega : N≤2*N)]


-- @@ L697-697 verbatim
end


-- @@ L699-700 verbatim
variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]


-- @@ L702-717 verbatim
theorem logarithm_diagonal (N : ℕ) (T : Module.End ℚ V) (R : Module.End ℚ W)
    (hT : T^(N+1)=0) (hR : R^(N+1)=0)
    (Δ : V →ₗ[ℚ] Z) (B : W →ₗ[ℚ] W →ₗ[ℚ] Z) (a : V) (b : W)
    (h : ∀ m : ℕ,Δ (((1+T)^m) a)=B (((1+R)^m) b) (((1+R)^m) b)) :
    Δ (logarithm N T a)=B (logarithm N R b) b+B b (logarithm N R b) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro l
  have hp : valuePolynomial N T a (l.comp Δ)=pairPolynomial N R R B b b l := by
    apply polynomial_ext_nat
    intro m
    rw [value_eval,pair_eval,interpolate_nat N T hT,interpolate_nat N R hR]
    exact congrArg l (h m)
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff 1) hp
  rw [value_one,pair_one] at hc
  simpa only [map_sub,sub_eq_zero,LinearMap.comp_apply] using hc


-- @@ L719-719 verbatim
end OperatorLog


-- @@ L721-721 verbatim
namespace KZPrimitiveValue

-- @@ L722-722 verbatim
open scoped TensorProduct

-- @@ L723-723 verbatim
open CutoffDepth CutoffKZ CutoffDiagonal KZComparison

 
-- @@ L725-729 verbatim
theorem theta_diagonal (N : ℕ) (u : Q ℝ (N+N)) :
    diagonal N (theta (N+N) u)=
      Algebra.TensorProduct.congr (theta N) (theta N) (diagonal N u) :=
  ConjugateCoalgebra.theta_diagonal N _ _ _ _ _ _ _ _
    (KZGroupLike.positive_diagonal N) (KZGroupLike.negative_diagonal N) u

 
-- @@ L731-734 verbatim
theorem arrow_diagonal (N : ℕ) : diagonal N (arrow (N+N):Q ℝ (N+N))=
    (arrow N:Q ℝ N)⊗ₜ[ℝ](arrow N:Q ℝ N) :=
  ConjugateCoalgebra.arrow_diagonal N _ _ _ _ _ _ _ _
    (KZGroupLike.positive_diagonal N) (KZGroupLike.negative_diagonal N)

 
-- @@ L736-737 verbatim
def S (N : ℕ) : Module.End ℝ (Q ℝ N) :=
  (LinearMap.mulLeft ℝ (arrow N:Q ℝ N)).comp (theta N).toLinearMap
 
-- @@ L738-738 verbatim
@[simp] theorem S_apply (N : ℕ) (u : Q ℝ N) : S N u=(arrow N:Q ℝ N)*theta N u := rfl

 
-- @@ L740-745 verbatim
theorem category_S (N : ℕ) : (category N).S false true=(S N).restrictScalars ℚ := by
  apply LinearMap.ext
  intro u
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,frames,inv_one,
    Units.val_one,mul_one]
  rfl

 
-- @@ L747-756 verbatim
theorem S_diagonal (N : ℕ) (u : Q ℝ (N+N)) :
    diagonal N (S (N+N) u)=TensorProduct.map (S N) (S N) (diagonal N u) := by
  rw [S_apply,map_mul,arrow_diagonal,theta_diagonal]
  generalize diagonal N u=z
  induction z using TensorProduct.inductionOn with

  | add z w hz hw => simp only [map_add,mul_add,hz,hw]
  | tmul a b =>
    rw [ConjugateCoalgebra.congr_tmul,Algebra.TensorProduct.tmul_mul_tmul]
    rfl

 
-- @@ L758-761 verbatim
def tmulQ (N : ℕ) : Q ℝ N →ₗ[ℚ] Q ℝ N →ₗ[ℚ] Q ℝ N⊗[ℝ]Q ℝ N :=
  LinearMap.mk₂ ℚ (fun a b => a⊗ₜ[ℝ]b)
    TensorProduct.add_tmul (fun c a b => (TensorProduct.smul_tmul' c a b).symm)
    TensorProduct.tmul_add TensorProduct.tmul_smul

 
-- @@ L763-775 verbatim
theorem orbit_diagonal (N m : ℕ) :
    diagonal N ((((category (N+N)).S false true)^m) (1:Q ℝ (N+N)))=
      ((((category N).S false true)^m) (1:Q ℝ N))⊗ₜ[ℝ]
        ((((category N).S false true)^m) (1:Q ℝ N)) := by
  induction m with
  | zero => simp only [pow_zero,Module.End.one_apply,map_one,Algebra.TensorProduct.one_def]
  | succ m ih =>
    simp only [pow_succ',Module.End.mul_apply]
    rw [category_S]
    change diagonal N (S (N+N) _)=_
    rw [category_S] at ih
    rw [S_diagonal,ih,TensorProduct.map_tmul,category_S]
    rfl

 
-- @@ L777-792 verbatim
theorem value_diagonal (N : ℕ) : diagonal N (value (N+N))=
    value N⊗ₜ[ℝ](1:Q ℝ N)+(1:Q ℝ N)⊗ₜ[ℝ]value N := by
  let T := (category (N+N)).S false true-1
  let R := (category N).S false true-1
  have hT : T^(N+N+1+1)=0 := (category (N+N)).nilpotent false true
  have hR : R^(N+1+1)=0 := (category N).nilpotent false true
  have hR' : R^(N+N+1+1)=0 := pow_eq_zero_of_le (by omega) hR
  have hh := OperatorLog.logarithm_diagonal (N+N+1) T R hT hR'
    ((diagonal N).toLinearMap.restrictScalars ℚ) (tmulQ N) 1 1 (by
      intro m
      have ht : 1+T=(category (N+N)).S false true := by dsimp only [T]; abel
      have hr : 1+R=(category N).S false true := by dsimp only [R]; abel
      rw [ht,hr]
      exact orbit_diagonal N m)
  rw [←OperatorLog.logarithm_stable R hR (by omega : N+1≤N+N+1)] at hh
  exact hh


-- @@ L794-794 verbatim
end KZPrimitiveValue


-- @@ L796-796 verbatim
namespace KZCutoffComparison

-- @@ L797-797 verbatim
open CutoffDepth CutoffKZ CutoffDiagonal KZComparison ConjugateComparison

 
-- @@ L799-818 verbatim
theorem transport_natural (M N : ℕ) (f : Q ℝ M →ₐ[ℝ] Q ℝ N)
    (hgen : ∀ b,f (gen M b)=gen N b) (P : (Q ℝ M)ˣ) (p : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map f.toMonoidHom P=p) (u : Q ℝ M) :
    f (transport M P hP u)=transport N p hp (f u) := by
  have hv : f (P:Q ℝ M)=(p:Q ℝ N) := congrArg Units.val h
  have hi : f ((P⁻¹:(Q ℝ M)ˣ):Q ℝ M)=((p⁻¹:(Q ℝ N)ˣ):Q ℝ N) :=
    congrArg (fun v => ((v⁻¹:(Q ℝ N)ˣ):Q ℝ N)) h
  have he : f.comp (transport M P hP).toAlgHom=(transport N p hp).toAlgHom.comp f := by
    apply TruncatedSubstitution.hom_ext M
    intro b
    change f (transport M P hP (gen M b))=transport N p hp (f (gen M b))
    rw [ConjugateCoalgebra.transport_cutoff_gen,hgen,ConjugateCoalgebra.transport_cutoff_gen]
    cases b
    · exact hgen false
    · change f (((P⁻¹:(Q ℝ M)ˣ):Q ℝ M)*gen M true*(P:Q ℝ M))=_
      rw [map_mul,map_mul,hi,hv,hgen]
      rfl
  exact AlgHom.congr_fun he u

 
-- @@ L820-831 verbatim
theorem theta_natural (M N : ℕ) (f : Q ℝ M →ₐ[ℝ] Q ℝ N)
    (hgen : ∀ b,f (gen M b)=gen N b) (P V : (Q ℝ M)ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hV : (V:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map f.toMonoidHom P=p) (k : Units.map f.toMonoidHom V=v) (u : Q ℝ M) :
    f (ConjugateComparison.theta M P V hP hV u)=ConjugateComparison.theta N p v hp hv (f u) := by
  rw [ConjugateComparison.theta,AlgEquiv.trans_apply,transport_natural M N f hgen V v hV hv k,
    ConjugateCoalgebra.natural_inverse f (transport M P hP) (transport N p hp)
      (transport_natural M N f hgen P p hP hp h)]
  rfl

 
-- @@ L833-847 verbatim
theorem arrow_natural (M N : ℕ) (f : Q ℝ M →ₐ[ℝ] Q ℝ N)
    (hgen : ∀ b,f (gen M b)=gen N b) (P V : (Q ℝ M)ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hV : (V:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map f.toMonoidHom P=p) (k : Units.map f.toMonoidHom V=v) :
    Units.map f.toMonoidHom (unitArrow M P V hP hV)=unitArrow N p v hp hv := by
  have ht : Units.map f.toMonoidHom (Units.map (ConjugateComparison.theta M P V hP hV).toMonoidHom P)=
      Units.map (ConjugateComparison.theta N p v hp hv).toMonoidHom p := by
    apply Units.ext
    change f (ConjugateComparison.theta M P V hP hV (P:Q ℝ M))=_
    rw [theta_natural M N f hgen P V p v hP hV hp hv h k,show f (P:Q ℝ M)=(p:Q ℝ N) from congrArg Units.val h]
    rfl
  simp only [unitArrow,map_mul,map_inv,k,ht]

 
-- @@ L849-853 verbatim
theorem positive_drop (M N : ℕ) (h : N≤M) :
    Units.map (drop M N h).toMonoidHom (positive M)=positive N := by
  apply Units.ext
  change drop M N h (positive M:Q ℝ M)=(positive N:Q ℝ N)
  rw [positive_val,positive_val,drop_associator]
 
-- @@ L854-861 verbatim
theorem negative_drop (M N : ℕ) (h : N≤M) :
    Units.map (drop M N h).toMonoidHom (negative M)=negative N := by
  apply Units.ext
  change drop M N h (negative M:Q ℝ M)=(negative N:Q ℝ N)
  rw [negative_val,negative_val,KZCollar.map_associator_general (drop M N h) (weight M) (weight N)
    ((weight M).space 1|>.neg_mem (gen_weight M false)) ((weight M).space 1|>.neg_mem (gen_weight M true))
    (by simpa only [map_neg,drop_gen] using ((weight N).space 1).neg_mem (gen_weight N false))
    (by simpa only [map_neg,drop_gen] using ((weight N).space 1).neg_mem (gen_weight N true)),map_neg,map_neg,drop_gen,drop_gen]

 
-- @@ L863-866 verbatim
theorem theta_drop (M N : ℕ) (h : N≤M) (u : Q ℝ M) :
    drop M N h (KZComparison.theta M u)=KZComparison.theta N (drop M N h u) :=
  theta_natural M N (drop M N h) (drop_gen M N h) _ _ _ _ _ _ _ _
    (positive_drop M N h) (negative_drop M N h) u
 
-- @@ L867-869 verbatim
theorem arrow_drop (M N : ℕ) (h : N≤M) : Units.map (drop M N h).toMonoidHom (arrow M)=arrow N :=
  arrow_natural M N (drop M N h) (drop_gen M N h) _ _ _ _ _ _ _ _
    (positive_drop M N h) (negative_drop M N h)
 
-- @@ L870-876 verbatim
theorem S_drop (M N : ℕ) (h : N≤M) (u : Q ℝ M) :
    drop M N h ((category M).S false true u)=(category N).S false true (drop M N h u) := by
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,frames,inv_one,
    Units.val_one,mul_one]
  change drop M N h ((arrow M:Q ℝ M)*KZComparison.theta M u)=_
  rw [map_mul,theta_drop,show drop M N h (arrow M:Q ℝ M)=(arrow N:Q ℝ N) from congrArg Units.val (arrow_drop M N h)]
  rfl
 
-- @@ L877-887 verbatim
theorem value_drop (M N : ℕ) (h : N≤M) : drop M N h (value M)=value N := by
  have hn : ∀ u,drop M N h (((category M).S false true-1) u)=
      ((category N).S false true-1) (drop M N h u) := by
    intro u
    simp only [LinearMap.sub_apply,Module.End.one_apply,map_sub,S_drop]
  have hh := OperatorLog.logarithm_natural (M+1) ((category M).S false true-1)
    ((category N).S false true-1) ((drop M N h).toLinearMap.restrictScalars ℚ) hn 1
  rw [←OperatorLog.logarithm_stable _ ((category N).nilpotent false true) (by omega : N+1≤M+1)] at hh
  change drop M N h (value M)=OperatorLog.logarithm (N+1) _ (drop M N h 1) at hh
  rw [map_one] at hh
  exact hh


-- @@ L889-889 verbatim
end KZCutoffComparison


-- @@ L891-891 verbatim
namespace CutoffPrimitiveExtract

-- @@ L892-892 verbatim
open AssociativeElimination WordGrading TensorProjection

-- @@ L893-893 verbatim
open scoped TensorProduct

-- @@ L894-894 verbatim
variable {R α : Type*} [CommRing R]


-- @@ L896-897 verbatim
def truncVal (N : ℕ) : A R α →ₗ[R] A R α :=
  (TruncatedFree.B R α N).subtype.comp (TruncatedFree.trunc N)


-- @@ L899-908 verbatim
theorem piece_trunc (N n : ℕ) (hn : n≤N) (p : A R α) : piece n (truncVal N p)=piece n p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change piece n (project (fun w => len w≤N) (word w))=piece n (word w)
    rw [project_word]
    by_cases hw : len w≤N
    · rw [ite_eq_left hw]
    · rw [ite_eq_right hw,map_zero,TensorProjection.piece,WordGrading.piece,project_word,ite_eq_right (by change len w≠n; omega)]
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]


-- @@ L910-920 verbatim
theorem totalPiece_trunc (N n : ℕ) (hn : n≤N) (u : A R α⊗[R]A R α) :
    totalPiece n (TensorProduct.map (truncVal N) (truncVal N) u)=totalPiece n u := by
  induction u using TensorProduct.inductionOn with

  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul p q =>
    simp only [TensorProduct.map_tmul,totalPiece,LinearMap.sum_apply,TensorProduct.map_tmul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [piece_trunc N i (by have hi' := Finset.mem_range.mp hi; omega),
      piece_trunc N (n-i) (by omega)]


-- @@ L922-923 verbatim
def leftPair : A R α →ₐ[R] PrimitiveWords.B R α :=
  MonoidAlgebra.mapDomainAlgHom R R ((MonoidHom.id _).prod (1:FreeMonoid α →* FreeMonoid α))

-- @@ L924-925 verbatim
def rightPair : A R α →ₐ[R] PrimitiveWords.B R α :=
  MonoidAlgebra.mapDomainAlgHom R R ((1:FreeMonoid α →* FreeMonoid α).prod (MonoidHom.id _))

-- @@ L926-927 verbatim
@[simp] theorem leftPair_word (w : FreeMonoid α) : leftPair (word (R:=R) w)=PrimitiveWords.pair w 1 := by
  simp [leftPair,word,PrimitiveWords.pair,MonoidAlgebra.mapDomainAlgHom]

-- @@ L928-929 verbatim
@[simp] theorem rightPair_word (w : FreeMonoid α) : rightPair (word (R:=R) w)=PrimitiveWords.pair 1 w := by
  simp [rightPair,word,PrimitiveWords.pair,MonoidAlgebra.mapDomainAlgHom]


-- @@ L931-943 verbatim
theorem pair_commute (p q : A R α) : Commute (leftPair p) (rightPair q) := by
  change leftPair p*rightPair q=rightPair q*leftPair p
  induction p using MonoidAlgebra.induction_on with
  | of u =>
    change leftPair (word u)*rightPair q=rightPair q*leftPair (word u)
    induction q using MonoidAlgebra.induction_on with
    | of v =>
      change leftPair (word u)*rightPair (word v)=rightPair (word v)*leftPair (word u)
      simp only [leftPair_word,rightPair_word,←PrimitiveWords.pair_mul,mul_one,one_mul]
    | add q r hq hr => simp only [map_add,mul_add,add_mul,hq,hr]
    | smul c q hq => simp only [map_smul,mul_smul_comm,smul_mul_assoc,hq]
  | add p r hp hr => simp only [map_add,mul_add,add_mul,hp,hr]
  | smul c p hp => simp only [map_smul,mul_smul_comm,smul_mul_assoc,hp]


-- @@ L945-946 verbatim
def pairMap : A R α⊗[R]A R α →ₐ[R] PrimitiveWords.B R α :=
  Algebra.TensorProduct.lift leftPair rightPair pair_commute


-- @@ L948-957 verbatim
theorem pairMap_coproduct (p : A R α) : (pairMap (R:=R) (α:=α)) ((coproduct (R:=R) (α:=α)) p)=PrimitiveWords.coproduct p := by
  have he : (pairMap (R:=R) (α:=α)).comp coproduct=PrimitiveWords.coproduct := by
    apply AssociativeElimination.hom_ext
    intro a
    change (pairMap (R:=R) (α:=α)) ((coproduct (R:=R) (α:=α)) (atom a))=PrimitiveWords.coproduct (atom a)
    rw [TensorProjection.coproduct_atom,PrimitiveWords.coproduct_atom,map_add]
    simp only [pairMap,Algebra.TensorProduct.lift_tmul,map_one,mul_one,one_mul]
    change leftPair (word (FreeMonoid.of a))+rightPair (word (FreeMonoid.of a))=_
    rw [leftPair_word,rightPair_word]
  exact AlgHom.congr_fun he p


-- @@ L959-966 verbatim
theorem leftPair_eq (p : A R α) : leftPair p=PrimitiveWords.left p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change leftPair (word w)=PrimitiveWords.left (word w)
    rw [leftPair_word]
    simp [PrimitiveWords.left,word]
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

-- @@ L967-974 verbatim
theorem rightPair_eq (p : A R α) : rightPair p=PrimitiveWords.right p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rightPair (word w)=PrimitiveWords.right (word w)
    rw [rightPair_word]
    simp [PrimitiveWords.right,word]
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]


-- @@ L976-981 verbatim
theorem primitive_of_tensor (p : A R α) (h : (coproduct (R:=R) (α:=α)) p=p⊗ₜ[R]1+(1:A R α)⊗ₜ[R]p) :
    PrimitiveWords.Primitive p := by
  unfold PrimitiveWords.Primitive
  have hh := congrArg (pairMap (R:=R) (α:=α)) h
  rw [pairMap_coproduct,map_add] at hh
  simpa only [pairMap,Algebra.TensorProduct.lift_tmul,map_one,mul_one,one_mul,leftPair_eq,rightPair_eq] using hh


-- @@ L983-983 verbatim
open CutoffDepth CutoffKZ CutoffDiagonal


-- @@ L985-986 verbatim
def normalVal (N : ℕ) : Q ℝ N →ₗ[ℝ] A ℝ Bool :=
  (TruncatedFree.B ℝ Bool N).subtype.comp (TruncatedFree.normal N)

-- @@ L987-991 verbatim
@[simp] theorem normalVal_quotient (N : ℕ) (p : A ℝ Bool) :
    normalVal N (TruncatedWords.quotient ∅ N p)=truncVal N p := by
  change (TruncatedFree.normal N (TruncatedWords.quotient ∅ N p)).val=_
  rw [TruncatedFree.normal_quotient]
  rfl

-- @@ L992-997 verbatim
@[simp] theorem normalVal_one (N : ℕ) : normalVal N 1=1 := by
  have h := normalVal_quotient N (1:A ℝ Bool)
  rw [map_one] at h
  rw [h]
  change project _ (word 1)=word 1
  rw [project_word,ite_eq_left (by simp)]


-- @@ L999-1010 verbatim
theorem diagonal_quotient (N : ℕ) (p : A ℝ Bool) :
    diagonal N (TruncatedWords.quotient ∅ (N+N) p)=
      TensorProduct.map (TruncatedWords.quotient ∅ N).toLinearMap (TruncatedWords.quotient ∅ N).toLinearMap ((coproduct (R:=ℝ) (α:=Bool)) p) := by
  have he : (diagonal N).comp (TruncatedWords.quotient ∅ (N+N))=
      (Algebra.TensorProduct.map (TruncatedWords.quotient ∅ N) (TruncatedWords.quotient ∅ N)).comp coproduct := by
    apply AssociativeElimination.hom_ext
    intro a
    change diagonal N (gen (N+N) a)=_
    rw [diagonal_gen]
    simp only [AlgHom.comp_apply,coproduct_atom,map_add,Algebra.TensorProduct.map_tmul,map_one]
    rfl
  exact AlgHom.congr_fun he p


-- @@ L1012-1018 verbatim
theorem drop_quotient (M N : ℕ) (h : N≤M) (p : A ℝ Bool) :
    drop M N h (TruncatedWords.quotient ∅ M p)=TruncatedWords.quotient ∅ N p := by
  have he : (drop M N h).comp (TruncatedWords.quotient ∅ M)=TruncatedWords.quotient ∅ N := by
    apply AssociativeElimination.hom_ext
    intro a
    exact drop_gen M N h a
  exact AlgHom.congr_fun he p


-- @@ L1020-1050 verbatim
theorem piece_primitive (N n : ℕ) (hn : n≤N) (u : Q ℝ (N+N)) (v : Q ℝ N)
    (hd : diagonal N u=v⊗ₜ[ℝ]1+(1:Q ℝ N)⊗ₜ[ℝ]v)
    (hc : drop (N+N) N (by omega) u=v) :
    PrimitiveWords.Primitive (piece n (normalVal N v)) := by
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (TruncatedWords.relations (∅:Set (A ℝ Bool)) (N+N)) u
  change drop (N+N) N _ (TruncatedWords.quotient ∅ (N+N) p)=v at hc
  rw [drop_quotient] at hc
  subst v
  rw [normalVal_quotient,piece_trunc N n hn]
  apply primitive_of_tensor
  rw [coproduct_piece]
  change diagonal N (TruncatedWords.quotient ∅ (N+N) p)=_ at hd
  have hh := congrArg (fun z => totalPiece n (TensorProduct.map (normalVal N) (normalVal N) z)) hd
  rw [diagonal_quotient] at hh
  have hmap : (TensorProduct.map (normalVal N) (normalVal N)).comp
      (TensorProduct.map (TruncatedWords.quotient ∅ N).toLinearMap (TruncatedWords.quotient ∅ N).toLinearMap)=
      TensorProduct.map (truncVal N) (truncVal N) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change (TensorProduct.map (normalVal N) (normalVal N))
      ((TensorProduct.map (TruncatedWords.quotient ∅ N).toLinearMap (TruncatedWords.quotient ∅ N).toLinearMap) (a⊗ₜ[ℝ]b))=_
    change normalVal N (TruncatedWords.quotient ∅ N a)⊗ₜ[ℝ]
      normalVal N (TruncatedWords.quotient ∅ N b)=truncVal N a⊗ₜ[ℝ]truncVal N b
    rw [normalVal_quotient,normalVal_quotient]
  change totalPiece n (((TensorProduct.map (normalVal N) (normalVal N)).comp _) ((coproduct (R:=ℝ) (α:=Bool)) p))=_ at hh
  rw [hmap,totalPiece_trunc N n hn] at hh
  simpa only [map_add,TensorProduct.map_tmul,normalVal_quotient,normalVal_one,
    totalPiece_left,totalPiece_right,piece_trunc N n hn] using hh


-- @@ L1052-1058 verbatim
theorem KZ_value_lie (N n : ℕ) (hn : 0<n) (hnN : n≤N) :
    ∃ q : FreeLieAlgebra ℝ Bool,q∈LieGrading.homogeneousLie (fun _ => 1) n ∧
      embed q=piece n (normalVal N (KZComparison.value N)) := by
  apply PrimitiveWords.exists_lie_of_primitive hn
  · exact project_mem _ _
  · exact piece_primitive N n hnN _ _ (KZPrimitiveValue.value_diagonal N)
      (KZCutoffComparison.value_drop (N+N) N (by omega))

-- @@ L1059-1059 verbatim
end CutoffPrimitiveExtract


-- @@ L1061-1061 verbatim
namespace OperatorLog

-- @@ L1062-1062 verbatim
open Polynomial

-- @@ L1063-1063 verbatim
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

-- @@ L1064-1064 verbatim
variable (N : ℕ) (T : Module.End ℚ V) (hT : T^(N+1)=0)

 
-- @@ L1066-1066 verbatim
include hT
 
-- @@ L1067-1072 verbatim
theorem value_taylor (a : V) (l : V →ₗ[ℚ] ℚ) (m : ℕ) :
    taylor (m:ℚ) (valuePolynomial N T a l)=valuePolynomial N T (((1+T)^m) a) l := by
  apply polynomial_ext_nat
  intro n
  rw [taylor_eval,←Nat.cast_add,value_eval,interpolate_nat N T hT,value_eval,
    interpolate_nat N T hT,pow_add,Module.End.mul_apply]

 
-- @@ L1074-1079 verbatim
theorem value_derivative (a : V) (l : V →ₗ[ℚ] ℚ) :
    (valuePolynomial N T a l).derivative=valuePolynomial N T a (l.comp (logarithm N T)) := by
  apply polynomial_ext_nat
  intro m
  rw [←taylor_coeff_one,value_taylor N T hT,value_one,value_eval,interpolate_nat N T hT]
  rfl

 
-- @@ L1081-1084 verbatim
theorem value_zero (a : V) (l : V →ₗ[ℚ] ℚ) : (valuePolynomial N T a l).coeff 0=l a := by
  rw [coeff_zero_eq_eval_zero,value_eval]
  have h := interpolate_nat N T hT 0
  simpa only [Nat.cast_zero,pow_zero,Module.End.one_apply] using congrArg (fun f : Module.End ℚ V => l (f a)) h

 
-- @@ L1086-1101 verbatim
theorem value_coeff (a : V) (l : V →ₗ[ℚ] ℚ) (k : ℕ) :
    (valuePolynomial N T a l).coeff k=(k.factorial:ℚ)⁻¹*l (((logarithm N T)^k) a) := by
  induction k generalizing l with
  | zero => simp only [value_zero N T hT,Nat.factorial_zero,Nat.cast_one,inv_one,pow_zero,Module.End.one_apply,one_mul]
  | succ k ih =>
    have hh := congrArg (fun p : ℚ[X] => p.coeff k) (value_derivative N T hT a l)
    rw [coeff_derivative,ih] at hh
    have hk : (k+1:ℚ)≠0 := by positivity
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [pow_succ',Module.End.mul_apply]
    change _= _*l (logarithm N T (((logarithm N T)^k) a))
    change (valuePolynomial N T a l).coeff (k+1)*(↑k+1:ℚ)=
      (↑k.factorial:ℚ)⁻¹*l (logarithm N T (((logarithm N T)^k) a)) at hh
    have hf : (k.factorial:ℚ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp at hh ⊢
    nlinarith [hh]

 
-- @@ L1103-1119 verbatim
theorem exp_logarithm (hL : IsNilpotent (logarithm N T)) :
    IsNilpotent.exp (logarithm N T)=1+T := by
  apply LinearMap.ext
  intro a
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro l
  rw [map_sub]
  obtain ⟨m,hm⟩ := hL
  let M := m+(valuePolynomial N T a l).natDegree+1
  have hmM : (logarithm N T)^M=0 := pow_eq_zero_of_le (by dsimp [M]; omega) hm
  rw [IsNilpotent.exp_eq_sum hmM,LinearMap.sum_apply,map_sum]
  have hp := (valuePolynomial N T a l).eval_eq_sum_range' (n:=M) (by dsimp [M]; omega) (1:ℚ)
  simp only [one_pow,mul_one,value_coeff N T hT] at hp
  have hi : interpolate N T 1=1+T := by simpa only [Nat.cast_one,pow_one] using interpolate_nat N T hT 1
  rw [value_eval,hi] at hp
  simp only [LinearMap.smul_apply,map_smul,smul_eq_mul,hp,sub_self]

-- @@ L1120-1120 verbatim
end OperatorLog


-- @@ L1122-1122 verbatim
namespace OperatorExp

-- @@ L1123-1123 verbatim
open IsNilpotent

-- @@ L1124-1124 verbatim
open scoped TensorProduct

-- @@ L1125-1128 verbatim
variable {R V W U : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module ℚ V]
  [AddCommGroup W] [Module R W] [Module ℚ W]
  [AddCommGroup U] [Module R U] [Module ℚ U]


-- @@ L1130-1135 verbatim
omit [Algebra ℚ R] in
 theorem natural (A : Module.End R V) (B : Module.End R W)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (f : V →ₗ[R] W)
    (h : ∀ v,B (f v)=f (A v)) (v : V) : exp B (f v)=f (exp A v) := by
  apply LinearMap.congr_fun (Module.End.commute_exp_left_of_commute hA hB _) v
  exact LinearMap.ext h


-- @@ L1137-1161 verbatim
omit [Algebra ℚ R] in
 theorem bilinear (A : Module.End R V) (B : Module.End R W) (C : Module.End R U)
    (hA : IsNilpotent A) (hB : IsNilpotent B) (hC : IsNilpotent C)
    (m : V →ₗ[R] W →ₗ[R] U)
    (h : ∀ v w,C (m v w)=m (A v) w+m v (B w)) (v : V) (w : W) :
    exp C (m v w)=m (exp A v) (exp B w) := by
  let X : Module.End R (V⊗[R]W) := A.rTensor W
  let Y : Module.End R (V⊗[R]W) := B.lTensor V
  have hX : IsNilpotent X := hA.map (Module.End.rTensorAlgHom R V W)
  have hY : IsNilpotent Y := hB.map (Module.End.lTensorAlgHom R W V)
  have hc : Commute X Y := by ext; simp [X,Y]
  have hXY : IsNilpotent (X+Y) := hc.isNilpotent_add hX hY
  have hm : ∀ u,C (TensorProduct.lift m u)=TensorProduct.lift m ((X+Y) u) := by
    intro u
    induction u using TensorProduct.inductionOn with

    | add u z hu hz => simp only [map_add,hu,hz]
    | tmul a b => simpa only [LinearMap.add_apply,LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul,map_add,TensorProduct.lift.tmul,X,Y] using h a b
  have hh := natural (X+Y) C hXY hC (TensorProduct.lift m) hm (v⊗ₜ[R]w)
  rw [exp_add_of_commute hc hX hY] at hh
  have hx : exp X=(exp A).rTensor W := (hA.map_exp (Module.End.rTensorAlgHom R V W)).symm
  have hy : exp Y=(exp B).lTensor V := (hB.map_exp (Module.End.lTensorAlgHom R W V)).symm
  simpa only [hx,hy,Module.End.mul_apply,LinearMap.rTensor_tmul,LinearMap.lTensor_tmul,
    TensorProduct.lift.tmul] using hh


-- @@ L1163-1173 verbatim
omit [Algebra ℚ R] in
 theorem fixed (A : Module.End R V) (hA : IsNilpotent A) {v : V} (hv : A v=0) :
    exp A v=v := by
  obtain ⟨n,hn⟩ := hA
  have hn' : A^(n+1)=0 := pow_eq_zero_of_le (by omega) hn
  rw [exp_eq_sum hn',LinearMap.sum_apply,Finset.sum_range_succ']
  have hz : ∀ i : ℕ,(A^(i+1)) v=0 := by
    intro i
    rw [_root_.pow_succ,Module.End.mul_apply,hv,map_zero]
  simp only [LinearMap.smul_apply,hz,smul_zero,Finset.sum_const_zero,pow_zero,
    Module.End.one_apply,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,zero_add]


-- @@ L1175-1175 verbatim
end OperatorExp


-- @@ L1177-1177 verbatim
namespace CategoryExp


-- @@ L1179-1179 verbatim
section

-- @@ L1180-1180 verbatim
open IsNilpotent

-- @@ L1181-1182 verbatim
variable {R A B O P : Type*} [CommRing R] [Ring A] [Algebra R A] [Module ℚ A]
  [Ring B] [Algebra R B] [Module ℚ B]


-- @@ L1184-1187 verbatim
structure Data (R A O : Type*) [CommRing R] [Ring A] [Algebra R A] where
  D : O → O → Module.End R A
  comp : ∀ p q r (a b : A),D p r (b*a)=D q r b*a+b*D p q a
  one : ∀ p,D p p 1=0

 
-- @@ L1189-1198 verbatim
def gauge (d : Module.End R A) (hd : ∀ a b,d (a*b)=d a*b+a*d b)
    (h1 : d 1=0) (h : O → A) : Data R A O where
  D p q := d+LinearMap.mulLeft R (h q)-LinearMap.mulRight R (h p)
  comp p q r a b := by
    simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply,hd]
    noncomm_ring
  one p := by
    simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply,h1,zero_add,mul_one,one_mul,sub_self]

 
-- @@ L1200-1200 verbatim
def act (g : Data R A O) (p q : O) : Module.End R A := exp (g.D p q)

 
-- @@ L1202-1205 verbatim
theorem composition (g : Data R A O) (hn : ∀ p q,IsNilpotent (g.D p q))
    (p q r : O) (a b : A) : act g p r (b*a)=act g q r b*act g p q a :=
  OperatorExp.bilinear _ _ _ (hn q r) (hn p q) (hn p r) (LinearMap.mul R A)
    (fun b a => g.comp p q r a b) b a

 
-- @@ L1207-1208 verbatim
@[simp] theorem one (g : Data R A O) (hn : ∀ p q,IsNilpotent (g.D p q)) (p : O) :
    act g p p 1=1 := OperatorExp.fixed _ (hn p p) (g.one p)

 
-- @@ L1210-1215 verbatim
theorem natural (g : Data R A O) (k : Data R B P)
    (hg : ∀ p q,IsNilpotent (g.D p q)) (hk : ∀ p q,IsNilpotent (k.D p q))
    (f : A →ₗ[R] B) (o : O → P)
    (hf : ∀ p q a,k.D (o p) (o q) (f a)=f (g.D p q a)) (p q : O) (a : A) :
    act k (o p) (o q) (f a)=f (act g p q a) :=
  OperatorExp.natural _ _ (hg p q) (hk (o p) (o q)) f (hf p q) a

 
-- @@ L1217-1219 verbatim
theorem kills (g : Data R A O) (hg : ∀ p q,IsNilpotent (g.D p q))
    (p q : O) {a : A} (ha : g.D p q a=0) : act g p q a=a :=
  OperatorExp.fixed _ (hg p q) ha

 
-- @@ L1221-1226 verbatim
def neg (g : Data R A O) : Data R A O where
  D p q := -g.D p q
  comp p q r a b := by
    change -(g.D p r (b*a))= -(g.D q r b)*a+b*(-(g.D p q a))
    rw [g.comp,neg_add,neg_mul,mul_neg]
  one p := by simp only [LinearMap.neg_apply,g.one,neg_zero]

 
-- @@ L1228-1231 verbatim
theorem inverse (g : Data R A O) (hg : ∀ p q,IsNilpotent (g.D p q))
    (p q : O) (a : A) : act (neg g) p q (act g p q a)=a := by
  have hh := exp_neg_mul_exp_self (hg p q)
  exact LinearMap.congr_fun hh a

 
-- @@ L1233-1238 verbatim
def equivalence (g : Data R A O) (hg : ∀ p q,IsNilpotent (g.D p q))
    (p q : O) : A ≃ₗ[R] A :=
  { act g p q with
    invFun := act (neg g) p q
    left_inv := inverse g hg p q
    right_inv := fun a => LinearMap.congr_fun (exp_mul_exp_neg_self (hg p q)) a }

 
-- @@ L1240-1248 verbatim
omit [Module ℚ A] in
 theorem pow_mem {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (d : Module.End R A) (hd : ∀ n a,a∈F.step n → d a∈F.step (n+1))
    (i n : ℕ) {a : A} (ha : a∈F.step n) : (d^i) a∈F.step (n+i) := by
  induction i with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.add_zero] using ha
  | succ i ih =>
    rw [_root_.pow_succ',Module.End.mul_apply]
    simpa only [Nat.add_assoc] using hd (n+i) _ ih

 
-- @@ L1250-1255 verbatim
omit [Module ℚ A] in
 theorem nilpotent {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (d : Module.End R A) (hd : ∀ n a,a∈F.step n → d a∈F.step (n+1)) : IsNilpotent d := by
  refine ⟨N+1,LinearMap.ext (fun a => ?_)⟩
  have hh := pow_mem F d hd (N+1) 0 (a:=a) (by rw [F.initial]; trivial)
  simpa only [Nat.zero_add,F.terminal,Submodule.mem_bot,LinearMap.zero_apply] using hh

 
-- @@ L1257-1265 verbatim
theorem preserves [Algebra ℚ R] [IsScalarTower ℚ R A] {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (d : Module.End R A) (hd : ∀ n a,a∈F.step n → d a∈F.step (n+1))
    (n : ℕ) {a : A} (ha : a∈F.step n) : exp d a∈F.step n := by
  obtain ⟨m,hm⟩ := nilpotent F d hd
  rw [exp_eq_sum hm,LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i hi
  change (↑i.factorial : ℚ)⁻¹ • (d^i) a∈F.step n
  exact ((F.step n).restrictScalars ℚ).smul_mem _ (F.decreasing (Nat.le_add_right n i) (pow_mem F d hd i n ha))


-- @@ L1267-1267 verbatim
end


-- @@ L1269-1269 verbatim
open IsNilpotent

-- @@ L1270-1271 verbatim
variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V]
  [Module R V] [Module ℚ V] [IsScalarTower ℚ R V]

-- @@ L1272-1274 verbatim
variable {N : ℕ} (F : FilteredComparison.Filtration R V N)
  (d : Module.End R V) (k : ℕ)
  (hd : ∀ n a,a∈F.step n → d a∈F.step (n+k))


-- @@ L1276-1276 verbatim
include hd

-- @@ L1277-1283 verbatim
omit [Algebra ℚ R] [Module ℚ V] [IsScalarTower ℚ R V] in
 theorem pow_mem_shift (i n : ℕ) {a : V} (ha : a∈F.step n) : (d^i) a∈F.step (n+i*k) := by
  induction i with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.zero_mul,Nat.add_zero] using ha
  | succ i ih =>
    rw [_root_.pow_succ',Module.End.mul_apply]
    simpa only [Nat.succ_mul,Nat.add_assoc] using hd (n+i*k) _ ih

 
-- @@ L1285-1305 verbatim
theorem first_order (hk : 0<k) (n : ℕ) {a : V} (ha : a∈F.step n) :
    exp d a-a-d a∈F.step (n+2*k) := by
  have hn : IsNilpotent d := by
    refine ⟨N+1,LinearMap.ext (fun a => ?_)⟩
    have hp := pow_mem_shift F d k hd (N+1) 0 (a:=a) (by rw [F.initial]; trivial)
    have hp' := F.decreasing (show N+1≤0+(N+1)*k by simpa using Nat.le_mul_of_pos_right (N+1) hk) hp
    simpa only [F.terminal,Submodule.mem_bot,LinearMap.zero_apply] using hp'
  obtain ⟨s,hs⟩ := hn
  have hs' : d^(2+s)=0 := pow_eq_zero_of_le (by omega) hs
  rw [exp_eq_sum hs',LinearMap.sum_apply,Finset.sum_range_add]
  have htwo : (∑ i∈Finset.range 2,((↑i.factorial : ℚ)⁻¹ • d^i) a)=a+d a := by
    simp [Finset.sum_range_succ]
  rw [htwo]
  have hsum : (∑ i∈Finset.range s,((↑(2+i).factorial : ℚ)⁻¹ • d^(2+i)) a)∈F.step (n+2*k) := by
    apply Submodule.sum_mem
    intro i hi
    change (↑(2+i).factorial : ℚ)⁻¹ • (d^(2+i)) a∈_
    apply ((F.step (n+2*k)).restrictScalars ℚ).smul_mem
    apply F.decreasing _ (pow_mem_shift F d k hd (2+i) n ha)
    exact Nat.add_le_add_left (Nat.mul_le_mul_right k (by omega)) n
  convert hsum using 1; abel

 
-- @@ L1307-1315 verbatim
theorem unit_leading (hk : 0<k) {a u : V} (_hu : u∈F.step 0) (ha : a-u∈F.step 1) :
    exp d a-a-d u∈F.step (k+1) := by
  have ha0 : a∈F.step 0 := by rw [F.initial]; trivial
  have h₁ := first_order F d k hd hk 0 ha0
  have h₂ := hd 1 (a-u) ha
  rw [map_sub] at h₂
  have h₁' : exp d a-a-d a∈F.step (k+1) := F.decreasing (by omega) h₁
  have h₂' : d a-d u∈F.step (k+1) := by simpa only [Nat.add_comm 1 k] using h₂
  convert (F.step (k+1)).add_mem h₁' h₂' using 1; abel

 
-- @@ L1317-1320 verbatim
theorem normalizes (hk : 0<k) {a b u : V} (hu : u∈F.step 0) (ha : a-u∈F.step 1)
    (hfirst : b-a-d u∈F.step (k+1)) : b-exp d a∈F.step (k+1) := by
  have hh := unit_leading F d k hd hk hu ha
  convert (F.step (k+1)).sub_mem hfirst hh using 1; abel


-- @@ L1322-1322 verbatim
end CategoryExp


-- @@ L1324-1324 verbatim
namespace RealOperatorLog

-- @@ L1325-1325 verbatim
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℚ V] [IsScalarTower ℚ ℝ V]
 
-- @@ L1326-1327 verbatim
def logarithm (N : ℕ) (T : Module.End ℝ V) : Module.End ℝ V :=
  ∑ k∈Finset.range N,((-1:ℚ)^k/(k+1)) • T^(k+1)
 
-- @@ L1328-1332 verbatim
theorem pow_restrict (T : Module.End ℝ V) (k : ℕ) (a : V) :
    ((T.restrictScalars ℚ)^k) a=(T^k) a := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pow_succ',Module.End.mul_apply,ih]; rfl
 
-- @@ L1333-1338 verbatim
theorem restrict (N : ℕ) (T : Module.End ℝ V) :
    (logarithm N T).restrictScalars ℚ=OperatorLog.logarithm N (T.restrictScalars ℚ) := by
  apply LinearMap.ext
  intro a
  change logarithm N T a=OperatorLog.logarithm N (T.restrictScalars ℚ) a
  simp only [OperatorLog.logarithm_eq,logarithm,LinearMap.sum_apply,LinearMap.smul_apply,pow_restrict]
 
-- @@ L1339-1349 verbatim
theorem raises {M : ℕ} (F : FilteredComparison.Filtration ℝ V M)
    (N : ℕ) (T : Module.End ℝ V) (hT : ∀ m a,a∈F.step m → T a∈F.step (m+1))
    (m : ℕ) (a : V) (ha : a∈F.step m) : logarithm N T a∈F.step (m+1) := by
  rw [logarithm,LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro k hk
  change ((-1:ℚ)^k/(k+1)) • (T^(k+1)) a∈_
  apply ((F.step (m+1)).restrictScalars ℚ).smul_mem
  have hp := CategoryExp.pow_mem_shift F T 1 hT (k+1) m ha
  simp only [Nat.mul_one] at hp
  exact F.decreasing (by omega) hp
 
-- @@ L1350-1356 verbatim
theorem nilpotent {M : ℕ} (F : FilteredComparison.Filtration ℝ V M)
    (N : ℕ) (T : Module.End ℝ V) (hT : ∀ m a,a∈F.step m → T a∈F.step (m+1)) :
    IsNilpotent (logarithm N T) := by
  refine ⟨M+1,LinearMap.ext (fun a => ?_)⟩
  have hh := CategoryExp.pow_mem_shift F (logarithm N T) 1 (raises F N T hT) (M+1) 0
    (a:=a) (by rw [F.initial]; trivial)
  simpa only [Nat.mul_one,Nat.zero_add,F.terminal,Submodule.mem_bot,LinearMap.zero_apply] using hh
 
-- @@ L1357-1366 verbatim
theorem exp_restrict (T : Module.End ℝ V) (hT : IsNilpotent T) (a : V) :
    IsNilpotent.exp (T.restrictScalars ℚ) a=IsNilpotent.exp T a := by
  obtain ⟨k,hk⟩ := hT
  have hkr : (T.restrictScalars ℚ)^k=0 := by
    apply LinearMap.ext
    intro u
    rw [pow_restrict,hk]
    rfl
  rw [IsNilpotent.exp_eq_sum hk,IsNilpotent.exp_eq_sum hkr,LinearMap.sum_apply,LinearMap.sum_apply]
  simp only [LinearMap.smul_apply,pow_restrict]
 
-- @@ L1367-1383 verbatim
theorem exp_logarithm (N : ℕ) (T : Module.End ℝ V) (hT : T^(N+1)=0)
    (hL : IsNilpotent (logarithm N T)) : IsNilpotent.exp (logarithm N T)=1+T := by
  have hTr : (T.restrictScalars ℚ)^(N+1)=0 := by
    apply LinearMap.ext
    intro a
    rw [pow_restrict,hT]
    rfl
  have hLr : IsNilpotent (OperatorLog.logarithm N (T.restrictScalars ℚ)) := by
    rw [←restrict]
    obtain ⟨k,hk⟩ := hL
    refine ⟨k,LinearMap.ext (fun a => ?_)⟩
    rw [pow_restrict,hk]
    rfl
  apply LinearMap.ext
  intro a
  rw [←exp_restrict _ hL,restrict,OperatorLog.exp_logarithm N _ hTr hLr]
  rfl

-- @@ L1384-1384 verbatim
end RealOperatorLog


-- @@ L1386-1386 verbatim
namespace TruncatedDerivation

-- @@ L1387-1387 verbatim
open AssociativeElimination WordGrading TruncatedWords

-- @@ L1388-1388 verbatim
variable {R α : Type*} [CommRing R]

-- @@ L1389-1389 verbatim
variable (P : Set (A R α)) (N : ℕ)

-- @@ L1390-1390 verbatim
local notation "Q" => TruncatedWords.Q P N

-- @@ L1391-1391 verbatim
local notation "F" => filtration P N

 
-- @@ L1393-1393 verbatim
def gen (a : α) : Q := quotient P N (atom a)
 
-- @@ L1394-1395 verbatim
theorem gen_mem (a : α) : gen P N a∈F 1 :=
  ⟨atom a,word_mem (FreeMonoid.of a) (by simp [wt]),rfl⟩

 
-- @@ L1397-1398 verbatim
def jet (v : α → Q) : A R α →ₐ[R] TrivSqZeroExt Q Q :=
  AssociativeElimination.lift (R:=R) (fun a => (⟨gen P N a,v a⟩ : TrivSqZeroExt Q Q))

 
-- @@ L1400-1402 verbatim
@[simp] theorem jet_atom (v : α → Q) (a : α) : jet P N v (atom a)=⟨gen P N a,v a⟩ := by
  unfold jet
  exact AssociativeElimination.lift_atom (R:=R) (B:=TrivSqZeroExt Q Q) (fun a => (⟨gen P N a,v a⟩ : TrivSqZeroExt Q Q)) a

 
-- @@ L1404-1411 verbatim
theorem fst_jet (v : α → Q) (p : A R α) : (jet P N v p).fst=quotient P N p := by
  have he : (TrivSqZeroExt.fstHom R Q Q).comp (jet P N v)=quotient P N := by
    apply hom_ext
    intro a
    change (jet P N v (atom a)).fst=quotient P N (atom a)
    rw [jet_atom]
    rfl
  exact AlgHom.congr_fun he p

 
-- @@ L1413-1414 verbatim
def raw (v : α → Q) : A R α →ₗ[R] Q :=
  ((TrivSqZeroExt.sndHom Q Q).restrictScalars R).comp (jet P N v).toLinearMap

 
-- @@ L1416-1419 verbatim
@[simp] theorem raw_atom (v : α → Q) (a : α) : raw P N v (atom a)=v a := by
  change (jet P N v (atom a)).snd=v a
  rw [jet_atom]
  rfl
 
-- @@ L1420-1422 verbatim
@[simp] theorem raw_one (v : α → Q) : raw P N v 1=0 := by
  change (jet P N v 1).snd=0
  rw [map_one,TrivSqZeroExt.snd_one]
 
-- @@ L1423-1427 verbatim
theorem raw_mul (v : α → Q) (p q : A R α) :
    raw P N v (p*q)=quotient P N p*raw P N v q+raw P N v p*quotient P N q := by
  change (jet P N v (p*q)).snd=_
  rw [map_mul,TrivSqZeroExt.snd_mul,fst_jet,fst_jet]
  rfl

 
-- @@ L1429-1440 verbatim
theorem raw_word_mem (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1)) (w : FreeMonoid α) :
    raw P N v (word w)∈F (degree wt w+k) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,raw_one]; exact Submodule.zero_mem _
  | of_mul a w ih =>
    rw [word_mul,word_of,raw_mul,raw_atom,degree_mul,degree_of]
    change _∈F (1+degree wt w+k)
    apply Submodule.add_mem
    · simpa only [Nat.add_assoc,wt,gen] using filtration_mul P N 1 _ (gen_mem P N a) ih
    · have hm : quotient P N (word w)∈F (degree wt w) := ⟨word w,word_mem w le_rfl,rfl⟩
      simpa only [show k+1+degree wt w=1+degree wt w+k by omega] using
        filtration_mul P N (k+1) _ (hv a) hm

 
-- @@ L1442-1445 verbatim
theorem raw_mem (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    {n : ℕ} {p : A R α} (hp : p∈above wt n) : raw P N v p∈F (n+k) :=
  map_space (raw P N v) _ (fun w hw =>
    filtration_antitone P N (Nat.add_le_add_right hw k) (raw_word_mem P N k v hv w)) hp

 
-- @@ L1447-1461 verbatim
def descend (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) : Q →ₐ[R] TrivSqZeroExt Q Q :=
  RingQuot.liftAlgHom R ⟨jet P N v,by
    rintro p q ⟨rfl,hp⟩
    rw [map_zero]
    apply TrivSqZeroExt.ext
    · rw [fst_jet]
      rcases hp with hp|hp
      · exact quotient_relation P N hp
      · exact quotient_above P N hp
    · change raw P N v p=0
      rcases hp with hp|hp
      · exact hP p hp
      · have hh := filtration_antitone P N (Nat.le_add_right (N+1) k) (raw_mem P N k v hv hp)
        simpa only [filtration_terminal,Submodule.mem_bot] using hh⟩

 
-- @@ L1463-1466 verbatim
@[simp] theorem descend_quotient (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) (p : A R α) :
    descend P N k v hv hP (quotient P N p)=jet P N v p := by
  simp only [descend,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]

 
-- @@ L1468-1471 verbatim
theorem descend_fst (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) (p : Q) : (descend P N k v hv hP p).fst=p := by
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations P N) p
  rw [←quotient,descend_quotient,fst_jet]

 
-- @@ L1473-1475 verbatim
def derivation (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) : Module.End R Q :=
  ((TrivSqZeroExt.sndHom Q Q).restrictScalars R).comp (descend P N k v hv hP).toLinearMap

 
-- @@ L1477-1482 verbatim
@[simp] theorem derivation_quotient (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) (p : A R α) :
    derivation P N k v hv hP (quotient P N p)=raw P N v p := by
  change (descend P N k v hv hP (quotient P N p)).snd=_
  rw [descend_quotient]
  rfl

 
-- @@ L1484-1486 verbatim
@[simp] theorem derivation_one (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) : derivation P N k v hv hP 1=0 := by
  rw [←map_one (quotient P N),derivation_quotient,raw_one]

 
-- @@ L1488-1493 verbatim
theorem derivation_mul (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) (p q : Q) :
    derivation P N k v hv hP (p*q)=derivation P N k v hv hP p*q+p*derivation P N k v hv hP q := by
  change (descend P N k v hv hP (p*q)).snd=_
  rw [map_mul,TrivSqZeroExt.snd_mul,descend_fst,descend_fst]
  exact add_comm _ _

 
-- @@ L1495-1501 verbatim
theorem derivation_mem (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) {n : ℕ} {p : Q} (hp : p∈F n) :
    derivation P N k v hv hP p∈F (n+k) := by
  obtain ⟨p,hp,rfl⟩ := hp
  change derivation P N k v hv hP (quotient P N p)∈_
  rw [derivation_quotient]
  exact raw_mem P N k v hv hp


-- @@ L1503-1503 verbatim
end TruncatedDerivation


-- @@ L1505-1505 verbatim
namespace CutoffCategory

-- @@ L1506-1506 verbatim
open AssociativeElimination WordGrading TruncatedWords

-- @@ L1507-1507 verbatim
variable {α O : Type*} (P : Set (A ℝ α)) (N : ℕ)

 
-- @@ L1509-1513 verbatim
theorem initial : (TruncatedWords.filtration P N) 0=⊤ := by
  apply top_unique
  intro a _
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (relations P N) a
  exact ⟨p,TruncatedFree.all_ge_zero p,rfl⟩

 
-- @@ L1515-1519 verbatim
def filtration : FilteredComparison.Filtration ℝ (TruncatedWords.Q P N) N where
  step := (TruncatedWords.filtration P N)
  decreasing := filtration_antitone P N
  initial := initial P N
  terminal := filtration_terminal P N

 
-- @@ L1521-1522 verbatim
variable (d : Module.End ℝ (TruncatedWords.Q P N)) (hd : ∀ a b,d (a*b)=d a*b+a*d b) (h1 : d 1=0)
  (h : O → (TruncatedWords.Q P N))

 
-- @@ L1524-1524 verbatim
abbrev data : CategoryExp.Data ℝ (TruncatedWords.Q P N) O := CategoryExp.gauge d hd h1 h

 
-- @@ L1526-1526 verbatim
theorem apply (p q : O) (a : (TruncatedWords.Q P N)) : (data P N d hd h1 h).D p q a=d a+h q*a-a*h p := rfl

 
-- @@ L1528-1529 verbatim
theorem one (p q : O) : (data P N d hd h1 h).D p q 1=h q-h p := by
  rw [apply,h1,zero_add,mul_one,one_mul]

 
-- @@ L1531-1538 verbatim
theorem raises (k : ℕ) (hdF : ∀ n a,a∈(TruncatedWords.filtration P N) n → d a∈(TruncatedWords.filtration P N) (n+k)) (hhF : ∀ p,h p∈(TruncatedWords.filtration P N) k)
    (p q : O) (n : ℕ) (a : (TruncatedWords.Q P N)) (ha : a∈(TruncatedWords.filtration P N) n) : (data P N d hd h1 h).D p q a∈(TruncatedWords.filtration P N) (n+k) := by
  rw [apply]
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · exact hdF n a ha
    · simpa only [Nat.add_comm k n] using filtration_mul P N k n (hhF q) ha
  · exact filtration_mul P N n k ha (hhF p)

 
-- @@ L1540-1544 verbatim
theorem nilpotent (k : ℕ) (hk : 0<k) (hdF : ∀ n a,a∈(TruncatedWords.filtration P N) n → d a∈(TruncatedWords.filtration P N) (n+k)) (hhF : ∀ p,h p∈(TruncatedWords.filtration P N) k)
    (p q : O) : IsNilpotent ((data P N d hd h1 h).D p q) := by
  apply CategoryExp.nilpotent (filtration P N)
  intro n a ha
  exact filtration_antitone P N (show n+1≤n+k by omega) (raises P N d hd h1 h k hdF hhF p q n a ha)

 
-- @@ L1546-1551 verbatim
theorem leading (k : ℕ) (hk : 0<k) (hdF : ∀ n a,a∈(TruncatedWords.filtration P N) n → d a∈(TruncatedWords.filtration P N) (n+k)) (hhF : ∀ p,h p∈(TruncatedWords.filtration P N) k)
    (p q : O) {a : (TruncatedWords.Q P N)} (ha : a-1∈(TruncatedWords.filtration P N) 1) :
    CategoryExp.act (data P N d hd h1 h) p q a-a-(h q-h p)∈(TruncatedWords.filtration P N) (k+1) := by
  rw [←one P N d hd h1 h p q]
  exact CategoryExp.unit_leading (filtration P N) _ k (raises P N d hd h1 h k hdF hhF p q)
    hk (filtration_one P N) ha


-- @@ L1553-1553 verbatim
end CutoffCategory


-- @@ L1555-1555 verbatim
namespace KZRealLog

-- @@ L1556-1556 verbatim
open KZComparison CutoffDepth CutoffKZ
 
-- @@ L1557-1558 verbatim
def S (N : ℕ) (p q : Bool) : Module.End ℝ (Q ℝ N) :=
  ((LinearMap.mulLeft ℝ (frames N q:Q ℝ N)).comp (LinearMap.mulRight ℝ ((frames N p)⁻¹:(Q ℝ N)ˣ))).comp (theta N).toLinearMap
 
-- @@ L1559-1562 verbatim
theorem S_apply (N : ℕ) (p q : Bool) (a : Q ℝ N) :
    S N p q a=(frames N q:Q ℝ N)*theta N a*((frames N p)⁻¹:(Q ℝ N)ˣ) := by
  simp only [S,LinearMap.comp_apply,LinearMap.mulLeft_apply,LinearMap.mulRight_apply,mul_assoc]
  rfl
 
-- @@ L1563-1567 verbatim
theorem S_restrict (N : ℕ) (p q : Bool) : (S N p q).restrictScalars ℚ=(category N).S p q := by
  apply LinearMap.ext
  intro a
  rw [show (S N p q).restrictScalars ℚ a=S N p q a from rfl,S_apply]
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,AlgEquiv.restrictScalars_apply]
 
-- @@ L1568-1569 verbatim
def D (N : ℕ) (p q : Bool) : Module.End ℝ (Q ℝ N) :=
  RealOperatorLog.logarithm (N+1) (S N p q-1)
 
-- @@ L1570-1580 verbatim
theorem D_restrict (N : ℕ) (p q : Bool) :
    (D N p q).restrictScalars ℚ=LogCategory.delta (category N) p q := by
  rw [D,RealOperatorLog.restrict]
  have hh : (S N p q-1).restrictScalars ℚ=(category N).S p q-1 := by
    apply LinearMap.ext
    intro a
    change S N p q a-a=(category N).S p q a-a
    rw [←S_restrict]
    rfl
  rw [hh]
  rfl
 
-- @@ L1581-1583 verbatim
theorem D_apply (N : ℕ) (p q : Bool) (a : Q ℝ N) :
    D N p q a=LogCategory.delta (category N) p q a :=
  LinearMap.congr_fun (D_restrict N p q) a
 
-- @@ L1584-1587 verbatim
def data (N : ℕ) : CategoryExp.Data ℝ (Q ℝ N) Bool where
  D := D N
  comp p q r a b := by simp only [D_apply]; exact LogCategory.delta_comp _ p q r a b
  one p := by rw [D_apply,LogCategory.delta_one_loop]
 
-- @@ L1588-1588 verbatim
theorem value (N : ℕ) : D N false true 1=KZComparison.value N := D_apply N false true 1
 
-- @@ L1589-1593 verbatim
theorem frames_weight (N : ℕ) (p : Bool) :
    (frames N p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  cases p
  · simp [frames]
  · exact ConjugateComparison.unitArrow_normalized N _ _ _ _
 
-- @@ L1594-1602 verbatim
theorem S_raises (N : ℕ) (p q : Bool) (m : ℕ) (a : Q ℝ N)
    (ha : a∈TruncatedWords.filtration ∅ N m) : S N p q a-a∈TruncatedWords.filtration ∅ N (m+1) := by
  have h0 : ((TruncatedWords.filtration (∅:Set (AssociativeElimination.A ℝ Bool)) N 0).restrictScalars ℚ)=⊤ := by
    rw [CutoffCategory.initial]
    rfl
  exact GaugeAutomorphism.raises ((theta N).restrictScalars ℚ) (frames N)
    (fun m => (TruncatedWords.filtration ∅ N m).restrictScalars ℚ)
    (TruncatedWords.filtration_antitone ∅ N) h0 (TruncatedWords.filtration_mul ∅ N)
    (ConjugateComparison.theta_raises N _ _ _ _) (frames_weight N) p q m a ha
 
-- @@ L1603-1605 verbatim
theorem raises (N : ℕ) (p q : Bool) (m : ℕ) (a : Q ℝ N)
    (ha : a∈TruncatedWords.filtration ∅ N m) : D N p q a∈TruncatedWords.filtration ∅ N (m+1) :=
  RealOperatorLog.raises (CutoffCategory.filtration ∅ N) (N+1) (S N p q-1) (S_raises N p q) m a ha
 
-- @@ L1606-1607 verbatim
theorem nilpotent (N : ℕ) (p q : Bool) : IsNilpotent (D N p q) :=
  CategoryExp.nilpotent (CutoffCategory.filtration ∅ N) (D N p q) (raises N p q)
 
-- @@ L1608-1622 verbatim
theorem exp_eq (N : ℕ) (p q : Bool) : IsNilpotent.exp (D N p q)=S N p q := by
  have hn : (S N p q-1)^(N+1+1)=0 := by
    apply LinearMap.ext
    intro a
    have h := LinearMap.congr_fun ((category N).nilpotent p q) a
    have hr : (S N p q-1).restrictScalars ℚ=(category N).S p q-1 := by
      apply LinearMap.ext
      intro a
      change S N p q a-a=(category N).S p q a-a
      rw [←S_restrict]
      rfl
    rw [←hr,RealOperatorLog.pow_restrict] at h
    exact h
  rw [D,RealOperatorLog.exp_logarithm (N+1) _ hn (nilpotent N p q)]
  abel
 
-- @@ L1623-1626 verbatim
theorem exp_comparison (N : ℕ) :
    IsNilpotent.exp (D N false true) (positive N:Q ℝ N)=(negative N:Q ℝ N) := by
  rw [exp_eq,S_apply]
  simpa only [frames,inv_one,Units.val_one,mul_one] using exact_comparison N
 
-- @@ L1627-1633 verbatim
theorem loop_x (N : ℕ) : D N false false (X N)=0 := by
  rw [D_apply]
  apply OperatorLog.logarithm_fixed
  change (category N).S false false (X N)-X N=0
  rw [←S_restrict]
  change S N false false (X N)-X N=0
  simp only [S_apply,frames,Units.val_one,inv_one,mul_one,one_mul,theta_x,sub_self]
 
-- @@ L1634-1640 verbatim
theorem loop_y (N : ℕ) : D N true true (Y N)=0 := by
  rw [D_apply]
  apply OperatorLog.logarithm_fixed
  change (category N).S true true (Y N)-Y N=0
  rw [←S_restrict]
  change S N true true (Y N)-Y N=0
  simp only [S_apply,frames,theta_y,mul_assoc,Units.mul_inv_cancel_left,Units.mul_inv,mul_one,sub_self]
 
-- @@ L1641-1649 verbatim
theorem loop_false_y (N : ℕ) :
    D N false false (Y N)=Y N*KZComparison.value N-KZComparison.value N*Y N := by
  have hh := LogCategory.delta_formula (category N) false true true (Y N)
  rw [←D_apply,loop_y] at hh
  rw [←D_apply N false false] at hh
  change 0=D N false false (Y N)+KZComparison.value N*Y N-Y N*KZComparison.value N at hh
  apply eq_sub_iff_add_eq.mpr
  have hh' : D N false false (Y N)+KZComparison.value N*Y N=Y N*KZComparison.value N := sub_eq_zero.mp hh.symm
  exact hh'
 
-- @@ L1650-1653 verbatim
theorem edge_formula (N : ℕ) (a : Q ℝ N) :
    D N false true a=D N false false a+KZComparison.value N*a := by
  rw [D_apply,LogCategory.delta_formula (category N) false,LogCategory.delta_one_loop,mul_zero,sub_zero,←D_apply]
  rfl

-- @@ L1654-1654 verbatim
end KZRealLog


-- @@ L1656-1656 verbatim
end DeligneDrinfeld


-- @@ L1658-1658 verbatim
end


-- @@ L1660-1660 verbatim
end OAI
