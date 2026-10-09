import OAI.Computability.RationalHitting.RationalBinary


-- @@ L3-3 verbatim
namespace OAI



-- @@ L6-6 verbatim
namespace RationalHitting


-- @@ L8-15 verbatim
/-- A concrete syntax for nonnegative polynomial bounds. This is only used to
bound actual stack transitions, never as an additional machine instruction. -/
inductive TimeBound where
  | const : ℕ → TimeBound
  | variable : TimeBound
  | add : TimeBound → TimeBound → TimeBound
  | mul : TimeBound → TimeBound → TimeBound
  deriving DecidableEq


-- @@ L17-17 verbatim
namespace TimeBound

-- @@ L18-18 verbatim
instance {n : ℕ} : OfNat TimeBound n := ⟨const n⟩

-- @@ L19-19 verbatim
instance : Add TimeBound := ⟨add⟩

-- @@ L20-20 verbatim
instance : Mul TimeBound := ⟨mul⟩


-- @@ L22-26 verbatim
def eval : TimeBound → ℕ → ℕ
  | .const c, _ => c
  | .variable, n => n
  | .add a b, n => a.eval n + b.eval n
  | .mul a b, n => a.eval n * b.eval n


-- @@ L28-28 verbatim
@[simp] lemma eval_const (a n : ℕ) : (const a).eval n = a := rfl

-- @@ L29-29 verbatim
@[simp] lemma eval_variable (n : ℕ) : variable.eval n = n := rfl

-- @@ L30-30 verbatim
@[simp] lemma eval_add (a b : TimeBound) (n : ℕ) : (a+b).eval n=a.eval n+b.eval n := rfl

-- @@ L31-31 verbatim
@[simp] lemma eval_mul (a b : TimeBound) (n : ℕ) : (a*b).eval n=a.eval n*b.eval n := rfl

-- @@ L32-32 verbatim
@[simp] lemma eval_numeral (a n : ℕ) : (ofNat(a) : TimeBound).eval n = a := rfl


-- @@ L34-39 verbatim
lemma monotone (p : TimeBound) : Monotone p.eval := by
  induction p with
  | const c => exact monotone_const
  | «variable» => exact monotone_id
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact fun a b h => Nat.mul_le_mul (hp h) (hq h)


-- @@ L41-46 verbatim
/-- Substitution is again a polynomial with nonnegative coefficients. -/
def comp : TimeBound → TimeBound → TimeBound
  | .const c, _ => .const c
  | .variable, q => q
  | .add a b, q => a.comp q + b.comp q
  | .mul a b, q => a.comp q * b.comp q


-- @@ L48-50 verbatim
@[simp] lemma eval_comp (p q : TimeBound) (n : ℕ) :
    (p.comp q).eval n = p.eval (q.eval n) := by
  induction p <;> simp_all [comp,eval]


-- @@ L52-79 verbatim
/-- These certificates imply an ordinary fixed positive-coefficient, positive-
degree power bound. This prevents any hidden superpolynomial time allowance. -/
theorem growth (p : TimeBound) :
    ∃ C k : ℕ, 0<C ∧ 0<k ∧ ∀ n : ℕ, 1≤n → p.eval n≤C*n^k := by
  induction p with
  | const c =>
    refine ⟨c+1,1,by omega,by omega,?_⟩
    intro n hn
    simp only [eval,pow_one]
    nlinarith only [hn]
  | «variable» => exact ⟨1,1,by omega,by omega,by intro n _; simp [eval]⟩
  | add p q hp hq =>
    obtain ⟨C,k,hC,hk,hp⟩ := hp
    obtain ⟨D,l,hD,hl,hq⟩ := hq
    refine ⟨C+D,k+l,by omega,by omega,?_⟩
    intro n hn
    have hp' := (hp n hn).trans (Nat.mul_le_mul_left C
      (Nat.pow_le_pow_right hn (Nat.le_add_right k l)))
    have hq' := (hq n hn).trans (Nat.mul_le_mul_left D
      (Nat.pow_le_pow_right hn (Nat.le_add_left l k)))
    simpa only [eval,Nat.add_mul] using Nat.add_le_add hp' hq'
  | mul p q hp hq =>
    obtain ⟨C,k,hC,hk,hp⟩ := hp
    obtain ⟨D,l,hD,hl,hq⟩ := hq
    refine ⟨C*D,k+l,Nat.mul_pos hC hD,by omega,?_⟩
    intro n hn
    calc p.eval n*q.eval n ≤ (C*n^k)*(D*n^l) := Nat.mul_le_mul (hp n hn) (hq n hn)
         _ = (C*D)*n^(k+l) := by rw [pow_add]; ac_rfl


-- @@ L81-81 verbatim
end TimeBound

-- @@ L82-82 verbatim
end RationalHitting



-- @@ L85-86 verbatim
/-! Compositional finite-stack implementation. All the constants introduced
here describe actual finite programs, not arithmetic-operation oracles. -/

-- @@ L87-87 verbatim
namespace RationalHitting.StackLanguage

-- @@ L88-88 verbatim
open Function


-- @@ L90-90 verbatim
variable {K L : Type} [DecidableEq K] [DecidableEq L]


-- @@ L92-92 verbatim
def single (k : K) (w : List Bool) : Store K := update (fun _ => []) k w


-- @@ L94-95 verbatim
@[simp] lemma single_self (k : K) (w : List Bool) : single k w k = w := by
  simp [single]

-- @@ L96-97 verbatim
@[simp] lemma single_other {k j : K} (w : List Bool) (h : j≠k) : single k w j = [] := by
  simp [single,h]

-- @@ L98-99 verbatim
@[simp] lemma single_nil (k : K) : single k [] = fun _ => [] := by
  funext j; by_cases h : j=k <;> simp [single,h]


-- @@ L101-108 verbatim
lemma extend_single (f : K → L) (hf : Injective f) (k : K) (w : List Bool) :
    extend f (single k w) (fun _ => []) = single (f k) w := by
  rw [single, extend_update_store f hf]
  congr 1
  funext l
  by_cases h : ∃ a, f a=l
  · obtain ⟨a,rfl⟩ := h; simp [hf.extend_apply]
  · simp [extend_apply' _ _ _ h]


-- @@ L110-113 verbatim
lemma Eval.rename_single {p : Program K} {i o : K} {x y : List Bool} {t : ℕ}
    (h : Eval p (single i x) (single o y) t) (f : K → L) (hf : Injective f) :
    Eval (p.rename f) (single (f i) x) (single (f o) y) t := by
  simpa only [extend_single f hf] using h.rename f hf (fun _ => [])


-- @@ L115-128 verbatim
/-- A quantitative implementation, with completely clean stack input and
output. Both execution and result size are polynomially bounded. -/
structure Procedure {A B : Type} (ca : A → List Bool) (cb : B → List Bool) (f : A → B) where
  Registers : Type
  finite : Fintype Registers
  decEq : DecidableEq Registers
  input : Registers
  output : Registers
  program : @Program Registers
  bound : TimeBound
  correct : ∀ a, ∃ t ≤ bound.eval ((ca a).length+1),
    @Eval Registers decEq program (@single Registers decEq input (ca a))
      (@single Registers decEq output (cb (f a))) t
  size : ∀ a, (cb (f a)).length ≤ bound.eval ((ca a).length+1)


-- @@ L130-130 verbatim
attribute [instance] Procedure.finite Procedure.decEq


-- @@ L132-134 verbatim
/-- A compositional polynomial-time feasibility predicate. -/
def Feasible {A B : Type} (ca : A → List Bool) (cb : B → List Bool) (f : A → B) : Prop :=
  Nonempty (Procedure ca cb f)



-- @@ L137-138 verbatim
/-- Order-preserving transfer, implemented using two stack reversals. -/
def move (a b tmp : K) : Program K := .seq (reverse a tmp) (reverse tmp b)


-- @@ L140-154 verbatim
lemma eval_move {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (s : Store K) (hb : s b=[]) (ht : s tmp=[]) :
    Eval (move a b tmp) s (update (update s a []) b (s a)) (4*(s a).length+3) := by
  have h₁ := eval_reverse hat s
  have h₂ := eval_reverse hbt.symm (update (update s a []) tmp ((s a).reverse++s tmp))
  have hh := Eval.seq h₁ h₂
  have he : update (update (update (update s a []) tmp ((s a).reverse++s tmp)) tmp []) b
      (((update (update s a []) tmp ((s a).reverse++s tmp)) tmp).reverse ++
        (update (update s a []) tmp ((s a).reverse++s tmp)) b) =
      update (update s a []) b (s a) := by
    funext j
    by_cases hja : j=a <;> by_cases hjb : j=b <;> by_cases hjt : j=tmp <;>
      simp_all
  rw [he] at hh
  convert hh using 1 <;> simp [move,ht]; omega


-- @@ L156-162 verbatim
lemma Eval.move_single {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (w : List Bool) :
    Eval (move a b tmp) (single a w) (single b w) (4*w.length+3) := by
  have h := eval_move hab hat hbt (single a w) (by simp [hab.symm]) (by simp [hat.symm])
  have he : update (update (single a w) a []) b w=single b w := by
    simp [single,update_idem]
  simpa only [single_self,he] using h


-- @@ L164-181 verbatim
/-- Run in an embedded register bank, preserving every register outside it. -/
lemma Eval.runAt {p : Program K} {i o : K} {x y : List Bool} {t : ℕ}
    (h : Eval p (single i x) (single o y) t) (f : K → L) (hf : Injective f)
    (s : Store L) (hs : ∀ k, s (f k)=single i x k) :
    Eval (p.rename f) s (update (update s (f i) []) (f o) y) t := by
  have hi : (fun k => s (f k))=single i x := funext hs
  have he : extend f (fun _ => []) s=update s (f i) [] := by
    funext l
    by_cases hl : ∃ k, f k=l
    · obtain ⟨k,rfl⟩ := hl
      rw [hf.extend_apply]
      by_cases hk : k=i
      · subst k; simp
      · simp [update_of_ne (fun hh => hk (hf hh)),hs,single,hk]
    · have hn : l≠f i := fun hh => hl ⟨i,hh.symm⟩
      simp [extend_apply' _ _ _ hl,hn]
  have hh := eval_rename_from f hf s (hi.symm ▸ h)
  simpa only [single,extend_update_store f hf,he] using hh


-- @@ L183-183 verbatim
namespace Procedure

-- @@ L184-185 verbatim
variable {A B C : Type} {ca : A → List Bool} {cb : B → List Bool} {cc : C → List Bool}
  {f : A → B} {g : B → C}


-- @@ L187-197 verbatim
/-- Identity has no operation of unbounded cost. -/
def identity (ca : A → List Bool) : Procedure ca ca id where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .skip
  bound := TimeBound.variable+1
  correct a := ⟨1,by simp,Eval.skip _⟩
  size a := by simp; omega


-- @@ L199-225 verbatim
/-- Composition uses disjoint scratch banks and an actual order-preserving
stack transfer. -/
def comp (q : Procedure cb cc g) (p : Procedure ca cb f) : Procedure ca cc (g ∘ f) where
  Registers := p.Registers ⊕ (q.Registers ⊕ Unit)
  finite := inferInstance
  decEq := inferInstance
  input := Sum.inl p.input
  output := Sum.inr (Sum.inl q.output)
  program := .seq (p.program.rename Sum.inl)
    (.seq (move (Sum.inl p.output) (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ())))
      (q.program.rename (Sum.inr ∘ Sum.inl)))
  bound := 5*p.bound + q.bound.comp (p.bound+1) + 5
  correct a := by
    obtain ⟨t,ht,he⟩ := p.correct a
    obtain ⟨u,hu,hq⟩ := q.correct (f a)
    refine ⟨1+t+(1+(4*(cb (f a)).length+3)+u),?_,?_⟩
    · have hsize := p.size a
      have hu' := hu.trans (q.bound.monotone (Nat.add_le_add_right hsize 1))
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_comp] at *
      omega
    · exact Eval.seq (he.rename_single Sum.inl Sum.inl_injective)
        (Eval.seq (Eval.move_single (by simp) (by simp) (by simp) _)
          (hq.rename_single (Sum.inr ∘ Sum.inl) (Sum.inr_injective.comp Sum.inl_injective)))
  size a := by
    have hs := (q.size (f a)).trans (q.bound.monotone (Nat.add_le_add_right (p.size a) 1))
    simp only [comp_apply,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_comp]
    omega


-- @@ L227-244 verbatim
/-- Reinterpret equal input/output words, with no additional computation. -/
def recode {A' B' : Type} (p : Procedure ca cb f) (ca' : A' → List Bool)
    (cb' : B' → List Bool) (f' : A' → B') (e : A' → A)
    (hi : ∀ a, ca (e a)=ca' a) (ho : ∀ a, cb (f (e a))=cb' (f' a)) :
    Procedure ca' cb' f' where
  Registers := p.Registers
  finite := p.finite
  decEq := p.decEq
  input := p.input
  output := p.output
  program := p.program
  bound := p.bound
  correct a := by
    obtain ⟨t,ht,he⟩ := p.correct (e a)
    rw [hi,ho] at he
    rw [hi] at ht
    exact ⟨t,ht,he⟩
  size a := by simpa only [hi,ho] using p.size (e a)



-- @@ L247-247 verbatim
end Procedure

-- @@ L248-248 verbatim
end RationalHitting.StackLanguage


-- @@ L250-250 verbatim
end OAI
