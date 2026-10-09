import OAI.Computability.RationalHitting.OutputAdapter


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace RationalHitting.TMTime.Link

-- @@ L6-6 verbatim
open Turing

-- @@ L7-7 verbatim
variable {Γ Λ Δ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Δ]

-- @@ L8-8 verbatim
local instance sumInhabited : Inhabited (Sum Λ Δ) := ⟨Sum.inl default⟩


-- @@ L10-10 verbatim
def left (a : TM0.Cfg Γ Λ) : TM0.Cfg Γ (Sum Λ Δ) := ⟨Sum.inl a.q,a.Tape⟩

-- @@ L11-11 verbatim
def right (a : TM0.Cfg Γ Δ) : TM0.Cfg Γ (Sum Λ Δ) := ⟨Sum.inr a.q,a.Tape⟩


-- @@ L13-17 verbatim
def machine (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ) : TM0.Machine Γ (Sum Λ Δ)
  | .inl q,a => match F q a with
    | none => some (.inr default,.write a)
    | some (r,s) => some (.inl r,s)
  | .inr q,a => (G q a).map (fun (r,s) => (.inr r,s))


-- @@ L19-30 verbatim
lemma step_left (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ)
    {a b : TM0.Cfg Γ Λ} (h : TM0.step F a=some b) :
    TM0.step (machine F G) (left a)=some (left b) := by
  rcases a with ⟨q,T⟩
  simp only [TM0.step] at h
  cases he : F q T.head with
  | none => simp [he] at h
  | some qr =>
    rcases qr with ⟨r,s⟩
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst b
    cases s <;> simp [TM0.step,machine,left,he]


-- @@ L32-36 verbatim
lemma switch (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ)
    {a : TM0.Cfg Γ Λ} (h : TM0.step F a=none) :
    TM0.step (machine F G) (left a)=some (right (⟨default,a.Tape⟩ : TM0.Cfg Γ Δ)) := by
  have he : F a.q a.Tape.head=none := Option.map_eq_none_iff.mp h
  simp [TM0.step,machine,left,right,he]


-- @@ L38-42 verbatim
lemma step_right (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ) (a : TM0.Cfg Γ Δ) :
    TM0.step (machine F G) (right a)=(TM0.step G a).map right := by
  rcases a with ⟨q,T⟩
  simp only [TM0.step,machine,right,Option.map_map]
  congr 1


-- @@ L44-52 verbatim
lemma run_left (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ)
    (t : ℕ) {a b : TM0.Cfg Γ Λ} (h : exec (TM0.step F) t a=some b) :
    exec (TM0.step (machine F G)) t (left a)=some (left b) := by
  induction t generalizing a with
  | zero => simpa only [exec_zero,Option.some.injEq] using congrArg (fun x => left (Δ:=Δ) x) (Option.some.inj h)
  | succ t ih =>
    obtain ⟨c,hc,hr⟩ := Option.bind_eq_some_iff.mp h
    simp only [exec,step_left F G hc,Option.bind_some]
    exact ih hr


-- @@ L54-61 verbatim
lemma run_right (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ)
    (t : ℕ) (a : TM0.Cfg Γ Δ) :
    exec (TM0.step (machine F G)) t (right a)=(exec (TM0.step G) t a).map right := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    simp only [exec,step_right]
    cases TM0.step G a <;> simp [ih]


-- @@ L63-88 verbatim
/-- Splice two halting finite transducers with exactly one glue step. The
intermediate output is the literal tape required by the second input. -/
theorem finite_sequence [Fintype Λ] [Fintype Δ]
    (F : TM0.Machine Γ Λ) (G : TM0.Machine Γ Δ) :
    ∃ (m : ℕ) (H : TM0.Machine Γ (Fin (m+1))),
      ∀ (w v : List Γ) (t u : ℕ) (a : TM0.Cfg Γ Λ) (b : TM0.Cfg Γ Δ),
        exec (TM0.step F) t (TM0.init w)=some a → TM0.step F a=none →
        a.Tape=Tape.mk₁ v → exec (TM0.step G) u (TM0.init v)=some b → TM0.step G b=none →
        ∃ c, exec (TM0.step H) (t+1+u) (TM0.init w)=some c ∧ TM0.step H c=none ∧ c.Tape=b.Tape := by
  classical
  let S : Finset (Sum Λ Δ) := Finset.univ
  have hs : TM0.Supports (machine F G) (S : Set (Sum Λ Δ)) := by
    constructor
    · simp [S]
    · intro q hq a r s hr
      simp [S]
  obtain ⟨m,H,hH⟩ := FiniteStates.finite_machine (machine F G) S hs
  refine ⟨m,H,?_⟩
  intro w v t u a b ha hh ht hb hh'
  have h1 : exec (TM0.step (machine F G)) t (TM0.init w)=some (left a) := run_left F G t ha
  have h2 : exec (TM0.step (machine F G)) 1 (left a)=some (right (TM0.init v)) := by
    simp only [exec,switch F G hh,Option.bind_some,TM0.init,ht]
  have h3 : exec (TM0.step (machine F G)) u (right (TM0.init v))=some (right b) := by
    rw [run_right,hb,Option.map_some]
  have hr := exec_trans (exec_trans h1 h2) h3
  exact hH w (t+1+u) (right b) hr (by rw [step_right,hh',Option.map_none])


-- @@ L90-90 verbatim
end RationalHitting.TMTime.Link


-- @@ L92-92 verbatim
namespace RationalHitting.TMTime.BinaryLift

-- @@ L93-93 verbatim
open Turing

-- @@ L94-94 verbatim
abbrev A := Fin 4

-- @@ L95-95 verbatim
def bit (b : Bool) : A := if b then 1 else 0

-- @@ L96-96 verbatim
def bitMap : PointedMap Bool A := ⟨bit,rfl⟩

-- @@ L97-97 verbatim
@[simp] lemma bit_read (b : Bool) : (bit b==1)=b := by cases b <;> decide

-- @@ L98-98 verbatim
variable {Λ : Type*} [Inhabited Λ]

-- @@ L99-101 verbatim
def stmt : TM0.Stmt Bool → TM0.Stmt A
  | .move d => .move d
  | .write b => .write (bit b)

-- @@ L102-103 verbatim
def machine (F : TM0.Machine Bool Λ) : TM0.Machine A Λ :=
  fun q a => (F q (a==1)).map (fun (r,s) => (r,stmt s))

-- @@ L104-104 verbatim
def cfg (a : TM0.Cfg Bool Λ) : TM0.Cfg A Λ := ⟨a.q,a.Tape.map bitMap⟩

-- @@ L105-111 verbatim
lemma step (F : TM0.Machine Bool Λ) (a : TM0.Cfg Bool Λ) :
    TM0.step (machine F) (cfg a)=(TM0.step F a).map cfg := by
  rcases a with ⟨q,T⟩
  simp only [cfg,machine,TM0.step,Tape.map_fst,bitMap,bit_read,Option.map_map]
  congr 1
  funext ⟨r,s⟩
  cases s <;> simp only [Function.comp_apply,stmt,cfg,Tape.map_move,Tape.map_write,bitMap]

-- @@ L112-118 verbatim
lemma run (F : TM0.Machine Bool Λ) (t : ℕ) (a : TM0.Cfg Bool Λ) :
    exec (TM0.step (machine F)) t (cfg a)=(exec (TM0.step F) t a).map cfg := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    simp only [exec,step]
    cases TM0.step F a <;> simp [ih]


-- @@ L120-128 verbatim
lemma run_init (F : TM0.Machine Bool Λ) (w : List Bool) (t : ℕ) (a : TM0.Cfg Bool Λ)
    (hr : exec (TM0.step F) t (TM0.init w)=some a) (hh : TM0.step F a=none) :
    exec (TM0.step (machine F)) t (TM0.init (w.map bit))=some (cfg a) ∧
      TM0.step (machine F) (cfg a)=none := by
  have hi : cfg (Λ:=Λ) (TM0.init w)=TM0.init (w.map bit) := by
    simp only [cfg,TM0.init,Tape.map_mk₁,bitMap]
  constructor
  · rw [←hi,run,hr,Option.map_some]
  · rw [step,hh,Option.map_none]

-- @@ L129-129 verbatim
end RationalHitting.TMTime.BinaryLift


-- @@ L131-131 verbatim
namespace RationalHitting.TMTime.Alphabet

-- @@ L132-132 verbatim
open Turing

-- @@ L133-136 verbatim
lemma tape_init {Γ : Type*} [Inhabited Γ] {b : ℕ}
    (enc : Γ → List.Vector Bool b) (h0 : enc default=List.Vector.replicate b false) (w : List Γ) :
    TM1to1.trTape h0 (Tape.mk₁ w)=Tape.mk₁ (w.flatMap (fun a => (enc a).toList)) := by
  exact congrArg TM1.Cfg.Tape (compiled_init (Λ:=Unit) (σ:=Unit) enc h0 w)

-- @@ L137-137 verbatim
end RationalHitting.TMTime.Alphabet


-- @@ L139-139 verbatim
namespace RationalHitting.StackLanguage.Compiler

-- @@ L140-140 verbatim
open Turing RationalHitting.TMTime

-- @@ L141-141 verbatim
variable {K : Type} [DecidableEq K] [Fintype K]


-- @@ L143-188 verbatim
/-- End-to-end, finite-state, Fin4 one-tape compilation. Input and output are
literal 1/2 digit strings, NOT different encodings hidden by an interface. The
stack program is a single fixed finite syntax tree. Final scratch must be empty;
the designated output stack has reversed output order, as explicitly stated. -/
theorem raw_compilation (p : Program K) (ki ko : K) :
    ∃ (m : ℕ) (G : TM0.Machine (Fin 4) (Fin (m+1))) (C : ℕ), 0<C ∧
      ∀ (w xs : List Bool) (t : ℕ), w≠[] →
        Eval p (Function.update (fun _ => []) ki w)
          (Function.update (fun _ => []) ko xs.reverse) t →
        ∃ u≤C*(w.length+t+xs.length+3)^2, ∃ a,
          exec (TM0.step G) u (TM0.init (w.map InputAdapter.raw))=some a ∧
          TM0.step G a=none ∧ a.Tape=Tape.mk₁ (xs.map OutputAdapter.raw) := by
  classical
  obtain ⟨b,enc,dec,h0,hd,m₁,F,B,hB,hF⟩ := binary_compilation p
  obtain ⟨m₀,I,A,hA,hI⟩ := InputAdapter.raw_stack_input ki b enc
  obtain ⟨m₂,O,D,hD,hO⟩ := OutputAdapter.raw_stack_output ko enc dec h0 hd
  obtain ⟨m₃,J,hJ⟩ := Link.finite_sequence I (BinaryLift.machine F)
  obtain ⟨m₄,H,hH⟩ := Link.finite_sequence J O
  refine ⟨m₄,H,A+B+D+2,by omega,?_⟩
  intro w xs t hw he
  obtain ⟨i,hi,a,ha,hha,hta⟩ := hI w hw
  obtain ⟨j,hj,c,hc,hhc,e,htr,htc⟩ := hF ki w (Function.update (fun _ => []) ko xs.reverse) t he
  obtain ⟨hlift,hhlift⟩ := BinaryLift.run_init F _ j c hc hhc
  have hcle : c.Tape=Tape.mk₁ ((TM2to1.trInit ko xs.reverse).flatMap (fun z => (enc z).toList)) := by
    rw [htc,StackTape.clean ko xs.reverse htr,Alphabet.tape_init]
  have hcl : (BinaryLift.cfg c).Tape=Tape.mk₁
      (((TM2to1.trInit ko xs.reverse).flatMap (fun z => (enc z).toList)).map InputAdapter.bit) := by
    simp only [BinaryLift.cfg,hcle,Tape.map_mk₁]
    rfl
  obtain ⟨a₃,ha₃,hh₃,ht₃⟩ := hJ (w.map InputAdapter.raw)
    (((TM2to1.trInit ki w).flatMap (fun z => (enc z).toList)).map InputAdapter.bit)
    i j a (BinaryLift.cfg c) ha hha hta (by rw [show InputAdapter.bit = BinaryLift.bit from rfl]; exact hlift) hhlift
  have hxt : a₃.Tape=Tape.mk₁
      (((TM2to1.trInit ko xs.reverse).flatMap (fun z => (enc z).toList)).map InputAdapter.bit) := ht₃.trans hcl
  obtain ⟨k,hk,a₂,ha₂,hh₂,ht₂⟩ := hO xs
  obtain ⟨a₄,ha₄,hh₄,ht₄⟩ := hH (w.map InputAdapter.raw)
    (((TM2to1.trInit ko xs.reverse).flatMap (fun z => (enc z).toList)).map InputAdapter.bit)
    (i+1+j) k a₃ a₂ ha₃ hh₃ hxt ha₂ hh₂
  refine ⟨i+1+j+1+k,?_,a₄,ha₄,hh₄,ht₄.trans ht₂⟩
  let R := w.length+t+xs.length+3
  have hi' : i≤A*R^2 := hi.trans (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega : w.length+1≤R) 2))
  have hj' : j≤B*R^2 := hj.trans (Nat.mul_le_mul_left B (Nat.pow_le_pow_left (by omega : w.length+t+3≤R) 2))
  have hk' : k≤D*R^2 := hk.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left (by omega : xs.length+1≤R) 2))
  have hR : 1≤R^2 := one_le_pow₀ (by dsimp [R]; omega)
  change i+1+j+1+k≤(A+B+D+2)*R^2
  nlinarith only [hi',hj',hk',hR]


-- @@ L190-190 verbatim
end RationalHitting.StackLanguage.Compiler



-- @@ L193-193 verbatim
namespace RationalHitting.ExecutableGenerator

-- @@ L194-194 verbatim
open Turing StackLanguage TMTime


-- @@ L196-200 verbatim
/-- A fixed finite stack program with literal unary input and exact
canonical output, bounded by a fixed polynomial in the input length. -/

def unaryWord (n s : ℕ) : List Bool :=
  List.replicate n true ++ [false] ++ List.replicate s true


-- @@ L202-207 verbatim
def StackImplementation : Prop :=
  ∃ (r : ℕ) (p : Program (Fin (r+1))) (ki ko : Fin (r+1)) (C k : ℕ),
    0<C ∧ 0<k ∧ ∀ n s : ℕ, 1 ≤ n → 1 ≤ s →
      ∃ t≤C*(n+s+1)^k,
        Eval p (Function.update (fun _ => []) ki (unaryWord n s))
          (Function.update (fun _ => []) ko (encoded n s).reverse) t


-- @@ L209-213 verbatim
lemma run_eq_exec {m : ℕ} (G : Machine m) (t : ℕ) (a : Config m) :
    run G t a = exec (TM0.step G) t a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih => simp only [run,exec,ih]


-- @@ L215-216 verbatim
lemma unaryWord_raw (n s : ℕ) : (unaryWord n s).map TMTime.InputAdapter.raw = unaryInput n s := by
  simp [unaryWord,unaryInput,TMTime.InputAdapter.raw]


-- @@ L218-219 verbatim
lemma encoded_raw (n s : ℕ) : (encoded n s).map TMTime.OutputAdapter.raw =
    (encodeOutput (list n s)).map tapeBit := rfl


-- @@ L221-223 verbatim
lemma compilation_sum_bound (x t y R C A : ℕ) (hx : x≤R)
    (ht : t≤C*R) (hy : y≤A*R) (hR : 1≤R) : x+t+y+3≤(C+A+4)*R := by
  nlinarith only [hx, ht, hy, hR]


-- @@ L225-227 verbatim
lemma compilation_square_bound (D C A x E : ℕ) :
    D*((C+A+4)*x^E)^2 = D*(C+A+4)^2*x^(2*E) := by
  rw [Nat.mul_pow, ←pow_mul, Nat.mul_comm E 2, Nat.mul_assoc]


-- @@ L229-266 verbatim
/-- The raw compiler preserves literal input/output and gives a fixed
finite alphabet and state space with a polynomial transition bound. -/

theorem implementation_of_stack (h : StackImplementation) : Implementation := by
  obtain ⟨r,p,ki,ko,C,k,hC,hk,hp⟩ := h
  obtain ⟨m,G,D,hD,hG⟩ := Compiler.raw_compilation p ki ko
  let A := PolynomialBounds.outputConstant
  let E := k+104
  refine ⟨m,G,D*(C+A+4)^2,2*E,by positivity,by dsimp [E]; omega,?_⟩
  intro n s hn hs
  obtain ⟨t,ht,he⟩ := hp n s hn hs
  have hw : unaryWord n s≠[] := by
    intro heq
    have hh := congrArg List.length heq
    simp [unaryWord] at hh
  obtain ⟨u,hu,a,ha,hhalt,hout⟩ := hG (unaryWord n s) (encoded n s) t hw he
  have hlen : (unaryWord n s).length=n+s+1 := by simp [unaryWord]; omega
  have hsize : (encoded n s).length≤A*(n+s+1)^104 := (exact_output n s hn hs).2.1
  have hm : 1≤n+s+1 := by omega
  have hmE : n+s+1≤(n+s+1)^E := by
    exact (le_refl (n+s+1)).trans (by
      have hh := Nat.pow_le_pow_right hm (by dsimp [E]; omega : 1≤E)
      simpa using hh)
  have ht' : t≤C*(n+s+1)^E := ht.trans (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right hm (by dsimp [E]; omega)))
  have ho' : (encoded n s).length≤A*(n+s+1)^E := hsize.trans (Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right hm (by dsimp [E]; omega)))
  have h1 : 1≤(n+s+1)^E := one_le_pow₀ hm
  have htotal : (unaryWord n s).length+t+(encoded n s).length+3 ≤
      (C+A+4)*(n+s+1)^E := by
    rw [hlen]
    exact compilation_sum_bound _ _ _ _ _ _ hmE ht' ho' h1
  refine ⟨u, hu.trans (le_trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left htotal 2))
    (le_of_eq (compilation_square_bound D C A (n+s+1) E))), a, ?_, hhalt, ?_⟩
  · rw [run_eq_exec,←unaryWord_raw]
    exact ha
  · rw [hout, encoded_raw]
    exact Turing.Tape.mk'_right₀ _ _


-- @@ L268-268 verbatim
end RationalHitting.ExecutableGenerator


-- @@ L270-270 verbatim
end OAI
