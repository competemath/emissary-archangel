import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace ExactFourier

-- @@ L6-6 verbatim
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))

-- @@ L7-7 verbatim
end ExactFourier


-- @@ L9-42 verbatim
/-!
# Exact scalar and index RAM used for the algorithm

Finite, first-order, expression/program syntax. Arrays below are random-access arrays of
registers (an array-valued register holds its address). An expression building an array uses
a fresh array; `sow` builds by a loop of writes instead of a loop supplying consecutive
entries. Programs have their usual sequential stack evaluation. Evaluation here records work
(including stack, index and array work), the high water mark on produced/logically looped-over
integer values (addresses *within* arrays are integers too), the value, and the side condition
required along the executed path (in particular no division by zero). The charged units of
work are constant time; as usual constant rescalings between ways to charge a fixed number
of scalar or address operations are immaterial.

Enough address bits must be provided BOTH for the integer high water mark (and inputs), AND
for the work bound together with input size, as will be required in the theorem. Indeed we
use the particularly simple RAM convention where temporaries aren't reused: one work unit can
leave at most a constant number of cells (stack, pairs or array cells); whenever many array
entries are made their number is charged. So a constant number of words of those sizes also
suffices for arena addresses. Nothing charges constant work for changing an already published
array to a different array as a whole. Register and stack layouts, and the convention whether
registers hold pairs or addresses of pairs, only have constant factors (the program is fixed).

Scalar and data field registers are separated. Tests and loop/request sizes are on nonnegative
integer registers. There is no instruction for an arbitrary complex constant. A supplied
specified root will be an input. Divisions are on prepared scalars; valid runs require every
such denominator nonzero; the side condition is *not* a test performed by the algorithm.
The Bool mode on the syntax allows or prohibits general products (two-input convolution
versus the transform); even when allowed we use separate register kinds before and after
the bilinear products.

Definitions are mathematical operation-count semantics, not a model of running Lean code.
E.g. a function on Fin n represents the n cells of a random-access array, not a function
closure at runtime.
-/


-- @@ L44-44 verbatim
namespace PowerSaving


-- @@ L46-46 verbatim
universe u v


-- @@ L48-48 verbatim
variable {α : Type u} {β : Type v}


-- @@ L50-53 verbatim
/-- Register arrays. -/
structure Tape (α : Type u) where
  len : ℕ
  pos : Fin len → α


-- @@ L55-55 verbatim
namespace Tape


-- @@ L57-57 verbatim
def empty (α : Type u) : Tape α := ⟨0, Fin.elim0⟩


-- @@ L59-60 verbatim
/-- Materialized array. -/
def tab (n : ℕ) (f : ℕ → α) : Tape α := ⟨n, fun i => f i.val⟩


-- @@ L62-64 verbatim
/-- Read with fixed out of bounds default. -/
def look (v : Tape α) (i : ℕ) (z : α) : α :=
  if h : i < v.len then v.pos ⟨i,h⟩ else z


-- @@ L66-67 verbatim
@[simp] theorem look_of_lt (v : Tape α) (z : α) {i} (h : i < v.len) :
    v.look i z = v.pos ⟨i,h⟩ := by simp [look, h]


-- @@ L69-70 verbatim
@[simp] theorem look_of_le (v : Tape α) (z : α) {i} (h : v.len ≤ i) :
    v.look i z = z := by simp [look, Nat.not_lt.mpr h]


-- @@ L72-75 verbatim
/-- Semantics of a write into fresh storage; out-of-range writes are ignored. Only used
  during construction, never a whole-tape functional update instruction. -/
def set (v : Tape α) (i : ℕ) (x : α) : Tape α :=
  ⟨v.len, fun j => if j.val = i then x else v.pos j⟩


-- @@ L77-82 verbatim
def sow (len count : ℕ) (z : α) (f : ℕ → ℕ × α) : Tape α :=
  iter count
where
  iter : ℕ → Tape α
  | 0 => tab len (fun _ => z)
  | i+1 => (iter i).set (f i).1 (f i).2


-- @@ L84-84 verbatim
def map (f : α → β) (v : Tape α) : Tape β := ⟨v.len, fun i => f (v.pos i)⟩


-- @@ L86-86 verbatim
end Tape


-- @@ L88-88 verbatim
namespace RAM


-- @@ L90-94 verbatim
inductive Paint
  | scalar
  | left
  | right
  | both


-- @@ L96-100 verbatim
inductive Ty
  | w
  | c : Paint → Ty
  | p : Ty → Ty → Ty
  | a : Ty → Ty


-- @@ L102-102 verbatim
open Ty


-- @@ L104-104 verbatim
abbrev sc := c .scalar


-- @@ L106-110 verbatim
@[reducible] def Ty.T : Ty → Type
  | w => ℕ
  | c _ => ℂ
  | p s b => s.T × b.T
  | a b => Tape b.T


-- @@ L112-116 verbatim
noncomputable def Ty.blank : (t : Ty) → t.T
  | w => 0
  | c _ => 0
  | p s t => (s.blank, t.blank)
  | a b => Tape.empty b.T


-- @@ L118-125 verbatim
/-- One basic work unit below pays for O(1) primitive RAM operations; includes loop and
  stack overhead. `peak` tracks produced/needed integer quantities beyond inputs
  (total allocation for stack and array bases is covered separately by work). -/
structure Bill (α : Type u) where
  val : α
  work : ℕ
  peak : ℕ
  valid : Prop


-- @@ L127-127 verbatim
namespace Bill


-- @@ L129-131 verbatim
/-- Charge some work and optionally a new word bound. -/
def pay (b : Bill α) (n : ℕ) (m : ℕ) : Bill α :=
  ⟨b.val, b.work+n, max b.peak m, b.valid⟩


-- @@ L133-136 verbatim
/-- Both computations are evaluated. -/
def pass (b : Bill α) (f : α → Bill β) : Bill β :=
  let d := f b.val
  ⟨d.val, b.work+d.work, max b.peak d.peak, b.valid ∧ d.valid⟩


-- @@ L138-138 verbatim
def one (x : α) : Bill α := ⟨x,1,0,True⟩

-- @@ L139-139 verbatim
def word (x : ℕ) : Bill ℕ := ⟨x,1,x,True⟩


-- @@ L141-144 verbatim
/-- Execute f 0 through f (n-1), iterating an accumulator. -/
def steps (init : α) (f : ℕ → α → Bill α) : ℕ → Bill α
  | 0 => Bill.one init
  | i+1 => ((steps init f i).pass (f i)).pay 1 (i+1)


-- @@ L146-149 verbatim
/-- Build Tape len by count writes (initialized with a blank z). -/
def sow (len count : ℕ) (z : α) (f : ℕ → Bill (ℕ × α)) : Bill (Tape α) :=
  (steps (Tape.tab len (fun _ => z))
    (fun i v => (f i).pass (fun s => one (v.set s.1 s.2))) count).pay (1+len) len


-- @@ L151-153 verbatim
/-- Build Tape len. As for sow we can first allocate then perform writes. -/
def tab (len : ℕ) (z : α) (f : ℕ → Bill α) : Bill (Tape α) :=
  sow len len z (fun i => (f i).pass (fun y => one (i,y)))


-- @@ L155-155 verbatim
end Bill


-- @@ L157-158 verbatim
inductive NOp
  | add | sub | mul | div | mod | lt  -- truncated subtraction; compare returns 1 or 0


-- @@ L160-175 verbatim
inductive Atom (allow : Bool) : Ty → Ty → Type
  | lit {a} (n : ℕ) : Atom allow a w
  | int (f : NOp) : Atom allow (p w w) w
  | cz (t) {a} : Atom allow a (c t)
  | cone {a} : Atom allow a sc
  | add (t) : Atom allow (p (c t) (c t)) (c t)
  | sub (t) : Atom allow (p (c t) (c t)) (c t)
  | scale (t) : Atom allow (p sc (c t)) (c t)
  | inv : Atom allow sc sc
  | cross (h : allow = true) :
      Atom allow (p (c .left) (c .right)) (c .both)
  | id {a} : Atom allow a a
  | fst {a b} : Atom allow (p a b) a
  | snd {a b} : Atom allow (p a b) b
  | len {s} : Atom allow (a s) w
  | look {s} : Atom allow (p (a s) w) s


-- @@ L177-183 verbatim
noncomputable def NOp.run : NOp → (ℕ × ℕ) → Bill ℕ
  | .add, (i,j) => Bill.word (i+j)
  | .sub, (i,j) => Bill.word (i-j)
  | .mul, (i,j) => Bill.word (i*j)
  | .div, (i,j) => Bill.word (i/j) -- includes usual guard (returns zero)
  | .mod, (i,j) => Bill.word (i%j) -- like Lean: returns i if j=0
  | .lt, (i,j) => Bill.word (if i<j then 1 else 0)


-- @@ L185-199 verbatim
noncomputable def Atom.run {allow a b} : Atom allow a b → a.T → Bill b.T
  | .lit n, _ => Bill.word n
  | .int f, x => f.run x
  | .cz _, _ => Bill.one 0
  | .cone, _ => Bill.one 1
  | .add _, (x,y) => Bill.one (x+y)
  | .sub _, (x,y) => Bill.one (x-y)
  | .scale _, (x,y) => Bill.one (x*y)
  | .inv, x => ⟨x⁻¹,1,0,x ≠ 0⟩
  | .cross _, (x,y) => Bill.one (x*y)
  | .id, x => Bill.one x
  | .fst, x => Bill.one x.1
  | .snd, x => Bill.one x.2
  | .len, x => Bill.word x.len
  | @Atom.look _ s, (x,i) => Bill.one (x.look i s.blank)


-- @@ L201-201 verbatim
abbrev Port := Option (Ty × Ty)


-- @@ L203-220 verbatim
/-- `call` is internal for bounded recursion; a program has Port = none. `loop`, `tab`
  and `sow` retain the input to access parameters in the body. `descend` sets up bounded
  recursion, reading fuel and initial argument. -/
inductive Code (allow : Bool) : Port → Ty → Ty → Type
  | atom {r s t} (op : Atom allow s t) : Code allow r s t
  | comp {r s t u} (f : Code allow r s t) (g : Code allow r t u) : Code allow r s u
  | fork {r s t u} (f : Code allow r s t) (g : Code allow r s u) : Code allow r s (p t u)
  | ifz {r s t} (q : Code allow r s w) (f g : Code allow r s t) : Code allow r s t
  | loop {r s t} (n : Code allow r s w) (init : Code allow r s t)
      (body : Code allow r (p s (p w t)) t) : Code allow r s t
  | tab {r s t} (n : Code allow r s w)
      (body : Code allow r (p s w) t) : Code allow r s (a t)
  | sow {r s t} (n count : Code allow r s w)
      (body : Code allow r (p s w) (p w t)) : Code allow r s (a t)
  | importClosed {r s t} (f : Code allow none s t) : Code allow r s t
  | call {s t} : Code allow (some (s,t)) s t
  | descend {r s t} (base : Code allow none s t)
      (body : Code allow (some (s,t)) s t) : Code allow r (p w s) t


-- @@ L222-224 verbatim
@[reducible] def Handler : Port → Type
  | none => Unit
  | some (s,t) => s.T → Bill t.T


-- @@ L226-229 verbatim
def depthRun (base : α → Bill β)
    (step : (α → Bill β) → (α → Bill β)) : ℕ → α → Bill β
  | 0, x => (base x).pay 1 0
  | n+1, x => (step (depthRun base step n) x).pay 1 (n+1)


-- @@ L231-249 verbatim
noncomputable def Code.run {allow r s t} : Code allow r s t → Handler r → s.T → Bill t.T
  | .atom op, _, x => op.run x
  | .comp f g, h, x => ((f.run h x).pass (g.run h)).pay 1 0
  | .fork f g, h, x => (f.run h x).pass (fun y => (g.run h x).pass (fun z => Bill.one (y,z)))
  | .ifz q f g, h, x => ((q.run h x).pass (fun y =>
      if (y : ℕ) = 0 then f.run h x else g.run h x)).pay 1 0
  | .loop n init body, h, x =>
      ((n.run h x).pass (fun l => (init.run h x).pass (fun y =>
        Bill.steps y (fun i z => body.run h (x,(i,z))) l))).pay 1 0
  | @Code.tab _ _ _ t n body, h, x =>
      ((n.run h x).pass (fun l =>
        Bill.tab l t.blank (fun i => body.run h (x,i)))).pay 1 0
  | @Code.sow _ _ _ t n count body, h, x =>
      ((n.run h x).pass (fun l => (count.run h x).pass (fun k =>
        Bill.sow l k t.blank (fun i => body.run h (x,i))))).pay 1 0
  | .importClosed f, _, x => (f.run () x).pay 1 0
  | .call, h, x => (h x).pay 1 0
  | .descend base step, _, (k,x) =>
      (depthRun (base.run ()) (step.run) k x).pay 1 k


-- @@ L251-251 verbatim
abbrev Prog (allow : Bool) (s t : Ty) := Code allow none s t


-- @@ L253-254 verbatim
noncomputable abbrev run {allow s t} (f : Prog allow s t) (x : s.T) : Bill t.T :=
  f.run () x


-- @@ L256-256 verbatim
end RAM

-- @@ L257-257 verbatim
end PowerSaving



-- @@ L260-260 verbatim
namespace PowerSaving

-- @@ L261-261 verbatim
noncomputable section

-- @@ L262-262 verbatim
open RAM RAM.Ty Filter Asymptotics


-- @@ L264-264 verbatim
def paperM : ℝ := 1000000

-- @@ L265-265 verbatim
def paperW : ℝ := ((2 : ℕ) : ℝ) ^ (71:ℕ)

-- @@ L266-266 verbatim
def paperDelta : ℝ := 6871402692000000

-- @@ L267-267 verbatim
def paperMultiplier := paperM - paperDelta / paperW

-- @@ L268-268 verbatim
def theta : ℝ := Real.log paperMultiplier / Real.log paperM

-- @@ L269-269 verbatim
def decimalExponent : ℝ := 1 - 1/(10^(13:ℕ))


-- @@ L271-272 verbatim
def paperTime (n : ℕ) : ℝ :=
  (n:ℝ) * (Real.log (n:ℝ)) ^ theta * (Real.log (Real.log (n:ℝ))) ^ (4-theta)


-- @@ L274-274 verbatim
def decimalTime (n : ℕ) : ℝ := (n:ℝ) * (Real.log (n:ℝ)) ^ decimalExponent


-- @@ L276-276 verbatim
def nlogn (n : ℕ) : ℝ := (n:ℝ) * Real.log (n:ℝ)


-- @@ L278-278 verbatim
abbrev root := ExactFourier.zeta


-- @@ L280-280 verbatim
abbrev Vec (n : ℕ) := Fin n → ℂ


-- @@ L282-283 verbatim
def dft (n : ℕ) (x : Vec n) : Vec n :=
  fun j => ∑ k, (root n) ^ (j.val*k.val) * x k


-- @@ L285-286 verbatim
def conv (n : ℕ) (x y : Vec n) : Vec (2*n-1) :=
  fun k => ∑ r : Fin n, ∑ s : Fin n, if r.val+s.val=k.val then x r*y s else 0


-- @@ L288-288 verbatim
abbrev dftInKind := p w (p sc (a (c Paint.left)))

-- @@ L289-289 verbatim
abbrev dftOutKind := a (c Paint.left)

-- @@ L290-290 verbatim
abbrev convInKind := p w (p sc (p (a (c Paint.left)) (a (c Paint.right))))

-- @@ L291-291 verbatim
abbrev convOutKind := a (c Paint.both)


-- @@ L293-303 verbatim
def DFTProgram (order : Prog false w w) (solve : Prog false dftInKind dftOutKind)
    (W : ℕ → ℕ) : Prop :=
  ∃ cBound : ℕ, ∀ n : ℕ, 0<n →
    let cap := (n+2)^cBound
    let d := run order n
    W n + 10*(n+2) ≤ cap ∧ d.peak ≤ cap ∧ d.valid ∧
    0 < d.val ∧ d.val < 1024*n^3 ∧ d.val ≤ cap ∧
    ∀ x : Vec n,
      let result := run solve (n, root d.val, (⟨n,x⟩ : Tape ℂ))
      result.valid ∧ result.peak ≤ cap ∧ d.work+1+result.work ≤ W n ∧
      result.val = (⟨n, dft n x⟩ : Tape ℂ)


-- @@ L305-315 verbatim
def ConvProgram (order : Prog false w w) (solve : Prog true convInKind convOutKind)
    (W : ℕ → ℕ) : Prop :=
  ∃ cBound : ℕ, ∀ n : ℕ, 0<n →
    let cap := (n+2)^cBound
    let d := run order n
    W n + 10*(n+2) ≤ cap ∧ d.peak ≤ cap ∧ d.valid ∧
    0 < d.val ∧ d.val < 1024*(2*n-1)^3 ∧ d.val ≤ cap ∧
    ∀ x y : Vec n,
      let result := run solve (n, root d.val, (⟨n,x⟩ : Tape ℂ),(⟨n,y⟩ : Tape ℂ))
      result.valid ∧ result.peak ≤ cap ∧ d.work+1+result.work ≤ W n ∧
      result.val = (⟨2*n-1, conv n x y⟩ : Tape ℂ)


-- @@ L317-319 verbatim
def TimeBounds (W : ℕ → ℕ) : Prop :=
  let W' := fun n : ℕ => (W n : ℝ)
  W' =O[atTop] paperTime ∧ W' =O[atTop] decimalTime ∧ W' =o[atTop] nlogn


-- @@ L321-321 verbatim
def DFTGoal : Prop := ∃ order solve W, DFTProgram order solve W ∧ TimeBounds W


-- @@ L323-323 verbatim
def ConvGoal : Prop := ∃ order solve W, ConvProgram order solve W ∧ TimeBounds W


-- @@ L325-327 verbatim
/-- One fixed program computes every positive-length canonical DFT, including preparation. -/
theorem transform_main : DFTGoal := by
  sorry


-- @@ L329-331 verbatim
/-- One fixed bilinear program computes convolution with the same asymptotic bounds. -/
theorem convolution_main : ConvGoal := by
  sorry


-- @@ L333-333 verbatim
end

-- @@ L334-334 verbatim
end PowerSaving


-- @@ L336-336 verbatim
end OAI
