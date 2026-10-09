import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace RationalHitting


-- @@ L7-7 verbatim
universe u


-- @@ L9-15 verbatim
inductive Formula (n : ℕ) where
  | var : Fin n → Formula n
  | const : ℚ → Formula n
  | add : Formula n → Formula n → Formula n
  | mul : Formula n → Formula n → Formula n
  | inv : Formula n → Formula n
  deriving DecidableEq


-- @@ L17-17 verbatim
namespace Formula


-- @@ L19-22 verbatim
def size {n : ℕ} : Formula n → ℕ
  | .var _ | .const _ => 1
  | .add f g | .mul f g => f.size + g.size + 1
  | .inv f => f.size + 1


-- @@ L24-32 verbatim
/-- Evaluation in any rational algebra; a unary inverse requires an actual
    two-sided inverse of the evaluated operand, not a totalized inverse. -/
inductive Eval {n : ℕ} {R : Type u} [Ring R]
    (c : ℚ →+* R) (X : Fin n → R) : Formula n → R → Prop where
  | var (i) : Eval c X (.var i) (X i)
  | const (a) : Eval c X (.const a) (c a)
  | add {f g a b} : Eval c X f a → Eval c X g b → Eval c X (.add f g) (a + b)
  | mul {f g a b} : Eval c X f a → Eval c X g b → Eval c X (.mul f g) (a * b)
  | inv {f a b} : Eval c X f a → a * b = 1 → b * a = 1 → Eval c X (.inv f) b


-- @@ L34-34 verbatim
end Formula


-- @@ L36-36 verbatim
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℚ

-- @@ L37-37 verbatim
abbrev Tuple (n d : ℕ) := Fin n → Mat d


-- @@ L39-40 verbatim
def Evaluates {n d : ℕ} (f : Formula n) (X : Tuple n d) (v : Mat d) : Prop :=
  f.Eval (algebraMap ℚ (Mat d)) X v


-- @@ L42-43 verbatim
def Admissible {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v


-- @@ L45-46 verbatim
def Nonzero {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v ∧ v ≠ 0


-- @@ L48-52 verbatim
/-- All output tuples have one common positive dimension. -/
structure Output (n : ℕ) where
  dimension : ℕ
  dimension_pos : 0 < dimension
  tuples : List (Tuple n dimension)


-- @@ L54-58 verbatim
/-- Little-endian unsigned binary, prefixed by a unary bit-length and a zero
    terminator. This is a self-delimiting binary encoding, including zero. -/
def encodeNat (a : ℕ) : List Bool :=
  let ds := (Nat.digits 2 a).map (fun b => b != 0)
  List.replicate ds.length true ++ [false] ++ ds


-- @@ L60-63 verbatim
/-- Sign bit, binary numerator magnitude, and positive binary denominator.
    Rat.num and Rat.den are the canonical reduced numerator and denominator. -/
def encodeRat (a : ℚ) : List Bool :=
  [decide (a.num < 0)] ++ encodeNat a.num.natAbs ++ encodeNat a.den


-- @@ L65-68 verbatim
def encodeTuple {n d : ℕ} (X : Tuple n d) : List Bool :=
  (List.finRange n).flatMap fun i =>
    (List.finRange d).flatMap fun j =>
      (List.finRange d).flatMap fun k => encodeRat (X i j k)


-- @@ L70-71 verbatim
def encodeOutput {n : ℕ} (H : Output n) : List Bool :=
  encodeNat H.dimension ++ encodeNat H.tuples.length ++ H.tuples.flatMap encodeTuple


-- @@ L73-75 verbatim
/-- 0 is blank, 1 and 2 are the two literal binary digits, 3 is work space.
    Fixed finite tape alphabet and finite state space; no advice or oracle. -/
abbrev Alphabet := Fin 4

-- @@ L76-76 verbatim
abbrev Machine (m : ℕ) := Turing.TM0.Machine Alphabet (Fin (m + 1))

-- @@ L77-77 verbatim
abbrev Config (m : ℕ) := Turing.TM0.Cfg Alphabet (Fin (m + 1))


-- @@ L79-79 verbatim
def tapeBit (b : Bool) : Alphabet := if b then 2 else 1


-- @@ L81-82 verbatim
def unaryInput (n s : ℕ) : List Alphabet :=
  List.replicate n 2 ++ [1] ++ List.replicate s 2


-- @@ L84-87 verbatim
/-- Exactly t ordinary deterministic TM0 transitions. -/
def run {m : ℕ} (G : Machine m) : ℕ → Config m → Option (Config m)
  | 0, a => some a
  | t + 1, a => (Turing.TM0.step G a).bind (run G t)


-- @@ L89-93 verbatim
def OutputsWithin {m n : ℕ} (G : Machine m) (s bound : ℕ) (H : Output n) : Prop :=
  ∃ t ≤ bound, ∃ a : Config m,
    run G t (Turing.TM0.init (unaryInput n s)) = some a ∧
    Turing.TM0.step G a = none ∧
    a.Tape.right₀ = Turing.ListBlank.mk ((encodeOutput H).map tapeBit)


-- @@ L95-97 verbatim
def Hits {n : ℕ} (s : ℕ) (H : Output n) : Prop :=
  ∀ f : Formula n, f.size ≤ s → Admissible f → Nonzero f →
    ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v


-- @@ L99-106 verbatim
/-- A fixed polynomial bound on bit time, full binary output length,
and common positive dimension. -/
def MainStatement : Prop :=
  ∃ (m : ℕ) (G : Machine m) (C k : ℕ), 0 < C ∧ 0 < k ∧
    ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → ∃ H : Output n,
      H.dimension ≤ C * (n + s + 1) ^ k ∧
      (encodeOutput H).length ≤ C * (n + s + 1) ^ k ∧
      OutputsWithin G s (C * (n + s + 1) ^ k) H ∧ Hits s H


-- @@ L108-108 verbatim
end RationalHitting


-- @@ L110-110 verbatim
end OAI
