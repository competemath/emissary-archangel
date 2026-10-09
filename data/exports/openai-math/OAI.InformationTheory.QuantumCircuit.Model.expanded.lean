import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Matrix.Norms.L2Operator


-- @@ L8-8 verbatim
namespace QAC


-- @@ L10-10 verbatim
abbrev Bit := Fin 2

-- @@ L11-11 verbatim
abbrev Word (N : ℕ) := Fin N → Bit

-- @@ L12-12 verbatim
abbrev Operator (N : ℕ) := Matrix (Word N) (Word N) ℂ

-- @@ L13-13 verbatim
abbrev QubitOperator := Matrix Bit Bit ℂ


-- @@ L15-17 verbatim
/-- Tensor product in the computational basis. -/
def tensorMatrix {N : ℕ} (a : Fin N → QubitOperator) : Operator N :=
  fun x y => ∏ i, a i (x i) (y i)


-- @@ L19-22 verbatim
/-- A one-qubit unitary or an unbounded-arity Toffoli gate. -/
inductive Gate (N : ℕ) where
  | local (q : Fin N) (u : Matrix.unitaryGroup Bit ℂ)
  | toffoli (controls : Finset (Fin N)) (target : Fin N) (hne : target ∉ controls)


-- @@ L24-24 verbatim
namespace Gate


-- @@ L26-28 verbatim
def support {N : ℕ} : Gate N → Finset (Fin N)
  | .local q _ => {q}
  | .toffoli c t _ => insert t c


-- @@ L30-32 verbatim
/-- A Toffoli flips its target iff all controls are one. -/
def toffoliWord {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (x : Word N) : Word N :=
  if ∀ i ∈ c, x i = 1 then Function.update x t (1 - x t) else x


-- @@ L34-36 verbatim
def matrix {N : ℕ} : Gate N → Operator N
  | .local q u => tensorMatrix fun i => if i = q then (u : QubitOperator) else 1
  | .toffoli c t _ => fun x y => if x = toffoliWord c t y then 1 else 0


-- @@ L38-38 verbatim
end Gate


-- @@ L40-42 verbatim
structure PhysicalLayer (N : ℕ) where
  gates : List (Gate N)
  disjoint : gates.Pairwise (fun A B => Disjoint A.support B.support)


-- @@ L44-45 verbatim
def physicalLayerMatrix {N : ℕ} (L : PhysicalLayer N) : Operator N :=
  (L.gates.map Gate.matrix).prod


-- @@ L47-49 verbatim
/-- Chronological order: the rightmost matrix acts first. -/
def physicalCircuitMatrix {N : ℕ} (layers : List (PhysicalLayer N)) : Operator N :=
  ((layers.map physicalLayerMatrix).reverse).prod


-- @@ L51-53 verbatim
/-- The computational-basis input with the remaining qubits initialized to zero. -/
def inputWord {n N : ℕ} (x : Word n) : Word N :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else 0


-- @@ L55-55 verbatim
def parity {n : ℕ} (x : Word n) : Bit := ∑ i, x i


-- @@ L57-59 verbatim
/-- Born probability, summing all final garbage with no cleanliness assumption. -/
def successProbability {n N : ℕ} (W : Operator N) (out : Fin N) (x : Word n) : ℝ :=
  ∑ y : Word N, if y out = parity x then Complex.normSq (W y (inputWord x)) else 0


-- @@ L61-67 verbatim
/-- The literal measured-output, polynomial-total-qubit parity lower bound. -/
def ParityStatement : Prop :=
  ∀ (d : ℕ) (c ε : ℝ), 1 ≤ c → 0 < ε → ε ≤ 1 / 2 →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, n ≤ N → (N : ℝ) ≤ (n : ℝ) ^ c →
      ∀ layers : List (PhysicalLayer N), layers.length ≤ d →
        ∀ out : Fin N, ¬ (∀ x : Word n,
          1 / 2 + ε ≤ successProbability (physicalCircuitMatrix layers) out x)


-- @@ L69-69 verbatim
end QAC


-- @@ L71-71 verbatim
end


-- @@ L73-73 verbatim
end OAI
