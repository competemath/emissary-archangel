import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Superstring


-- @@ L7-7 verbatim
abbrev Symbol := List Bool

-- @@ L8-8 verbatim
abbrev Word := List Symbol

-- @@ L9-9 verbatim
abbrev Instance := List Word


-- @@ L11-14 verbatim
/-- Prefix markers encode the list spine, including its final boundary. -/
def encodeList {α : Type} (enc : α → List Bool) : List α → List Bool
  | [] => [true]
  | a :: as => false :: (enc a ++ encodeList enc as)


-- @@ L16-16 verbatim
def encodeSymbol : Symbol → List Bool := encodeList (fun b => [b])

-- @@ L17-17 verbatim
def encodeWord : Word → List Bool := encodeList encodeSymbol

-- @@ L18-18 verbatim
def encodeInstance : Instance → List Bool := encodeList encodeWord


-- @@ L20-22 verbatim
/-- Ordinary contiguous substring containment, including the empty word. -/
def IsCommonSuperstring (S : Instance) (T : Word) : Prop :=
  ∀ s ∈ S, s <:+: T


-- @@ L24-26 verbatim
/-- The optimum in symbols, not in bits. -/
noncomputable def opt (S : Instance) : ℕ :=
  sInf {n : ℕ | ∃ T : Word, IsCommonSuperstring S T ∧ T.length = n}


-- @@ L28-32 verbatim
/-- A deterministic finite-stack-machine implementation, with a polynomial bound
on bit-level running time in the explicitly encoded input length. -/
def HasPolynomialImplementation (f : Instance → Word) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime encodeInstance encodeWord f,
    ∀ k : M.tm.K, Finite (M.tm.Γ k)


-- @@ L34-34 verbatim
end Superstring


-- @@ L36-36 verbatim
end OAI
