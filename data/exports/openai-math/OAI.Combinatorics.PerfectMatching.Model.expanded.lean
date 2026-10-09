import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u_1 u_2


-- @@ L7-7 verbatim
namespace MatchingEntropy

-- @@ L8-11 verbatim
structure LooplessGraph (V : Type u_1) (E : Type u_2) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

-- @@ L12-12 verbatim
namespace LooplessGraph

-- @@ L13-13 verbatim
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

-- @@ L14-15 verbatim
def Incident (G : LooplessGraph V E) (v : V) (e : E) : Prop :=
  G.left e=v ∨ G.right e=v

-- @@ L16-17 verbatim
def IsPerfectMatching (G : LooplessGraph V E) (M : Finset E) : Prop :=
  ∀ v, ∃! e, e∈M ∧ G.Incident v e

-- @@ L18-18 verbatim
abbrev Matching (G : LooplessGraph V E) := {M : Finset E // G.IsPerfectMatching M}

-- @@ L19-20 verbatim
noncomputable instance matchingFintype (G : LooplessGraph V E) : Fintype G.Matching :=
  Fintype.ofFinite _

-- @@ L21-21 verbatim
end LooplessGraph

-- @@ L22-22 verbatim
end MatchingEntropy


-- @@ L24-24 verbatim
namespace BinaryMatching

-- @@ L25-25 verbatim
abbrev Pair (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

-- @@ L26-29 verbatim
def completeGraph (n : ℕ) : MatchingEntropy.LooplessGraph (Fin n) (Pair n) where
  left e := e.val.1
  right e := e.val.2
  loopless e := ne_of_lt e.property


-- @@ L31-35 verbatim
structure Record where
  left : ℕ
  right : ℕ
  multiplicity : ℕ
  deriving DecidableEq


-- @@ L37-41 verbatim
structure Input where
  n : ℕ
  records : List Record
  valid : ∀ e∈records, e.left < e.right ∧ e.right < n
  unique : (records.map (fun e => (e.left,e.right))).Nodup


-- @@ L43-46 verbatim
def multiplicity (G : Input) (e : Pair G.n) : ℕ :=
  match G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
  | none => 0
  | some r => r.multiplicity


-- @@ L48-49 verbatim
noncomputable def count (G : Input) : ℕ :=
  ∑ M : (completeGraph G.n).Matching, ∏ e∈M.val, multiplicity G e


-- @@ L51-52 verbatim
def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length false ++ true :: n.bits


-- @@ L54-55 verbatim
def encodeRecord (r : Record) : List Bool :=
  encodeNat r.left ++ encodeNat r.right ++ encodeNat r.multiplicity


-- @@ L57-58 verbatim
def encodeInput (G : Input) : List Bool :=
  encodeNat G.n ++ encodeNat G.records.length ++ G.records.flatMap encodeRecord


-- @@ L60-60 verbatim
end BinaryMatching


-- @@ L62-62 verbatim
end OAI
