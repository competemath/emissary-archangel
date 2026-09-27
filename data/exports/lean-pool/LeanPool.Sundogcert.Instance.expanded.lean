/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/
module

public import LeanPool.Sundogcert.Certificate
public import Mathlib.Algebra.Field.ZMod          -- Field (ZMod 2) via Fact (Nat.Prime 2)
public import Mathlib.LinearAlgebra.Matrix.Notation -- !![; ] matrix literal notation


-- @@ L12-24 verbatim
/-!
  Sundogcert/Instance.lean — the concrete executable ZMod 2 instance.
  A [n=4, k=2, m=2, τ=1] GF(2) syndrome certificate. Two verifiers on ONE scheme:
    vSupp (lb = supportLb)  — degenerate support bound (rejects only at τ=0)
    vCol  (lb = colWeightLb) — non-degenerate column-weight bound (rejects at τ>0)
  hHG proved AXIOM-CLEAN by `decide` (kernel; 4 secrets, tiny matrices).
  HEADLINE: y=1100 & y=1110 DIVERGE (vSupp quarantine, vCol reject) — the
  non-degenerate bound earning its keep at τ=1.
  HONESTY NOTE: colBound H = 1 here, so colWeightLb is TIGHT on this code — a FAVORABLE case.
  In general (non-uniform H) the bound is loose: it divides by the GLOBAL worst column weight
  (see Certificate.lean). This instance demonstrates the bound's SOUNDNESS and its τ>0 reach,
  NOT general tightness.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
open Matrix


-- @@ L30-30 verbatim
namespace Sundog.Certificate.Instance


-- @@ L32-34 verbatim
/-- The concrete code is `C = ker H = {y : y0 = y1 = 0}`.  `G`'s rows are codewords
    (coords 2,3), so `H *ᵥ (s ᵥ* G) = 0` for every secret. -/
def G : Matrix (Fin 2) (Fin 4) (ZMod 2) := !![0, 0, 1, 0; 0, 0, 0, 1]

-- @@ L35-36 verbatim
/-- Parity-check matrix of the concrete code: `H *ᵥ y = (y 0, y 1)`. -/
def H : Matrix (Fin 2) (Fin 4) (ZMod 2) := !![1, 0, 0, 0; 0, 1, 0, 0]


-- @@ L38-39 verbatim
/-- The dual-pair law, AXIOM-CLEAN by `decide` (4 secrets over ZMod 2, 2×4 / 2×2 matrices). -/
theorem hHG_decide : ∀ s : Fin 2 → ZMod 2, H *ᵥ (s ᵥ* G) = 0 := by decide


-- @@ L41-49 verbatim
/-- The concrete scheme. -/
def S : Scheme (ZMod 2) where
  n := 4
  k := 2
  m := 2
  G := G
  H := H
  τ := 1
  hHG := hHG_decide


-- @@ L51-51 verbatim
/-! ### The shared witness search and the two verifiers. -/


-- @@ L53-55 verbatim
/-- Forward witness: if `y` is already light (`wt y ≤ τ`) it is its own same-syndrome witness. -/
def witnessOpt (y : Fin S.n → ZMod 2) : Option (Fin S.n → ZMod 2) :=
  if wt y ≤ S.τ then some y else none


-- @@ L57-66 verbatim
theorem witness_sound :
    ∀ y e', witnessOpt y = some e' → S.H *ᵥ e' = S.H *ᵥ y ∧ wt e' ≤ S.τ := by
  intro y e' h
  unfold witnessOpt at h
  by_cases hwt : wt y ≤ S.τ
  · simp only [hwt, ite_true, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hwt⟩
  · simp only [hwt, ite_false] at h
    exact absurd h (by simp)


-- @@ L68-72 verbatim
/-- Verifier with the degenerate support bound `supportLb`. -/
def vSupp : Verifier S where
  witnessOpt := witnessOpt
  lb := supportLb S
  witness_sound := witness_sound


-- @@ L74-78 verbatim
/-- Verifier with the non-degenerate column-weight bound `colWeightLb`. -/
def vCol : Verifier S where
  witnessOpt := witnessOpt
  lb := colWeightLb S
  witness_sound := witness_sound


-- @@ L80-80 verbatim
/-! ### Display instance for the three-valued verdict. -/


-- @@ L82-86 verbatim
instance : ToString Verdict where
  toString
    | Verdict.accept => "accept"
    | Verdict.reject => "reject"
    | Verdict.quarantine => "quarantine"


-- @@ L88-88 verbatim
/-! ### The six test bodies as `Fin 4 → ZMod 2` vectors. -/


-- @@ L90-91 verbatim
/-- Test body `0000`: the zero vector (a codeword). -/
def y0000 : Fin 4 → ZMod 2 := ![0, 0, 0, 0]

-- @@ L92-93 verbatim
/-- Test body `0010`: weight-one error inside the code's support. -/
def y0010 : Fin 4 → ZMod 2 := ![0, 0, 1, 0]

-- @@ L94-95 verbatim
/-- Test body `1000`: weight-one error on a syndrome coordinate. -/
def y1000 : Fin 4 → ZMod 2 := ![1, 0, 0, 0]

-- @@ L96-97 verbatim
/-- Test body `0011`: weight-two body that is itself a codeword. -/
def y0011 : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

-- @@ L98-99 verbatim
/-- Test body `1100`: weight-two error on both syndrome coordinates. -/
def y1100 : Fin 4 → ZMod 2 := ![1, 1, 0, 0]

-- @@ L100-101 verbatim
/-- Test body `1110`: weight-three body mixing syndrome and code coordinates. -/
def y1110 : Fin 4 → ZMod 2 := ![1, 1, 1, 0]


-- @@ L103-104 verbatim
/-! ### The verdict table — BOTH verifiers on each body.
    Format per line: "input  vSupp  vCol". -/



-- @@ L107-107 verbatim
/-! ### Axiom audit. -/



-- @@ L110-110 verbatim
end Sundog.Certificate.Instance
