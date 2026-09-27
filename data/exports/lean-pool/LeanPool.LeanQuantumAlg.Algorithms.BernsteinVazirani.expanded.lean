/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Primitives.WalshHadamard
public import LeanPool.LeanQuantumAlg.Core.Cost


-- @@ L12-51 verbatim
/-!
# Bernstein-Vazirani algorithm

The Bernstein-Vazirani problem gives oracle access to the inner-product
function `x ↦ x · s mod 2` of an unknown string `s`, and asks to find `s`
[dW19, qcnotes.tex:1282-1283]. The original problem is due to Bernstein and
Vazirani (1997).

The circuit is exactly the Deutsch-Jozsa circuit [dW19, qcnotes.tex:1288]:
after one query, the input register holds the phase pattern
`(1/√N) ∑_x (-1)^{x·s} |x⟩` [dW19, qcnotes.tex:1293-1294], and the second
Hadamard layer maps it exactly to the classical state `|s⟩`
[dW19, qcnotes.tex:1296]. One query therefore
recovers the whole hidden string.

This module reuses the shared Walsh-Hadamard pipeline
(`WalshHadamard.finalJointState` applied to the inner-product oracle): the
query is the actual XOR-oracle gate, bridged by phase kickback. The new
mathematical content is Walsh-character orthogonality, proved by a
pair-cancellation involution (flip a bit on which the two characters
disagree).

## Conventions

- Bit order: `WalshHadamard.bit x k = x.val.testBit k.val`, as in the
  `WalshHadamard` primitive. The recovered string is expressed in the same
  convention used by the oracle, so the statement is convention-consistent.
- Big-endian basis labelling as in `Core/State.lean`.

## Main results

- `LeanPool.LeanQuantumAlg.BernsteinVazirani.oracle` — the inner-product oracle of a
  hidden string, as a `WalshHadamard` Boolean oracle.
- `LeanPool.LeanQuantumAlg.BernsteinVazirani.sum_walshSign_mul_walshSign` —
  Walsh-character orthogonality via the bit-flip involution.
- `LeanPool.LeanQuantumAlg.BernsteinVazirani.finalState_oracle` — the final input
  register is exactly `|s⟩`.
- `LeanPool.LeanQuantumAlg.BernsteinVazirani.main` — the joint register after the
  circuit is exactly `|s⟩ ⊗ |−⟩`: one query recovers the hidden string.
-/


-- @@ L53-53 verbatim
@[expose] public section


-- @@ L55-55 verbatim
namespace QuantumAlg


-- @@ L57-57 verbatim
open PureState Gate


-- @@ L59-59 verbatim
noncomputable section


-- @@ L61-61 verbatim
variable {n : ℕ}


-- @@ L63-63 verbatim
namespace BernsteinVazirani


-- @@ L65-65 verbatim
open WalshHadamard


-- @@ L67-70 verbatim
/-- The Bernstein-Vazirani oracle for hidden string `s`: the inner-product
function `x ↦ x · s mod 2` [dW19, qcnotes.tex:1283], queried through
`Gate.xorOracle` like any Deutsch-Jozsa oracle. -/
def oracle (s : Fin (2 ^ n)) : WalshHadamard.Oracle n := fun x => dotParity x s


-- @@ L72-72 verbatim
/-! ### Walsh-sign algebra -/


-- @@ L74-82 verbatim
/-- The bitwise inner-product parity is symmetric. -/
theorem dotParity_comm (x y : Fin (2 ^ n)) : dotParity x y = dotParity y x := by
  have hset : (Finset.univ.filter fun k : Fin n => bit x k && bit y k)
      = Finset.univ.filter fun k : Fin n => bit y k && bit x k := by
    apply Finset.filter_congr
    intro k _
    rw [Bool.and_comm]
  unfold WalshHadamard.dotParity
  rw [hset]


-- @@ L84-87 verbatim
/-- The Walsh sign is symmetric. -/
theorem walshSign_comm (x y : Fin (2 ^ n)) : walshSign x y = walshSign y x := by
  unfold WalshHadamard.walshSign
  rw [dotParity_comm]


-- @@ L89-92 verbatim
/-- A Walsh sign squares to `1`. -/
theorem walshSign_mul_self (x y : Fin (2 ^ n)) :
    walshSign x y * walshSign x y = 1 := by
  simp_all


-- @@ L94-94 verbatim
/-! ### Bit-flip involution -/


-- @@ L96-99 verbatim
/-- Flip bit `k` of a basis label. -/
def flipBit (x : Fin (2 ^ n)) (k : Fin n) : Fin (2 ^ n) :=
  ⟨x.val ^^^ 2 ^ k.val,
    Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right one_lt_two k.isLt)⟩


-- @@ L101-107 verbatim
theorem bit_flipBit (x : Fin (2 ^ n)) (k k' : Fin n) :
    bit (flipBit x k) k' = (bit x k' ^^ decide (k = k')) := by
  change (x.val ^^^ 2 ^ k.val).testBit k'.val = (bit x k' ^^ decide (k = k'))
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  congr 1
  rw [decide_eq_decide]
  exact Fin.val_inj


-- @@ L109-113 verbatim
theorem flipBit_flipBit (x : Fin (2 ^ n)) (k : Fin n) :
    flipBit (flipBit x k) k = x := by
  unfold flipBit
  ext
  simp [Nat.xor_assoc]


-- @@ L115-118 verbatim
theorem flipBit_ne (x : Fin (2 ^ n)) (k : Fin n) : flipBit x k ≠ x := by
  intro h
  have hb := congrArg (fun y : Fin (2 ^ n) => bit y k) h
  simp [bit_flipBit] at hb


-- @@ L120-160 verbatim
/-- Flipping bit `k` of `x` toggles the parity `x · z` exactly when bit `k`
of `z` is set. -/
theorem dotParity_flipBit (x z : Fin (2 ^ n)) (k : Fin n) :
    dotParity (flipBit x k) z = (dotParity x z ^^ bit z k) := by
  unfold WalshHadamard.dotParity
  cases hz : bit z k
  · rw [Bool.xor_false]
    have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
        = Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
      apply Finset.filter_congr
      intro k' _
      rcases eq_or_ne k k' with rfl | hk
      · simp [bit_flipBit, hz]
      · simp [bit_flipBit, hk]
    rw [hset]
  · rw [Bool.xor_true]
    by_cases hx : bit x k
    · -- `k` is in the original index set; flipping removes it.
      have hmem : k ∈ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx, hz]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k').erase k := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, ← decide_not, decide_eq_decide,
        ← Finset.card_erase_add_one hmem, Nat.odd_add_one, not_not]
    · -- `k` is not in the original index set; flipping inserts it.
      have hnot : k ∉ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = insert k (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k') := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx, hz]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, Finset.card_insert_of_notMem hnot, ← decide_not,
        decide_eq_decide, Nat.odd_add_one]


-- @@ L162-173 verbatim
/-- Two distinct labels differ at some bit. -/
theorem exists_bit_ne {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∃ k : Fin n, bit y k ≠ bit s k := by
  by_contra hall
  push Not at hall
  refine h (Fin.val_injective (Nat.eq_of_testBit_eq fun i => ?_))
  by_cases hi : i < n
  · exact hall ⟨i, hi⟩
  · push Not at hi
    have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    have hs : s.val < 2 ^ i := lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    rw [Nat.testBit_lt_two_pow hy, Nat.testBit_lt_two_pow hs]


-- @@ L175-177 verbatim
private theorem if_xor_true (a : Bool) :
    (if (a ^^ true) = true then (-1 : ℂ) else 1) = -(if a = true then -1 else 1) := by
  cases a <;> simp


-- @@ L179-194 verbatim
/-- Flipping a bit on which `y` and `s` disagree negates the product of their
Walsh signs. -/
theorem walshSign_mul_walshSign_flipBit {y s : Fin (2 ^ n)} {k : Fin n}
    (hk : bit y k ≠ bit s k) (x : Fin (2 ^ n)) :
    walshSign y (flipBit x k) * walshSign s (flipBit x k)
      = -(walshSign y x * walshSign s x) := by
  unfold WalshHadamard.walshSign
  simp only [dotParity_comm y (flipBit x k), dotParity_comm s (flipBit x k),
    dotParity_flipBit, dotParity_comm x y, dotParity_comm x s]
  cases hy : bit y k <;> cases hs : bit s k
  · exact absurd (hy.trans hs.symm) hk
  · rw [Bool.xor_false, if_xor_true]
    ring
  · rw [Bool.xor_false, if_xor_true]
    ring
  · exact absurd (hy.trans hs.symm) hk


-- @@ L196-205 verbatim
/-- Walsh-character orthogonality: for `y ≠ s` the signed sum over all basis
labels cancels in pairs under the bit-flip involution. -/
theorem sum_walshSign_mul_walshSign {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∑ x, walshSign y x * walshSign s x = 0 := by
  obtain ⟨k, hk⟩ := exists_bit_ne h
  refine Finset.sum_involution (fun x _ => flipBit x k)
    (fun x _ => ?_) (fun x _ _ => flipBit_ne x k)
    (fun x _ => Finset.mem_univ _) (fun x _ => flipBit_flipBit x k)
  rw [walshSign_mul_walshSign_flipBit hk x]
  ring


-- @@ L207-207 verbatim
/-! ### Circuit correctness -/


-- @@ L209-214 verbatim
/-- Querying the inner-product oracle phases each basis label by its Walsh
sign with the hidden string [dW19, qcnotes.tex:1293]. -/
theorem phaseSign_oracle (s x : Fin (2 ^ n)) :
    phaseSign (oracle s) x = walshSign s x := by
  unfold WalshHadamard.phaseSign WalshHadamard.walshSign oracle
  rw [dotParity_comm]


-- @@ L216-231 verbatim
/-- The second Hadamard layer maps the Bernstein-Vazirani phase pattern
exactly to the classical state `|s⟩` [dW19, qcnotes.tex:1296]. -/
theorem finalState_oracle (s : Fin (2 ^ n)) :
    finalState (oracle s) = ket s := by
  ext y
  rw [WalshHadamard.finalState, Gate.apply_apply, ket_apply]
  have hterm : ∀ j, hadamardLayer n y j * afterPhaseQuery (oracle s) j
      = ((2 ^ n : ℕ) : ℂ)⁻¹ * (walshSign y j * walshSign s j) := fun j => by
    change (invSqrtCard n * walshSign y j)
        * (invSqrtCard n * phaseSign (oracle s) j) = _
    rw [phaseSign_oracle, mul_mul_mul_comm, invSqrtCard_mul_self]
  simp only [hterm]
  rw [← Finset.mul_sum]
  by_cases hys : y = s
  · simp_all
  · rw [ite_eq_right hys, sum_walshSign_mul_walshSign hys, mul_zero]


-- @@ L233-235 verbatim
/-- The final Bernstein-Vazirani joint state, annotated with one oracle query. -/
def timedFinalJointState (s : Fin (2 ^ n)) : Timed (PureState (n + 1)) :=
  Timed.trusted 1 (WalshHadamard.finalJointState (oracle s))


-- @@ L237-239 verbatim
@[simp]
theorem timedFinalJointState_ret (s : Fin (2 ^ n)) :
    (timedFinalJointState s).ret = WalshHadamard.finalJointState (oracle s) := rfl


-- @@ L241-243 verbatim
@[simp]
theorem timedFinalJointState_time (s : Fin (2 ^ n)) :
    (timedFinalJointState s).time = 1 := rfl


-- @@ L245-251 verbatim
/-- Public resource profile for the Bernstein-Vazirani circuit:
one oracle query and two `n`-qubit Hadamard layers plus the target Hadamard. -/
def resourceProfile (n : ℕ) : ResourceProfile where
  oracleQueries := 1
  hadamardGates := 2 * n + 1
  elementaryGates := 2 * n + 1
  classicalOps := 0


-- @@ L253-255 verbatim
@[simp]
theorem resourceProfile_oracleQueries (n : ℕ) :
    (resourceProfile n).oracleQueries = 1 := rfl


-- @@ L257-259 verbatim
@[simp]
theorem resourceProfile_hadamardGates (n : ℕ) :
    (resourceProfile n).hadamardGates = 2 * n + 1 := rfl


-- @@ L261-263 verbatim
@[simp]
theorem resourceProfile_elementaryGates (n : ℕ) :
    (resourceProfile n).elementaryGates = 2 * n + 1 := rfl


-- @@ L265-267 verbatim
theorem resourceProfile_exact (n : ℕ) :
    ResourceProfile.HasExactCounts (resourceProfile n) 1 (2 * n + 1) (2 * n + 1) 0 := by
  simp [ResourceProfile.HasExactCounts, resourceProfile]


-- @@ L269-271 verbatim
/-- The final Bernstein-Vazirani joint state with its public resource profile. -/
def profiledFinalJointState (s : Fin (2 ^ n)) : Profiled (PureState (n + 1)) :=
  Profiled.trusted (resourceProfile n) (WalshHadamard.finalJointState (oracle s))


-- @@ L273-275 verbatim
@[simp]
theorem profiledFinalJointState_ret (s : Fin (2 ^ n)) :
    (profiledFinalJointState s).ret = WalshHadamard.finalJointState (oracle s) := rfl


-- @@ L277-279 verbatim
@[simp]
theorem profiledFinalJointState_resources (s : Fin (2 ^ n)) :
    (profiledFinalJointState s).resources = resourceProfile n := rfl


-- @@ L281-289 verbatim
/-- **Bernstein-Vazirani correctness**: running the Deutsch-Jozsa circuit
with the inner-product oracle of hidden string `s` leaves the joint register
in exactly `|s⟩ ⊗ |−⟩` [dW19, qcnotes.tex:1296], so a single query recovers
the hidden string (Bernstein and Vazirani 1997). -/
theorem main (s : Fin (2 ^ n)) :
    WalshHadamard.finalJointState (oracle s)
      = (ket s).tensor ketMinus := by
  rw [WalshHadamard.finalJointState_eq_finalState_tensor,
    finalState_oracle]


-- @@ L291-294 verbatim
/-- Bernstein-Vazirani correctness, phrased through the TimeM return value. -/
theorem timedFinalJointState_correct (s : Fin (2 ^ n)) :
    (timedFinalJointState s).ret = (ket s).tensor ketMinus := by
  exact main s


-- @@ L296-304 verbatim
/-- Bernstein-Vazirani supporting theorem for the public statement: the profiled
circuit returns `|s⟩ ⊗ |-⟩` and records the accepted exact resource counts. -/
theorem main_with_resources (s : Fin (2 ^ n)) :
    (profiledFinalJointState s).ret = (ket s).tensor ketMinus ∧
      ResourceProfile.HasExactCounts (profiledFinalJointState s).resources
        1 (2 * n + 1) (2 * n + 1) 0 := by
  constructor
  · exact main s
  · simp [resourceProfile_exact n]


-- @@ L306-306 verbatim
end BernsteinVazirani


-- @@ L308-308 verbatim
end


-- @@ L310-310 verbatim
end QuantumAlg
