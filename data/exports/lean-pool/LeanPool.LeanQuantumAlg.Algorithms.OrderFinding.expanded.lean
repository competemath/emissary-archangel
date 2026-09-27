/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Algorithms.QPE


-- @@ L11-19 verbatim
/-!
# Order finding (exact, dyadic period `r ∣ 2^t`)

Order finding is the quantum core of Shor's factoring algorithm. This module
formalizes the exact regime where the period divides the register size,
`r ∣ 2^t`. In that regime the eigenphase `s/r` is dyadic, quantum phase
estimation returns the basis index `j = s * (2^t / r)` exactly, and a classical
gcd recovers the order.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace QuantumAlg


-- @@ L25-25 verbatim
open PureState Gate


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
/-! ### Classical order recovery -/


-- @@ L31-31 verbatim
namespace OrderFinding


-- @@ L33-47 verbatim
/-- Exact order recovery from the dyadic phase-estimation output. -/
theorem main_recovery {t s r : ℕ} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (hsr : Nat.Coprime s r) :
    2 ^ t / Nat.gcd (s * (2 ^ t / r)) (2 ^ t) = r := by
  obtain ⟨m, hm⟩ := hrt
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · simp_all
    · exact hm0
  have hdiv : 2 ^ t / r = m := by
    simp_all
  have hsr1 : Nat.gcd s r = 1 := hsr
  have hgcd : Nat.gcd (s * (2 ^ t / r)) (2 ^ t) = m := by
    rw [hdiv, hm, Nat.gcd_mul_right, hsr1, Nat.one_mul]
  simp_all


-- @@ L49-49 verbatim
end OrderFinding


-- @@ L51-51 verbatim
/-! ### Exact order finding via phase estimation -/


-- @@ L53-53 verbatim
namespace OrderFinding


-- @@ L55-75 verbatim
/-- Exact order finding through the decoupled QPE interface. The inverse-QFT
readout is stated at the raw-vector layer because the phase superposition is a
linear combination before it is packaged as a `PureState`. -/
theorem main_exact_dyadic {t s r : ℕ} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (hsr : Nat.Coprime s r) (j : Fin (2 ^ t))
    (hj : j.val = s * (2 ^ t / r)) :
    (invQFT t).applyVec (phaseState t ((s : ℝ) / r)) = (ket j : StateVector t)
      ∧ 2 ^ t / Nat.gcd j.val (2 ^ t) = r := by
  refine ⟨?_, ?_⟩
  · apply QuantumPhaseEstimation.main_exact_dyadic
    rw [hj]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have h2t0 : (2 : ℝ) ^ t ≠ 0 := by positivity
    have hrr : (r : ℝ) * ((2 ^ t / r : ℕ) : ℝ) = (2 : ℝ) ^ t := by
      exact_mod_cast Nat.mul_div_cancel' hrt
    rw [div_eq_div_iff hr0 h2t0]
    push_cast
    rw [← hrr]
    ring
  · rw [hj]
    exact main_recovery hr hrt hsr


-- @@ L77-77 verbatim
end OrderFinding


-- @@ L79-79 verbatim
namespace OrderFinding


-- @@ L81-87 verbatim
/-- Trusted decoupled resource profile for exact order finding: one modular-
exponentiation oracle call feeding an inverse-QFT/readout layer. -/
def orderFindingExactResourceProfile (t : ℕ) : ResourceProfile where
  oracleQueries := 1
  hadamardGates := t
  elementaryGates := t ^ 2
  classicalOps := 1


-- @@ L89-92 verbatim
theorem orderFindingExactResourceProfile_exact (t : ℕ) :
    ResourceProfile.HasExactCounts
      (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 := by
  simp [ResourceProfile.HasExactCounts, orderFindingExactResourceProfile]


-- @@ L94-99 verbatim
/-- Register assumptions for the modular-exponentiation oracle used in exact
order finding. The target register has `m` qubits, large enough to hold
residues modulo `N`. -/
structure ModExpOracleAccess (N x t m : ℕ) where
  modulus_pos : 0 < N
  register_fits : N ≤ 2 ^ m


-- @@ L101-107 verbatim
/-- Target-register update for the modular-exponentiation oracle:
`y ↦ y xor (x^a mod N)`. -/
def modExpOracleTarget {N x t m : ℕ} (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) : Fin (2 ^ m) :=
  ⟨Nat.xor y.val (x ^ a.val % N),
    Nat.xor_lt_two_pow y.isLt
      (lt_of_lt_of_le (Nat.mod_lt _ A.modulus_pos) A.register_fits)⟩


-- @@ L109-113 verbatim
@[simp]
theorem modExpOracleTarget_val {N x t m : ℕ} (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    (modExpOracleTarget A a y).val = Nat.xor y.val (x ^ a.val % N) :=
  rfl


-- @@ L115-123 verbatim
/-- The basis permutation underlying the modular-exponentiation oracle. -/
def modExpOraclePerm {N x t m : ℕ} (A : ModExpOracleAccess N x t m) :
    Equiv.Perm (Fin (2 ^ t) × Fin (2 ^ m)) where
  toFun p := (p.1, modExpOracleTarget A p.1 p.2)
  invFun p := (p.1, modExpOracleTarget A p.1 p.2)
  left_inv p := by
    ext <;> simp [modExpOracleTarget, Nat.xor_assoc]
  right_inv p := by
    ext <;> simp [modExpOracleTarget, Nat.xor_assoc]


-- @@ L125-129 verbatim
@[simp]
theorem modExpOraclePerm_apply {N x t m : ℕ} (A : ModExpOracleAccess N x t m)
    (p : Fin (2 ^ t) × Fin (2 ^ m)) :
    modExpOraclePerm A p = (p.1, modExpOracleTarget A p.1 p.2) :=
  rfl


-- @@ L131-134 verbatim
@[simp]
theorem modExpOraclePerm_symm {N x t m : ℕ} (A : ModExpOracleAccess N x t m) :
    (modExpOraclePerm A).symm = modExpOraclePerm A :=
  rfl


-- @@ L136-139 verbatim
/-- The modular-exponentiation oracle gate in the public access model:
`U_x |a,y> = |a, y xor (x^a mod N)>`. -/
def modExpOracle {N x t m : ℕ} (A : ModExpOracleAccess N x t m) : Gate (t + m) :=
  Gate.ofPerm (prodEquiv.permCongr (modExpOraclePerm A))


-- @@ L141-144 verbatim
theorem modExpOracle_mem_unitaryGroup {N x t m : ℕ} (A : ModExpOracleAccess N x t m) :
    ((modExpOracle A : Gate (t + m)) : HilbertOperator (t + m))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ :=
  Gate.ofPerm_mem_unitaryGroup _


-- @@ L146-155 verbatim
/-- Basis action of the modular-exponentiation oracle. -/
theorem modExpOracle_apply_ket {N x t m : ℕ} (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    (modExpOracle A).apply (ket (prodEquiv (a, y))) =
      ket (prodEquiv (a, modExpOracleTarget A a y)) := by
  rw [modExpOracle, Gate.ofPerm_apply_ket]
  congr 1
  change prodEquiv ((modExpOraclePerm A).symm (prodEquiv.symm (prodEquiv (a, y))))
      = prodEquiv (a, modExpOracleTarget A a y)
  rw [Equiv.symm_apply_apply, modExpOraclePerm_symm, modExpOraclePerm_apply]


-- @@ L157-167 verbatim
/-- Exact order finding paired with the decoupled resource profile. -/
theorem main_exact_dyadic_with_resources {t s r : ℕ}
    (hr : 0 < r) (hrt : r ∣ 2 ^ t) (hsr : Nat.Coprime s r)
    (j : Fin (2 ^ t)) (hj : j.val = s * (2 ^ t / r)) :
    ((invQFT t).applyVec (phaseState t ((s : ℝ) / r)) = (ket j : StateVector t)
      ∧ 2 ^ t / Nat.gcd j.val (2 ^ t) = r) ∧
      ResourceProfile.HasExactCounts
        (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 := by
  constructor
  · exact main_exact_dyadic hr hrt hsr j hj
  · exact orderFindingExactResourceProfile_exact t


-- @@ L169-169 verbatim
end OrderFinding


-- @@ L171-171 verbatim
namespace OrderFinding


-- @@ L173-181 verbatim
/-- Source-level number-theoretic assumptions for exact order finding:
`N ≥ 2`, `x` is coprime to `N`, and `r` is the least positive exponent with
`x^r ≡ 1 (mod N)`. -/
structure Input (N x r : ℕ) : Prop where
  modulus_ge_two : 2 ≤ N
  coprime : Nat.Coprime x N
  order_pos : 0 < r
  order_eq_one : x ^ r % N = 1
  minimal : ∀ m : ℕ, 0 < m → x ^ m % N = 1 → r ≤ m


-- @@ L183-206 verbatim
/-- Exact order-finding output index paired with the public one-query resource
claim. If `q = 2^t` is a multiple of the order `r`, then every
`s ∈ {0, ..., r-1}` gives a valid phase-register output index
`j = s(q/r)`. The modular-exponentiation oracle body is treated as one oracle
call in this resource profile. -/
theorem main_output_with_resources {N x t r s : ℕ}
    (hinput : OrderFinding.Input N x r) (hrt : r ∣ 2 ^ t) (hs : s < r) :
    ∃ j : Fin (2 ^ t),
      j.val = s * (2 ^ t / r) ∧
        ResourceProfile.HasExactCounts
          (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 := by
  obtain ⟨q, hq⟩ := hrt
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hzero | hpos
    · simp_all
    · exact hpos
  have hdiv : 2 ^ t / r = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left q hinput.order_pos
  have hlt : s * q < 2 ^ t := by
    simp_all
  refine ⟨⟨s * q, hlt⟩, ?_, ?_⟩
  · rw [hdiv]
  · exact orderFindingExactResourceProfile_exact t


-- @@ L208-208 verbatim
end OrderFinding


-- @@ L210-210 verbatim
namespace OrderFinding


-- @@ L212-233 verbatim
/-- Integrated exact order-finding access theorem: the modular-exponentiation
oracle is a unitary gate with the public basis action, and the exact divisible
case has a phase-register output index with the trusted one-query resource
profile. -/
theorem main {N x t m r s : ℕ}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (hrt : r ∣ 2 ^ t) (hs : s < r) :
    (((modExpOracle A : Gate (t + m)) : HilbertOperator (t + m))
        ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ ∧
      ∀ a : Fin (2 ^ t), ∀ y : Fin (2 ^ m),
        (modExpOracle A).apply (ket (prodEquiv (a, y))) =
          ket (prodEquiv (a, modExpOracleTarget A a y))) ∧
      ∃ j : Fin (2 ^ t),
        j.val = s * (2 ^ t / r) ∧
          ResourceProfile.HasExactCounts
            (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 := by
  constructor
  · constructor
    · exact modExpOracle_mem_unitaryGroup A
    · intro a y
      exact modExpOracle_apply_ket A a y
  · exact main_output_with_resources hinput hrt hs


-- @@ L235-235 verbatim
end OrderFinding


-- @@ L237-237 verbatim
/-! ### Classical factoring reduction (gcd step) -/


-- @@ L239-239 verbatim
namespace OrderFinding


-- @@ L241-260 verbatim
/-- Factoring-reduction gcd step. If `N ∣ a * b` while `N` divides neither `a`
nor `b`, then `gcd(a, N)` is a nontrivial factor of `N`. -/
theorem main_factor_reduction {N a b : ℕ} (hN : 1 < N)
    (hdvd : N ∣ a * b) (ha : ¬ N ∣ a) (hb : ¬ N ∣ b) :
    1 < Nat.gcd a N ∧ Nat.gcd a N < N := by
  have hN0 : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hN)
  have hpos : 0 < Nat.gcd a N := Nat.gcd_pos_of_pos_right a hN0
  have hle : Nat.gcd a N ≤ N := Nat.le_of_dvd hN0 (Nat.gcd_dvd_right a N)
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge 1 (Nat.gcd a N) with h | h
    · exact h
    · exfalso
      have hg1 : Nat.gcd a N = 1 := by omega
      have hca : Nat.Coprime a N := hg1
      exact hb (hca.symm.dvd_of_dvd_mul_left hdvd)
  · rcases Nat.lt_or_ge (Nat.gcd a N) N with h | h
    · exact h
    · exfalso
      have hgN : Nat.gcd a N = N := le_antisymm hle h
      exact ha (hgN ▸ Nat.gcd_dvd_left a N)


-- @@ L262-262 verbatim
end OrderFinding


-- @@ L264-264 verbatim
end


-- @@ L266-266 verbatim
end QuantumAlg
