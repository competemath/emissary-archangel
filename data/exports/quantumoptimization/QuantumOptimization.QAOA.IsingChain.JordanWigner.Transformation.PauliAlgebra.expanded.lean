import QuantumOptimization.QAOA.IsingChain.UpperBound.ReducedChain


-- @@ L3-31 verbatim
/-!
# Single-site Pauli Algebra — Y/Z Hermiticity & squares, same-site (anti)commutators, three Pauli products, cross-site commutation

Foundational lifted-Pauli algebra for the Jordan–Wigner construction.
These lemmas extend the existing `localPauliX_*` interface (Hermiticity, square,
commutation) to `Y` and `Z`, and prove the same-site anticommutators, the three
single-site Pauli products, and general cross-site commutation. Each is a basis-
action calculation via `op_eq_of_on_computationalBasis`, mirroring the templates
`localPauliX_sq` / `localPauliX_commute` / `localPauliX_hermitian`.

All declarations live in the `QAOA.IsingChain.JordanWigner` namespace; downstream
JW files (`Operators`, `HamiltonianImage`) consume these via import.

## Main statements

* Hermiticity: `localPauliY_hermitian`, `localPauliZ_hermitian`.
* Squares: `localPauliY_sq`, `localPauliZ_sq`.
* Single-site products: `localPauliX_mul_localPauliY` (`X_j Y_j = i Z_j`),
  `localPauliY_mul_localPauliZ`, `localPauliZ_mul_localPauliX`.
* Same-site anticommutators: `localPauliX_anticomm_localPauliY`,
  `localPauliX_anticomm_localPauliZ`, `localPauliY_anticomm_localPauliZ`.
* Generic + nine specialized cross-site commutations: `localPauli_cross_commute`
  and `localPauliX_commute_localPauliX`, …, `localPauliZ_commute_localPauliZ`.

## Source pins

* See `JordanWigner/Transformation/Operators.lean` for the JW map conventions and
  the full source pin list (arXiv:1911.12259v2, arXiv:1706.02998v2).
-/


-- @@ L33-33 verbatim
namespace QAOA.IsingChain.JordanWigner


-- @@ L35-35 verbatim
open Quantum.Operators

-- @@ L36-36 verbatim
open Quantum.Gates

-- @@ L37-37 verbatim
open Qubits

-- @@ L38-38 verbatim
open scoped BigOperators


-- @@ L40-44 verbatim
noncomputable section

-- ============================================================================
-- Section: Single-site Pauli algebra (lifted level)
-- ============================================================================


-- @@ L46-52 verbatim
/-!
These lemmas extend the existing `localPauliX_*` interface (Hermiticity, square,
commutation) to `Y` and `Z`, and prove the same-site anticommutators, the three
single-site Pauli products, and general cross-site commutation. Each is a basis-
action calculation via `op_eq_of_on_computationalBasis`, mirroring the templates
`localPauliX_sq` / `localPauliX_commute` / `localPauliX_hermitian`.
-/


-- @@ L54-61 expanded
/-- Each local Pauli `Y` operator is Hermitian. -/
theorem localPauliY_hermitian {N : ℕ} (j : Fin N) :
    Matrix.conjTranspose (localPauliY j) = localPauliY j :=
  by
  rw [localPauliY_eq_localOp, localOp_conjTranspose]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.conjTranspose_apply, pauliY]


-- @@ L63-67 expanded
/-- Each local Pauli `Z` operator is Hermitian. -/
theorem localPauliZ_hermitian {N : ℕ} (j : Fin N) :
    Matrix.conjTranspose (localPauliZ j) = localPauliZ j :=
  by
  rw [localPauliZ_eq_localOp, localOp_conjTranspose]
  simp [pauliZ_hermitian]


-- @@ L69-71 expanded
/-- The diagonal entries of Pauli `Z` square to `1` (each is `±1`). -/
theorem pauliZ_diag_sq (b : Fin 2) : (pauliZ b b) * (pauliZ b b) = 1 := by
  fin_cases b <;> simp [pauliZ]


-- @@ L73-77 verbatim
/-- The `Y`-phase factors at a bit and its flip multiply to `1`
(`i · (-i) = 1`). -/
theorem pauliYPhase_mul_flip (b : Fin 2) :
    pauliYPhase (flipBit b) * pauliYPhase b = 1 := by
  fin_cases b <;> simp [pauliYPhase, flipBit, Complex.I_mul_I]


-- @@ L79-82 expanded
/-- `pauliYPhase b = i · (Z b b)`, the scalar identity behind `X_j Y_j = i Z_j`. -/
theorem pauliYPhase_eq_I_mul_diag (b : Fin 2) : pauliYPhase b = Complex.I * (pauliZ b b) := by
  fin_cases b <;> simp [pauliYPhase, pauliZ]


-- @@ L84-88 verbatim
/-- The `Y`-phase factors at a bit and its flip sum to zero (`i + (-i) = 0`),
the scalar identity behind the same-site `{X_j, Y_j} = 0`. -/
theorem pauliYPhase_add_flip (b : Fin 2) :
    pauliYPhase b + pauliYPhase (flipBit b) = 0 := by
  fin_cases b <;> simp [pauliYPhase, flipBit]


-- @@ L90-94 expanded
/-- The `Z`-diagonal entry flips sign under a bit flip:
`Z (flipBit b) (flipBit b) = - (Z b b)`. -/
theorem pauliZ_diag_flip (b : Fin 2) : pauliZ (flipBit b) (flipBit b) = -(pauliZ b b) := by
  fin_cases b <;> simp [pauliZ, flipBit]


-- @@ L96-100 expanded
/-- `(Z b b) * pauliYPhase b = Complex.I`, behind `Y_j Z_j = i X_j` (collecting
the `Z`-eigenvalue and the `Y`-phase). -/
theorem diag_mul_pauliYPhase (b : Fin 2) : (pauliZ b b) * pauliYPhase b = Complex.I := by
  fin_cases b <;> simp [pauliYPhase, pauliZ]


-- @@ L102-105 expanded
/-- `Z (flipBit b) (flipBit b) = Complex.I * pauliYPhase b`, behind `Z_j X_j = i Y_j`. -/
theorem diag_flip_eq_I_mul_pauliYPhase (b : Fin 2) :
    pauliZ (flipBit b) (flipBit b) = Complex.I * pauliYPhase b := by
  fin_cases b <;> simp [pauliYPhase, pauliZ, flipBit, Complex.I_mul_I]


-- @@ L107-112 verbatim
/-- The identity operator acts trivially on a computational-basis ket. -/
theorem one_mul_basisKet {N : ℕ} (z : BitString N) :
    (1 : NQubitOp N) * computationalBasisKet N z = computationalBasisKet N z := by
  ext i
  rw [op_mul_ket_vec]
  exact congrArg (fun v => v i) (Matrix.one_mulVec ((computationalBasisKet N z).vec))


-- @@ L114-119 verbatim
/-- The zero operator annihilates a computational-basis ket. -/
theorem zero_mul_basisKet {N : ℕ} (z : BitString N) :
    (0 : NQubitOp N) * computationalBasisKet N z = 0 := by
  ext i
  rw [op_mul_ket_vec]
  simp


-- @@ L121-128 verbatim
/-- Each local Pauli `Z` operator squares to the identity. -/
theorem localPauliZ_sq {N : ℕ} (j : Fin N) :
    localPauliZ j * localPauliZ j = (1 : NQubitOp N) := by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  rw [op_mul_op_mul_ket, localPauliZ_on_basis, op_mul_smul_ket, localPauliZ_on_basis,
      Ket.smul_smul, pauliZ_diag_sq]
  simp [one_mul_basisKet]


-- @@ L130-142 verbatim
/-- Each local Pauli `Y` operator squares to the identity. -/
theorem localPauliY_sq {N : ℕ} (j : Fin N) :
    localPauliY j * localPauliY j = (1 : NQubitOp N) := by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  rw [op_mul_op_mul_ket, localPauliY_on_basis, op_mul_smul_ket, localPauliY_on_basis,
      flipBitAt_apply_same, Ket.smul_smul, mul_comm, pauliYPhase_mul_flip,
      flipBitAt_involutive]
  simp [one_mul_basisKet]

-- ----------------------------------------------------------------------------
-- Subsection: Single-site Pauli products
-- ----------------------------------------------------------------------------


-- @@ L144-151 verbatim
/-- Single-site product `X_j Y_j = i Z_j`. -/
theorem localPauliX_mul_localPauliY {N : ℕ} (j : Fin N) :
    localPauliX j * localPauliY j = Complex.I • localPauliZ j := by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  rw [op_mul_op_mul_ket, localPauliY_on_basis, op_mul_smul_ket, localPauliX_on_basis,
      flipBitAt_involutive, smul_op_mul_ket, localPauliZ_on_basis, Ket.smul_smul,
      pauliYPhase_eq_I_mul_diag]


-- @@ L153-160 verbatim
/-- Single-site product `Y_j Z_j = i X_j`. -/
theorem localPauliY_mul_localPauliZ {N : ℕ} (j : Fin N) :
    localPauliY j * localPauliZ j = Complex.I • localPauliX j := by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  rw [op_mul_op_mul_ket, localPauliZ_on_basis, op_mul_smul_ket, localPauliY_on_basis,
      smul_op_mul_ket, localPauliX_on_basis, Ket.smul_smul,
      diag_mul_pauliYPhase]


-- @@ L162-173 verbatim
/-- Single-site product `Z_j X_j = i Y_j`. -/
theorem localPauliZ_mul_localPauliX {N : ℕ} (j : Fin N) :
    localPauliZ j * localPauliX j = Complex.I • localPauliY j := by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  rw [op_mul_op_mul_ket, localPauliX_on_basis, localPauliZ_on_basis,
      flipBitAt_apply_same, smul_op_mul_ket, localPauliY_on_basis, Ket.smul_smul,
      diag_flip_eq_I_mul_pauliYPhase]

-- ----------------------------------------------------------------------------
-- Subsection: Same-site Pauli anticommutators
-- ----------------------------------------------------------------------------


-- @@ L175-186 verbatim
/-- Same-site anticommutator `{X_j, Y_j} = 0`. -/
theorem localPauliX_anticomm_localPauliY {N : ℕ} (j : Fin N) :
    localPauliX j * localPauliY j + localPauliY j * localPauliX j = 0 := by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  rw [add_op_mul_ket, zero_mul_basisKet,
      op_mul_op_mul_ket, localPauliY_on_basis, op_mul_smul_ket, localPauliX_on_basis,
      flipBitAt_involutive,
      op_mul_op_mul_ket, localPauliX_on_basis, localPauliY_on_basis,
      flipBitAt_apply_same, flipBitAt_involutive, ← Ket.add_smul,
      pauliYPhase_add_flip]
  simp


-- @@ L188-197 verbatim
/-- Same-site anticommutator `{X_j, Z_j} = 0`. -/
theorem localPauliX_anticomm_localPauliZ {N : ℕ} (j : Fin N) :
    localPauliX j * localPauliZ j + localPauliZ j * localPauliX j = 0 := by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  rw [add_op_mul_ket, zero_mul_basisKet,
      op_mul_op_mul_ket, localPauliZ_on_basis, op_mul_smul_ket, localPauliX_on_basis,
      op_mul_op_mul_ket, localPauliX_on_basis, localPauliZ_on_basis,
      flipBitAt_apply_same, ← Ket.add_smul, pauliZ_diag_flip, add_neg_cancel]
  simp


-- @@ L199-217 expanded
/-- Same-site anticommutator `{Y_j, Z_j} = 0`. -/
theorem localPauliY_anticomm_localPauliZ {N : ℕ} (j : Fin N) :
    localPauliY j * localPauliZ j + localPauliZ j * localPauliY j = 0 :=
  by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  rw [add_op_mul_ket, zero_mul_basisKet, op_mul_op_mul_ket, localPauliZ_on_basis, op_mul_smul_ket,
    localPauliY_on_basis, Ket.smul_smul, op_mul_op_mul_ket, localPauliY_on_basis, op_mul_smul_ket,
    localPauliZ_on_basis, flipBitAt_apply_same, Ket.smul_smul, ← Ket.add_smul]
  rw [show
      pauliZ (z j) (z j) * pauliYPhase (z j) +
          pauliYPhase (z j) * pauliZ (flipBit (z j)) (flipBit (z j)) =
        pauliYPhase (z j) * (pauliZ (z j) (z j) + pauliZ (flipBit (z j)) (flipBit (z j)))
      by ring,
    pauliZ_diag_flip, add_neg_cancel, mul_zero]
  simp
    -- ----------------------------------------------------------------------------
    -- Subsection: Cross-site commutation of single-site Paulis
    -- ----------------------------------------------------------------------------


-- @@ L219-226 verbatim
/-!
Two single-site Pauli operators on distinct sites commute. We package each
Pauli's computational-basis action in the common shape
`P_j |z⟩ = sc (z j) • |perm z j⟩` where `perm` only touches bit `j` (`Z` uses the
trivial permutation `fun z _ ↦ z`, `X`/`Y` use `flipBitAt`), and prove a single
generic commutation lemma. The nine cross-site Pauli commutations are then
specializations.
-/


-- @@ L228-254 verbatim
/-- Generic cross-site commutation: if two operators `A`, `B` act on
computational-basis kets as local scalings/permutations at sites `j` and `k`
respectively, with permutations that only touch their own site and commute for
distinct sites, then `A` and `B` commute when `j ≠ k`.

The hypotheses encode:
* `hA`/`hB` — the basis action `P * |z⟩ = sc (z m) • |perm z⟩`;
* `hpermA_same`/`hpermB_same` — the permutation only changes its own bit;
* `hpermA_off`/`hpermB_off` — the permutation fixes every other bit.
-/
theorem localPauli_cross_commute {N : ℕ} {A B : NQubitOp N} {j k : Fin N}
    {scA scB : Fin 2 → ℂ} {permA permB : BitString N → BitString N}
    (hjk : j ≠ k)
    (hA : ∀ z : BitString N, A * computationalBasisKet N z =
      scA (z j) • computationalBasisKet N (permA z))
    (hB : ∀ z : BitString N, B * computationalBasisKet N z =
      scB (z k) • computationalBasisKet N (permB z))
    (hpermA_off : ∀ (z : BitString N) (i : Fin N), i ≠ j → permA z i = z i)
    (hpermB_off : ∀ (z : BitString N) (i : Fin N), i ≠ k → permB z i = z i)
    (hcomm : ∀ z : BitString N, permA (permB z) = permB (permA z)) :
    A * B = B * A := by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  rw [op_mul_op_mul_ket, hB, op_mul_smul_ket, hA,
      op_mul_op_mul_ket, hA, op_mul_smul_ket, hB,
      Ket.smul_smul, Ket.smul_smul]
  rw [hpermA_off z k hjk.symm, hpermB_off z j hjk, hcomm z, mul_comm]



-- @@ L257-261 verbatim
/-- Pauli `X` basis action in canonical scalar/perm shape (bare `flipBitAt z j`). -/
private theorem hX_act {N : ℕ} (j : Fin N) :
    ∀ z : BitString N, localPauliX j * computationalBasisKet N z =
      (fun _ : Fin 2 => (1 : ℂ)) (z j) • computationalBasisKet N (flipBitAt z j) :=
  fun z => by rw [localPauliX_on_basis]; simp


-- @@ L263-267 verbatim
/-- Pauli `Y` basis action in canonical scalar/perm shape (bare `flipBitAt z j`). -/
private theorem hY_act {N : ℕ} (j : Fin N) :
    ∀ z : BitString N, localPauliY j * computationalBasisKet N z =
      pauliYPhase (z j) • computationalBasisKet N (flipBitAt z j) :=
  fun z => localPauliY_on_basis j z


-- @@ L269-273 expanded
/-- Pauli `Z` basis action in canonical scalar/perm shape (identity perm). -/
private theorem hZ_act {N : ℕ} (j : Fin N) :
    ∀ z : BitString N,
      localPauliZ j * computationalBasisKet N z =
        (fun b => pauliZ b b) (z j) • computationalBasisKet N z :=
  fun z => localPauliZ_on_basis j z


-- @@ L275-277 verbatim
private theorem flip_off {N : ℕ} (j : Fin N) :
    ∀ (z : BitString N) (i : Fin N), i ≠ j → flipBitAt z j i = z i :=
  fun z _ hi => flipBitAt_apply_of_ne z hi


-- @@ L279-281 verbatim
private theorem id_off {N : ℕ} (j : Fin N) :
    ∀ (z : BitString N) (i : Fin N), i ≠ j → z i = z i :=
  fun _ _ _ => rfl


-- @@ L283-289 verbatim
/-- Cross-site commutation `[X_j, X_k] = 0` for `j ≠ k`. -/
theorem localPauliX_commute_localPauliX {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    localPauliX j * localPauliX k = localPauliX k * localPauliX j :=
  localPauli_cross_commute (scA := fun _ => 1) (scB := fun _ => 1)
    (permA := fun z => flipBitAt z j) (permB := fun z => flipBitAt z k) hjk
    (hX_act j) (hX_act k) (flip_off j) (flip_off k)
    (fun z => flipBitAt_comm z hjk.symm)


-- @@ L291-297 verbatim
/-- Cross-site commutation `[X_j, Y_k] = 0` for `j ≠ k`. -/
theorem localPauliX_commute_localPauliY {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    localPauliX j * localPauliY k = localPauliY k * localPauliX j :=
  localPauli_cross_commute (scA := fun _ => 1) (scB := pauliYPhase)
    (permA := fun z => flipBitAt z j) (permB := fun z => flipBitAt z k) hjk
    (hX_act j) (hY_act k) (flip_off j) (flip_off k)
    (fun z => flipBitAt_comm z hjk.symm)


-- @@ L299-305 expanded
/-- Cross-site commutation `[X_j, Z_k] = 0` for `j ≠ k`. -/
theorem localPauliX_commute_localPauliZ {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    localPauliX j * localPauliZ k = localPauliZ k * localPauliX j :=
  localPauli_cross_commute (scA := fun _ => 1) (scB := fun b => pauliZ b b) (permA := fun z =>
    flipBitAt z j) (permB := fun z => z) hjk (hX_act j) (hZ_act k) (flip_off j) (id_off k)
    (fun _ => rfl)


-- @@ L307-313 verbatim
/-- Cross-site commutation `[Y_j, X_k] = 0` for `j ≠ k`. -/
theorem localPauliY_commute_localPauliX {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    localPauliY j * localPauliX k = localPauliX k * localPauliY j :=
  localPauli_cross_commute (scA := pauliYPhase) (scB := fun _ => 1)
    (permA := fun z => flipBitAt z j) (permB := fun z => flipBitAt z k) hjk
    (hY_act j) (hX_act k) (flip_off j) (flip_off k)
    (fun z => flipBitAt_comm z hjk.symm)


-- @@ L315-321 verbatim
/-- Cross-site commutation `[Y_j, Y_k] = 0` for `j ≠ k`. -/
theorem localPauliY_commute_localPauliY {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    localPauliY j * localPauliY k = localPauliY k * localPauliY j :=
  localPauli_cross_commute (scA := pauliYPhase) (scB := pauliYPhase)
    (permA := fun z => flipBitAt z j) (permB := fun z => flipBitAt z k) hjk
    (hY_act j) (hY_act k) (flip_off j) (flip_off k)
    (fun z => flipBitAt_comm z hjk.symm)


-- @@ L323-329 expanded
/-- Cross-site commutation `[Y_j, Z_k] = 0` for `j ≠ k`. -/
theorem localPauliY_commute_localPauliZ {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    localPauliY j * localPauliZ k = localPauliZ k * localPauliY j :=
  localPauli_cross_commute (scA := pauliYPhase) (scB := fun b => pauliZ b b) (permA := fun z =>
    flipBitAt z j) (permB := fun z => z) hjk (hY_act j) (hZ_act k) (flip_off j) (id_off k)
    (fun _ => rfl)


-- @@ L331-337 expanded
/-- Cross-site commutation `[Z_j, X_k] = 0` for `j ≠ k`. -/
theorem localPauliZ_commute_localPauliX {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    localPauliZ j * localPauliX k = localPauliX k * localPauliZ j :=
  localPauli_cross_commute (scA := fun b => pauliZ b b) (scB := fun _ => 1) (permA := fun z => z)
    (permB := fun z => flipBitAt z k) hjk (hZ_act j) (hX_act k) (id_off j) (flip_off k)
    (fun _ => rfl)


-- @@ L339-345 expanded
/-- Cross-site commutation `[Z_j, Y_k] = 0` for `j ≠ k`. -/
theorem localPauliZ_commute_localPauliY {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    localPauliZ j * localPauliY k = localPauliY k * localPauliZ j :=
  localPauli_cross_commute (scA := fun b => pauliZ b b) (scB := pauliYPhase) (permA := fun z => z)
    (permB := fun z => flipBitAt z k) hjk (hZ_act j) (hY_act k) (id_off j) (flip_off k)
    (fun _ => rfl)


-- @@ L347-353 expanded
/-- Cross-site commutation `[Z_j, Z_k] = 0` for `j ≠ k`. -/
theorem localPauliZ_commute_localPauliZ {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    localPauliZ j * localPauliZ k = localPauliZ k * localPauliZ j :=
  localPauli_cross_commute (scA := fun b => pauliZ b b) (scB := fun b => pauliZ b b) (permA :=
    fun z => z) (permB := fun z => z) hjk (hZ_act j) (hZ_act k) (id_off j) (id_off k) (fun _ => rfl)


-- @@ L355-355 verbatim
end


-- @@ L357-357 verbatim
end QAOA.IsingChain.JordanWigner
