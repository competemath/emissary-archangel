import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.LayerBlockMatch
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.FGGClosure


-- @@ L4-26 verbatim
/-!
# NoncommProd Block Calculus — `windowBlock` of a `noncommProd`, cross-dimension generator block-match

This file builds the cross-dimension `noncommProd` block calculus needed to close
the two FGG §III generator-block-match lemmas (`mixer_factor_block_match`,
`cost_factor_block_match`) of `CanonicalMatching.lean`.

The mechanism is:

* `windowBlock_noncommProd` — push `windowBlock` through a `noncommProd` of
  factors **all tensor-supported on the window** `W`, via `windowBlock_mul`
  (block multiplicativity) by `Finset.cons_induction`. The block of the product
  is the `noncommProd` of the blocks (computed entirely in dimension `m`).

* `windowBlock_noncommProd_reindex` — combine the above with a reindexing of the
  index `Finset` (a subset of `Fin N` that is the `windowEquiv`-image of the
  offsets) and a per-offset block match `windowBlock ε (G (windowEquiv … o)) =
  H o`, so the whole product block is a `noncommProd` over `Fin (2P+2)` of the
  chain-independent per-offset block `H`. Both chains then yield the **same**
  offset-indexed `noncommProd`, hence equal blocks.

Source: FGG arXiv:1411.4028v1 §II l.130–135, §III.
-/


-- @@ L28-28 verbatim
namespace QAOA.IsingChain.UpperBound.LightCone


-- @@ L30-30 verbatim
open Quantum.Operators

-- @@ L31-31 verbatim
open Quantum.Gates

-- @@ L32-32 verbatim
open scoped BigOperators


-- @@ L34-38 verbatim
noncomputable section

-- ============================================================================
-- Section: `windowBlock` of a `noncommProd` (window-supported factors)
-- ============================================================================


-- @@ L40-93 verbatim
/-- **`windowBlock` of a `noncommProd`.** For a finite index set `s` and a
family `f` whose every value `f k` (for `k ∈ s`) is tensor-supported on the
window `W` (card `m` via `ε`), the block of the noncomm product is the noncomm
product of the blocks, computed entirely in dimension `m`.

Proof: `Finset.cons_induction` on `s`, using `windowBlock_mul` (block
multiplicativity) for the cons step and `windowBlock_one` for the base. Block
multiplicativity needs the *tail product* tensor-supported on `W`, which follows
from `tensorSupportedOn_noncommProd` collapsed via `Finset.biUnion_subset`. -/
theorem windowBlock_noncommProd {N m : ℕ} {W : Finset (Fin N)} (ε : Fin m ≃ W)
    {ι : Type*} (s : Finset ι) (f : ι → Qubits.NQubitOp N)
    (comm : (s : Set ι).Pairwise (Function.onFun Commute f))
    (hsupp : ∀ k ∈ s, tensorSupportedOn W (f k)) :
    windowBlock ε (s.noncommProd f comm) =
      s.noncommProd (fun k => windowBlock ε (f k))
        (fun i hi j hj hij =>
          show Commute (windowBlock ε (f i)) (windowBlock ε (f j)) by
            have hc : Commute (f i) (f j) := comm hi hj hij
            have hfi := hsupp i hi
            have hfj := hsupp j hj
            -- Commute lifts through `windowBlock` since it is multiplicative on
            -- window-supported factors.
            unfold Commute SemiconjBy
            rw [← windowBlock_mul ε hfi hfj, ← windowBlock_mul ε hfj hfi]
            exact congrArg (windowBlock ε) hc) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.noncommProd_empty]
    exact windowBlock_one ε
  | @insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
        Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    -- The tail product is tensor-supported on `W`.
    have htail : tensorSupportedOn W
        (s.noncommProd f (comm.mono (by
          intro x hx; exact Finset.mem_insert_of_mem hx))) := by
      have hbi := tensorSupportedOn_noncommProd s f (fun _ => W)
        (comm.mono (by intro x hx; exact Finset.mem_insert_of_mem hx))
        (fun k hk => hsupp k (Finset.mem_insert_of_mem hk))
      -- `s.biUnion (fun _ => W) ⊆ W`, so transport the support.
      refine tensorSupportedOn_mono ?_ hbi
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨i, _, hxW⟩ := hx
      exact hxW
    rw [windowBlock_mul ε (hsupp a (Finset.mem_insert_self a s)) htail]
    congr 1
    exact ih (comm.mono (by intro x hx; exact Finset.mem_insert_of_mem hx))
      (fun k hk => hsupp k (Finset.mem_insert_of_mem hk))

-- ============================================================================
-- Section: `noncommProd` reindexing along a `Finset.map`
-- ============================================================================


-- @@ L95-114 verbatim
/-- **`noncommProd` over a `Finset.map`.** Reindex a noncomm product over the
embedded image `s.map e` of an embedding `e : ι ↪ κ` as a product over `s` of
the precomposed family. The proof unfolds `Finset.noncommProd` to its underlying
multiset and uses `Finset.map_val` + `Multiset.map_map`. -/
theorem noncommProd_map_embedding {ι κ β : Type*} [Monoid β] (e : ι ↪ κ)
    (s : Finset ι) (g : κ → β)
    (comm : ((s.map e : Finset κ) : Set κ).Pairwise (Function.onFun Commute g)) :
    (s.map e).noncommProd g comm =
      s.noncommProd (fun i => g (e i))
        (fun _ hi _ hj hij =>
          comm (Finset.mem_map_of_mem e hi) (Finset.mem_map_of_mem e hj)
            (fun h => hij (e.injective h))) := by
  unfold Finset.noncommProd
  congr 1
  rw [Finset.map_val, Multiset.map_map]
  rfl

-- ============================================================================
-- Section: matrix entry of a single local Pauli `X`
-- ============================================================================


-- @@ L116-143 verbatim
/-- The matrix entry of `localPauliX j` in the computational basis: column
`bitStringEquiv z` is the basis vector `|flipBitAt z j⟩`, so the `(ix, be z)`
entry is `1` iff `ix` indexes `flipBitAt z j`. -/
theorem localPauliX_matrix_entry {N : ℕ} (j : Fin N) (z : Qubits.BitString N)
    (ix : Fin (Qubits.NQubitDim N)) :
    Qubits.localPauliX j ix ((Qubits.bitStringEquiv N) z) =
      (if (Qubits.bitStringEquiv N) (Qubits.flipBitAt z j) = ix then 1 else 0) := by
  have hbasis := Qubits.localPauliX_on_basis j z
  have hvec := congrArg (fun (k : Quantum.Operators.Ket _) => k.vec ix) hbasis
  simp only [Quantum.Operators.op_mul_ket_vec, Qubits.computationalBasisKet,
    Quantum.Operators.stdKet_apply] at hvec
  -- LHS of hvec: (localPauliX j).mulVec (stdKet (be z)).vec ix
  --            = ∑ k, (localPauliX j) ix k * (if be z = k then 1 else 0)
  --            = (localPauliX j) ix (be z).
  rw [show (Qubits.localPauliX j).mulVec
        (Quantum.Operators.stdKet (Qubits.NQubitDim N) ((Qubits.bitStringEquiv N) z)).vec ix =
        Qubits.localPauliX j ix ((Qubits.bitStringEquiv N) z) from by
      rw [Matrix.mulVec]
      simp only [Quantum.Operators.stdKet_apply, dotProduct]
      rw [Finset.sum_eq_single ((Qubits.bitStringEquiv N) z)]
      · rw [if_pos rfl, mul_one]
      · intro b _ hb; rw [if_neg (fun h => hb h.symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h] at hvec
  rw [hvec]

-- ============================================================================
-- Section: block transport of a single window Pauli `X`
-- ============================================================================


-- @@ L145-242 verbatim
/-- **Block of a window Pauli `X` is the offset Pauli `X`.** For a site
`ε o` inside the window `W` (card `m` via `ε`), the window block of the single-
site Pauli `X` at that site equals the dimension-`m` Pauli `X` at the offset
`o`. The block-flip at `ε o` corresponds exactly to a bit-flip at offset `o`
through the window-data identification, independent of the ambient chain. -/
theorem windowBlock_localPauliX {N m : ℕ} {W : Finset (Fin N)} (ε : Fin m ≃ W)
    (o : Fin m) :
    windowBlock ε (Qubits.localPauliX ((ε o : Fin N))) = Qubits.localPauliX o := by
  classical
  funext a b
  -- Rewrite `b` as the encoding of its decoded bitstring.
  obtain ⟨zb, rfl⟩ : ∃ zb, (Qubits.bitStringEquiv m) zb = b :=
    ⟨(Qubits.bitStringEquiv m).symm b, by rw [Equiv.apply_symm_apply]⟩
  unfold windowBlock restrictedMatrixEntry
  -- Full-chain side: the entry of `localPauliX (ε o)` at the encoded extensions.
  rw [localPauliX_matrix_entry (ε o : Fin N)
        (extendByZeroOnS W (windowData ε ((Qubits.bitStringEquiv m) zb)))]
  rw [localPauliX_matrix_entry o zb]
  -- Both `if` conditions are equivalent: the window-data flip at `ε o` matches
  -- the offset flip at `o`.
  have hbitstring :
      Qubits.flipBitAt (extendByZeroOnS W (windowData ε ((Qubits.bitStringEquiv m) zb)))
          (ε o : Fin N) =
        extendByZeroOnS W (windowData ε ((Qubits.bitStringEquiv m) (Qubits.flipBitAt zb o))) := by
    funext k
    -- LHS: `flipBitAt X (εo) k = if k = εo then flipBit (X k) else X k`.
    change (if k = (ε o : Fin N) then Qubits.flipBit _ else _) = _
    by_cases hk : k ∈ W
    · -- inside the window: read through `ε.symm k`.
      rw [extendByZeroOnS_apply_mem (h := hk)]
      by_cases hko : k = (ε o : Fin N)
      · -- the flipped site.
        rw [if_pos hko]
        have hsym : ε.symm ⟨k, hk⟩ = o := by
          apply ε.injective
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext hko
        change Qubits.flipBit (windowData ε ((Qubits.bitStringEquiv m) zb) ⟨k, hk⟩) =
          extendByZeroOnS W
            (windowData ε ((Qubits.bitStringEquiv m) (Qubits.flipBitAt zb o))) k
        rw [extendByZeroOnS_apply_mem (h := hk)]
        unfold windowData
        rw [hsym, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
            Qubits.flipBitAt, if_pos rfl]
      · rw [if_neg hko]
        have hsym : ε.symm ⟨k, hk⟩ ≠ o := by
          intro hc
          apply hko
          have : ε (ε.symm ⟨k, hk⟩) = ε o := by rw [hc]
          rw [Equiv.apply_symm_apply] at this
          exact congrArg Subtype.val this
        change windowData ε ((Qubits.bitStringEquiv m) zb) ⟨k, hk⟩ =
          extendByZeroOnS W
            (windowData ε ((Qubits.bitStringEquiv m) (Qubits.flipBitAt zb o))) k
        rw [extendByZeroOnS_apply_mem (h := hk)]
        unfold windowData
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply,
            Qubits.flipBitAt, if_neg hsym]
    · -- outside the window: both extensions are `0`, flip leaves it (since
      -- `ε o ∈ W`, so `k ≠ ε o`).
      have hkne : k ≠ (ε o : Fin N) := by
        intro hc; exact hk (hc ▸ (ε o).2)
      rw [if_neg hkne,
          extendByZeroOnS_apply_not_mem (h := hk),
          extendByZeroOnS_apply_not_mem (h := hk)]
  -- Now match the two `if` conditions. Both reduce to
  -- `bitStringEquiv m (flipBitAt zb o) = a` via injectivity of the encodings
  -- and `windowDataEquiv`.
  rw [hbitstring]
  -- The condition equivalence.
  have hcond_iff :
      ((Qubits.bitStringEquiv N) (extendByZeroOnS W
          (windowData ε ((Qubits.bitStringEquiv m) (Qubits.flipBitAt zb o)))) =
        (Qubits.bitStringEquiv N) (extendByZeroOnS W (windowData ε a))) ↔
      ((Qubits.bitStringEquiv m) (Qubits.flipBitAt zb o) = a) := by
    constructor
    · intro h
      have h1 := (Qubits.bitStringEquiv N).injective h
      have h2 : windowData ε ((Qubits.bitStringEquiv m) (Qubits.flipBitAt zb o)) =
          windowData ε a := by
        funext k
        have := congrFun h1 (k : Fin N)
        rwa [extendByZeroOnS_apply_mem (h := k.2),
            extendByZeroOnS_apply_mem (h := k.2)] at this
      -- `windowData ε x = windowData ε y → x = y` via `windowDataEquiv` injective.
      have h3 : windowDataEquiv ε ((Qubits.bitStringEquiv m) (Qubits.flipBitAt zb o)) =
          windowDataEquiv ε a := by
        rw [windowDataEquiv_apply, windowDataEquiv_apply]; exact h2
      exact (windowDataEquiv ε).injective h3
    · intro h; rw [h]
  by_cases hcond :
      (Qubits.bitStringEquiv m) (Qubits.flipBitAt zb o) = a
  · rw [if_pos (hcond_iff.mpr hcond), if_pos hcond]
  · rw [if_neg (fun h => hcond (hcond_iff.mp h)), if_neg hcond]

-- ============================================================================
-- Section: matrix entry and block transport of a single local Pauli `Z`
-- ============================================================================


-- @@ L244-267 expanded
/-- The matrix entry of `localPauliZ j` in the computational basis: it acts
diagonally with eigenvalue `Z (z j) (z j)` on the basis ket `|z⟩`. -/
theorem localPauliZ_matrix_entry {N : ℕ} (j : Fin N) (z : Qubits.BitString N)
    (ix : Fin (Qubits.NQubitDim N)) :
    Qubits.localPauliZ j ix ((Qubits.bitStringEquiv N) z) =
      (if (Qubits.bitStringEquiv N) z = ix then pauliZ (z j) (z j) else 0) :=
  by
  have hbasis := Qubits.localPauliZ_on_basis j z
  have hvec := congrArg (fun (k : Quantum.Operators.Ket _) => k.vec ix) hbasis
  simp only [Quantum.Operators.op_mul_ket_vec, Qubits.computationalBasisKet,
    Quantum.Operators.Ket.smul_vec] at hvec
  rw [show
      (Qubits.localPauliZ j).mulVec
          (Quantum.Operators.stdKet (Qubits.NQubitDim N) ((Qubits.bitStringEquiv N) z)).vec ix =
        Qubits.localPauliZ j ix ((Qubits.bitStringEquiv N) z)
      from by
      rw [Matrix.mulVec]
      simp only [Quantum.Operators.stdKet_apply, dotProduct]
      rw [Finset.sum_eq_single ((Qubits.bitStringEquiv N) z)]
      · rw [if_pos rfl, mul_one]
      · intro b _ hb; rw [if_neg (fun h => hb h.symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h] at hvec
  rw [hvec]
  simp only [Quantum.Operators.stdKet_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hcond : (Qubits.bitStringEquiv N) z = ix
  · rw [if_pos hcond, if_pos hcond, mul_one]
  · rw [if_neg hcond, if_neg hcond, mul_zero]


-- @@ L269-318 verbatim
/-- **Block of a window Pauli `Z` is the offset Pauli `Z`.** For a site `ε o`
inside the window `W`, the window block of `localPauliZ (ε o)` equals the
dimension-`m` Pauli `Z` at the offset `o`. The eigenvalue read at site `ε o`
through the window-data identification is the bit at offset `o`, independent of
the ambient chain. -/
theorem windowBlock_localPauliZ {N m : ℕ} {W : Finset (Fin N)} (ε : Fin m ≃ W)
    (o : Fin m) :
    windowBlock ε (Qubits.localPauliZ ((ε o : Fin N))) = Qubits.localPauliZ o := by
  classical
  funext a b
  obtain ⟨zb, rfl⟩ : ∃ zb, (Qubits.bitStringEquiv m) zb = b :=
    ⟨(Qubits.bitStringEquiv m).symm b, by rw [Equiv.apply_symm_apply]⟩
  unfold windowBlock restrictedMatrixEntry
  rw [localPauliZ_matrix_entry (ε o : Fin N)
        (extendByZeroOnS W (windowData ε ((Qubits.bitStringEquiv m) zb)))]
  rw [localPauliZ_matrix_entry o zb]
  -- The eigenvalue: read the bit at site `ε o` through the window data = bit at
  -- offset `o`.
  have heig : extendByZeroOnS W (windowData ε ((Qubits.bitStringEquiv m) zb))
      (ε o : Fin N) = zb o := by
    rw [extendByZeroOnS_apply_mem (h := (ε o).2)]
    unfold windowData
    rw [show (⟨(ε o : Fin N), (ε o).2⟩ : ↥W) = ε o from rfl,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [heig]
  -- The diagonal condition: encodings agree iff offsets agree.
  have hcond_iff :
      ((Qubits.bitStringEquiv N) (extendByZeroOnS W
          (windowData ε ((Qubits.bitStringEquiv m) zb))) =
        (Qubits.bitStringEquiv N) (extendByZeroOnS W (windowData ε a))) ↔
      ((Qubits.bitStringEquiv m) zb = a) := by
    constructor
    · intro h
      have h1 := (Qubits.bitStringEquiv N).injective h
      have h2 : windowData ε ((Qubits.bitStringEquiv m) zb) = windowData ε a := by
        funext k
        have := congrFun h1 (k : Fin N)
        rwa [extendByZeroOnS_apply_mem (h := k.2),
            extendByZeroOnS_apply_mem (h := k.2)] at this
      have h3 : windowDataEquiv ε ((Qubits.bitStringEquiv m) zb) = windowDataEquiv ε a := by
        rw [windowDataEquiv_apply, windowDataEquiv_apply]; exact h2
      exact (windowDataEquiv ε).injective h3
    · intro h; rw [h]
  by_cases hcond : (Qubits.bitStringEquiv m) zb = a
  · rw [if_pos (hcond_iff.mpr hcond), if_pos hcond]
  · rw [if_neg (fun h => hcond (hcond_iff.mp h)), if_neg hcond]

-- ============================================================================
-- Section: block transport of a single mixer factor
-- ============================================================================


-- @@ L320-338 verbatim
/-- **Block of a window mixer factor is the offset mixer factor.** For a site
`ε o` inside the window `W`, the window block of the single-site mixer
exponential `exp(-iβ X_{ε o})` equals the dimension-`m` mixer exponential
`exp(-iβ X_o)` at the offset `o`. Proof: closed form `exp(-iβ X) = cos β · 1 -
i sin β · X` + linearity of `windowBlock` + `windowBlock_localPauliX`. -/
theorem windowBlock_mixerFactor {N m : ℕ} {W : Finset (Fin N)} (ε : Fin m ≃ W)
    (o : Fin m) (β : ℝ) :
    windowBlock ε
        (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) •
          Qubits.localPauliX ((ε o : Fin N)))) =
      NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX o) := by
  rw [QAOA.exp_localPauliX, QAOA.exp_localPauliX]
  unfold QAOA.localMixerFactor
  rw [windowBlock_add, windowBlock_smul, windowBlock_smul, windowBlock_one,
      windowBlock_localPauliX]

-- ============================================================================
-- Section: the window embedding `Fin m ↪ Fin N` and its image
-- ============================================================================


-- @@ L340-342 verbatim
/-- The composite embedding `Fin m ↪ ↥W ↪ Fin N` induced by `ε : Fin m ≃ ↥W`. -/
def windowEmbedding {N m : ℕ} {W : Finset (Fin N)} (ε : Fin m ≃ W) : Fin m ↪ Fin N :=
  ε.toEmbedding.trans (Function.Embedding.subtype (· ∈ W))


-- @@ L344-345 verbatim
@[simp] theorem windowEmbedding_apply {N m : ℕ} {W : Finset (Fin N)} (ε : Fin m ≃ W)
    (o : Fin m) : windowEmbedding ε o = (ε o : Fin N) := rfl


-- @@ L347-362 verbatim
/-- The image of the window embedding is the window `W` itself. -/
theorem windowEmbedding_map_univ {N m : ℕ} {W : Finset (Fin N)} (ε : Fin m ≃ W)
    (hcard : Fintype.card (Fin m) = W.card) :
    (Finset.univ : Finset (Fin m)).map (windowEmbedding ε) = W := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨o, _, hox⟩ := hx
    rw [← hox, windowEmbedding_apply]
    exact (ε o).2
  · rw [Finset.card_map, Finset.card_univ, hcard]

-- ============================================================================
-- Section: `windowBlock` of `mixerTouchingProd` as an offset `noncommProd`
-- ============================================================================


-- @@ L364-397 verbatim
/-- **`windowBlock` of `mixerTouchingProd` is the offset mixer product.** For a
window `W` (card `m` via `ε`), the window block of the mixer touching-product
over `W` equals the `noncommProd` over the offsets `Fin m` of the offset mixer
factors `exp(-iβ X_o)` — entirely chain-independent. -/
theorem windowBlock_mixerTouchingProd {N m : ℕ} {W : Finset (Fin N)}
    (ε : Fin m ≃ W) (hcard : Fintype.card (Fin m) = W.card) (β : ℝ) :
    windowBlock ε (mixerTouchingProd W β) =
      (Finset.univ : Finset (Fin m)).noncommProd
        (fun o => NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX o))
        (fun i _ j _ _ =>
          (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp) := by
  classical
  unfold mixerTouchingProd
  -- The mixer touching set `{j | j ∈ W}` is the window `W`.
  have hfilter : (Finset.univ.filter (fun j : Fin N => j ∈ W)) = W := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  -- Push `windowBlock` through the product (all factors window-supported).
  rw [windowBlock_noncommProd ε _ _ _ (by
        intro k hk
        rw [hfilter] at hk
        refine tensorSupportedOn_mono (S := ({k} : Finset (Fin N))) ?_
          (tensorSupportedOn_exp_localPauliX β k)
        intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact hk)]
  -- Rewrite the index set to the embedded image of the offsets, then reindex.
  rw [Finset.noncommProd_congr (hfilter.trans (windowEmbedding_map_univ ε hcard).symm)
        (fun _ _ => rfl)]
  rw [noncommProd_map_embedding (windowEmbedding ε) Finset.univ]
  -- Per-offset block match.
  exact Finset.noncommProd_congr rfl
    (fun o _ => by rw [windowEmbedding_apply]; exact windowBlock_mixerFactor ε o β) _

-- ============================================================================
-- Section: block transport of a single cost bond / cost factor
-- ============================================================================


-- @@ L399-421 verbatim
/-- **Block of a window cost bond is the offset cost bond.** For a bond `ε o`
whose right endpoint `nextSite (ε o)` is the window site at the offset
`nextSite o` (i.e. the window respects adjacency at `o`), the window block of
`chainPairInteraction (ε o) = Z_{ε o} Z_{nextSite (ε o)}` equals the
dimension-`m` cost bond `chainPairInteraction o`, via block multiplicativity and
the single-site `Z` block transport. -/
theorem windowBlock_chainPairInteraction {N m : ℕ} {W : Finset (Fin N)}
    (ε : Fin m ≃ W) (o : Fin m)
    (hnext : IsingModel.nextSite ((ε o : Fin N)) = (ε (IsingModel.nextSite o) : Fin N)) :
    windowBlock ε (IsingModel.chainPairInteraction ((ε o : Fin N))) =
      IsingModel.chainPairInteraction o := by
  unfold IsingModel.chainPairInteraction
  rw [hnext]
  rw [windowBlock_mul ε
        (tensorSupportedOn_mono (S := ({(ε o : Fin N)} : Finset (Fin N)))
          (by intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact (ε o).2)
          (tensorSupportedOn_localPauliZ _))
        (tensorSupportedOn_mono
          (S := ({(ε (IsingModel.nextSite o) : Fin N)} : Finset (Fin N)))
          (by intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]
              exact (ε (IsingModel.nextSite o)).2)
          (tensorSupportedOn_localPauliZ _))]
  rw [windowBlock_localPauliZ, windowBlock_localPauliZ]


-- @@ L423-439 verbatim
/-- **Block of a window cost factor is the offset cost factor.** For a bond
`ε o` with right endpoint at offset `nextSite o`, the window block of the cost
exponential `exp(-iγ chainPairInteraction (ε o))` equals the dimension-`m` cost
exponential `exp(-iγ chainPairInteraction o)`. Proof: closed form + linearity +
the bond block transport. -/
theorem windowBlock_costFactor {N m : ℕ} {W : Finset (Fin N)} (ε : Fin m ≃ W)
    (o : Fin m)
    (hnext : IsingModel.nextSite ((ε o : Fin N)) = (ε (IsingModel.nextSite o) : Fin N))
    (γ : ℝ) :
    windowBlock ε
        (NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction ((ε o : Fin N)))) =
      NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
        IsingModel.chainPairInteraction o) := by
  rw [exp_chainPairInteraction_closed_form, exp_chainPairInteraction_closed_form]
  rw [windowBlock_add, windowBlock_smul, windowBlock_smul, windowBlock_one,
      windowBlock_chainPairInteraction ε o hnext]


-- @@ L441-441 verbatim
end


-- @@ L443-443 verbatim
end QAOA.IsingChain.UpperBound.LightCone
