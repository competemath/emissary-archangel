/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.SymmEncAlg.Defs
public import VCVio.EvalDist.Prod
public import VCVio.OracleComp.ProbComp


-- @@ L12-28 verbatim
/-!
# Symmetric Encryption Schemes

This file gives the discrete-probability-facing correctness and perfect-secrecy predicates for
`SymmEncAlg m M K C`.

The struct follows the same pattern as `AsymmEncAlg`, `KEMScheme`, `MacAlg`, etc.: it is
parameterized by an ambient monad `m` and uses plain `Type` parameters. Asymptotic security
statements are expressed externally by quantifying over a family
`(sp : ℕ) → SymmEncAlg m (M sp) (K sp) (C sp)`.

Perfect secrecy is captured by `perfectSecrecyAt` (the canonical independence form), with
equivalent formulations `perfectSecrecyPosteriorEqPriorAt` (cross-multiplied posterior/prior
form) and `perfectSecrecyJointFactorizationAt` (factorization with named marginals); the
`_iff_` lemmas record the equivalences. `perfectSecrecyAtAllPriors` is the strong PMF-level
quantification, equivalent to `ciphertextRowsEqualAt` over finite message spaces.
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
universe u


-- @@ L34-34 verbatim
open OracleComp ENNReal


-- @@ L36-36 verbatim
namespace SymmEncAlg


-- @@ L38-38 verbatim
variable {m : Type → Type u} [Monad m] {M K C : Type}


-- @@ L40-43 expanded
/-- An encryption scheme is complete if decryption recovers every message with
probability `1`. -/
def Complete [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ msg : M, probOutput (encAlg.CompleteExp msg) msg = 1


-- @@ L45-45 verbatim
section perfectSecrecy


-- @@ L47-48 verbatim
variable [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
  [MonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L50-59 expanded
omit [MonadLiftT m SetM] [EvalDistCompatible m] in
lemma probOutput_PerfectSecrecyExp_eq_mul_cipherGivenMsg [LawfulMonad m]
    (encAlg : SymmEncAlg m M K C) (mgen : m M) (msg : M) (σ : C) :
    probOutput (encAlg.PerfectSecrecyExp mgen) (msg, σ) =
      probOutput mgen msg * probOutput (encAlg.PerfectSecrecyCipherGivenMsgExp msg) σ :=
  by
  have : DecidableEq M := Classical.decEq M
  rw [encAlg.PerfectSecrecyExp_eq_bind mgen, probOutput_bind_eq_tsum,
    tsum_eq_single msg fun msg' hmsg' => by simp [Ne.symm hmsg']]
  simp


-- @@ L61-68 expanded
omit [MonadLiftT m SetM] [EvalDistCompatible m] in
lemma probOutput_PerfectSecrecyCipherExp_eq_tsum [LawfulMonad m] (encAlg : SymmEncAlg m M K C)
    (mgen : m M) (σ : C) :
    probOutput (encAlg.PerfectSecrecyCipherExp mgen) σ =
      ∑' msg : M, probOutput mgen msg * probOutput (encAlg.PerfectSecrecyCipherGivenMsgExp msg) σ :=
  by rw [encAlg.PerfectSecrecyCipherExp_eq_bind mgen, probOutput_bind_eq_tsum]


-- @@ L70-75 expanded
/-- Strong perfect secrecy: ciphertexts are independent of messages
for every prior distribution on messages (PMF-level quantification). -/
def perfectSecrecyAtAllPriors (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ (μ : PMF M) (msg : M) (σ : C),
    let row := fun x : M => probOutput (encAlg.PerfectSecrecyCipherGivenMsgExp x) σ
    μ msg * row msg = μ msg * (∑' x : M, μ x * row x)


-- @@ L77-82 expanded
/-- Equivalent channel-style formulation: every message induces the same ciphertext
distribution. -/
def ciphertextRowsEqualAt (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ (msg₀ msg₁ : M) (σ : C),
    probOutput (encAlg.PerfectSecrecyCipherGivenMsgExp msg₀) σ =
      probOutput (encAlg.PerfectSecrecyCipherGivenMsgExp msg₁) σ


-- @@ L84-104 expanded
omit [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [EvalDistCompatible m] in
/-- Over a finite message space, strong perfect secrecy is equivalent to all ciphertext
rows being equal. -/
theorem perfectSecrecyAtAllPriors_iff_ciphertextRowsEqualAt (encAlg : SymmEncAlg m M K C)
    [Finite M] : encAlg.perfectSecrecyAtAllPriors ↔ encAlg.ciphertextRowsEqualAt :=
  by
  have : Fintype M := Fintype.ofFinite M
  constructor
  · intro hAll msg₀ msg₁ σ
    have : Nonempty M := ⟨msg₀⟩
    let μ : PMF M := PMF.uniformOfFintype M
    let row := fun x : M => probOutput (encAlg.PerfectSecrecyCipherGivenMsgExp x) σ
    have key :
      ∀ x : M,
        (Fintype.card M : ℝ≥0∞)⁻¹ * row x = (Fintype.card M : ℝ≥0∞)⁻¹ * ∑' y : M, μ y * row y :=
      fun x => by
      simpa [perfectSecrecyAtAllPriors, μ, row, PMF.uniformOfFintype_apply] using hAll μ x σ
    exact
      (ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 (by simp))
            (ENNReal.inv_ne_top.2 (by exact_mod_cast Fintype.card_ne_zero))).1
        ((key msg₀).trans (key msg₁).symm)
  · intro hRows μ msg σ
    simp only [hRows _ msg σ, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]


-- @@ L106-111 expanded
/-- Standard perfect secrecy expressed as independence:
`Pr[(M, C)] = Pr[M] * Pr[C]`. -/
def perfectSecrecyAt (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ (mgen : m M) (msg : M) (σ : C),
    probOutput (encAlg.PerfectSecrecyExp mgen) (msg, σ) =
      probOutput mgen msg * probOutput (encAlg.PerfectSecrecyCipherExp mgen) σ


-- @@ L113-117 expanded
/-- Posterior-equals-prior form, written in cross-multiplied form to avoid division. -/
def perfectSecrecyPosteriorEqPriorAt (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ (mgen : m M) (msg : M) (σ : C),
    probOutput (encAlg.PerfectSecrecyExp mgen) (msg, σ) =
      probOutput (encAlg.PerfectSecrecyCipherExp mgen) σ * probOutput mgen msg


-- @@ L119-124 expanded
/-- Joint-factorization form (same mathematical statement as independence, with explicit
named priors/marginals). -/
def perfectSecrecyJointFactorizationAt (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ (mgen : m M) (msg : M) (σ : C),
    probOutput (encAlg.PerfectSecrecyExp mgen) (msg, σ) =
      probOutput mgen msg * probOutput (encAlg.PerfectSecrecyCipherExp mgen) σ


-- @@ L126-130 verbatim
omit [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    in
lemma perfectSecrecyAt_iff_posteriorEqPriorAt (encAlg : SymmEncAlg m M K C) :
    encAlg.perfectSecrecyAt ↔ encAlg.perfectSecrecyPosteriorEqPriorAt := by
  simp [perfectSecrecyAt, perfectSecrecyPosteriorEqPriorAt, mul_comm]


-- @@ L132-135 verbatim
omit [LawfulMonadLiftT m PMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    in
lemma perfectSecrecyAt_iff_jointFactorizationAt (encAlg : SymmEncAlg m M K C) :
    encAlg.perfectSecrecyAt ↔ encAlg.perfectSecrecyJointFactorizationAt := Iff.rfl


-- @@ L137-161 expanded
/-- Core uniformity lemma: uniform keygen plus unique key per (message, ciphertext) pair
implies every (message, ciphertext) conditional has probability `(card K)⁻¹`.
Both Shannon theorems follow from this. -/
theorem cipherGivenMsg_uniform_of_uniformKey_of_uniqueKey (encAlg : SymmEncAlg m M K C) [Fintype K]
    (deterministicEnc : ∀ (k : K) (msg : M), ∃ c, support (encAlg.encrypt k msg) = { c })
    (hKeyUniform : ∀ k : K, probOutput encAlg.keygen k = (Fintype.card K : ℝ≥0∞)⁻¹)
    (hUniqueKey :
      ∀ msg : M, ∀ c : C, ∃! k : K, k ∈ support encAlg.keygen ∧ c ∈ support (encAlg.encrypt k msg))
    (msg : M) (σ : C) :
    probOutput (encAlg.PerfectSecrecyCipherGivenMsgExp msg) σ = (Fintype.card K : ℝ≥0∞)⁻¹ :=
  by
  obtain ⟨k0, hk0, hk0uniq⟩ := hUniqueKey msg σ
  have henc_one : probOutput (encAlg.encrypt k0 msg) σ = 1 :=
    by
    obtain ⟨c0, hc0⟩ := deterministicEnc k0 msg
    obtain rfl : σ = c0 := by simpa [hc0] using hk0.2
    exact probOutput_eq_one_iff.2 ⟨probFailure_of_liftM_PMF _, by simpa using hc0⟩
  simp only [PerfectSecrecyCipherGivenMsgExp, probOutput_bind_eq_tsum]
  rw [tsum_eq_single k0 fun k hkne =>
      mul_eq_zero.2 <|
        (not_and_or.1 fun h => hkne (hk0uniq k h)).imp probOutput_eq_zero_of_not_mem_support
          probOutput_eq_zero_of_not_mem_support]
  simp [hKeyUniform k0, henc_one]


-- @@ L163-177 expanded
theorem ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey (encAlg : SymmEncAlg m M K C) [Fintype K]
    (deterministicEnc : ∀ (k : K) (msg : M), ∃ c, support (encAlg.encrypt k msg) = { c })
    (hKeyUniform : ∀ k : K, probOutput encAlg.keygen k = (Fintype.card K : ℝ≥0∞)⁻¹)
    (hUniqueKey :
      ∀ msg : M,
        ∀ c : C, ∃! k : K, k ∈ support encAlg.keygen ∧ c ∈ support (encAlg.encrypt k msg)) :
    encAlg.ciphertextRowsEqualAt := by
  intro msg₀ msg₁ σ
  rw [encAlg.cipherGivenMsg_uniform_of_uniformKey_of_uniqueKey deterministicEnc hKeyUniform
      hUniqueKey msg₀ σ,
    encAlg.cipherGivenMsg_uniform_of_uniformKey_of_uniqueKey deterministicEnc hKeyUniform hUniqueKey
      msg₁ σ]


-- @@ L179-206 expanded
/-- Constructive Shannon direction: if keygen is uniform and each `(message, ciphertext)`
pair is realized by a unique key in support, then perfect secrecy holds.

`deterministicEnc` asserts encryption is deterministic in distribution
(singleton support for each fixed `(key, message)`). -/
theorem perfectSecrecyAt_of_uniformKey_of_uniqueKey [LawfulMonad m] (encAlg : SymmEncAlg m M K C)
    [Fintype K]
    (deterministicEnc : ∀ (k : K) (msg : M), ∃ c, support (encAlg.encrypt k msg) = { c }) :
    ((∀ k : K, probOutput encAlg.keygen k = (Fintype.card K : ℝ≥0∞)⁻¹) ∧
        (∀ msg : M,
          ∀ c : C, ∃! k : K, k ∈ support encAlg.keygen ∧ c ∈ support (encAlg.encrypt k msg))) →
      encAlg.perfectSecrecyAt :=
  by
  intro ⟨hKeyUniform, hUniqueKey⟩
  have hCipherGiven_uniform :=
    encAlg.cipherGivenMsg_uniform_of_uniformKey_of_uniqueKey deterministicEnc hKeyUniform hUniqueKey
  have hCipher_uniform :
    ∀ (mgen : m M) (σ : C),
      probOutput (encAlg.PerfectSecrecyCipherExp mgen) σ = (Fintype.card K : ℝ≥0∞)⁻¹ :=
    by
    intro mgen σ
    rw [encAlg.probOutput_PerfectSecrecyCipherExp_eq_tsum mgen σ]
    simp_rw [hCipherGiven_uniform _ σ, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF mgen,
      one_mul]
  intro mgen msg σ
  rw [encAlg.probOutput_PerfectSecrecyExp_eq_mul_cipherGivenMsg mgen msg σ,
    hCipherGiven_uniform msg σ, hCipher_uniform mgen σ]


-- @@ L208-224 expanded
/-- Constructive Shannon direction for all priors: uniform keys plus uniqueness
imply perfect secrecy for all prior distributions on messages. -/
theorem perfectSecrecyAtAllPriors_of_uniformKey_of_uniqueKey (encAlg : SymmEncAlg m M K C)
    [Finite M] [Fintype K]
    (deterministicEnc : ∀ (k : K) (msg : M), ∃ c, support (encAlg.encrypt k msg) = { c }) :
    ((∀ k : K, probOutput encAlg.keygen k = (Fintype.card K : ℝ≥0∞)⁻¹) ∧
        (∀ msg : M,
          ∀ c : C, ∃! k : K, k ∈ support encAlg.keygen ∧ c ∈ support (encAlg.encrypt k msg))) →
      encAlg.perfectSecrecyAtAllPriors :=
  by
  intro ⟨hKeyUniform, hUniqueKey⟩
  exact
    (encAlg.perfectSecrecyAtAllPriors_iff_ciphertextRowsEqualAt).2
      (encAlg.ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey deterministicEnc hKeyUniform
        hUniqueKey)


-- @@ L226-226 verbatim
end perfectSecrecy


-- @@ L228-228 verbatim
end SymmEncAlg
