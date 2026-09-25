/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.EvalDist.BitVec
public import VCVio.EvalDist.Prod


-- @@ L12-18 verbatim
/-!
# Probability lemmas for uniform `BitVec` sampling

Lemmas about `probOutput` for `ProbComp (BitVec n)` computations involving XOR with
uniformly sampled keys. These are reusable building blocks for encryption proofs
(e.g., one-time pad privacy).
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open OracleSpec OracleComp ENNReal


-- @@ L24-33 expanded
lemma probOutput_xor_uniform (sp : ℕ) (msg σ : BitVec sp) :
    probOutput ((fun k : BitVec sp => k ^^^ msg) <$> (uniformSample (BitVec sp))) σ =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ :=
  by
  calc
    probOutput ((fun k : BitVec sp => k ^^^ msg) <$> (uniformSample (BitVec sp))) σ =
        probOutput ((msg ^^^ ·) <$> (uniformSample (BitVec sp))) σ :=
      by simp [BitVec.xor_comm]
    _ = probOutput (uniformSample (BitVec sp)) (msg ^^^ σ) := by simp
    _ = (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by simp [probOutput_uniformSample]


-- @@ L35-71 expanded
lemma probOutput_pair_xor_uniform (sp : ℕ) (mx : ProbComp (BitVec sp)) (msg σ : BitVec sp) :
    probOutput
        (do
          let msg' ← mx
          let k ← uniformSample (BitVec sp)
          return (msg', k ^^^ msg'))
        (msg, σ) =
      probOutput mx msg * (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ :=
  by
  let inv : ℝ≥0∞ := (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹
  rw [probOutput_bind_eq_tsum]
  have hinner (msg' : BitVec sp) :
    probOutput
        (do
          let k ← uniformSample (BitVec sp)
          return (msg', k ^^^ msg'))
        (msg, σ) =
      if msg = msg' then inv else 0 :=
    by
    calc
      probOutput
            (do
              let k ← uniformSample (BitVec sp)
              return (msg', k ^^^ msg'))
            (msg, σ) =
          probOutput
            ((msg', ·) <$> ((fun k : BitVec sp => k ^^^ msg') <$> (uniformSample (BitVec sp))))
            (msg, σ) :=
        by simp
      _ =
          if msg = msg' then
            probOutput ((fun k : BitVec sp => k ^^^ msg') <$> (uniformSample (BitVec sp))) σ
          else 0 :=
        by
        simpa using
          (probOutput_prod_mk_snd_map (my :=
            (fun k : BitVec sp => k ^^^ msg') <$> (uniformSample (BitVec sp))) (x := msg') (z :=
            (msg, σ)))
      _ = if msg = msg' then inv else 0 := by
        by_cases h : msg = msg' <;> simp [h, inv, probOutput_xor_uniform]
  simp_rw [hinner]
  calc
    ∑' msg', probOutput mx msg' * (if msg = msg' then inv else 0) =
        ∑' msg', (probOutput mx msg' * (if msg = msg' then 1 else 0)) * inv :=
      by
      refine tsum_congr fun msg' => ?_
      by_cases h : msg = msg' <;> simp [h, inv, mul_comm]
    _ = (∑' msg', probOutput mx msg' * (if msg = msg' then 1 else 0)) * inv := by
      rw [ENNReal.tsum_mul_right]
    _ = probOutput mx msg * inv := by simp


-- @@ L73-84 expanded
lemma probOutput_cipher_from_pair_uniform (sp : ℕ) (mx : ProbComp (BitVec sp)) (σ : BitVec sp) :
    probOutput
        (do
          let msg' ← mx
          let k ← uniformSample (BitVec sp)
          return (k ^^^ msg'))
        σ =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ :=
  by
  rw [probOutput_bind_of_const (mx := mx) (y := σ) (r := (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹)]
  · simp
  · intro msg hmsg
    simpa using probOutput_xor_uniform sp msg σ

