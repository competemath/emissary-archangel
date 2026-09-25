/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Map


-- @@ L10-17 verbatim
/-!
# Evaluation Distributions of Computations with `BitVec`

Lemmas about `probOutput` involving `BitVec`, generic over any monad `m` with `[MonadLiftT m SPMF]`.

The `SampleableType (BitVec n)` instance is defined in
`VCVio.OracleComp.Constructions.SampleableType`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open BitVec


-- @@ L23-25 verbatim
variable {α β γ : Type _} {m : Type _ → Type _} [Monad m] [LawfulMonad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L27-29 expanded
@[simp, grind =]
lemma probOutput_ofFin_map {n : ℕ} (mx : m (Fin (2 ^ n))) (x : BitVec n) :
    probOutput (ofFin <$> mx) x = probOutput mx (toFin x) := by aesop


-- @@ L31-33 expanded
@[simp, grind =]
lemma probOutput_bitVec_toFin_map {n : ℕ} (mx : m (BitVec n)) (x : Fin (2 ^ n)) :
    probOutput (toFin <$> mx) x = probOutput mx (ofFin x) := by aesop


-- @@ L35-41 expanded
omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
@[simp]
lemma probOutput_xor_map {n : ℕ} (mx : m (BitVec n)) (x y : BitVec n) :
    probOutput ((x ^^^ ·) <$> mx) y = probOutput mx (x ^^^ y) :=
  by
  have hinj : Function.Injective (x ^^^ ·) := fun a b h => by simpa using congrArg (x ^^^ ·) h
  conv_lhs => rw [show y = x ^^^ (x ^^^ y) by simp]
  exact probOutput_map_injective mx hinj (x ^^^ y)

