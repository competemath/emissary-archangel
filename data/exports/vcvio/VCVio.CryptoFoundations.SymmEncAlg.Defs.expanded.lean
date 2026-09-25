/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Mathlib.Control.Monad.Basic


-- @@ L10-15 verbatim
/-!
# Symmetric encryption schemes

This module contains the probability-independent data and experiments for symmetric encryption.
Semantic notions of correctness and secrecy live in separate compatibility and measure modules.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
universe u


-- @@ L21-29 verbatim
/-- A monad-generic symmetric encryption scheme over an ambient monad `m`, with message space `M`,
key space `K`, and ciphertext space `C`. -/
structure SymmEncAlg (m : Type → Type u) [Monad m] (M K C : Type) where
  /-- Sample a key. -/
  keygen : m K
  /-- Encrypt a message under a key. -/
  encrypt : K → M → m C
  /-- Decrypt a ciphertext under a key, returning `none` on failure. -/
  decrypt : K → C → m (Option M)


-- @@ L31-31 verbatim
namespace SymmEncAlg


-- @@ L33-33 verbatim
variable {m : Type → Type u} [Monad m] {M K C : Type}


-- @@ L35-39 verbatim
/-- Round-trip experiment: sample a key, encrypt `msg`, then decrypt. -/
def CompleteExp (encAlg : SymmEncAlg m M K C) (msg : M) : m (Option M) := do
  let k ← encAlg.keygen
  let σ ← encAlg.encrypt k msg
  encAlg.decrypt k σ


-- @@ L41-41 verbatim
/-! ## Perfect-secrecy experiments -/


-- @@ L43-47 verbatim
/-- Joint message/ciphertext experiment used to express perfect secrecy. -/
def PerfectSecrecyExp (encAlg : SymmEncAlg m M K C) (mgen : m M) : m (M × C) := do
  let msg' ← mgen
  let k ← encAlg.keygen
  return (msg', ← encAlg.encrypt k msg')


-- @@ L49-51 verbatim
/-- Ciphertext marginal induced by the perfect-secrecy experiment. -/
def PerfectSecrecyCipherExp (encAlg : SymmEncAlg m M K C) (mgen : m M) : m C :=
  Prod.snd <$> encAlg.PerfectSecrecyExp mgen


-- @@ L53-56 verbatim
/-- Ciphertext experiment conditioned on a fixed message. -/
def PerfectSecrecyCipherGivenMsgExp (encAlg : SymmEncAlg m M K C) (msg : M) : m C := do
  let k ← encAlg.keygen
  encAlg.encrypt k msg


-- @@ L58-61 verbatim
lemma PerfectSecrecyExp_eq_bind [LawfulMonad m] (encAlg : SymmEncAlg m M K C) (mgen : m M) :
    encAlg.PerfectSecrecyExp mgen =
      mgen >>= fun msg ↦ (msg, ·) <$> encAlg.PerfectSecrecyCipherGivenMsgExp msg := by
  simp [PerfectSecrecyExp, PerfectSecrecyCipherGivenMsgExp, monad_norm]


-- @@ L63-67 verbatim
lemma PerfectSecrecyCipherExp_eq_bind [LawfulMonad m]
    (encAlg : SymmEncAlg m M K C) (mgen : m M) :
    encAlg.PerfectSecrecyCipherExp mgen =
      mgen >>= fun msg ↦ encAlg.PerfectSecrecyCipherGivenMsgExp msg := by
  simp [PerfectSecrecyCipherExp, PerfectSecrecyExp_eq_bind, monad_norm]


-- @@ L69-69 verbatim
end SymmEncAlg
