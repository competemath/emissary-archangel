/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Instances
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.ProbCompLift
public import PolyFun.Control.Monad.Hom


-- @@ L13-17 verbatim
/-!
# Asymmetric Encryption Schemes

Core definitions for asymmetric encryption schemes and correctness.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open OracleSpec OracleComp ENNReal


-- @@ L23-23 verbatim
universe u v w


-- @@ L25-33 verbatim
/-- An `AsymmEncAlg` with message space `M`, key spaces `PK` and `SK`, and ciphertexts in `C`.
`m` is the monad used to execute key generation, encryption, and decryption. The scheme data stays
purely algorithmic; probabilistic semantics and public-randomness injection are supplied
separately when defining security experiments. -/
@[ext]
structure AsymmEncAlg (m : Type → Type u) [Monad m] (M PK SK C : Type) where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) → m C
  decrypt : (sk : SK) → (c : C) → m (Option M)


-- @@ L35-43 verbatim
/-- An explicit-coins asymmetric encryption scheme in the monad `m`.

Key generation runs in `m`, while encryption and decryption become pure once the randomness type
`R` is supplied explicitly. This is the natural refinement used by FO-style transforms, where the
coins are sampled externally or derived from an oracle. -/
structure AsymmEncAlg.ExplicitCoins (m : Type → Type u) [Monad m] (M PK SK R C : Type) where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) → (coins : R) → C
  decrypt : (sk : SK) → (c : C) → Option M


-- @@ L45-45 verbatim
abbrev PKE_Alg := AsymmEncAlg


-- @@ L47-47 verbatim
namespace AsymmEncAlg

-- @@ L48-49 verbatim
variable {m : Type → Type v} [Monad m] {M PK SK C : Type}
  (encAlg : AsymmEncAlg m M PK SK C)


-- @@ L51-51 verbatim
section map


-- @@ L53-53 verbatim
variable {n : Type → Type w} [Monad n]


-- @@ L55-60 verbatim
/-- Transport an asymmetric encryption scheme across a monad morphism by mapping each algorithmic
component. -/
def map (F : m →ᵐ n) : AsymmEncAlg n M PK SK C where
  keygen := F encAlg.keygen
  encrypt pk msg := F (encAlg.encrypt pk msg)
  decrypt sk c := F (encAlg.decrypt sk c)


-- @@ L62-64 verbatim
@[simp]
lemma map_keygen {encAlg : AsymmEncAlg m M PK SK C} (F : m →ᵐ n) :
    (encAlg.map F).keygen = F encAlg.keygen := rfl


-- @@ L66-68 verbatim
@[simp]
lemma map_encrypt {encAlg : AsymmEncAlg m M PK SK C} (F : m →ᵐ n) (pk : PK) (msg : M) :
    (encAlg.map F).encrypt pk msg = F (encAlg.encrypt pk msg) := rfl


-- @@ L70-72 verbatim
@[simp]
lemma map_decrypt {encAlg : AsymmEncAlg m M PK SK C} (F : m →ᵐ n) (sk : SK) (c : C) :
    (encAlg.map F).decrypt sk c = F (encAlg.decrypt sk c) := rfl


-- @@ L74-74 verbatim
end map


-- @@ L76-76 verbatim
section Correct


-- @@ L78-78 verbatim
variable [DecidableEq M]


-- @@ L80-88 verbatim
/-- Correctness experiment: returns `true` iff decrypting the ciphertext recovers the message.

The game returns a `Bool` directly rather than using `guard`, so it does not require
`AlternativeMonad`. -/
def CorrectExp (msg : M) : m Bool := do
  let (pk, sk) ← encAlg.keygen
  let c ← encAlg.encrypt pk msg
  let msg' ← encAlg.decrypt sk c
  return decide (msg' = some msg)


-- @@ L90-93 expanded
/-- An asymmetric encryption scheme is perfectly correct under the given runtime when decrypting a
fresh encryption of any message succeeds with probability `1`. -/
def PerfectlyCorrect (runtime : ProbCompRuntime m) : Prop :=
  ∀ (msg : M), probOutput (runtime.evalSPMF (encAlg.CorrectExp msg)) true = 1


-- @@ L95-95 verbatim
end Correct


-- @@ L97-97 verbatim
namespace ExplicitCoins

-- @@ L98-99 verbatim
variable {m : Type → Type v} [Monad m] {M PK SK R C : Type}
  (encAlg : AsymmEncAlg.ExplicitCoins m M PK SK R C)


-- @@ L101-108 expanded
/-- Forget the explicit-coins presentation by sampling the coins through the ambient runtime's
public-randomness capability. -/
def toAsymmEncAlg [SampleableType R] (runtime : ProbCompRuntime m) : AsymmEncAlg m M PK SK C :=
  { keygen := encAlg.keygen
    encrypt pk
      msg := do
      let r ← runtime.liftProbComp (uniformSample R)
      return encAlg.encrypt pk msg r
    decrypt sk c := return encAlg.decrypt sk c }


-- @@ L110-110 verbatim
end ExplicitCoins


-- @@ L112-112 verbatim
end AsymmEncAlg
