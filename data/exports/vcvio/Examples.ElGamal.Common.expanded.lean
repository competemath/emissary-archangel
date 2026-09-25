/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType


-- @@ L10-14 verbatim
/-!
# Shared ElGamal-family helpers

Small distribution lemmas shared by the plain and hashed ElGamal examples.
-/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
open OracleComp OracleSpec ENNReal


-- @@ L21-21 verbatim
namespace ElGamalExamples


-- @@ L23-23 verbatim
variable {A M : Type} [AddGroup M] [SampleableType M]


-- @@ L25-43 expanded
/-- A fixed header plus a uniform additive mask hides which payload was chosen, even after an
arbitrary continuation from ciphertexts. -/
lemma uniformMaskedCipher_bind_dist_indep {β : Type} (head : A) (m₁ m₂ : M)
    (cont : A × M → ProbComp β) :
    (evalSPMF do
        let y ← (uniformSample M)
        cont (head, m₁ + y)) =
      evalSPMF do
        let y ← (uniformSample M)
        cont (head, m₂ + y) :=
  by
  have hmask :
    evalSPMF ((fun y : M => (head, m₁ + y)) <$> (uniformSample M)) =
      evalSPMF ((fun y : M => (head, m₂ + y)) <$> (uniformSample M)) :=
    by
    simpa using
      evalSPMF_map_eq_of_evalSPMF_eq (h := evalSPMF_add_left_uniform_eq (α := M) m₁ m₂) (f :=
        fun z : M => (head, z))
  simpa [monad_norm, Function.comp, evalSPMF_bind] using
    congrArg (fun p => p >>= fun c => evalSPMF (cont c)) hmask


-- @@ L45-45 verbatim
end ElGamalExamples
