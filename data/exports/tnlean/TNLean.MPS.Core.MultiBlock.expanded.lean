/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.TraceReindex
import TNLean.MPS.Defs
import TNLean.MPS.Core.MultiBlockWord

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex


-- @@ L14-23 verbatim
/-!
# Multi-block canonical forms for MPS tensors

This file introduces the lightweight `CanonicalForm` structure for
block-diagonal MPS tensors with injective blocks, and constructs the
associated tensor `CanonicalForm.toTensor`. The generic Σ-type
`Kraus.evalWord`/`blockDiagonal'`-compatibility infrastructure this used to carry
(lines 69–149 of the pre-split file) now lives in
`TNLean/Kraus/MultiBlockWord.lean`.
-/


-- @@ L25-25 verbatim
open scoped Matrix BigOperators


-- @@ L27-27 verbatim
namespace MPSTensor


-- @@ L29-43 verbatim
/-- A block-injective canonical form for an MPS tensor: block diagonal with injective blocks.

This is the lightweight data structure for tensors of the form
`⊕_k μ_k A_k`. -/
structure CanonicalForm (d : ℕ) where
  /-- Number of blocks -/
  numBlocks : ℕ
  /-- Bond dimension of each block -/
  blockDim : Fin numBlocks → ℕ
  /-- The tensor for each block -/
  blockTensor : (k : Fin numBlocks) → MPSTensor d (blockDim k)
  /-- Scaling factor for each block -/
  μ : Fin numBlocks → ℂ
  /-- Each block tensor is injective. -/
  block_injective : ∀ k, Kraus.IsInjective (blockTensor k)


-- @@ L45-45 verbatim
namespace CanonicalForm


-- @@ L47-47 verbatim
variable {d : ℕ} (C : CanonicalForm d)


-- @@ L49-50 verbatim
/-- Total bond dimension of the block-diagonal tensor. -/
noncomputable def totalDim : ℕ := ∑ k : Fin C.numBlocks, C.blockDim k


-- @@ L52-66 verbatim
/-- Turn a canonical form into an actual MPS tensor by putting the blocks on the diagonal.

We use the dependent block-diagonal construction `Matrix.blockDiagonal'`, and then reindex the
resulting `Σ`-indexed matrix as a `Fin (∑ k, blockDim k)`-indexed matrix using
`finSigmaFinEquiv`. -/
noncomputable def toTensor : MPSTensor d C.totalDim := fun i : Fin d =>
  let blocks : (k : Fin C.numBlocks) → Matrix (Fin (C.blockDim k)) (Fin (C.blockDim k)) ℂ :=
    fun k => (C.μ k) • (C.blockTensor k i)
  let BD :
      Matrix ((k : Fin C.numBlocks) × Fin (C.blockDim k))
        ((k : Fin C.numBlocks) × Fin (C.blockDim k)) ℂ :=
    Matrix.blockDiagonal' blocks
  let e : ((k : Fin C.numBlocks) × Fin (C.blockDim k)) ≃ Fin C.totalDim :=
    (finSigmaFinEquiv (m := C.numBlocks) (n := C.blockDim))
  (Matrix.reindex e e) BD


-- @@ L68-68 verbatim
end CanonicalForm


-- @@ L70-70 verbatim
end MPSTensor
