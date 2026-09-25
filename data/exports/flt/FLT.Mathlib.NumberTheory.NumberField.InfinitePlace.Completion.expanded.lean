/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace


-- @@ L10-14 verbatim
/-!
# Completion

Material destined for Mathlib.
-/


-- @@ L16-18 verbatim
@[expose] public section

-- TODO upstream


-- @@ L20-24 verbatim
instance NumberField.InfinitePlace.Completion.secondCountableTopology
    {K : Type*} [Field K] (v : InfinitePlace K) :
    SecondCountableTopology (v.Completion) :=
  (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding
    v).isEmbedding.isInducing.secondCountableTopology
