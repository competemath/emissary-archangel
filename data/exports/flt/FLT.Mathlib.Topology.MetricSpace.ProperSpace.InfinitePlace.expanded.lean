/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Analysis.CStarAlgebra.Classes


-- @@ L11-15 verbatim
/-!
# Infinite Place

Material destined for Mathlib.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open NumberField


-- @@ L21-21 verbatim
open InfinitePlace.Completion


-- @@ L23-25 verbatim
variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

-- TODO these should really be a proof of ProperSpace v.Completion etc


-- @@ L27-28 verbatim
instance : SecondCountableTopology (v.Completion) :=
  (isometry_extensionEmbedding v).isEmbedding.isInducing.secondCountableTopology


-- @@ L30-31 verbatim
instance : SecondCountableTopology (InfiniteAdeleRing K) :=
    inferInstanceAs (SecondCountableTopology (∀ _, _))
