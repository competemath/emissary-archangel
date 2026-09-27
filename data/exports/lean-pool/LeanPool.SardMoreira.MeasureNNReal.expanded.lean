/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import LeanPool.SardMoreira.MeasureComap


-- @@ L11-13 verbatim
/-!
# LeanPool.SardMoreira.MeasureNNReal
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open scoped ENNReal NNReal Set.Notation Pointwise

-- @@ L18-18 verbatim
open MeasureTheory Filter Set Function Metric Topology


-- @@ L20-21 verbatim
noncomputable instance instMeasureSpaceNNRealLeanPool : MeasureSpace ℝ≥0 where
  volume := .comap (↑) (volume : Measure ℝ)


-- @@ L23-25 verbatim
theorem NNReal.volume_def : (volume : Measure ℝ≥0) = .comap (↑) (volume : Measure ℝ) := rfl

-- TODO: should we have this instance? I'm not sure.

-- @@ L26-26 verbatim
instance : SigmaFinite (volume : Measure ℝ≥0) := .comap _ (by fun_prop)
