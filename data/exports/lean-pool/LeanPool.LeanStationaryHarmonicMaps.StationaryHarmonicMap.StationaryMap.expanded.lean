/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
module

public import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.SobolevWitness
public import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.StationarityBridge
import Mathlib.Data.Nat.Factorial.DoubleFactorial


-- @@ L12-21 verbatim
/-!
# Stationary Sobolev map package

This file adds stationarity to the Sobolev witness layer.  The package is the
paper-facing input for the monotonicity theorem: a local Sobolev map with an
explicit weak gradient, plus vanishing domain first variation.

The target-manifold constraint is intentionally absent.  The monotonicity proof
uses only this stationary package.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open MeasureTheory Set

-- @@ L28-28 verbatim
open scoped Topology BigOperators ENNReal


-- @@ L30-30 verbatim
namespace LeanStationaryHarmonicMaps

-- @@ L31-31 verbatim
namespace StationaryHarmonicMap


-- @@ L33-42 verbatim
/-- A stationary local `W^{1,2}` map witness.

The stationarity field is exactly the domain-variation first-variation
identity. No target-manifold structure is used by the monotonicity proof. -/
structure StationaryW12LocMap {n m : Nat}
    (u : Domain n -> Target m) (Omega : Set (Domain n)) where
  /-- Sobolev data together with the displayed weak gradient. -/
  w12 : W12LocMapWitness u Omega
  /-- Vanishing domain first variation for the displayed weak gradient. -/
  stationary : DomainVariationStationaryIn u w12.weakGrad Omega


-- @@ L44-44 verbatim
namespace StationaryW12LocMap


-- @@ L46-60 verbatim
/-- Build a stationary Sobolev witness from component hypotheses. -/
def ofComponents {n m : Nat}
    {u : Domain n -> Target m} {Du : Domain n -> Gradient n m}
    {Omega : Set (Domain n)}
    (hu_memLp : LocallyMemLpTwoIn u Omega)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Omega)
    (hDu_memLp : LocallyMemLpTwoIn Du Omega)
    (hweakGradient : DistributionalWeakGradientIn u Du Omega)
    (hfirstVariation : DomainVariationStationaryIn u Du Omega) :
    StationaryW12LocMap u Omega where
  w12 :=
    W12LocMapWitness.ofComponents
      (u := u) (Du := Du) (Omega := Omega)
      hu_memLp hDu_aesm hDu_memLp hweakGradient
  stationary := hfirstVariation


-- @@ L62-68 verbatim
/-- Forget the witness package to the earlier paper-facing stationary Sobolev
package. -/
theorem toStationarySobolevMapIn {n m : Nat}
    {u : Domain n -> Target m} {Omega : Set (Domain n)}
    (h : StationaryW12LocMap u Omega) :
    StationarySobolevMapIn u h.w12.weakGrad Omega :=
  ⟨h.w12.toSobolevW12LocIn, h.stationary⟩


-- @@ L70-76 verbatim
/-- Forget the witness package to the custom weak stationary map interface used
inside the proof. -/
theorem toWeakStationaryMapIn {n m : Nat}
    {u : Domain n -> Target m} {Omega : Set (Domain n)}
    (h : StationaryW12LocMap u Omega) :
    WeakStationaryMapIn u h.w12.weakGrad Omega :=
  h.toStationarySobolevMapIn.toWeakStationaryMapIn


-- @@ L78-78 verbatim
end StationaryW12LocMap


-- @@ L80-80 verbatim
end StationaryHarmonicMap

-- @@ L81-81 verbatim
end LeanStationaryHarmonicMaps


-- @@ L83-83 verbatim
end
