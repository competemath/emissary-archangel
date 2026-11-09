/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact


-- @@ L20-36 verbatim
/-!
# `IsStableUnderBaseChangeAlong` / `RespectsIso` for the standard morphism properties

**v4.33 bump compatibility.** Mathlib derives both

* `[P.IsStableUnderBaseChange] → P.IsStableUnderBaseChangeAlong f`
  (`CategoryTheory/MorphismProperty/Limits.lean`), and
* `[P.IsStableUnderBaseChange] → P.RespectsIso` (priority 900, same file),

but neither derivation fires by unification for the `AlgebraicGeometry` properties on this
pin, even with the relevant `IsStableUnderBaseChange` instance in scope — this was checked
in isolation for `@Surjective`. Supplying the instances at each concrete property makes them
fire; this file does that once so the ~20 affected call sites across `ModularCurves` need
only an import.

Delete this file when the derivations fire again upstream.
-/


-- @@ L38-38 verbatim
universe u


-- @@ L40-40 verbatim
open CategoryTheory AlgebraicGeometry


-- @@ L42-42 verbatim
namespace ModularCurves.BumpCompat


-- @@ L44-46 verbatim
instance stableAlong_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Surjective) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L48-50 verbatim
instance stableAlong_flat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Flat) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L52-54 verbatim
instance stableAlong_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsFinite) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L56-58 verbatim
instance stableAlong_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsProper) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L60-62 verbatim
instance stableAlong_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsClosedImmersion) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L64-66 verbatim
instance stableAlong_isSeparated {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsSeparated) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L68-71 verbatim
instance stableAlong_smoothOfRelativeDimension (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@SmoothOfRelativeDimension n) f :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L73-74 verbatim
instance respectsIso_isFinite : MorphismProperty.RespectsIso (@IsFinite) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso


-- @@ L76-77 verbatim
instance respectsIso_flat : MorphismProperty.RespectsIso (@Flat) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso


-- @@ L79-80 verbatim
instance respectsIso_isProper : MorphismProperty.RespectsIso (@IsProper) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso


-- @@ L82-83 verbatim
instance respectsIso_isClosedImmersion : MorphismProperty.RespectsIso (@IsClosedImmersion) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso


-- @@ L85-87 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance zariskiLocalAtTarget_isFinite : IsZariskiLocalAtTarget (@IsFinite) :=
  inferInstance


-- @@ L89-92 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance hasAffineProperty_isFinite : HasAffineProperty (@IsFinite)
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (Scheme.Hom.appTop f).hom) :=
  inferInstance


-- @@ L94-96 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance zariskiLocalAtTarget_etale : IsZariskiLocalAtTarget (@Etale) :=
  inferInstance


-- @@ L98-100 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance respectsIso_etale : MorphismProperty.RespectsIso (@Etale) :=
  inferInstance


-- @@ L102-104 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance zariskiLocalAtTarget_flat : IsZariskiLocalAtTarget (@Flat) :=
  inferInstance


-- @@ L106-109 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance respectsIso_formallyUnramified :
    MorphismProperty.RespectsIso (@FormallyUnramified) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso


-- @@ L111-114 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance stableAlong_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@FormallyUnramified) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L116-118 verbatim
instance stableAlong_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiCompact) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L120-122 verbatim
instance stableAlong_etale {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Etale) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩


-- @@ L124-126 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance zariskiLocalAtSource_flat : IsZariskiLocalAtSource (@Flat) :=
  inferInstance


-- @@ L128-131 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance zariskiLocalAtSource_locallyOfFinitePresentation :
    IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
  inferInstance


-- @@ L133-137 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance descendsAlong_etale_fppf :
    MorphismProperty.DescendsAlong (@Etale)
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  inferInstance


-- @@ L139-142 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance zariskiLocalAtTarget_smoothOfRelativeDimension (n : ℕ) :
    IsZariskiLocalAtTarget (@SmoothOfRelativeDimension n) :=
  inferInstance


-- @@ L144-146 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance zariskiLocalAtTarget_isAffineHom : IsZariskiLocalAtTarget (@IsAffineHom) :=
  inferInstance


-- @@ L148-151 verbatim
set_option backward.isDefEq.respectTransparency.types false in
instance stableUnderComposition_etale :
    MorphismProperty.IsStableUnderComposition (@Etale) :=
  inferInstance


-- @@ L153-153 verbatim
end ModularCurves.BumpCompat
