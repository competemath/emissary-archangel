/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import LeanPool.JacobianDiffgeo.JacobianConstruction.Basic
import Mathlib.CategoryTheory.Category.Init


-- @@ L11-24 verbatim
/-!
# The `→ₜ+` functoriality substrate, wrapped through the `ULift` shell (§9.4)

Unit: jacobian-construction. Wraps `Torus.inducedHom`/`Torus.contMDiff_inducedHom` (the abstract
`V ⧸ L → V' ⧸ L'` substrate, §9.2–§9.3) through the `ULift` shell to produce a `→ₜ+` map
`Jacobian X →ₜ+ Jacobian Y` from a `ℂ`-linear map `T` between the ambient period spaces
respecting the period subgroups.

**Out of scope for this unit** (flagged, not silently dropped, per design §9.4/R4): constructing
the *specific* `T` for a given holomorphic `f : X → Y` (via pullback-of-forms), and the actual
`Jacobian.pushforward`/`Jacobian.pullback` challenge definitions built from a real `f`. No
blueprint unit currently owns "pullback of holomorphic `1`-forms along a holomorphic map" — see
this unit's final report for the flag to the orchestrator.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
open scoped ContDiff Manifold


-- @@ L30-30 verbatim
universe u


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace RS


-- @@ L36-36 verbatim
/-! ### `ULift` as a `→ₜ+` equivalence (generic transport toolkit) -/


-- @@ L38-38 verbatim
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]


-- @@ L40-43 verbatim
/-- `ULift.up`, bundled as a continuous additive homomorphism. -/
def uliftUpHom : G →ₜ+ ULift.{u} G :=
  { (AddEquiv.ulift (α := G)).symm.toAddMonoidHom with
    continuous_toFun := (Homeomorph.ulift (X := G)).symm.continuous }


-- @@ L45-48 verbatim
/-- `ULift.down`, bundled as a continuous additive homomorphism. -/
def uliftDownHom : ULift.{u} G →ₜ+ G :=
  { (AddEquiv.ulift (α := G)).toAddMonoidHom with
    continuous_toFun := (Homeomorph.ulift (X := G)).continuous }


-- @@ L50-51 verbatim
omit [IsTopologicalAddGroup G] in
@[simp] theorem uliftUpHom_apply (x : G) : uliftUpHom.{u} x = ULift.up x := rfl


-- @@ L53-54 verbatim
omit [IsTopologicalAddGroup G] in
@[simp] theorem uliftDownHom_apply (x : ULift.{u} G) : uliftDownHom x = x.down := rfl


-- @@ L56-56 verbatim
end RS


-- @@ L58-59 verbatim
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- @@ L60-61 verbatim
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]


-- @@ L63-63 verbatim
namespace Jacobian


-- @@ L65-81 verbatim
/-- A `ℂ`-linear map on the ambient period spaces, respecting the period subgroups (at the raw,
undiscretized `periodSubgroup` level — the natural hypothesis to check for a map arising from a
holomorphic `f : X → Y`, e.g. via naturality of periods under post-composition), induces the
functoriality substrate `Jacobian X →ₜ+ Jacobian Y`. The *closure*-level hypothesis
`Torus.inducedHom` needs is derived from this one via minimality of the topological closure
(`AddSubgroup.topologicalClosure_minimal`), since `(periodSubgroup Y).topologicalClosure` is
already closed and `T` is continuous (finite-dimensional). -/
noncomputable def inducedHom {T : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)}
    (hT : RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap T.toAddMonoidHom) :
    Jacobian X →ₜ+ Jacobian Y :=
  RS.uliftUpHom.comp
    ((RS.inducedHom (RS.periodSubgroup X).topologicalClosure
        (RS.periodSubgroup Y).topologicalClosure T
        (AddSubgroup.topologicalClosure_minimal (RS.periodSubgroup X) hT
          (((RS.periodSubgroup Y).isClosed_topologicalClosure).preimage
            T.continuous_of_finiteDimensional))).comp
      RS.uliftDownHom)


-- @@ L83-101 verbatim
/-- The induced map on Jacobians is `ω`-smooth, given discreteness of both period-subgroup
closures (needed for the manifold structure on either side, per `Basic.lean`'s ledger). -/
theorem contMDiff_inducedHom {T : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)}
    (hT : RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap T.toAddMonoidHom)
    [DiscreteTopology (RS.periodSubgroup X).topologicalClosure]
    [DiscreteTopology (RS.periodSubgroup Y).topologicalClosure] :
    ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω (inducedHom hT) := by
  unfold inducedHom
  have hclosure : (RS.periodSubgroup X).topologicalClosure ≤
      (RS.periodSubgroup Y).topologicalClosure.comap T.toAddMonoidHom :=
    AddSubgroup.topologicalClosure_minimal (RS.periodSubgroup X) hT
      (((RS.periodSubgroup Y).isClosed_topologicalClosure).preimage
        T.continuous_of_finiteDimensional)
  have h1 := RS.contMDiff_uliftUp (RS.periodSubgroup Y).topologicalClosure
  have h2 := RS.contMDiff_inducedHom (L := (RS.periodSubgroup X).topologicalClosure)
    (L' := (RS.periodSubgroup Y).topologicalClosure) hclosure
  have h3 := RS.contMDiff_uliftDown (RS.periodSubgroup X).topologicalClosure
  have := (h1.comp h2).comp h3
  exact this


-- @@ L103-103 verbatim
end Jacobian
