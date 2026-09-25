/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import FLT.Mathlib.Topology.Algebra.Module.CompactOpen
public import FLT.Mathlib.Topology.Constructions


-- @@ L12-20 verbatim
/-!
# The internal hom of continuous representations

This file constructs `ContRepresentation.linHom ρ2 ρ3`, the continuous representation of `G` on
`M2 →L[k] M3` by conjugation, `g • φ = ρ3 g ∘L φ ∘L ρ2 g⁻¹`, where `M2 →L[k] M3` carries the
topology induced from the compact-open topology on `C(M2, M3)`.

Material destined for `Mathlib.RepresentationTheory.Continuous.Basic`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
universe u v w


-- @@ L26-26 verbatim
open ContinuousLinearMap.CompactOpen


-- @@ L28-28 verbatim
namespace ContRepresentation


-- @@ L30-30 verbatim
variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]


-- @@ L32-32 verbatim
section LinHom


-- @@ L34-37 verbatim
variable {M2 M3 : Type w}
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3] (ρ2 : ContRepresentation k G M2) (ρ3 : ContRepresentation k G M3)


-- @@ L39-54 verbatim
/-- The continuous representation of `G` on `M2 →L[k] M3` by conjugation,
`g • φ = ρ3 g ∘L φ ∘L ρ2 g⁻¹`, where `M2 →L[k] M3` carries the topology induced from the
compact-open topology on `C(M2, M3)`. -/
def linHom : ContRepresentation k G (M2 →L[k] M3) where
  toMonoidHom.toFun g := {
    toFun f := ρ3 g ∘L f ∘L ρ2 g⁻¹
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := by
      refine continuous_induced_rng.2 ?_
      change Continuous fun f : M2 →L[k] M3 ↦
        (ρ3 g : C(M3, M3)).comp ((⟨f.toFun, f.cont⟩ : C(M2, M3)).comp (ρ2 g⁻¹ : C(M2, M2)))
      exact ((ρ3 g : C(M3, M3)).continuous_postcomp).comp
        (((ρ2 g⁻¹ : C(M2, M2)).continuous_precomp).comp continuous_induced_dom) }
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' g₁ g₂ := by ext; simp


-- @@ L56-58 verbatim
@[simp]
lemma linHom_apply (g : G) (φ : M2 →L[k] M3) :
    linHom ρ2 ρ3 g φ = ρ3 g ∘L φ ∘L ρ2 g⁻¹ := rfl


-- @@ L60-60 verbatim
end LinHom


-- @@ L62-62 verbatim
section DiscretePairing


-- @@ L64-70 verbatim
variable {M1 M2 M3 : Type w}
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3]
  {ρ1 : ContRepresentation k G M1} {ρ2 : ContRepresentation k G M2}
  {ρ3 : ContRepresentation k G M3}


-- @@ L72-77 verbatim
/-- When the source module of an intertwining map into an internal hom is discrete, its
uncurried pairing is automatically jointly continuous. -/
lemma continuous_pair_of_discrete [DiscreteTopology M1] (f : ρ1 →ⁱL linHom ρ2 ρ3) :
    Continuous fun p : M1 × M2 ↦ f p.1 p.2 :=
  (continuous_of_discreteTopology_snd (g := fun p : M2 × M1 ↦ f p.2 p.1)
    fun v ↦ (f v).continuous).comp continuous_swap


-- @@ L79-79 verbatim
end DiscretePairing


-- @@ L81-81 verbatim
end ContRepresentation
