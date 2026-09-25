/-
Copyright (c) 2025 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras, Kevin Buzzard
-/
module

public import FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import FLT.Deformations.Algebra.InverseLimit.Basic
public import Mathlib.Topology.Algebra.Ring.Basic


-- @@ L12-18 verbatim
/-!
# Topology on inverse limits

The inverse limit of a system of topological algebraic structures inherits
a natural topological structure as a subspace of the product. We record
basic continuity properties of the canonical maps.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open TopologicalSpace


-- @@ L24-24 verbatim
variable {ι : Type*} [Preorder ι] {G : ι → Type*}

-- @@ L25-25 verbatim
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}

-- @@ L26-26 verbatim
variable [∀ i j (h : i ≤ j), FunLike (T h) (G j) (G i)]

-- @@ L27-28 verbatim
variable [∀ i : ι, TopologicalSpace (G i)]
  {cont : ∀ {i j}, (h : i ≤ j) → Continuous (f i j h)}


-- @@ L30-30 verbatim
namespace InverseLimit


-- @@ L32-32 verbatim
variable {W : Type*} {M : ι → Type*} (maps : ∀ i, M i) [∀ i, FunLike (M i) W (G i)]

-- @@ L33-33 verbatim
variable (inverseSystemHom : InverseSystemHom G f maps)

-- @@ L34-34 verbatim
variable [TopologicalSpace W]

-- @@ L35-35 verbatim
variable (maps_cont : (i : ι) → Continuous (maps i))


-- @@ L37-38 verbatim
instance : TopologicalSpace (InverseLimit G f) :=
  inferInstanceAs (TopologicalSpace {x : (i : ι) → G i // ∀ i j h, f i j h (x j) = x i})


-- @@ L40-42 verbatim
@[fun_prop, continuity]
lemma val_continuous : Continuous (fun (x : InverseLimit G f) ↦ x.val) := by
  continuity


-- @@ L44-44 verbatim
section ToComponent


-- @@ L46-51 verbatim
@[fun_prop, continuity]
lemma toComponent_continuous (i : ι) : Continuous (toComponent G f i) := by
  rw [toComponent_def]
  have : (fun (z : InverseLimit G f) ↦ z.val i) = (fun y ↦ y i) ∘ (fun z ↦ z.val) := rfl
  rw [this]
  exact Continuous.comp (by fun_prop) (val_continuous ..)


-- @@ L53-53 verbatim
end ToComponent


-- @@ L55-55 verbatim
section Maps


-- @@ L57-61 verbatim
@[fun_prop, continuity]
lemma lift_continuous (maps_cont : ∀ i, Continuous (maps i)) :
    Continuous (lift G f maps inverseSystemHom) := by
  rw [lift_def]
  fun_prop


-- @@ L63-63 verbatim
end Maps


-- @@ L65-65 verbatim
section TopologicalStructures


-- @@ L67-78 verbatim
instance [∀ i, Group (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)]
    [∀ i : ι, IsTopologicalGroup (G i)] :
    IsTopologicalGroup (InverseLimit G f) := by
  unfold InverseLimit
  let S : Subgroup ((i : ι) → G i) := {
    carrier := { x | ∀ (i j : ι) (h : i ≤ j), (f i j h) (x j) = x i }
    mul_mem' := by aesop
    one_mem' := by aesop
    inv_mem' := by aesop
  }
  change IsTopologicalGroup S
  infer_instance


-- @@ L80-93 verbatim
instance [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)]
    [∀ i : ι, IsTopologicalRing (G i)] :
    IsTopologicalRing (InverseLimit G f) := by
  unfold InverseLimit
  let S : Subring ((i : ι) → G i) := {
    carrier := { x | ∀ (i j : ι) (h : i ≤ j), (f i j h) (x j) = x i }
    mul_mem' := by aesop
    one_mem' := by aesop
    add_mem' := by aesop
    zero_mem' := by aesop
    neg_mem' := by aesop
  }
  change IsTopologicalRing S
  infer_instance


-- @@ L95-107 verbatim
instance {R : Type*} [Ring R] [TopologicalSpace R]
    [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    [∀ i j h, LinearMapClass (T h) R (G j) (G i)]
    [∀ i : ι, IsTopologicalModule R (G i)] : IsTopologicalModule R (InverseLimit G f) := by
  unfold InverseLimit
  let S : Submodule R ((i : ι) → G i) := {
    carrier := { x | ∀ (i j : ι) (h : i ≤ j), (f i j h) (x j) = x i }
    add_mem' := by aesop
    zero_mem' := by aesop
    smul_mem' := by aesop
  }
  change IsTopologicalModule R S
  infer_instance



-- @@ L110-110 verbatim
end TopologicalStructures


-- @@ L112-112 verbatim
end InverseLimit
