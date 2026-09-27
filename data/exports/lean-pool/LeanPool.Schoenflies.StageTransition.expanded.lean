/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.FiniteTransferTarget


-- @@ L10-26 verbatim
/-!
# The common output of one transferred stage

Both directions of finite transfer produce the four pieces of data needed between consecutive
matched cellulations: compatible source and target refinements, growth of the realized source
skeleton, and agreement of the new skeleton homeomorphism with the old one.  `StageTransition`
packages that shared output and proves that transitions compose.

## Blueprint

* `Schoenflies.StageTransition` — one step of the quantitative-refinement recursion, stripped of
  the particular ambient graph used to construct it.
* `Schoenflies.IsPartialTransferOf.stageTransition`,
  `Schoenflies.IsTargetPartialTransferOf.stageTransition` — both finite-transfer directions
  expose the same stage interface.
* `Schoenflies.StageTransition.trans` — consecutive transferred refinements compose.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
open Set


-- @@ L32-32 verbatim
namespace Schoenflies


-- @@ L34-35 verbatim
variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}


-- @@ L37-48 verbatim
/-- The information about consecutive generated pairs consumed by `StageSequence`. -/
structure StageTransition
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (par : γ → γ) : Prop where
  /-- The new source realization refines the preceding source realization. -/
  refines_src : T.src.Refines P.src par
  /-- The target realizations refine along the same abstract parent map. -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The realized source skeleton grows. -/
  sourceSkeletonSet_subset : P.src.skeletonSet ⊆ T.src.skeletonSet
  /-- The new skeleton homeomorphism extends the preceding one. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet


-- @@ L50-50 verbatim
namespace StageTransition


-- @@ L52-53 verbatim
variable {P Q T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {par₁ par₂ : γ → γ}


-- @@ L55-61 verbatim
/-- Target skeletons grow as well.  This follows from source-skeleton growth and agreement of
the two skeleton homeomorphisms on the old source skeleton. -/
theorem targetSkeletonSet_subset {par : γ → γ}
    (h : StageTransition T P par) : P.tgt.skeletonSet ⊆ T.tgt.skeletonSet := by
  rw [← P.homeo.image_skeletonSet, ← T.homeo.image_skeletonSet]
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h.sourceSkeletonSet_subset hx, h.homeo_eqOn hx⟩


-- @@ L63-75 verbatim
/-- Consecutive stage transitions compose their parent maps and their nesting data. -/
theorem trans (h₂ : StageTransition T Q par₂) (h₁ : StageTransition Q P par₁) :
    StageTransition T P (par₁ ∘ par₂) where
  refines_src := h₂.refines_src.trans h₁.refines_src
  refines_tgt := h₂.refines_tgt.trans h₁.refines_tgt
  sourceSkeletonSet_subset :=
    h₁.sourceSkeletonSet_subset.trans h₂.sourceSkeletonSet_subset
  homeo_eqOn := by
    intro x hx
    calc
      T.homeo.toFun x = Q.homeo.toFun x :=
        h₂.homeo_eqOn (h₁.sourceSkeletonSet_subset hx)
      _ = P.homeo.toFun x := h₁.homeo_eqOn hx


-- @@ L77-77 verbatim
end StageTransition


-- @@ L79-87 verbatim
/-- Direction (a)'s induction invariant supplies one stage transition. -/
theorem IsPartialTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsPartialTransferOf T P B Hdraw par) : StageTransition T P par where
  refines_src := h.refines_src
  refines_tgt := h.refines_tgt
  sourceSkeletonSet_subset := h.sourceSkeletonSet_subset
  homeo_eqOn := h.homeo_eqOn


-- @@ L89-97 verbatim
/-- Direction (b)'s induction invariant supplies the identical stage transition. -/
theorem IsTargetPartialTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTargetPartialTransferOf T P B Hdraw par) : StageTransition T P par where
  refines_src := h.refines_src
  refines_tgt := h.refines_tgt
  sourceSkeletonSet_subset := h.sourceSkeletonSet_subset
  homeo_eqOn := h.homeo_eqOn


-- @@ L99-104 verbatim
/-- The admissible conclusion of direction (a) forgets to the same stage transition. -/
theorem IsTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTransferOf T P H Hdraw par) : StageTransition T P par :=
  h.toIsPartialTransferOf.stageTransition


-- @@ L106-111 verbatim
/-- The admissible conclusion of direction (b) forgets to the same stage transition. -/
theorem IsTargetTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTargetTransferOf T P H Hdraw par) : StageTransition T P par :=
  h.toIsTargetPartialTransferOf.stageTransition


-- @@ L113-113 verbatim
end Schoenflies
