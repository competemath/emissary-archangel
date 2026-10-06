/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.TilingExp
import DescriptiveComplexity.Problems.Tiling.CorridorMem
import DescriptiveComplexity.Exponential.Classes


-- @@ L10-24 verbatim
/-!
# The wide corridor: a strip as wide as the addresses

`DescriptiveComplexity.CORRIDOR` with one exponent added in the semantics of the
problem, exactly as `DescriptiveComplexity.WideTiling` adds one to
`DescriptiveComplexity.TILING`: the columns are the **subsets** of the instance,
while the tiles stay an ordinary part of it, and the rows are numbers.

So an instance of size `n` asks whether a corridor of width `2ⁿ` can be tiled
upward until an accepting tile appears – the classical second complete problem
of EXPSPACE beside a machine. The tile system it reads off an instance is the
same `DescriptiveComplexity.wideTileData` as the square's, so the two problems
differ only in the question asked, and the membership is again a composition:
the corridor of the exponential expansion, `CORRIDOR` being in PSPACE.
-/


-- @@ L26-26 verbatim
namespace DescriptiveComplexity


-- @@ L28-28 verbatim
open FirstOrder


-- @@ L30-30 verbatim
open Language Structure


-- @@ L32-32 verbatim
/-! ### The problem -/


-- @@ L34-34 verbatim
section Problem


-- @@ L36-45 verbatim
/-- **The two halves transport**, in either direction. -/
theorem wideCorridor_map {A B : Type} [Language.wtile.Structure A] [Language.wtile.Structure B]
    (e : A ≃[Language.wtile] B)
    (h : (wideTileData A).WellFormed ∧ (wideTileData A).CorridorTileable) :
    (wideTileData B).WellFormed ∧ (wideTileData B).CorridorTileable :=
  ⟨TileData.wellFormed_map _ (wtPointEquiv e) _ (wtPosn_map e) (wtLe_point_map e) h.1,
    TileData.corridorTileable_map _ (wtPointEquiv e) _ (wtPosn_map e) (wtLe_point_map e)
      (wtTile_point_map e) (wtAcc_point_map e) (wtHoriz_point_map e)
      (wtVert_point_map e) (wtFirst_point_map e) (wtBase_point_map e)
      (wtStart_point_map e) (wtEdgeL_point_map e) (wtEdgeR_point_map e) h.2⟩


-- @@ L47-52 verbatim
/-- **Tiling a wide corridor.** Can the strip whose width is the *subsets* of
the instance be tiled upward, from the bottom row the description allows until
an accepting tile appears? -/
def WideCorridor : DecisionProblem Language.wtile where
  Holds := fun A _ => (wideTileData A).WellFormed ∧ (wideTileData A).CorridorTileable
  iso_invariant := fun {_ _} _ _ e => ⟨wideCorridor_map e, wideCorridor_map e.symm⟩


-- @@ L54-54 verbatim
end Problem


-- @@ L56-56 verbatim
/-! ### The membership -/


-- @@ L58-58 verbatim
section Membership


-- @@ L60-60 verbatim
open WideTile


-- @@ L62-92 verbatim
/-- **A wide corridor is an ordinary corridor of the expansion.** The tile
system is the one `DescriptiveComplexity.WideTile.wtileAgree` matches field by
field; only the question differs. -/
theorem wideCorridor_iff_expansion (A : Type) [Language.wtile.Structure A] [LinearOrder A] :
    letI := wtileStructure A
    (WideCorridor A ↔ CORRIDOR (wtileExp.Map A)) := by
  let := wtileStructure A
  obtain ⟨hposn, hle, htile, hacc, hhoriz, hvert, hfirst, hbase, hstart, hel, her⟩ :=
    wtileAgree (A := A)
  constructor
  · exact fun h => ⟨TileData.wellFormed_map _ wtileEquiv _ hposn hle h.1,
      TileData.corridorTileable_map _ wtileEquiv _ hposn hle htile hacc hhoriz hvert hfirst
        hbase hstart hel her h.2⟩
  · -- and back, along the inverse bijection
    have hback : ∀ {P : WPoint A → Prop} {Q : wtileExp.Map A → Prop},
        (∀ p, P p ↔ Q (wtileEquiv p)) → ∀ p, Q p ↔ P (wtileEquiv.symm p) := by
      intro P Q h p
      have h' := h (wtileEquiv.symm p)
      rw [Equiv.apply_symm_apply] at h'
      exact h'.symm
    have hback₂ : ∀ {P : WPoint A → WPoint A → Prop} {Q : wtileExp.Map A → wtileExp.Map A → Prop},
        (∀ p q, P p q ↔ Q (wtileEquiv p) (wtileEquiv q)) →
        ∀ p q, Q p q ↔ P (wtileEquiv.symm p) (wtileEquiv.symm q) := by
      intro P Q h p q
      have h' := h (wtileEquiv.symm p) (wtileEquiv.symm q)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
      exact h'.symm
    exact fun h => ⟨TileData.wellFormed_map _ wtileEquiv.symm _ (hback hposn) (hback₂ hle) h.1,
      TileData.corridorTileable_map _ wtileEquiv.symm _ (hback hposn) (hback₂ hle)
        (hback htile) (hback hacc) (hback₂ hhoriz) (hback₂ hvert) (hback₂ hfirst)
        (hback hbase) (hback hstart) (hback hel) (hback her) h.2⟩


-- @@ L94-103 verbatim
/-- **The wide corridor is in EXPSPACE**, which is `PSPACE.exp`: the expansion
turns it into `DescriptiveComplexity.CORRIDOR`, and that problem is in PSPACE.
This is the second natural member the class has, beside the wide machine. -/
theorem wideCorridor_mem_EXPSPACE : WideCorridor ∈ EXPSPACE := by
  let hinst : ∀ (A : Type) [Language.wtile.Structure A] [LinearOrder A],
      Language.tiling.Structure (wtileExp.Map A) := fun A => wtileStructure A
  rw [EXPSPACE_eq_PSPACE_exp]
  refine ⟨wtileExp, CORRIDOR, corridor_mem_PSPACE, ?_⟩
  intro A _ _ _ _
  exact wideCorridor_iff_expansion A


-- @@ L105-105 verbatim
end Membership


-- @@ L107-107 verbatim
end DescriptiveComplexity
