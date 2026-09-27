/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import LeanPool.WhiteheadTheorem.Shapes.Disk
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs


-- @@ L13-17 verbatim
/-!
# LeanPool.WhiteheadTheorem.CWComplex.Basic

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.CWComplex.Basic`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-34 verbatim
/-!
# CW-complexes
This file defines (relative) CW-complexes.
## Main definitions
* `RelativeCWComplex`: A relative CW-complex is the colimit of an expanding sequence of subspaces
  `sk i` (called the $(i-1)$-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the $(-1)$-skeleton) is an
  arbitrary topological space, and each `sk (n + 1)` (i.e., the $n$-skeleton) is obtained from
  `sk n` (i.e., the $(n-1)$-skeleton) by attaching `n`-disks.
* `CWComplex`: A CW-complex is a relative CW-complex whose `sk 0` (i.e., $(-1)$-skeleton) is empty.
## References
* [R. Fritsch and R. Piccinini, *Cellular Structures in Topology*][fritsch-piccinini1990]
* The definition of CW-complexes follows David Wärn's suggestion on
  [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080).
-/



-- @@ L37-37 verbatim
open CategoryTheory TopCat


-- @@ L39-39 verbatim
universe u


-- @@ L41-41 verbatim
namespace RelCWComplex


-- @@ L43-50 verbatim
/-- A type witnessing that `X'` is obtained from `X` by attaching generalized cells `f : S ⟶ D` -/
structure AttachGeneralizedCells {S D : TopCat.{u}} (f : S ⟶ D) (X X' : TopCat.{u}) where
  /-- The index type over the generalized cells -/
  cells : Type u
  /-- An attaching map for each generalized cell -/
  attachMaps : cells → (S ⟶ X)
  /-- `X'` is the pushout of `∐ S ⟶ X` and `∐ S ⟶ ∐ D`. -/
  isoPushout : X' ≅ Limits.pushout (Limits.Sigma.desc attachMaps) (Limits.Sigma.map fun _ ↦ f)


-- @@ L52-53 verbatim
/-- A type witnessing that `X'` is obtained from `X` by attaching `(n + 1)`-disks -/
abbrev AttachCells (n : ℕ) := AttachGeneralizedCells.{u} (diskBoundaryIncl n)


-- @@ L55-55 verbatim
end RelCWComplex



-- @@ L58-67 verbatim
/-- A relative CW-complex consists of an expanding sequence of subspaces `sk i` (called the
$(i-1)$-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the $(-1)$-skeleton) is an arbitrary topological
space, and each `sk (n + 1)` (i.e., the `n`-skeleton) is obtained from `sk n` (i.e., the
$(n-1)$-skeleton) by attaching `n`-disks. -/
structure RelCWComplex where
  /-- The skeletons. Note: `sk i` is usually called the $(i-1)$-skeleton in the math literature. -/
  sk : ℕ → TopCat.{u}
  /-- Each `sk (n + 1)` (i.e., the $n$-skeleton) is obtained from `sk n`
  (i.e., the $(n-1)$-skeleton) by attaching `n`-disks. -/
  attachCells (n : ℕ) : RelCWComplex.AttachCells n (sk n) (sk (n + 1))


-- @@ L69-72 verbatim
/-- A CW-complex is a relative CW-complex whose `sk 0` (i.e., $(-1)$-skeleton) is empty. -/
structure CWComplex extends RelCWComplex.{u} where
  /-- `sk 0` (i.e., the $(-1)$-skeleton) is empty. -/
  isEmpty_sk_zero : IsEmpty (sk 0)



-- @@ L75-75 verbatim
namespace RelCWComplex


-- @@ L77-77 verbatim
variable {n : ℕ} {X X' : TopCat.{u}}


-- @@ L79-79 verbatim
namespace AttachCells


-- @@ L81-85 verbatim
/-- The inclusion map from `X` to `X'`, given that `X'` is obtained from `X` by attaching
`(n + 1)`-disks -/
noncomputable def incl (att : AttachCells n X X') : X ⟶ X' :=
  Limits.pushout.inl (Limits.Sigma.desc att.attachMaps)
    (Limits.Sigma.map fun _ ↦ diskBoundaryIncl n) ≫ att.isoPushout.inv


-- @@ L87-89 verbatim
/-- The top side of the pushout square -/
noncomputable abbrev sigmaAttachMaps (att : AttachCells n X X') :=
  Limits.Sigma.desc att.attachMaps


-- @@ L91-94 expanded
/-- The left side of the pushout square -/
noncomputable abbrev sigmaDiskBoundaryIncl (att : AttachCells n X X') :
    (∐ fun (_ : att.cells) ↦ diskBoundary n) ⟶ ∐ fun (_ : att.cells) ↦ disk n :=
  Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n


-- @@ L96-103 verbatim
/-- The right side of the pushout square
(TODO: after updating mathlib on 2025-03-08,
using the abbreviation `att.sigmaDiskBoundaryIncl` results in type mismatch,
which seems to be a universe level issue.
So the abbreviation is temporarily replaced with the full definition.) -/
noncomputable abbrev pushoutInl (att : AttachCells.{u} n X X') :=
  Limits.pushout.inl att.sigmaAttachMaps
    (Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n)


-- @@ L105-108 verbatim
/-- The bottom side of the pushout square -/
noncomputable abbrev pushoutInr (att : AttachCells n X X') :=
  Limits.pushout.inr att.sigmaAttachMaps
    (Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n)


-- @@ L110-115 verbatim
/-- The pushout square is a pushout. -/
lemma pushout_isPushout (att : AttachCells n X X') :
    IsPushout att.sigmaAttachMaps (Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n)
      att.pushoutInl att.pushoutInr :=
  IsPushout.of_hasPushout att.sigmaAttachMaps
    (Limits.Sigma.map fun (_ : att.cells) ↦ diskBoundaryIncl n)


-- @@ L117-117 verbatim
end AttachCells


-- @@ L119-122 verbatim
/-- The inclusion map from `sk n` (i.e., the $(n-1)$-skeleton) to `sk (n + 1)` (i.e., the
$n$-skeleton) of a relative CW-complex -/
noncomputable def skInclSucc (X : RelCWComplex) (n : ℕ) : X.sk n ⟶ X.sk (n + 1) :=
  (X.attachCells n).incl


-- @@ L124-128 verbatim
/-- The inclusion map from `sk n` (i.e., the $(n-1)$-skeleton) to `sk m` (i.e., the
$(m-1)$-skeleton) of a relative CW-complex -/
noncomputable def skInclToSk (X : RelCWComplex) {n : ℕ} {m : ℕ} (hnm : n ≤ m) :
    X.sk n ⟶ X.sk m :=
  (Functor.ofSequence X.skInclSucc).map (homOfLE hnm)


-- @@ L130-132 verbatim
/-- The topology on a relative CW-complex -/
noncomputable def toTopCat (X : RelCWComplex) : TopCat.{u} :=
  Limits.colimit (Functor.ofSequence X.skInclSucc)


-- @@ L134-135 verbatim
noncomputable instance : Coe RelCWComplex TopCat where
  coe X := toTopCat X


-- @@ L137-138 verbatim
noncomputable instance : Coe CWComplex TopCat where
  coe X := toTopCat X.toRelCWComplex


-- @@ L140-142 verbatim
/-- The inclusion map from `sk n` (i.e., the $(n-1)$-skeleton of `X`) to `X` -/
noncomputable def skIncl (X : RelCWComplex.{u}) (n : ℕ) : X.sk n ⟶ X :=
  Limits.colimit.ι (Functor.ofSequence _) n


-- @@ L144-150 verbatim
@[simp]
lemma skInclSucc_skIncl_eq (X : RelCWComplex.{u}) (n : ℕ) :
    X.skInclSucc n ≫ X.skIncl (n + 1) = X.skIncl n := by
  unfold skIncl
  rw [show X.skInclSucc n = (Functor.ofSequence X.skInclSucc).map (homOfLE (Nat.le_succ n)) from
    (Functor.ofSequence_map_homOfLE_succ X.skInclSucc n).symm]
  exact Limits.colimit.w (Functor.ofSequence X.skInclSucc) (homOfLE (Nat.le_succ n))



-- @@ L153-153 verbatim
namespace AttachGeneralizedCells


-- @@ L155-155 verbatim
variable {S D : TopCat.{u}} {f : S ⟶ D} {X X' : TopCat.{u}}

-- @@ L156-156 verbatim
variable (att : AttachGeneralizedCells f X X') (α : att.cells)


-- @@ L158-160 verbatim
/-- `pushoutInl` -/
noncomputable abbrev pushoutInl :=
  Limits.pushout.inl (Limits.Sigma.desc att.attachMaps) (Limits.Sigma.map fun _ ↦ f)

-- @@ L161-163 verbatim
/-- `pushoutInr` -/
noncomputable abbrev pushoutInr :=
  Limits.pushout.inr (Limits.Sigma.desc att.attachMaps) (Limits.Sigma.map fun _ ↦ f)


-- @@ L165-167 verbatim
lemma attachMaps_apply_eq_ι_desc : att.attachMaps α =
    Limits.Sigma.ι (fun _ ↦ S) α ≫ Limits.Sigma.desc att.attachMaps :=
  (Limits.Sigma.ι_comp_desc _ _).symm


-- @@ L169-181 verbatim
/--
```
S --> ∐ S
|      |
f      |
↓      ↓
D --> ∐ D
```
-/
@[reassoc]
lemma w_sigma_cells : f ≫ Limits.Sigma.ι (fun _ ↦ D) α =
    Limits.Sigma.ι (fun _ ↦ S) α ≫ (Limits.Sigma.map fun _ ↦ f) := by
  simp [Limits.Sigma.ι_map]


-- @@ L183-195 verbatim
/--
```
S --> ∐ S --> X
|      |      |
f      |      |
↓      ↓      ↓    ≅
D --> ∐ D --> ⬝ ------> X'
```
-/
@[reassoc]
lemma w_cell' : f ≫ Limits.Sigma.ι (fun _ ↦ D) α ≫ att.pushoutInr =
    Limits.Sigma.ι (fun _ ↦ S) α ≫ Limits.Sigma.desc att.attachMaps ≫ att.pushoutInl := by
  rw [w_sigma_cells_assoc, Limits.pushout.condition]


-- @@ L197-209 verbatim
/--
```
S ----------> X
|             |
f             |
↓             ↓    ≅
D --> ∐ D --> ⬝ ------> X'
```
-/
@[reassoc]
lemma w_cell : f ≫ Limits.Sigma.ι (fun _ ↦ D) α ≫ att.pushoutInr =
    att.attachMaps α ≫ att.pushoutInl := by
  rw [attachMaps_apply_eq_ι_desc, w_cell']; rfl


-- @@ L211-211 verbatim
end AttachGeneralizedCells


-- @@ L213-213 verbatim
end RelCWComplex
