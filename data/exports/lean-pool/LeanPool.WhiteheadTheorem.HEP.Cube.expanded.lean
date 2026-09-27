/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import LeanPool.WhiteheadTheorem.HEP.Cofibration
public import LeanPool.WhiteheadTheorem.Shapes.Cube
import LeanPool.WhiteheadTheorem.Shapes.DiskHomeoCube


-- @@ L12-15 verbatim
/-!
In this file, the homotopy extension property (HEP) of the pair $(I^n, ∂I^n)$
is derived from the HEP of $(D^n, ∂D^n)$.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open CategoryTheory TopCat

-- @@ L20-20 verbatim
open scoped Topology unitInterval



-- @@ L23-36 verbatim
/--
```
  ∂𝔻 n ---φ---> ∂I^n ------h---> C(I, Y)
  |       ≃       |                |
  i               ι            pathStart
  |               |                |
  v       ≃       v                v
  𝔻 n ----Φ--> I^ (Fin n) ---f---> Y
```
-/
instance Cube.boundaryIncl_isCofibration (n : ℕ) :
    IsCofibration <| TopCat.ofHom (Cube.boundaryIncl n) where
  hasCurriedHEP _ :=
    ⟨HasLiftingProperty.of_arrow_iso_left (diskPair.homeoCubePair n) _⟩


-- @@ L38-41 verbatim
instance Cube.boundaryIncl_prod_unitInterval_isCofibration (n : ℕ) :
    IsCofibration <| TopCat.ofHom <| (Cube.boundaryIncl n).prodMap (ContinuousMap.id I) := by
  change IsCofibration <| TopCat.ofHom <| (TopCat.ofHom <| Cube.boundaryIncl n).hom.prodMap _
  apply IsCofibration.prod_unitInterval


-- @@ L43-47 verbatim
theorem Cube.boundaryIncl_hasHEP
    (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (Cube.boundaryIncl n) Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
    (Cube.boundaryIncl_isCofibration n) (TopCat.of Y)


-- @@ L49-53 verbatim
theorem Cube.boundaryIncl_prod_unitInterval_hasHEP
    (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty ((Cube.boundaryIncl n).prodMap (ContinuousMap.id I)) Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
     (Cube.boundaryIncl_prod_unitInterval_isCofibration n) (TopCat.of Y)



-- @@ L56-58 verbatim
/-!
The universe-polymorphic version of the above theorems
-/


-- @@ L60-60 verbatim
namespace TopCat


-- @@ L62-62 verbatim
universe u


-- @@ L64-67 verbatim
instance cubeBoundaryIncl_isCofibration (n : ℕ) :
    IsCofibration (cubeBoundaryIncl.{u} n) where
  hasCurriedHEP _ :=
    ⟨HasLiftingProperty.of_arrow_iso_left (diskPair.homeoCubePairULift n) _⟩


-- @@ L69-72 verbatim
instance cubeBoundaryIncl_prod_unitInterval_isCofibration (n : ℕ) :
    IsCofibration <| TopCat.ofHom <|
    (cubeBoundaryIncl.{u} n).hom.prodMap (ContinuousMap.id I) := by
  apply IsCofibration.prod_unitInterval


-- @@ L74-78 verbatim
theorem cubeBoundaryIncl_hasHEP
    (n : ℕ) (Y : Type u) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty (cubeBoundaryIncl.{u} n).hom Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
    (cubeBoundaryIncl_isCofibration n) (TopCat.of Y)


-- @@ L80-84 verbatim
theorem cubeBoundaryIncl_prod_unitInterval_hasHEP
    (n : ℕ) (Y : Type u) [TopologicalSpace Y] :
    HasHomotopyExtensionProperty ((cubeBoundaryIncl n).hom.prodMap (ContinuousMap.id I)) Y :=
  IsCofibration.iff_hasHomotopyExtensionProperty _ |>.mp
     (cubeBoundaryIncl_prod_unitInterval_isCofibration n) (TopCat.of Y)


-- @@ L86-86 verbatim
end TopCat
