/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.TorsionFreeCoordinate
public import LeanPool.Wallace.RationalAssembly
public import LeanPool.Wallace.PackageTransport
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init


-- @@ L14-21 verbatim
/-!
# The main theorem for every torsion-free Abelian group of cardinality continuum

This module closes the scope gap between the canonical rational construction and the exact main
theorem stated in the paper.  The rational character package is pulled back along the
coordinatization embedding from Section 2.  Its prescribed basis limits lie in the embedded
group by construction, so no new fusion or set-theoretic hypothesis is needed.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
open Cardinal


-- @@ L27-27 verbatim
namespace Wallace


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace RationalCoordinatization


-- @@ L33-33 verbatim
variable {G : Type} [AddCommGroup G]


-- @@ L35-49 verbatim
/-- Pull the fully constructed rational character package back to a coordinatized group. -/
def fullCharacterPackage (K : RationalCoordinatization G) : FullCharacterPackage G :=
  RationalAssembly.fullCharacterPackage.pullback
    K.embedding K.embedding_injective
    (fun s ↦ K.basisPreimage
      (RationalTriangularPreprocess.codeIndex
        (RationalAssembly.fullCharacterPackage.embeddedCode
          K.embedding K.embedding_injective s)))
    (fun s ↦ by
      simpa [RationalAssembly.fullCharacterPackage,
        RationalTriangularPreprocess.codeBasisVector] using
        K.embedding_basisPreimage
          (RationalTriangularPreprocess.codeIndex
            (RationalAssembly.fullCharacterPackage.embeddedCode
              K.embedding K.embedding_injective s)))


-- @@ L51-55 verbatim
/-- Every group with the paper's rational coordinatization inherits the complete topology
conclusion from the unconditional rational construction. -/
theorem hasMainGroupTopology (K : RationalCoordinatization G) :
    HasMainGroupTopology G :=
  K.fullCharacterPackage.hasMainGroupTopology


-- @@ L57-57 verbatim
end RationalCoordinatization


-- @@ L59-67 verbatim
/-- **Formal counterpart of the paper's main theorem.**  Every torsion-free Abelian group of
cardinality continuum admits a Hausdorff countably compact group topology in which every
convergent sequence is eventually constant.  The formal conclusion additionally records a
compatible totally bounded uniform group structure.  `Wallace.Audit` records the standard
classical Lean foundations used by the proof. -/
theorem torsionFreeAbelianGroup_mainTheorem
    (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (hcard : #G = 𝔠) : HasMainGroupTopology G :=
  (RationalCoordinatization.ofCardinalityContinuum hcard).hasMainGroupTopology


-- @@ L69-84 verbatim
/-- The exact paper-level projection of the main theorem, with only the properties printed in
the theorem statement and no additional uniform-space fields exposed. -/
theorem torsionFreeAbelianGroup_mainTheorem_exact
    (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (hcard : #G = 𝔠) :
    ∃ topology : TopologicalSpace G,
      @IsTopologicalAddGroup G topology _ ∧
      @T2Space G topology ∧
      @CountablyCompactSpace G topology ∧
      (∀ (s : ℕ → G) (x : G),
        Filter.Tendsto s Filter.atTop (@nhds G topology x) →
          ∀ᶠ n in Filter.atTop, s n = x) := by
  obtain ⟨topology, _uniformity, _hcompat, _huniformGroup,
    htopologicalGroup, hT2, hcompact, _htotallyBounded, hsequences⟩ :=
      torsionFreeAbelianGroup_mainTheorem G hcard
  exact ⟨topology, htopologicalGroup, hT2, hcompact, hsequences⟩


-- @@ L86-86 verbatim
end


-- @@ L88-88 verbatim
end Wallace
