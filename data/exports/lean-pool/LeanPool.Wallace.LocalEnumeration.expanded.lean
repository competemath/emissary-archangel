/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Encodable


-- @@ L12-14 verbatim
/-!
# Enumeration of a countable local direct sum
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace Wallace


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
universe u v


-- @@ L24-28 verbatim
/-- A fixed surjective enumeration of the direct sum over a countable coordinate set. -/
def countableFinsuppEnumeration {I : Type u} {R : Type v} [Zero R] [Countable R]
    (D : Set I) (hD : D.Countable) : ℕ → (D →₀ R) := by
  letI : Countable D := hD.to_subtype
  exact Classical.choose (exists_surjective_nat (D →₀ R))


-- @@ L30-34 verbatim
theorem countableFinsuppEnumeration_surjective {I : Type u} {R : Type v}
    [Zero R] [Countable R] (D : Set I) (hD : D.Countable) :
    Function.Surjective (countableFinsuppEnumeration D hD : ℕ → (D →₀ R)) := by
  let : Countable D := hD.to_subtype
  exact Classical.choose_spec (exists_surjective_nat (D →₀ R))


-- @@ L36-36 verbatim
end


-- @@ L38-38 verbatim
end Wallace
