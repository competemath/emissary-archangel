/-
Copyright (c) 2026 André Hernandez-Espiet, Vladimir Sedlacek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: André Hernandez-Espiet, Vladimir Sedlacek
-/
module

public import LeanPool.SyntheticEuclid4.Axioms
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L16-22 verbatim
/-!
Symmetry lemmas for the permutation tactics. These rewrite the geometric
primitives (`area`, `colinear`, `triangle`, `length`, `angle`, `SameSide`,
`diffside`, `para`) under permutations of their point arguments, and serve as
the building blocks for the `perm`/`perma`/`linperm` tactics defined in
`PermTactics`.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace SyntheticEuclid4


-- @@ L28-28 verbatim
open IncidenceGeometry


-- @@ L30-30 verbatim
variable [i : IncidenceGeometry] {a b c : Point}


-- @@ L32-32 verbatim
lemma ar132 : area a b c = area a c b := (area_invariant a b c).2


-- @@ L34-34 verbatim
lemma ar312 : area a b c = area c a b := (area_invariant a b c).1


-- @@ L36-37 verbatim
lemma ar231 : area a b c = area b c a :=
  by rw [(area_invariant a b c).1, (area_invariant c a b).1]


-- @@ L39-40 verbatim
lemma ar213 : area a b c = area b a c :=
  by rw [(area_invariant a b c).2, (area_invariant a c b).1]


-- @@ L42-43 verbatim
lemma ar321 : area a b c = area c b a :=
  by rw [(area_invariant a b c).2, (area_invariant c b a).1]


-- @@ L45-46 verbatim
lemma col213 : colinear a b c ↔ colinear b a c :=
  exists_congr fun _ => and_left_comm


-- @@ L48-49 verbatim
lemma col231 : colinear a b c ↔ colinear b c a :=
  exists_congr fun _ => and_rotate


-- @@ L51-51 verbatim
lemma col132 : colinear a b c ↔ colinear a c b := by conv => rhs; rw [col213]; rw [col231]


-- @@ L53-53 verbatim
lemma col312 : colinear a b c ↔ colinear c a b := by conv => lhs; rw [← col231]


-- @@ L55-55 verbatim
lemma col321 : colinear a b c ↔ colinear c b a := by conv => rhs; rw [col231]; rw [col213]


-- @@ L57-58 verbatim
lemma tr132 : triangle a b c ↔ triangle a c b := by
  constructor; all_goals dsimp [triangle]; rw [col132]; tauto


-- @@ L60-61 verbatim
lemma tr213 : triangle a b c ↔ triangle b a c := by
  constructor; all_goals dsimp [triangle]; rw [col213]; tauto


-- @@ L63-66 verbatim
lemma tr231 : triangle a b c ↔ triangle b c a := by
  constructor
  · dsimp [triangle]; rw [col231]; tauto
  · dsimp [triangle]; rw [← col231]; tauto


-- @@ L68-71 verbatim
lemma tr312 : triangle a b c ↔ triangle c a b := by
  constructor
  · dsimp [triangle]; rw [col312]; tauto
  · dsimp [triangle]; rw [← col312]; tauto


-- @@ L73-74 verbatim
lemma tr321 : triangle a b c ↔ triangle c b a := by
  constructor; all_goals dsimp [triangle]; rw [col321]; tauto


-- @@ L76-77 verbatim
lemma ss21 {a b : Point} {L : Line} : SameSide a b L ↔ SameSide b a L :=
  ⟨sameside_symm, sameside_symm⟩


-- @@ L79-81 verbatim
lemma ds21 {a b : Point} {L : Line} : diffside a b L ↔ diffside b a L :=
  ⟨fun ⟨naL, nbL, nss⟩ => ⟨nbL, naL, fun h => nss (sameside_symm h)⟩,
   fun ⟨naL, nbL, nss⟩ => ⟨nbL, naL, fun h => nss (sameside_symm h)⟩⟩


-- @@ L83-84 verbatim
lemma para21 {L M : Line} : para L M ↔ para M L :=
  ⟨fun p e => (p e).symm, fun p e => (p e).symm⟩


-- @@ L86-86 verbatim
end SyntheticEuclid4
