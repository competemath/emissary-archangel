/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.RoseTree.Defs


-- @@ L10-14 verbatim
/-!
# LeanPool.QuasiBorelSpaces.Rose.Encoding

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Rose.Encoding`.
-/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace Rose


-- @@ L21-21 verbatim
variable {A B C : Type*}


-- @@ L23-28 verbatim
/--
We derive the `QuasiBorelSpace` instance for `Rose A`s from their encoding as
`(_ : Rose Unit) × (List ℕ → A)`.
-/
abbrev Encoding (A : Type*) :=
  (_ : Rose Unit) × (List ℕ → A)


-- @@ L30-30 verbatim
namespace Encoding


-- @@ L32-37 verbatim
/-- The encoded version of `Rose.mk`. -/
def mk (x : A) (xs : List (Encoding A)) : Encoding A where
  fst := ⟨(), List.map Sigma.fst xs⟩
  snd := fun
    | [] => x
    | i :: is => (xs[i]?.map fun k ↦ k.2 is).getD x


-- @@ L39-58 verbatim
/-- The encoded version of `Rose.foldr`. -/
def fold (mk : A → List B → B) : Encoding A → B
  | ⟨⟨(), xs⟩, k⟩ => mk
    (k [])
    (List.ofFn fun i : Fin xs.length ↦ fold mk ⟨xs[i], fun is ↦ k (i :: is)⟩)
  decreasing_by
    simp only [Fin.getElem_fin, Sigma.mk.sizeOf_spec, sizeOf_default, Nat.add_zero, mk.sizeOf_spec,
      Unit.sizeOf, Nat.reduceAdd, Nat.add_lt_add_iff_left]
    induction xs with
    | nil => exact i.elim0
    | cons head tail ih =>
      cases i using Fin.cases with
      | zero =>
        simp only [
          List.length_cons, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          List.getElem_cons_zero, List.cons.sizeOf_spec]
        grind
      | succ i =>
        simp only [List.length_cons, Fin.val_succ, List.getElem_cons_succ, List.cons.sizeOf_spec]
        grind


-- @@ L60-67 verbatim
@[simp]
lemma fold_mk
    (f : A → List B → B) (x : A) (xs : List (Encoding A))
    : fold f (mk x xs) = f x (List.map (fold f) xs) := by
  simp only [
    mk, fold, List.length_map, Fin.getElem_fin, Fin.val_cast, List.getElem_map,
    Fin.is_lt, getElem?_pos, Option.map_some, Option.getD_some, Sigma.eta,
    List.ofFn_getElem_eq_map]


-- @@ L69-71 verbatim
/-- Encodes a `Rose A` as an `Encoding A`. -/
def encode : Rose A → Encoding A :=
  Rose.fold mk


-- @@ L73-75 verbatim
@[simp]
lemma encode_mk (x xs) : encode (A := A) (.mk x xs) = mk x (List.map encode xs) := by
  simp only [encode, Rose.fold.eq_1]


-- @@ L77-77 verbatim
end Encoding


-- @@ L79-79 verbatim
end Rose
