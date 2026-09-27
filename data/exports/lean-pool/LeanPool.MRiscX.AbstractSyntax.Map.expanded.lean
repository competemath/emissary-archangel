/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
/-
Maps

These maps are converted from
  title={Software foundations},
  author={Pierce, Benjamin C and Casinghino, Chris and Gaboardi, Marco and Greenberg, Michael
          and Hri{\c{t}}cu, C{\u{a}}t{\u{a}}lin and Sj{\"o}berg, Vilhelm and Yorgey, Brent},
  journal={Webpage: http://www. cis. upenn. edu/bcpierce/sf/current/index. html},
-/
module


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-38 verbatim
/--
Total map as recursive type with a key type α and value of type β.
The empty map takes a default value d of type β.
-/
inductive TMap (α : Type) (β : Type) where
  | empty (d : β): TMap α β
  | put (k : α ) (v : β) (t : TMap α β ) : TMap α β
deriving Repr, Inhabited


/-
In order to recieve a value to a given key, we need a
function that searches for key in map.
If the given key is found in map, return corresponding value.
If the key is not found in the map, return the default value.
When there are multiple keys in the map, the last one (the newest) value to that key will be
returned.
This function requires, that the type of the key `α` has the typeclasses BEq and LawfulBEq
implemented.
-/

-- @@ L39-39 verbatim
namespace TMap

  
-- @@ L41-48 verbatim
/--
    Let k ∈ α and v, d ∈ β.
    The function TMap.get(k) returns either the value v assigned to k or d as the default value if no assignment to k.
  -/
  def get {α : Type} [BEq α] [LawfulBEq α] {β : Type} (map : TMap α β) (k : α):=
    match map with
    | TMap.empty d => d
    | TMap.put k' v t => if k == k' then v else TMap.get t k


  
-- @@ L51-56 verbatim
/-- Accumulate the keys of a `TMap` onto `list`, used by `getKeys`. -/
  def getKeysAux {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : TMap α β) (list : List α)
      : List α :=
    match map with
    | TMap.empty _ => list
    | TMap.put k _ t => t.getKeysAux (k :: list)

  
-- @@ L58-62 verbatim
/--
    Get all keys of a map as a list
  -/
  def getKeys {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : TMap α β) : List α :=
    (map.getKeysAux [])

  
-- @@ L64-68 verbatim
/-- The most recently inserted key of a `TMap`, if any. -/
  def getLastKey {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : TMap α β) : Option α :=
    match map.getKeys.reverse with
    | List.cons v _ => some v
    | _ => none

  
-- @@ L70-75 verbatim
/-- Accumulate the values of a `TMap` onto `list`, used by `getValues`. -/
  def getValuesAux {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map: TMap α β) (list : List β)
      : List β :=
    match map with
    | TMap.empty _ => list
    | TMap.put _ v t => t.getValuesAux (v :: list)

  
-- @@ L77-81 verbatim
/--
    Get all values of a map as a list
  -/
  def getValues {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : TMap α β) : List β :=
    (map.getValuesAux [])

  
-- @@ L83-87 verbatim
/-- Render the bindings of a `TMap` as a `; `-separated string, used by `toString`. -/
  def toStringAux {α : Type} {β : Type} [ToString α][ToString β] (t : TMap α β) : String :=
    match t with
    | TMap.empty d => s!"{d}"
    | TMap.put k v t' => s!"{k} ↦ {v}; " ++ t'.toStringAux ++ ""

  
-- @@ L89-92 verbatim
/-- Render a `TMap` as a parenthesised string of its bindings. -/
  def toString {α : Type} {β : Type} [ToString α][ToString β] (t : TMap α β) : String :=
    let s := toStringAux t
    "(" ++ s ++ ")"

-- @@ L93-93 verbatim
end TMap


-- @@ L95-96 verbatim
instance {α β} [ToString α] [ToString β]: Repr (TMap (α : Type) (β :Type)) where
  reprPrec t _ := t.toString



-- @@ L99-100 verbatim
/-- Notation `(k ↦ v; m)` for inserting the binding `k ↦ v` into the total map `m`. -/
notation:60 "(" k " ↦ "v"; "m")" => TMap.put k v m



-- @@ L103-116 verbatim
/--
Partial map as recursive type with a key type α and value of type β is defined.
Returns an option.
-/
inductive PMap (α : Type) (β : Type) where
  | empty : PMap α β
  | put (k : α ) (v : β) (t : PMap α β )  : PMap α β
deriving Repr, Inhabited

/-
The get-function is also mandatory.
This function differs from the TMap.get by returning corresponding value as option.
If the key is not found in the map, return none.
-/

-- @@ L117-117 verbatim
namespace PMap
  
-- @@ L118-127 verbatim
/--
    Let k ∈ α and v ∈ β, then PMap.get(k) returns some v
      (v wrapped inside an option object),
    when k is assigned to some v.
    Return none, else.
  -/
  def get {α : Type} {β : Type}[BEq α](map : PMap α β) (k : α) :=
    match map with
    | PMap.empty => none
    | PMap.put k' v t => if k == k' then some v else PMap.get t k

  
-- @@ L129-134 verbatim
/-- Accumulate the keys of a `PMap` onto `list`, used by `getKeys`. -/
  def getKeysAux {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : PMap α β) (list : List α)
      : List α :=
    match map with
    | PMap.empty => list
    | PMap.put k _ t => t.getKeysAux (k :: list)

  
-- @@ L136-138 verbatim
/-- Get all keys of a `PMap` as a list. -/
  def getKeys {α : Type} {β : Type} [BEq α] [LawfulBEq α] (map : PMap α β) : List α :=
    (map.getKeysAux [])

  
-- @@ L140-144 verbatim
/-- Render the bindings of a `PMap` as a `; `-separated string, used by `toString`. -/
  def toStringAux {α : Type} {β : Type} [ToString α][ToString β] (p : PMap α β) : String :=
    match p with
    | PMap.empty => s!"()"
    | PMap.put k v p' => s!"{k} ↦ {v}; " ++ p'.toStringAux ++ ""

  
-- @@ L146-149 verbatim
/-- Render a `PMap` as a parenthesised string of its bindings. -/
  def toString {α : Type} {β : Type} [ToString α][ToString β] (p : PMap α β) : String :=
    let s := toStringAux p
    "p(" ++ s ++ ")"


-- @@ L151-151 verbatim
end PMap


-- @@ L153-154 verbatim
instance {α β} [ToString α] [ToString β]: Repr (PMap (α : Type) (β :Type)) where
  reprPrec p _ := p.toString



-- @@ L157-158 verbatim
/-- Notation `p(k ↦ v; m)` for inserting the binding `k ↦ v` into the partial map `m`. -/
notation:60 "p("k" ↦ "v"; "m")" => PMap.put k v m



-- @@ L161-173 expanded
/-- This theorem states, when a given map [t] which contains the key [k]
with the value [v] as last entry, the function `TMap.get` returns the
corresponding value [v].
-/
@[simp]
theorem t_update_eq :
    ∀ (α : Type) (β : Type) [BEq α] [LawfulBEq α] (t : TMap α β) (k : α) (v : β),
      (TMap.put k v t).get k = v :=
  by
  intros α β t k v ct
  unfold TMap.get
  simp


-- @@ L175-189 expanded
/-- If a total map [t] is updated with some k ∈ α and v ∈ β (k ↦ v; t),
and we search for some key [k'] with k ≠ k', we get the same result
as when we would just search [t] for [k'].
-/
@[simp]
theorem t_update_neq :
    ∀ (α : Type) (β : Type) [BEq α] [LawfulBEq α] (t : TMap α β) (k k' : α) (v : β),
      k ≠ k' → (TMap.put k v t).get k' = t.get k' :=
  by
  intros α β HBEq HLawfulBEq t k k' v HNeq
  simp at HNeq
  show (if k' == k then v else t.get k') = t.get k'
  rw [ite_eq_right]
  simpa only [beq_iff_eq] using fun h => HNeq h.symm


-- @@ L191-203 expanded
/-- This theorem states, when a given map [p] which contains the key [k]
with the value [v] as last entry, the function `PMap.get` returns the
corresponding value [v].
-/
@[simp]
theorem p_update_eq :
    ∀ (α : Type) (β : Type) [BEq α] [LawfulBEq α] (p : PMap α β) (k : α) (v : β),
      (PMap.put k v p).get k = v :=
  by
  intros α β p k v ct
  unfold PMap.get
  simp


-- @@ L205-219 expanded
/-- If a partial map [p] is updated with some k ∈ α and v ∈ β (k ↦ v; p),
and we search for some key [k'] with k ≠ k', we get the same result
as when we would just search [t] for [k'].
-/
@[simp]
theorem p_update_neq :
    ∀ (α : Type) (β : Type) [BEq α] [LawfulBEq α] (p : PMap α β) (k k' : α) (v : β),
      k ≠ k' → (PMap.put k v p).get k' = p.get k' :=
  by
  intros α β HBEq HLawfulBEq p k k' v HNeq
  simp at HNeq
  show (if k' == k then some v else p.get k') = p.get k'
  rw [ite_eq_right]
  simpa only [beq_iff_eq] using fun h => HNeq h.symm

