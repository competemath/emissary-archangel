module

public import Mathlib.Tactic.NormNum


-- @@ L5-6 verbatim
@[expose]
public meta section


-- @@ L8-8 verbatim
namespace Qq


-- @@ L10-10 verbatim
open Mathlib Qq Lean Elab Meta Tactic


-- @@ L12-12 verbatim
def rflQ {α : Q(Sort u)} (a : Q($α)) : Q($a = $a) := q(rfl)


-- @@ L14-22 verbatim
def toQList {α : Q(Type u)} : List Q($α) → Q(List $α)
  |     [] => q([])
  | a :: v => q($a :: $(toQList v))

lemma List.mem_of_eq {a b : α} {l} (h : a = b) : a ∈ b :: l := by simp [h]

lemma List.mem_of_mem {a b : α} {l : List α} (h : a ∈ l) : a ∈ b :: l := by simp [h]

lemma List.mem_singleton_of_eq (a b : α) (h : a = b) : a ∈ [b] := by simp [h]


-- @@ L24-32 verbatim
def memQList? {α : Q(Type u)} (a : Q($α)) : (l : List Q($α)) → MetaM <| Option Q($a ∈ $(toQList l))
  |     [] => return none
  | b :: l => do
    if (← isDefEq (← whnf a) (← whnf b)) then
      let e : Q($a = $b) := rflQ a
      return some q(List.mem_of_eq $e)
    else
      let some h ← memQList? a l | return none
      return some q(List.mem_of_mem $h)


-- @@ L34-36 verbatim
def memQList?' (a : Expr) (l : List Expr) : MetaM (Option Expr) := do
  let ⟨u, _, a⟩ ← inferTypeQ' a
  memQList? (u := u) a l


-- @@ L38-41 verbatim
partial def ofQList {α : Q(Type u)} (l : Q(List $α)) : MetaM <| List Q($α) := do
  match l with
  |       ~q([]) => return []
  | ~q($a :: $l) => return a :: (← ofQList l)


-- @@ L43-43 verbatim
end Qq


-- @@ L45-45 verbatim
end
