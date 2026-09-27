/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Syntax.Formula
import Mathlib.Tactic.Bound.Init


-- @@ L11-11 verbatim
/-! # Coding -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace FirstOrder


-- @@ L19-19 verbatim
variable {L : Language} [(k : ℕ) → Encodable (L.Func k)]


-- @@ L21-21 verbatim
variable {ξ : Type*} [Encodable ξ]


-- @@ L23-23 verbatim
open Encodable


-- @@ L25-25 verbatim
namespace Semiterm


-- @@ L27-32 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def toNat {n : ℕ} : Semiterm L ξ n → ℕ
  | #z                        => Nat.pair 0 z + 1
  | &x                        => Nat.pair 1 (encode x) + 1
  | func (arity := arity) f v =>
    (Nat.pair 2 <| Nat.pair arity <| Nat.pair (encode f) <| Matrix.vecToNat fun i ↦ toNat (v i)) + 1


-- @@ L34-57 verbatim
def ofNat (n : ℕ) : ℕ → Option (Semiterm L ξ n)
  | 0 => none
  | e + 1 =>
    match e.unpair.1 with
    | 0 => if h : e.unpair.2 < n then some #⟨e.unpair.2, h⟩ else none
    | 1 => (decode e.unpair.2).map (&·)
    | 2 =>
      let arity := e.unpair.2.unpair.1
      let ef := e.unpair.2.unpair.2.unpair.1
      let ev := e.unpair.2.unpair.2.unpair.2
      match hv : ev.natToVec arity with
      | some v' =>
        (decode ef).bind fun f : L.Func arity ↦
        (Matrix.getM fun i ↦
          have : v' i < e + 1 :=
            Nat.lt_succ_iff.mpr
              <| le_trans (le_of_lt <| Nat.lt_of_eq_natToVec hv i)
              <| le_trans (Nat.unpair_right_le _)
              <| le_trans (Nat.unpair_right_le _)
              <| Nat.unpair_right_le _
          ofNat n (v' i)).map fun v : Fin arity → Semiterm L ξ n ↦
        func f v
      | none => none
    | _ => none


-- @@ L59-69 verbatim
lemma ofNat_toNat {n : ℕ} : ∀ t : Semiterm L ξ n, ofNat n (toNat t) = some t
  | #z => by simp [toNat, ofNat]
  | &x => by simp [toNat, ofNat]
  | func f v => by
      simp only [toNat, ofNat, Nat.unpair_pair]
      rw [Nat.unpair_pair, Nat.unpair_pair, Nat.unpair_pair, Nat.natToVec_vecToNat]
      simp only [encodek, Option.bind_some, Option.map_eq_some_iff, func.injEq, heq_eq_eq,
        true_and, exists_eq_right]
      have : (fun i ↦ ofNat n (toNat (v i))) = (fun i ↦ pure (v i)) :=
        funext <| fun i ↦ ofNat_toNat (v i)
      simp_all


-- @@ L71-74 verbatim
instance encodable : Encodable (Semiterm L ξ n) where
  encode := toNat
  decode := ofNat n
  encodek := ofNat_toNat


-- @@ L76-76 verbatim
end Semiterm


-- @@ L78-78 verbatim
namespace Semiformula


-- @@ L80-80 verbatim
variable [(k : ℕ) → Encodable (L.Rel k)]


-- @@ L82-93 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def toNat : {n : ℕ} → Semiformula L ξ n → ℕ
  | _, rel (arity := arity) R v =>
    (Nat.pair 0 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  | _, nrel (arity := arity) R v =>
    (Nat.pair 1 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  | _, ⊤ => (Nat.pair 2 0) + 1
  | _, ⊥ => (Nat.pair 3 0) + 1
  | _, Wedge.wedge φ ψ => (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1
  | _, Vee.vee φ ψ => (Nat.pair 5 <| φ.toNat.pair ψ.toNat) + 1
  | _, UnivQuantifier.univ φ => (Nat.pair 6 <| φ.toNat) + 1
  | _, ExQuantifier.ex φ => (Nat.pair 7 <| φ.toNat) + 1


-- @@ L95-151 expanded
def ofNat : (n : ℕ) → ℕ → Option (Semiformula L ξ n)
  | _, 0 => none
  | n, e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 =>
      let arity := c.unpair.1
      let eR := c.unpair.2.unpair.1
      let ev := c.unpair.2.unpair.2
      match ev.natToVec arity with
      | some v' =>
        (decode eR).bind fun R : L.Rel arity ↦
          (Matrix.getM fun i ↦ decode (v' i)).map fun v : Fin arity → Semiterm L ξ n ↦ rel R v
      | none => none
    | 1 =>
      let arity := c.unpair.1
      let eR := c.unpair.2.unpair.1
      let ev := c.unpair.2.unpair.2
      match ev.natToVec arity with
      | some v' =>
        (decode eR).bind fun R : L.Rel arity ↦
          (Matrix.getM fun i ↦ decode (v' i)).map fun v : Fin arity → Semiterm L ξ n ↦ nrel R v
      | none => none
    | 2 => some ⊤
    | 3 => some ⊥
    | 4 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
      let φ ← ofNat n c.unpair.1
      let ψ ← ofNat n c.unpair.2
      return Wedge.wedge φ ψ
    | 5 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
      let φ ← ofNat n c.unpair.1
      let ψ ← ofNat n c.unpair.2
      return Vee.vee φ ψ
    | 6 =>
      have : c < e + 1 := Nat.lt_succ_iff.mpr <| Nat.unpair_right_le _
      do
      let φ ← ofNat (n + 1) c
      return UnivQuantifier.univ φ
    | 7 =>
      have : c < e + 1 := Nat.lt_succ_iff.mpr <| Nat.unpair_right_le _
      do
      let φ ← ofNat (n + 1) c
      return ExQuantifier.ex φ
    | _ => none


-- @@ L153-167 expanded
lemma ofNat_toNat : {n : ℕ} → ∀ φ : Semiformula L ξ n, ofNat n (toNat φ) = some φ
  | _, rel R v => by
    simp only [toNat, ofNat, Nat.unpair_pair]
    rw [Nat.unpair_pair, Nat.unpair_pair]
    simp []
  | _, nrel R v => by
    simp only [toNat, ofNat, Nat.unpair_pair]
    rw [Nat.unpair_pair, Nat.unpair_pair]
    simp []
  | _, ⊤ => by simp [toNat, ofNat]
  | _, ⊥ => by simp [toNat, ofNat]
  | _, Vee.vee φ ψ => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | _, Wedge.wedge φ ψ => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | _, UnivQuantifier.univ φ => by simp [toNat, ofNat, ofNat_toNat φ]
  | _, ExQuantifier.ex φ => by simp [toNat, ofNat, ofNat_toNat φ]


-- @@ L169-172 verbatim
instance encodable : Encodable (Semiformula L ξ n) where
  encode := toNat
  decode := ofNat n
  encodek := ofNat_toNat


-- @@ L174-174 verbatim
end Semiformula


-- @@ L176-176 verbatim
end FirstOrder

-- @@ L177-177 verbatim
end LO
