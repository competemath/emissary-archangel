/-
Copyright (c) 2026 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/
module

public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Attr.Core


-- @@ L11-28 verbatim
/-!
# The version of Fin.snoc for the fixed type.

## Main Definitions

- A `FirstOrder.ZFC.FixedSnoc.fixedSnoc` defines the version of Fin.snoc for the fixed type V.

## Main Statements

- A `FirstOrder.ZFC.FixedSnoc.snoc_conv` proves the relationship between Fin.snoc and fixedSnoc.
- `FirstOrder.ZFC.FixedSnoc.snoc_last` and `FirstOrder.ZFC.FixedSnoc.snoc_init` are
  to compute the values of fixedSnoc

## Implimentation notes

- Many theorems that make simp work better are proved.

-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
universe u


-- @@ L34-34 verbatim
namespace FirstOrder.ZFC.FixedSnoc


-- @@ L36-36 verbatim
variable {V : Type u}


-- @@ L38-40 verbatim
/-- Fin.snoc for the type V. -/
def fixedSnoc {n : ℕ} (xs : Fin n → V) (b : V) :=
    (fun (k : Fin (n + 1)) => if h : k.val < n then xs (Fin.castLT k h) else b)


-- @@ L42-45 verbatim
/-- Fin.snoc = fixedSnoc when applied to V. -/
@[simp]
theorem snoc_conv {n : ℕ} {xs : Fin n → V} {b : V} : Fin.snoc xs b = fixedSnoc xs b := by
  exact rfl


-- @@ L47-51 verbatim
/-- fixedSnoc xs a n = a when xs : Fin n → V -/
@[simp]
theorem snoc_last {n : ℕ} (xs : Fin n → V) (a : V) : (fixedSnoc xs a) (Fin.last n) = a := by
  rw [← snoc_conv]
  simp


-- @@ L53-58 verbatim
/-- fixedSnoc xs a k.castSucc = xs k when xs : Fin n → V and k : Fin n. -/
@[simp]
theorem snoc_init {V : Type u} {n : ℕ} {xs : Fin n → V} {a : V} {k : Fin n} :
    fixedSnoc xs a k.castSucc = xs k := by
  rw [← snoc_conv]
  simp


-- @@ L60-64 verbatim
/-- Rewrite castAdd by using castAdd with one castSucc. -/
@[simp]
theorem castAdd_to_castSucc {n m : ℕ} {k : Fin n} : k.castAdd (m+1) = (k.castAdd m).castSucc := by
  apply Fin.eq_of_val_eq
  simp


-- @@ L66-70 verbatim
/-- ofNat written by using Fin.last and castAdd. -/
theorem coe_to_cast_add {n n' : ℕ} : Fin.ofNat (n+1+n') n = (Fin.last n).castAdd n' := by
  apply Fin.eq_of_val_eq
  simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Fin.val_castAdd, Fin.val_last]
  rw [Nat.mod_eq_of_lt (by omega)]


-- @@ L72-77 verbatim
/-- ofNat n + ofNat m = ofNat (n + m). -/
theorem add_coe_eq_coe_add {n k m : ℕ} [NeZero (n + m)] :
    (Fin.ofNat (n+m) n + Fin.ofNat (n+m) k) = Fin.ofNat (n+m) (n+k) := by
  apply Fin.eq_of_val_eq
  rw [Fin.val_add]
  simp


-- @@ L79-84 verbatim
/-- Describes the cancellation of fixedSnoc and castSucc with Sum.elim. -/
@[simp]
theorem sum_fixedSnoc_castSucc {n : ℕ} {s : ℕ → V} {xs : Fin n → V} {a : V} :
    (Sum.elim s (fixedSnoc xs a) ∘ Sum.map id fun (i : Fin n) ↦ i.castSucc) = Sum.elim s xs := by
  funext i
  rcases i with k | k <;> simp


-- @@ L86-91 verbatim
/-- Describes the cancellation of fixedSnoc and castSucc with Sum.elim. -/
@[simp]
theorem fixedSnoc_castSucc {n : ℕ} {xs : Fin n → V} {a : V} :
    (fixedSnoc xs a ∘ Fin.castSucc) = xs := by
  funext k
  simp


-- @@ L93-94 verbatim
/-- `![a] 0 = a`. -/
theorem Fintuple_1_0 {a : V} : ![a] 0 = a := by rfl


-- @@ L96-97 verbatim
/-- `![a, b] (0 : Fin 2) = a`. -/
theorem Fintuple_2_0 {a b : V} : ![a, b] (0 : Fin 2) = a := by rfl


-- @@ L99-101 verbatim
/-- `![a] 0 = a` via `Nat.cast`. -/
theorem Fintuple_1_0' {a : V} :
    ![a] (@Nat.cast (Fin 1) (Fin.NatCast.instNatCast 1) 0) = a := by rfl


-- @@ L103-105 verbatim
/-- `![a, b] 0 = a` via `Nat.cast`. -/
theorem Fintuple_2_0' {a b : V} :
    ![a, b] (@Nat.cast (Fin 2) (Fin.NatCast.instNatCast 2) 0) = a := by rfl


-- @@ L107-109 verbatim
/-- `![a, b, c] 0 = a` via `Nat.cast`. -/
theorem Fintuple_3_0' {a b c : V} :
    ![a, b, c] (@Nat.cast (Fin 3) (Fin.NatCast.instNatCast 3) 0) = a := by rfl


-- @@ L111-114 verbatim
/-- `![a, b, c] 1 = b` via `Nat.cast`. -/
@[simp]
theorem Fintuple_3_1' {a b c : V} :
    ![a, b, c] (@Nat.cast (Fin 3) (Fin.NatCast.instNatCast 3) 1) = b := by rfl


-- @@ L116-118 verbatim
/-- `![a, b, c] 2 = c` via `Nat.cast`. -/
theorem Fintuple_3_2' {a b c : V} :
    ![a, b, c] (@Nat.cast (Fin 3) (Fin.NatCast.instNatCast 3) 2) = c := by rfl


-- @@ L120-122 verbatim
/-- `![a, b, c, d] 0 = a` via `Nat.cast`. -/
theorem Fintuple_4_0' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 0) = a := by rfl


-- @@ L124-127 verbatim
/-- `![a, b, c, d] 1 = b` via `Nat.cast`. -/
@[simp]
theorem Fintuple_4_1' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 1) = b := by rfl


-- @@ L129-131 verbatim
/-- `![a, b, c, d] 2 = c` via `Nat.cast`. -/
theorem Fintuple_4_2' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 2) = c := by rfl


-- @@ L133-135 verbatim
/-- `![a, b, c, d] 3 = d` via `Nat.cast`. -/
theorem Fintuple_4_3' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 3) = d := by rfl


-- @@ L137-140 verbatim
/-- `fixedSnoc (fixedSnoc xs a) b 0 = a` over `Fin 0`. -/
@[simp]
theorem FixedSnoc_2_0 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b 0 = a := by rfl


-- @@ L142-145 verbatim
/-- `fixedSnoc (fixedSnoc xs a) b 1 = b` over `Fin 0`. -/
@[simp]
theorem FixedSnoc_2_1 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b 1 = b := by rfl


-- @@ L147-150 verbatim
/-- `fixedSnoc (fixedSnoc xs a) b 0 = a` over `Fin (0 + 2)`. -/
theorem FixedSnoc_0_2_0 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b (@OfNat.ofNat (Fin (0 + 2)) 0 Fin.instOfNat) = a := by
  simp [fixedSnoc]


-- @@ L152-155 verbatim
/-- `fixedSnoc (fixedSnoc xs a) b 1 = b` over `Fin (0 + 2)`. -/
theorem FixedSnoc_0_2_1 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b (@OfNat.ofNat (Fin (0 + 2)) 1 Fin.instOfNat) = b := by
  simp [fixedSnoc]


-- @@ L157-162 verbatim
/-- `fixedSnoc^3 ... 0 = a` over `Fin (0 + 3)`. -/
@[simp]
theorem FixedSnoc_0_3_0 {xs : Fin 0 → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@OfNat.ofNat (Fin (0 + 3)) 0 Fin.instOfNat) = a := by
  simp [fixedSnoc]


-- @@ L164-169 verbatim
/-- `fixedSnoc^3 ... 1 = b` over `Fin (0 + 3)`. -/
@[simp]
theorem FixedSnoc_0_3_1 {xs : Fin 0 → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@OfNat.ofNat (Fin (0 + 3)) 1 Fin.instOfNat) = b := by
  simp [fixedSnoc]


-- @@ L171-176 verbatim
/-- `fixedSnoc^3 ... 2 = c` over `Fin (0 + 3)`. -/
@[simp]
theorem FixedSnoc_0_3_2 {xs : Fin 0 → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@OfNat.ofNat (Fin (0 + 3)) 2 Fin.instOfNat) = c := by
  simp [fixedSnoc]


-- @@ L178-183 verbatim
/-- `fixedSnoc^4 ... 0 = a` over `Fin (0 + 4)`. -/
@[simp]
theorem FixedSnoc_0_4_0 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@OfNat.ofNat (Fin (0 + 4)) 0 Fin.instOfNat) = a := by
  simp [fixedSnoc]


-- @@ L185-190 verbatim
/-- `fixedSnoc^4 ... 1 = b` over `Fin (0 + 4)`. -/
@[simp]
theorem FixedSnoc_0_4_1 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
      (@OfNat.ofNat (Fin (0 + 4)) 1 Fin.instOfNat) = b := by
  simp [fixedSnoc]


-- @@ L192-197 verbatim
/-- `fixedSnoc^4 ... 2 = c` over `Fin (0 + 4)`. -/
@[simp]
theorem FixedSnoc_0_4_2 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@OfNat.ofNat (Fin (0 + 4)) 2 Fin.instOfNat) = c := by
  simp [fixedSnoc]


-- @@ L199-204 verbatim
/-- `fixedSnoc^4 ... 3 = d` over `Fin (0 + 4)`. -/
@[simp]
theorem FixedSnoc_0_4_3 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@OfNat.ofNat (Fin (0 + 4)) 3 Fin.instOfNat) = d := by
  simp [fixedSnoc]


-- @@ L206-213 verbatim
/-- `fixedSnoc^2 ... n = a` over `Fin (n + 2)`. -/
@[simp]
theorem FixedSnoc_n_2_0 {n : ℕ} {xs : Fin n → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b
    (@Nat.cast (Fin (n + 1 + 1)) (Fin.NatCast.instNatCast (n + 1 + 1)) n) = a := by
  rw [show (@Nat.cast (Fin (n + 1 + 1)) (Fin.NatCast.instNatCast (n + 1 + 1)) n)
      = (Fin.last n).castSucc from Fin.eq_of_val_eq (by simp; omega)]
  simp


-- @@ L215-219 verbatim
/-- `fixedSnoc^2 ... (n+1) = b` over `Fin (n + 2)`. -/
theorem FixedSnoc_n_2_1 {n : ℕ} {xs : Fin n → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b (@Nat.cast (Fin (n + 1 + 1))
    (Fin.NatCast.instNatCast (n + 1 + 1)) (n + 1)) = b := by
  simp_all


-- @@ L221-228 verbatim
/-- `fixedSnoc^3 ... n = a` over `Fin (n + 3)`. -/
@[simp]
theorem FixedSnoc_n_3_0 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) n) = a := by
  rw [show (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) n)
      = (Fin.last n).castSucc.castSucc from Fin.eq_of_val_eq (by simp; omega)]
  simp


-- @@ L230-234 verbatim
/-- `fixedSnoc^3 ... (n+1) = b` over `Fin (n + 3)`. -/
theorem FixedSnoc_n_3_1 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) (n+1)) = b := by
  simp_all


-- @@ L236-240 verbatim
/-- `fixedSnoc^3 ... (n+2) = c` over `Fin (n + 3)`. -/
theorem FixedSnoc_n_3_2 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) (n+2)) = c := by
  simp_all


-- @@ L242-249 verbatim
/-- `fixedSnoc^4 ... n = a` over `Fin (n + 4)`. -/
@[simp]
theorem FixedSnoc_n_4_0 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n+4)) n) = a := by
  rw [show (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n+4)) n)
      = (Fin.last n).castSucc.castSucc.castSucc from Fin.eq_of_val_eq (by simp; omega)]
  simp


-- @@ L251-255 verbatim
/-- `fixedSnoc^4 ... (n+1) = b` over `Fin (n + 4)`. -/
theorem FixedSnoc_n_4_1 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n+4)) (n+1)) = b := by
  simp_all


-- @@ L257-261 verbatim
/-- `fixedSnoc^4 ... (n+2) = c` over `Fin (n + 4)`. -/
theorem FixedSnoc_n_4_2 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n + 4)) (n + 2)) = c := by
  simp_all


-- @@ L263-267 verbatim
/-- `fixedSnoc^4 ... (n+3) = d` over `Fin (n + 4)`. -/
theorem FixedSnoc_n_4_3 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n + 4)) (n + 3)) = d := by
  simp_all


-- @@ L269-275 verbatim
/-- `fixedSnoc^2 ... ∘ castSucc^2 = xs`. -/
@[simp]
theorem fixedSnoc_castSucc_2 {n : ℕ} {xs : Fin n → V} {a b : V} :
    (fixedSnoc (fixedSnoc xs a) b ∘ fun (i : Fin n) ↦ i.castSucc.castSucc)
    = xs := by
  funext k
  simp


-- @@ L277-282 verbatim
/-- `fixedSnoc^3 ... ∘ castSucc^3 = xs`. -/
@[simp]
theorem fixedSnoc_castSucc_3 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c ∘ fun i ↦ i.castSucc.castSucc.castSucc) = xs := by
  funext k
  simp


-- @@ L284-290 verbatim
/-- `fixedSnoc^4 ... ∘ castSucc^4 = xs`. -/
@[simp]
theorem fixedSnoc_castSucc_4 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    (fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    ∘ fun i ↦ i.castSucc.castSucc.castSucc.castSucc) = xs := by
  funext k
  simp


-- @@ L292-298 verbatim
/-- `fixedSnoc ∘ (castAdd ∘ castSucc) = xs ∘ castAdd`. -/
@[simp]
theorem fixedSnoc_castAdd_castSucc {n n' : ℕ} {xs : Fin (n + n') → V} {x : V} :
  (fixedSnoc xs x ∘ fun (i : Fin n) ↦ (Fin.castAdd n' i).castSucc) =
  (xs ∘ fun i ↦ Fin.castAdd n' i) := by
  funext k
  simp


-- @@ L300-300 verbatim
end FirstOrder.ZFC.FixedSnoc
