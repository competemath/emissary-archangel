/-
Copyright (c) 2025 LeanCert contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic


-- @@ L8-19 verbatim
/-! # Lucas Sequences — Computable Definitions

We define the generalized Lucas sequences `U_n(P, Q)` and `V_n(P, Q)` satisfying:
- `U_0 = 0, U_1 = 1, U_{n+2} = P · U_{n+1} - Q · U_n`
- `V_0 = 2, V_1 = P, V_{n+2} = P · V_{n+1} - Q · V_n`

Special cases:
- Fibonacci: `U_n(1, -1) = F_n`
- Pell: `U_n(2, -1) = P_n`
- Lucas numbers: `V_n(1, -1) = L_n`

All definitions are computable over `ℤ` for use with `native_decide`. -/


-- @@ L21-21 verbatim
namespace LeanCert.Engine.Pisano


-- @@ L23-23 verbatim
/-! ### Lucas sequence computation -/


-- @@ L25-30 verbatim
/-- Compute `(U_n, U_{n+1})` for the Lucas U-sequence with parameters `(P, Q)` over `ℤ`. -/
def lucasUPair (P Q : Int) : Nat → Int × Int
  | 0 => (0, 1)
  | n + 1 =>
    let (u, u') := lucasUPair P Q n
    (u', P * u' - Q * u)


-- @@ L32-34 verbatim
/-- The Lucas U-sequence: `U_n(P, Q)`. -/
def lucasU (P Q : Int) (n : Nat) : Int :=
  (lucasUPair P Q n).1


-- @@ L36-41 verbatim
/-- Compute `(V_n, V_{n+1})` for the Lucas V-sequence with parameters `(P, Q)` over `ℤ`. -/
def lucasVPair (P Q : Int) : Nat → Int × Int
  | 0 => (2, P)
  | n + 1 =>
    let (v, v') := lucasVPair P Q n
    (v', P * v' - Q * v)


-- @@ L43-45 verbatim
/-- The Lucas V-sequence: `V_n(P, Q)`. -/
def lucasV (P Q : Int) (n : Nat) : Int :=
  (lucasVPair P Q n).1


-- @@ L47-47 verbatim
/-! ### Modular versions -/


-- @@ L49-54 verbatim
/-- Compute `(U_n mod m, U_{n+1} mod m)` efficiently, reducing at each step. -/
def lucasUPairMod (P Q : Int) (m : Nat) : Nat → Int × Int
  | 0 => (0, 1 % m)
  | n + 1 =>
    let (u, u') := lucasUPairMod P Q m n
    (u' % m, (P * u' - Q * u) % m)


-- @@ L56-58 verbatim
/-- `U_n(P, Q) mod m`, computed efficiently with modular reduction at each step. -/
def lucasUMod (P Q : Int) (m : Nat) (n : Nat) : Int :=
  (lucasUPairMod P Q m n).1


-- @@ L60-60 verbatim
/-! ### Basic recurrence lemmas -/


-- @@ L62-62 verbatim
@[simp] theorem lucasUPair_zero (P Q : Int) : lucasUPair P Q 0 = (0, 1) := rfl


-- @@ L64-67 verbatim
theorem lucasUPair_succ (P Q : Int) (n : Nat) :
    lucasUPair P Q (n + 1) =
      let (u, u') := lucasUPair P Q n
      (u', P * u' - Q * u) := rfl


-- @@ L69-69 verbatim
@[simp] theorem lucasU_zero (P Q : Int) : lucasU P Q 0 = 0 := rfl


-- @@ L71-71 verbatim
@[simp] theorem lucasU_one (P Q : Int) : lucasU P Q 1 = 1 := rfl


-- @@ L73-75 verbatim
theorem lucasU_succ_succ (P Q : Int) (n : Nat) :
    lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := by
  simp only [lucasU, lucasUPair]


-- @@ L77-77 verbatim
/-! ### Connection to Nat.fib (Fibonacci = Lucas U with P=1, Q=-1) -/


-- @@ L79-90 verbatim
theorem lucasU_fib (n : Nat) : lucasU 1 (-1) n = Nat.fib n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp [Nat.fib]
    | n + 2 =>
      rw [lucasU_succ_succ]
      simp only [one_mul]
      rw [ih (n + 1) (by omega), ih n (by omega)]
      rw [Nat.fib_add_two]
      omega


-- @@ L92-92 verbatim
/-! ### Modular congruence -/


-- @@ L94-109 verbatim
private theorem lucasUPairMod_eq_mod (P Q : Int) (m : Nat) (n : Nat) :
    lucasUPairMod P Q m n =
      ((lucasUPair P Q n).1 % m, (lucasUPair P Q n).2 % m) := by
  induction n with
  | zero =>
    simp [lucasUPairMod, lucasUPair]
  | succ n ih =>
    simp only [lucasUPairMod, lucasUPair]
    rw [ih]
    ext
    · -- fst: (snd % m) % m = snd % m
      exact Int.emod_emod_of_dvd _ dvd_rfl
    · -- snd: (P * (snd % m) - Q * (fst % m)) % m = (P * snd - Q * fst) % m
      rw [Int.sub_emod, Int.mul_emod (a := P), Int.mul_emod (a := Q)]
      simp only [Int.emod_emod_of_dvd _ dvd_rfl]
      rw [← Int.mul_emod (a := P), ← Int.mul_emod (a := Q), ← Int.sub_emod]


-- @@ L111-113 verbatim
theorem lucasUMod_eq_mod (P Q : Int) (m : Nat) (_hm : 0 < m) (n : Nat) :
    lucasUMod P Q m n = lucasU P Q n % m := by
  simp only [lucasUMod, lucasU, lucasUPairMod_eq_mod P Q m n]


-- @@ L115-115 verbatim
end LeanCert.Engine.Pisano
