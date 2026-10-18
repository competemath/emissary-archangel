/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module


-- @@ L8-14 verbatim
/-!
# A kernel-checked Sieve of Eratosthenes

A Sieve of Eratosthenes over the numbers coprime to 6, in a form the Lean kernel evaluates by
reduction. The state is one natural number used as a bitset, `M` is its top index, and a bound of
`n` gives `M = index n`. `markMaskK` runs 32 doubling rounds, covering `M < 2^32`.
-/


-- @@ L16-16 verbatim
namespace PrimeCert.Sieve


-- @@ L18-19 verbatim
/-- Whether bit `i` of `b` is set (`testBitK_eq_testBit` in `SieveCorrect`). -/
@[expose] public def testBitK (b i : Nat) : Bool := Nat.ble 1 (b.land (Nat.shiftLeft 1 i))


-- @@ L21-22 verbatim
/-- The number sitting at coprime-to-6 index `k`: `0↦1, 1↦5, 2↦7, 3↦11, 4↦13, …`. -/
@[expose] public def value (k : Nat) : Nat := (k * 3 + 1) + k % 2


-- @@ L24-25 verbatim
/-- `value` in the raw `Nat` operations the kernel-side defs use. -/
@[expose] public def valueK (k : Nat) : Nat := (k.mul 3).succ.add (k.mod 2)


-- @@ L27-29 verbatim
/-- The coprime-to-6 index holding the number `q`, inverse to `value` on `1, 5, 7, 11, 13, …`
(`value_index` and `index_value` in `SieveCorrect`). -/
@[expose] public def index (q : Nat) : Nat := (q - 1) / 3


-- @@ L31-32 verbatim
/-- `index` in the raw `Nat` operations the kernel-side defs use. -/
@[expose] public def indexK (q : Nat) : Nat := (q.sub 1).div 3


-- @@ L34-42 verbatim
/-- The natural number whose binary digits below position `M` are set at the first `2^n` positions
of each of `A, A + 2*p, A + 4*p, …` and `B, B + 2*p, B + 4*p, …`; `n` counts doubling rounds. -/
@[expose] public noncomputable def buildMaskK (p M A B n : Nat) : Nat :=
  Nat.rec
    ((Nat.shiftLeft 1 A).lor (Nat.shiftLeft 1 B))
    (fun i Mk =>
      ((p.shiftLeft i.succ).ble M).rec Mk
        (Mk.lor (Mk.shiftLeft (p.shiftLeft i.succ))))
    n


-- @@ L44-47 verbatim
/-- One sieving step: clear from `bits` the bits at indices of coprime-to-6 multiples of `p`
(the multiples `5*p, 7*p, 11*p, …`). -/
@[expose] public noncomputable def markMaskK (bits p M : Nat) : Nat :=
  bits.sub (bits.land (buildMaskK p M (indexK (p.mul 5)) (indexK (p.mul 7)) 32))


-- @@ L49-55 verbatim
/-- Perform `fuel` sieving steps on the bitset `bits`, scanning indices `start, start+1, …`: at
each index whose bit is still set, clear the bits of that number's coprime-to-6 multiples.
`sieveK` runs this on `initK M`. -/
@[expose] public noncomputable def sieveLoopK (M bits start fuel : Nat) : Nat :=
  fuel.rec bits fun i b =>
      (testBitK b (start.add i)).rec b
        (markMaskK b (valueK (start.add i)) M)


-- @@ L57-58 verbatim
/-- Coprime-to-6 candidates `0..M`, all set except bit 0 (number 1, not prime). `= 2^(M+1) - 2`. -/
@[expose] public def initK (M : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 (Nat.succ M)) 2


-- @@ L60-63 verbatim
/-- The full sieve bitset for numbers up to `n`: bit `t` is set iff `value t` is prime, given
`n ≤ sqrtN * sqrtN` (`sieveK_testBit_iff` in `SieveCorrect`). -/
@[expose] public noncomputable def sieveK (n sqrtN : Nat) : Nat :=
  sieveLoopK (indexK n) (initK (indexK n)) 1 (indexK sqrtN)


-- @@ L65-70 verbatim
/-- Loop recurrence: peel the top index `start+fuel`, in the exact `Bool.rec` form the def uses. -/
public theorem sieveLoopK_succ {M bits start fuel : Nat} :
    sieveLoopK M bits start (fuel + 1)
      = Bool.rec (sieveLoopK M bits start fuel)
          (markMaskK (sieveLoopK M bits start fuel) (valueK (start + fuel)) M)
          (testBitK (sieveLoopK M bits start fuel) (start + fuel)) := rfl


-- @@ L72-76 verbatim
/-! ### Compiled twins

Executable copies of the definitions above, used by `run_sieve` to compute the batch literals.
The kernel checks each batch equation, so a twin that disagreed with its kernel definition would
make `run_sieve` fail. -/


-- @@ L78-84 verbatim
public def buildMask (p M A B n : Nat) : Nat := Id.run do
  let mut mask := (1 <<< A) ||| (1 <<< B)
  for i in [0:n] do
    let s := p <<< (i + 1)
    if s ≤ M then
      mask := mask ||| (mask <<< s)
  return mask


-- @@ L86-87 verbatim
public def markMask (bits p M : Nat) : Nat :=
  bits - (bits &&& buildMask p M (index (p * 5)) (index (p * 7)) 32)


-- @@ L89-95 verbatim
public def sieveLoop (M bits start fuel : Nat) : Nat := Id.run do
  let mut b := bits
  for i in [0:fuel] do
    let j := start + i
    if b &&& (1 <<< j) ≠ 0 then
      b := markMask b (value j) M
  return b


-- @@ L97-104 verbatim
/-- Fuel additivity: running `a + b` steps is running `a` steps, then `b` steps from where the
first run stopped. This is the glue that joins consecutive batches. -/
public theorem sieveLoopK_add {M bits start a b : Nat} :
    sieveLoopK M bits start (a + b)
      = sieveLoopK M (sieveLoopK M bits start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [sieveLoopK_succ]


-- @@ L106-113 verbatim
/-- One chain step: given `L = sieveLoopK M b start (len + rest)` and a kernel-checked batch
equation saying `len` steps from `b` reach `b'`, restate `L` as a loop from `b'` at index
`start + len` with `rest` steps left. -/
public theorem sieveLoopK_chain {L M b b' start len rest : Nat}
    (hP : L = sieveLoopK M b start (len.add rest))
    (h : (sieveLoopK M b start len).beq b') :
    L = sieveLoopK M b' (start.add len) rest := by
  grind [sieveLoopK_add, Nat.beq_eq]


-- @@ L115-121 verbatim
/-- Last chain step: with no steps left after this batch, the batch equation gives the value of
the whole run. -/
public theorem sieveLoopK_last {L M b b' start len : Nat}
    (hP : L = sieveLoopK M b start len)
    (h : (sieveLoopK M b start len).beq b') :
    L = b' := by
  grind [Nat.beq_eq]


-- @@ L123-123 verbatim
end PrimeCert.Sieve
