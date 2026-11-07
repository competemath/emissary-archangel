/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base

  Irreducible algorithm intermediates for n=2 full-path wrappers.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.CLZ
public import EvmAsm.Evm64.DivMod.LoopDefs.Iter


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
open EvmAsm.Rv64


-- @@ L18-20 verbatim
@[irreducible]
def fullDivN2Shift (b1 : Word) : Word :=
  (clzResult b1).1


-- @@ L22-24 verbatim
@[irreducible]
def fullDivN2AntiShift (b1 : Word) : Word :=
  signExtend12 (0 : BitVec 12) - fullDivN2Shift b1


-- @@ L26-33 verbatim
@[irreducible]
def fullDivN2NormV (b0 b1 b2 b3 : Word) : Word × Word × Word × Word :=
  let shift := fullDivN2Shift b1
  let antiShift := fullDivN2AntiShift b1
  (b0 <<< (shift.toNat % 64),
   (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)),
   (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)),
   (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64)))


-- @@ L35-44 verbatim
@[irreducible]
def fullDivN2NormU (a0 a1 a2 a3 b1 : Word) :
    Word × Word × Word × Word × Word :=
  let shift := fullDivN2Shift b1
  let antiShift := fullDivN2AntiShift b1
  (a0 <<< (shift.toNat % 64),
   (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)),
   (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)),
   (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)),
   a3 >>> (antiShift.toNat % 64))


-- @@ L46-52 verbatim
@[irreducible]
def fullDivN2R2 (bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  iterN2 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word)


-- @@ L54-62 verbatim
@[irreducible]
def fullDivN2R1 (bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  iterN2 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1


-- @@ L64-72 verbatim
@[irreducible]
def fullDivN2R0 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN2 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1


-- @@ L74-85 verbatim
@[irreducible]
def fullDivN2C3 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  if bltu_0 then
    (mulsubN4 (div128Quot r1.2.2.1 r1.2.1 v.2.1)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2
  else
    (mulsubN4 (signExtend12 4095 : Word)
      v.1 v.2.1 v.2.2.1 v.2.2.2 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1).2.2.2.2


-- @@ L87-90 verbatim
theorem fullDivN2Shift_unfold (b1 : Word) :
    fullDivN2Shift b1 = (clzResult b1).1 := by
  delta fullDivN2Shift
  rfl


-- @@ L92-95 verbatim
theorem fullDivN2AntiShift_unfold (b1 : Word) :
    fullDivN2AntiShift b1 = signExtend12 (0 : BitVec 12) - fullDivN2Shift b1 := by
  delta fullDivN2AntiShift
  rfl


-- @@ L97-106 verbatim
theorem fullDivN2NormV_unfold (b0 b1 b2 b3 : Word) :
    fullDivN2NormV b0 b1 b2 b3 =
    let shift := fullDivN2Shift b1
    let antiShift := fullDivN2AntiShift b1
    (b0 <<< (shift.toNat % 64),
     (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64)),
     (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64)),
     (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))) := by
  delta fullDivN2NormV
  rfl


-- @@ L108-118 verbatim
theorem fullDivN2NormU_unfold (a0 a1 a2 a3 b1 : Word) :
    fullDivN2NormU a0 a1 a2 a3 b1 =
    let shift := fullDivN2Shift b1
    let antiShift := fullDivN2AntiShift b1
    (a0 <<< (shift.toNat % 64),
     (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64)),
     (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64)),
     (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64)),
     a3 >>> (antiShift.toNat % 64)) := by
  delta fullDivN2NormU
  rfl


-- @@ L120-128 verbatim
theorem fullDivN2R2_unfold (bltu_2 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    iterN2 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) := by
  delta fullDivN2R2
  rfl


-- @@ L130-139 verbatim
theorem fullDivN2R1_unfold (bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r2 := fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    iterN2 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 := by
  delta fullDivN2R1
  rfl


-- @@ L141-150 verbatim
theorem fullDivN2R0_unfold (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r1 := fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    iterN2 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 := by
  delta fullDivN2R0
  rfl


-- @@ L152-152 verbatim
end EvmAsm.Evm64
