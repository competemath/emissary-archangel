/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Scratch

  One-step irreducible scratch-state transitions for n=2 full-path wrappers.
  The field projections stay transparent; only the transition bundles need
  opacity for composition proofs.
-/

module

public import EvmAsm.Evm64.DivMod.LoopDefs.Iter


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64


-- @@ L17-21 verbatim
open EvmAsm.Rv64

-- implicit_reducible: since v4.33 metavariable-assignment type checks run at
-- implicit transparency, so the n2Scratch*_unfold simp lemmas (binder typed
-- N2ScratchState) silently stop matching tuple-literal arguments without it.

-- @@ L22-23 verbatim
@[implicit_reducible] def N2ScratchState : Type :=
  Word × Word × Word × Word


-- @@ L25-26 verbatim
def n2ScratchRet (s : N2ScratchState) : Word :=
  s.1


-- @@ L28-29 verbatim
def n2ScratchD (s : N2ScratchState) : Word :=
  s.2.1


-- @@ L31-32 verbatim
def n2ScratchDLo (s : N2ScratchState) : Word :=
  s.2.2.1


-- @@ L34-35 verbatim
def n2ScratchUn0 (s : N2ScratchState) : Word :=
  s.2.2.2


-- @@ L37-43 verbatim
@[irreducible]
def fullDivN2Scratch2 (bltu_2 : Bool) (base v1 u2 retMem dMem dloMem scratch_un0 : Word) :
    N2ScratchState :=
  if bltu_2 then
    (base + div128CallRetOff, v1, div128DLo v1, div128Un0 u2)
  else
    (retMem, dMem, dloMem, scratch_un0)


-- @@ L45-53 verbatim
@[irreducible]
def fullDivN2Scratch1 (bltu_2 bltu_1 : Bool)
    (base v1 u2 r2_hi retMem dMem dloMem scratch_un0 : Word) :
    N2ScratchState :=
  let s2 := fullDivN2Scratch2 bltu_2 base v1 u2 retMem dMem dloMem scratch_un0
  if bltu_1 then
    (base + div128CallRetOff, v1, div128DLo v1, div128Un0 r2_hi)
  else
    s2


-- @@ L55-63 verbatim
@[irreducible]
def fullDivN2Scratch0 (bltu_2 bltu_1 bltu_0 : Bool)
    (base v1 u2 r2_hi r1_hi retMem dMem dloMem scratch_un0 : Word) :
    N2ScratchState :=
  let s1 := fullDivN2Scratch1 bltu_2 bltu_1 base v1 u2 r2_hi retMem dMem dloMem scratch_un0
  if bltu_0 then
    (base + div128CallRetOff, v1, div128DLo v1, div128Un0 r1_hi)
  else
    s1


-- @@ L65-68 verbatim
theorem n2ScratchRet_unfold (s : N2ScratchState) :
    n2ScratchRet s = s.1 := by
  delta n2ScratchRet
  rfl


-- @@ L70-73 verbatim
theorem n2ScratchD_unfold (s : N2ScratchState) :
    n2ScratchD s = s.2.1 := by
  delta n2ScratchD
  rfl


-- @@ L75-78 verbatim
theorem n2ScratchDLo_unfold (s : N2ScratchState) :
    n2ScratchDLo s = s.2.2.1 := by
  delta n2ScratchDLo
  rfl


-- @@ L80-83 verbatim
theorem n2ScratchUn0_unfold (s : N2ScratchState) :
    n2ScratchUn0 s = s.2.2.2 := by
  delta n2ScratchUn0
  rfl


-- @@ L85-89 verbatim
theorem fullDivN2Scratch2_true (base v1 u2 retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch2 true base v1 u2 retMem dMem dloMem scratch_un0 =
      (base + div128CallRetOff, v1, div128DLo v1, div128Un0 u2) := by
  delta fullDivN2Scratch2
  rfl


-- @@ L91-95 verbatim
theorem fullDivN2Scratch2_false (base v1 u2 retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch2 false base v1 u2 retMem dMem dloMem scratch_un0 =
      (retMem, dMem, dloMem, scratch_un0) := by
  delta fullDivN2Scratch2
  rfl


-- @@ L97-102 verbatim
theorem fullDivN2Scratch1_true (bltu_2 : Bool)
    (base v1 u2 r2_hi retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch1 bltu_2 true base v1 u2 r2_hi retMem dMem dloMem scratch_un0 =
      (base + div128CallRetOff, v1, div128DLo v1, div128Un0 r2_hi) := by
  delta fullDivN2Scratch1
  rfl


-- @@ L104-109 verbatim
theorem fullDivN2Scratch1_false (bltu_2 : Bool)
    (base v1 u2 r2_hi retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch1 bltu_2 false base v1 u2 r2_hi retMem dMem dloMem scratch_un0 =
      fullDivN2Scratch2 bltu_2 base v1 u2 retMem dMem dloMem scratch_un0 := by
  delta fullDivN2Scratch1
  rfl


-- @@ L111-117 verbatim
theorem fullDivN2Scratch0_true (bltu_2 bltu_1 : Bool)
    (base v1 u2 r2_hi r1_hi retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch0 bltu_2 bltu_1 true base v1 u2 r2_hi r1_hi
        retMem dMem dloMem scratch_un0 =
      (base + div128CallRetOff, v1, div128DLo v1, div128Un0 r1_hi) := by
  delta fullDivN2Scratch0
  rfl


-- @@ L119-125 verbatim
theorem fullDivN2Scratch0_false (bltu_2 bltu_1 : Bool)
    (base v1 u2 r2_hi r1_hi retMem dMem dloMem scratch_un0 : Word) :
    fullDivN2Scratch0 bltu_2 bltu_1 false base v1 u2 r2_hi r1_hi
        retMem dMem dloMem scratch_un0 =
      fullDivN2Scratch1 bltu_2 bltu_1 base v1 u2 r2_hi retMem dMem dloMem scratch_un0 := by
  delta fullDivN2Scratch0
  rfl


-- @@ L127-127 verbatim
end EvmAsm.Evm64
