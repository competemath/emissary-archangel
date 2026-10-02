/-
TolerantBuild.lean — elaborate ONE Lean file as module M exactly like `lean -o`, but write the .olean even when the file has
errors.

`lean -o M.olean M.lean` (and so `lake build`) writes nothing when a file has an error, so every module that imports it is
blocked too. Lean's own error recovery has by then turned each declaration that failed into one whose value uses `sorryAx`
(or, when its HEADER failed, left it out), so the environment at the end of the file is complete except for those
declarations. This writes that environment. A later check (scripts/bump/gate2_batch.py) rejects every declaration that
depends on `sorryAx`, so nothing unsound is ever banked; what the tolerance buys is that a failing proof costs one
declaration, not its whole module and everything downstream.

The body is `Lean.Elab.runFrontend` of the toolchain this is built with (src/Lean/Elab/Frontend.lean at the same tag), cut
at the point where it returns `none` on errors and instead writing the module.

  lean --run TolerantBuild.lean FILE MODULE OLEAN
  exit 0: no errors; exit 2: errors, olean written; exit 1: no environment (a bad import, a crash); messages on stdout.
-/
import Lean
open Lean Elab

def main (args : List String) : IO UInt32 := do
  let [file, modName, oleanFile] := args | throw <| IO.userError "usage: TolerantBuild FILE MODULE OLEAN"
  -- what the `lean` binary does before it reads a file: imported modules' `initialize` declarations (attributes, extensions) must run
  unsafe enableInitializersExecution
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let mainModuleName := modName.toName
  let trustLevel : UInt32 := 0
  let plugins : Array Plugin := #[]
  let opts : Options := {}
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet opts true
  let opts := Elab.async.setIfNotSet opts true
  let ctx := { inputCtx with }
  let setup stx := do
    return .ok {
      imports := stx.imports
      isModule := stx.isModule
      mainModuleName, opts, trustLevel, plugins
    }
  let processor := Language.Lean.process
  let snap ← processor setup none ctx
  let snaps := Language.toSnapshotTree snap
  let hasErrors ← snaps.runAndReport opts false {}
  let some cmdState := Language.Lean.waitForFinalCmdState? snap
    | return 1
  let env := cmdState.env
  let finalOpts := cmdState.scopes[0]!.opts
  writeModule (writeIR := !Compiler.compiler.postponeCompile.get finalOpts) env oleanFile
  Runtime.forget snaps
  return if hasErrors then 2 else 0
