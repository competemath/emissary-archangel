/-
Expand a corpus's own notations in its modules, so the text the pipeline pastes
carries no use of a `notation`/`notation3`/`macro` the corpus declares: the
tree's content lint refuses those declarations, and dropping them breaks every
use. Core and Mathlib notation is left alone. Runs under the corpus's own
toolchain, in its checkout, after `lake build`:

  lake env lean --run expand-notations.lean <outDir> <root1,root2,…> <module>…

Writes <outDir>/<module>.expanded.lean: the header verbatim, then each command as

  -- @@ L<startLine>-<endLine> <expanded|verbatim|unexpanded>
  <text>

A command in which no corpus macro fired is copied verbatim (comments and layout
kept). One that expanded is pretty-printed with hygiene scopes erased. One the
printer cannot round-trip is copied verbatim and marked `unexpanded` (the entry
then reaches the agent, as before). Positions are handled as byte indices so the
same file compiles from Lean v4.18 to v4.34 (typed `String.Pos` arrived late).
-/
import Lean
open Lean Elab Frontend Parser PrettyPrinter

/-- A syntax kind declared by the corpus: in a module under one of its roots, or
in the file being processed (declared above this command, not yet in a module). -/
def isCorpusKind (env : Environment) (roots : List String) (kind : Name) : Bool :=
  match env.getModuleIdxFor? kind with
  | some idx =>
    match env.header.moduleNames[idx]? with
    | some m => roots.any fun r => m.toString == r || m.toString.startsWith (r ++ ".")
    | none => false
  | none => env.contains kind

/-- Expansions allowed per command, and nested expansions per chain: a macro whose output contains
itself again, or keeps growing, otherwise expands until memory runs out (one formal-conjectures
command reached 33 GB). Past either budget the command is left verbatim. -/
def maxExpansions : Nat := 2000
def maxExpansionDepth : Nat := 64

/-- Expand corpus macros everywhere in `stx`, repeatedly; `true` when one fired. The state is the
number of expansions still allowed for this command. -/
partial def expandCorpus (env : Environment) (roots : List String) (depth : Nat := 0) : Syntax → StateT Nat MacroM (Syntax × Bool)
  | stx@(.node info kind args) => do
    if isCorpusKind env roots kind then
      -- expandMacroImpl? rather than Macro.expandMacro?: the latter answered `none`
      -- for every notation3 through the command-elab adapter.
      match (← liftM (Lean.Elab.expandMacroImpl? env stx : MacroM _)) with
      | some (_, .ok stx') =>
        let left ← get
        if left == 0 || depth ≥ maxExpansionDepth then
          liftM (Macro.throwError "expansion budget exceeded" : MacroM Unit)
        set (left - 1)
        return ((← expandCorpus env roots (depth + 1) stx').1, true)
      | _ => expandArgs info kind args
    else
      expandArgs info kind args
  | stx => return (stx, false)
where
  expandArgs (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : StateT Nat MacroM (Syntax × Bool) := do
    let mut fired := false
    let mut out := #[]
    for a in args do
      let (a', f) ← expandCorpus env roots depth a
      out := out.push a'
      fired := fired || f
    return (.node info kind out, fired)

/-- A quotation's identifiers carry macro scopes; printed, they are not source. The
names a corpus notation expands to are global constants, so erasing is right. -/
partial def eraseScopes : Syntax → Syntax
  | .ident info raw n pre => .ident info raw n.eraseMacroScopes pre
  | .node info k args => .node info k (args.map eraseScopes)
  | s => s

def slice (bytes : ByteArray) (a b : Nat) : String :=
  String.fromUTF8! (bytes.extract a b)

unsafe def main (args : List String) : IO Unit := do
  -- The macro tables are environment extensions; importing them needs this first.
  enableInitializersExecution
  let outDir :: rootsArg :: mods := args
    | throw (IO.userError "usage: expand-notations <outDir> <root1,root2,…> <module>…")
  let roots := (rootsArg.splitOn ",").filter (· ≠ "")
  initSearchPath (← findSysroot)
  IO.FS.createDirAll outDir
  for modStr in mods do
    -- the module's file: components may be «»-escaped (`Arxiv.«1102.4662»` is Arxiv/1102.4662/), so no dot-splitting
    let path : System.FilePath := modToFilePath "." modStr.toName "lean"
    let input ← IO.FS.readFile path
    let bytes := input.toUTF8
    let inputCtx := Parser.mkInputContext input path.toString
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (env, messages) ← processHeader header {} messages inputCtx
    let env := env.setMainModule modStr.toName
    -- Phase 1: the whole file, as the frontend does it. Interleaving expansion
    -- with the parse loop perturbed the frontend state; on the final state it
    -- cannot (a notation declared later in the file has no earlier use).
    let final ← IO.processCommands inputCtx parserState (Command.mkState env messages {})
    let cmds := final.commands.filter fun c => !Parser.isTerminalCommand c
    -- Phase 2: every command, in one elaboration context on that state.
    -- `some (some t)` expanded to t, `some none` could not be printed, `none` nothing fired.
    let fctx : Frontend.Context := { inputCtx }
    let (results, _) ← ((Frontend.runCommandElabM (do
        let env ← getEnv
        let mut acc : Array (Option (Option String)) := #[]
        for cmd in cmds do
          let r : Option (Option String) ← (do
              let ((stx, fired), _) ← liftMacroM ((expandCorpus env roots 0 cmd).run maxExpansions)
              if !fired then return none
              let fmt ← Command.liftCoreM (ppCommand ⟨eraseScopes stx⟩)
              return some (some (fmt.pretty 100)))
            <|> pure (some none)
          if (← IO.getEnv "EXPAND_DEBUG").isSome then IO.println s!"  {cmd.getKind} fired={r.isSome} kinds={(cmd.getArgs.map (·.getKind)).toList.take 3}"
          acc := acc.push r
        return acc)).run fctx).run final
    -- Verbatim text runs from one command's start to the next: comments and
    -- blank lines between commands stay with the command before them.
    let starts := cmds.map fun c => (c.getPos?.map (·.byteIdx)).getD bytes.size
    let mut out := slice bytes 0 parserState.pos.byteIdx
    let mut prev := parserState.pos.byteIdx
    let mut nExp := 0
    let mut nVerb := 0
    let mut nUnexp := 0
    for i in [0:cmds.size] do
      let cmd := cmds[i]!
      let sliceEnd := if i + 1 < cmds.size then starts[i + 1]! else bytes.size
      let raw := slice bytes prev sliceEnd
      prev := sliceEnd
      let startLine := (inputCtx.fileMap.toPosition (cmd.getPos?.getD parserState.pos)).line
      -- From the slice, not getTailPos? (which sat one line short on multi-line commands).
      let endLine := startLine + (raw.trimRight.toList.filter (· == '\n')).length
      let (kind, text) := match results[i]! with
        | some (some t) => ("expanded", t.trimRight ++ "\n\n")
        | some none => ("unexpanded", raw)
        | none => ("verbatim", raw)
      if kind == "expanded" then nExp := nExp + 1
      else if kind == "verbatim" then nVerb := nVerb + 1
      else nUnexp := nUnexp + 1
      out := out ++ s!"\n-- @@ L{startLine}-{endLine} {kind}\n" ++ text
    let outPath : System.FilePath := ⟨outDir ++ "/" ++ modStr ++ ".expanded.lean"⟩
    -- whole or not at all: a killed run must not leave a truncated file that the next run skips as done
    let tmpPath : System.FilePath := ⟨outPath.toString ++ ".tmp"⟩
    IO.FS.writeFile tmpPath out
    IO.FS.rename tmpPath outPath
    IO.println s!"{modStr}\t{nExp}\t{nVerb}\t{nUnexp}"
