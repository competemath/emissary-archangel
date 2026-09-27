/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Operator
import Mathlib.Tactic.Bound.Init


-- @@ L11-11 verbatim
/-! # BinderNotation -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
open Lean PrettyPrinter Delaborator SubExpr


-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace FirstOrder


-- @@ L21-21 verbatim
namespace BinderNotation


-- @@ L23-26 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev finSuccItr {n} (i : Fin n) : (m : ℕ) → Fin (n + m)
  | 0     => i
  | m + 1 => (finSuccItr i m).succ


-- @@ L28-28 verbatim
open Semiterm Semiformula


-- @@ L30-31 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
declare_syntax_cat firstOrderTerm


-- @@ L33-34 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "foTerm[" ident* " | " ident* " | " firstOrderTerm:0 "]" : term


-- @@ L36-37 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "(" firstOrderTerm ")" : firstOrderTerm


-- @@ L39-40 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max ident : firstOrderTerm         -- bounded variable

-- @@ L41-42 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "#" term:max : firstOrderTerm  -- bounded variable

-- @@ L43-44 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "&" term:max : firstOrderTerm  -- free variable

-- @@ L45-46 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:80 "!" term:max firstOrderTerm:81* (" ⋯")? : firstOrderTerm

-- @@ L47-48 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:80 "!!" term:max : firstOrderTerm

-- @@ L49-50 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:80 ".!" term:max firstOrderTerm:81* (" ⋯")? : firstOrderTerm

-- @@ L51-52 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:80 ".!!" term:max : firstOrderTerm


-- @@ L54-55 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax num : firstOrderTerm

-- @@ L56-57 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "↑" term:max : firstOrderTerm

-- @@ L58-59 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋆" : firstOrderTerm

-- @@ L60-61 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:50 firstOrderTerm:50 " + " firstOrderTerm:51 : firstOrderTerm

-- @@ L62-63 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 firstOrderTerm:60 " * " firstOrderTerm:61 : firstOrderTerm

-- @@ L64-65 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:65 firstOrderTerm:65 " ^ " firstOrderTerm:66 : firstOrderTerm

-- @@ L66-67 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:70 firstOrderTerm " ^' " num  : firstOrderTerm

-- @@ L68-69 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max firstOrderTerm "²"  : firstOrderTerm

-- @@ L70-71 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max firstOrderTerm "³"  : firstOrderTerm

-- @@ L72-73 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max firstOrderTerm "⁴"  : firstOrderTerm

-- @@ L74-75 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⌜" term:max "⌝" : firstOrderTerm


-- @@ L77-78 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:67  "exp " firstOrderTerm:68 : firstOrderTerm


-- @@ L80-144 unexpanded
macro_rules
  | `(foTerm[ $binders* | $fbinders* | ($e)    ]) => `(foTerm[ $binders* | $fbinders* | $e ])
  | `(foTerm[ $binders* | $fbinders* | $x:ident]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none => Macro.throwErrorAt x "error: variable did not found."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(&$i)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(#$i)
  | `(foTerm[ $_*       | $_*        | #$x:term   ]) => `(#$x)
  | `(foTerm[ $_*       | $_*        | &$x:term   ]) => `(&$x)
  | `(foTerm[ $_*       | $_*        | $m:num     ]) => `(Semiterm.numeral $m)
  | `(foTerm[ $_*       | $_*        | ↑$m:term   ]) => `(Semiterm.numeral $m)
  | `(foTerm[ $_*       | $_*        | ⌜$x:term⌝  ]) => `(⌜$x⌝)
  | `(foTerm[ $_*       | $_*        | ⋆          ]) => `(Operator.const Operator.Star.star)
  | `(foTerm[ $binders* | $fbinders* | $e₁ + $e₂  ]) =>
    `(Semiterm.Operator.Add.add.operator ![
      foTerm[ $binders* | $fbinders* | $e₁ ],
      foTerm[ $binders* | $fbinders* | $e₂ ]])
  | `(foTerm[ $binders* | $fbinders* | $e₁ * $e₂  ]) =>
    `(Semiterm.Operator.Mul.mul.operator ![
      foTerm[ $binders* | $fbinders* | $e₁ ],
      foTerm[ $binders* | $fbinders* | $e₂ ]])
  | `(foTerm[ $binders* | $fbinders* | $e₁ ^ $e₂  ]) =>
    `(Semiterm.Operator.Pow.pow.operator ![
      foTerm[ $binders* | $fbinders* | $e₁ ],
      foTerm[ $binders* | $fbinders* | $e₂ ]])
  | `(foTerm[ $binders* | $fbinders* | $e ^' $n   ]) =>
    `((Semiterm.Operator.npow _ $n).operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $binders* | $fbinders* | $e²        ]) =>
    `((Semiterm.Operator.npow _ 2).operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $binders* | $fbinders* | $e³        ]) =>
    `((Semiterm.Operator.npow _ 3).operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $binders* | $fbinders* | $e⁴        ]) =>
    `((Semiterm.Operator.npow _ 4).operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $binders* | $fbinders* | exp $e     ]) =>
    `(Semiterm.Operator.Exp.exp.operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $_*       | $_*        | !!$t:term  ]) => `($t)
  | `(foTerm[ $_*       | $_*        | .!!$t:term ]) => `(Rew.emb $t)
  | `(foTerm[ $binders* | $fbinders* | !$t:term $vs:firstOrderTerm* ])    => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![]))
      (fun a s => `(foTerm[ $binders* | $fbinders* | $a ] :> $s))
    `(Rew.substs $v $t)
  | `(foTerm[ $binders* | $fbinders* | !$t:term $vs:firstOrderTerm* ⋯ ])  =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _)
      (init := ← `(fun x ↦ #(finSuccItr x $length)))
      (fun a s ↦ `(foTerm[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.substs $v $t)
  | `(foTerm[ $binders* | $fbinders* | .!$t:term $vs:firstOrderTerm* ])   => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![]))
      (fun a s ↦ `(foTerm[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)
  | `(foTerm[ $binders* | $fbinders* | .!$t:term $vs:firstOrderTerm* ⋯ ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _)
      (init := ← `(fun x ↦ #(finSuccItr x $length)))
      (fun a s ↦ `(foTerm[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)


-- @@ L146-147 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "‘" firstOrderTerm:0 "’" : term

-- @@ L148-149 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "‘" ident* "| " firstOrderTerm:0 "’" : term

-- @@ L150-151 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "‘" ident* ". " firstOrderTerm:0 "’" : term


-- @@ L153-156 expanded
macro_rules
  | `(foTerm[ | | $e:firstOrderTerm]) => `(foTerm[ | | $e])
  | `(foTerm[ | $fbinders* | $e:firstOrderTerm]) => `(foTerm[ | $fbinders* | $e])
  | `(foTerm[$binders* | | $e:firstOrderTerm]) => `(foTerm[$binders* | | $e])


-- @@ L158-158 verbatim
section «lp_section_1»


-- @@ L160-164 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.numeral]
meta def unexpsnderNatLit : Unexpander
  | `($_ $_ $z:num) => `($z:num)
  | _ => throw ()


-- @@ L166-170 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.const]
meta def unexpsnderOperatorConst : Unexpander
  | `($_ $z:num) => `(‘ $z:num ’)
  | _ => throw ()


-- @@ L172-175 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.Add.add]
meta def unexpsnderAdd : Unexpander
  | `($_) => `(Add.add)


-- @@ L177-185 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.Mul.mul]
meta def unexpsnderMul : Unexpander
  | `($_) =>
    `(Mul.mul)
      /-
      
      
      -/


-- @@ L187-222 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.operator]
meta def unexpandFuncArith : Unexpander
  | `($_ op(+) ![‘$t:firstOrderTerm’,   ‘$u:firstOrderTerm’   ]) => `(‘($t     + $u    )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   #$x                     ]) => `(‘($t     + #$x   )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   &$x                     ]) => `(‘($t     + &$x   )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   $u                      ]) => `(‘($t     + !!$u  )’)
  | `($_ op(+) ![#$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(#$x    + $u    )’)
  | `($_ op(+) ![#$x,                     #$y                     ]) => `(‘(#$x    + #$y   )’)
  | `($_ op(+) ![#$x,                     &$y                     ]) => `(‘(#$x    + &$y   )’)
  | `($_ op(+) ![#$x,                     $u                      ]) => `(‘(#$x    + !!$u  )’)
  | `($_ op(+) ![&$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(&$x    + $u    )’)
  | `($_ op(+) ![&$x,                     #$y                     ]) => `(‘(&$x    + #$y   )’)
  | `($_ op(+) ![&$x,                     &$y                     ]) => `(‘(&$x    + &$y   )’)
  | `($_ op(+) ![&$x,                     $u                      ]) => `(‘(&$x    + !!$u  )’)
  | `($_ op(+) ![$t,                      ‘$u:firstOrderTerm’   ]) => `(‘(!!$t   + $u    )’)
  | `($_ op(+) ![$t,                      #$y                     ]) => `(‘(!!$t   + #$y   )’)
  | `($_ op(+) ![$t,                      &$y                     ]) => `(‘(!!$t   + &$y   )’)
  | `($_ op(+) ![$t,                      $u                      ]) => `(‘(!!$t   + !!$u  )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   ‘$u:firstOrderTerm’   ]) => `(‘($t     * $u    )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   #$x                     ]) => `(‘($t     * #$x   )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   &$x                     ]) => `(‘($t     * &$x   )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   $u                      ]) => `(‘($t     * !!$u  )’)
  | `($_ op(*) ![#$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(#$x    * $u    )’)
  | `($_ op(*) ![#$x,                     #$y                     ]) => `(‘(#$x    * #$y   )’)
  | `($_ op(*) ![#$x,                     &$y                     ]) => `(‘(#$x    * &$y   )’)
  | `($_ op(*) ![#$x,                     $u                      ]) => `(‘(#$x    * !!$u  )’)
  | `($_ op(*) ![&$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(&$x    * $u    )’)
  | `($_ op(*) ![&$x,                     #$y                     ]) => `(‘(&$x    * #$y   )’)
  | `($_ op(*) ![&$x,                     &$y                     ]) => `(‘(&$x    * &$y   )’)
  | `($_ op(*) ![&$x,                     $u                      ]) => `(‘(&$x    * !!$u  )’)
  | `($_ op(*) ![$t,                      ‘$u:firstOrderTerm’   ]) => `(‘(!!$t   * $u    )’)
  | `($_ op(*) ![$t,                      #$y                     ]) => `(‘(!!$t   * #$y   )’)
  | `($_ op(*) ![$t,                      &$y                     ]) => `(‘(!!$t   * &$y   )’)
  | `($_ op(*) ![$t,                      $u                      ]) => `(‘(!!$t   * !!$u  )’)
  | _                             => throw ()


-- @@ L224-228 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.numeral]
meta def unexpandNumeral : Unexpander
  | `($_ $n:num) => `(‘$n:num’)
  | _            => throw ()


-- @@ L230-230 verbatim
end «lp_section_1»


-- @@ L232-232 verbatim
open Semiformula


-- @@ L234-235 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
declare_syntax_cat firstOrderFormula


-- @@ L237-238 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "foFormula[" ident* " | " ident* " | " firstOrderFormula:0 "]" : term


-- @@ L240-241 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "(" firstOrderFormula ")" : firstOrderFormula


-- @@ L243-244 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 "!" term:max firstOrderTerm:61* ("⋯")? : firstOrderFormula

-- @@ L245-246 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 "!!" term:max : firstOrderFormula


-- @@ L248-249 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 ".!" term:max firstOrderTerm:61* ("⋯")? : firstOrderFormula

-- @@ L250-251 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 ".!!" term:max : firstOrderFormula


-- @@ L253-254 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "⊤" : firstOrderFormula

-- @@ L255-256 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "⊥" : firstOrderFormula

-- @@ L257-258 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:32 firstOrderFormula:33 " ∧ " firstOrderFormula:32 : firstOrderFormula

-- @@ L259-260 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:30 firstOrderFormula:31 " ∨ " firstOrderFormula:30 : firstOrderFormula

-- @@ L261-262 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "¬" firstOrderFormula:35 : firstOrderFormula

-- @@ L263-264 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:10 firstOrderFormula:9 " → " firstOrderFormula:10 : firstOrderFormula

-- @@ L265-266 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:5 firstOrderFormula " ↔ " firstOrderFormula : firstOrderFormula

-- @@ L267-268 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋀ " ident ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L269-270 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋁ " ident ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L271-272 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋀ " ident " < " term ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L273-274 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋁ " ident " < " term ", " firstOrderFormula:0 : firstOrderFormula


-- @@ L276-277 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident+ ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L278-279 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident+ ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L280-281 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀' " firstOrderFormula:0 : firstOrderFormula

-- @@ L282-283 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃' " firstOrderFormula:0 : firstOrderFormula

-- @@ L284-285 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀[" firstOrderFormula "] " firstOrderFormula:0 : firstOrderFormula

-- @@ L286-287 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃[" firstOrderFormula "] " firstOrderFormula:0 : firstOrderFormula


-- @@ L289-360 unexpanded
macro_rules
  | `(foFormula[ $binders* | $fbinders* | ($e:firstOrderFormula)          ]) =>
    `(foFormula[ $binders* | $fbinders* | $e ])
  | `(foFormula[ $_*       | $_*        | !!$φ:term                         ]) => `($φ)
  | `(foFormula[ $binders* | $fbinders* | !$φ:term $vs:firstOrderTerm*    ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s =>
      `(foTerm[ $binders* | $fbinders* | $a ] :> $s))
    `($φ <~ $v)
  | `(foFormula[ $binders* | $fbinders* | !$φ:term $vs:firstOrderTerm* ⋯  ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s
      ↦ `(foTerm[ $binders* | $fbinders* | $a] :> $s))
    `($φ <~ $v)
  | `(foFormula[ $_*       | $_*        | .!!$φ:term ])                        =>
    `(Rewriting.embedding $φ)
  | `(foFormula[ $_*       | $_*        | ⊤                                 ]) => `(⊤)
  | `(foFormula[ $_*       | $_*        | ⊥                                 ]) => `(⊥)
  | `(foFormula[ $binders* | $fbinders* | $φ ∧ $ψ                           ]) =>
    `(foFormula[ $binders* | $fbinders* | $φ ] ⋏ foFormula[ $binders* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | $φ ∨ $ψ                           ]) =>
    `(foFormula[ $binders* | $fbinders* | $φ ] ⋎ foFormula[ $binders* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | ¬$φ                               ]) =>
    `(∼foFormula[ $binders* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | $φ → $ψ                           ]) =>
    `(foFormula[ $binders* | $fbinders* | $φ ] ==> foFormula[ $binders* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | $φ ↔ $ψ                           ]) =>
    `(foFormula[ $binders* | $fbinders* | $φ ] <=> foFormula[ $binders* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | ⋀ $i, $φ                          ]) =>
    `(Matrix.conjVec fun $i ↦ foFormula[ $binders* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ⋁ $i, $φ                          ]) =>
    `(Matrix.disj fun $i ↦ foFormula[ $binders* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ⋀ $i < $t, $φ                     ]) =>
    `(conjLt (fun $i ↦ foFormula[ $binders* | $fbinders* | $φ ]) $t)
  | `(foFormula[ $binders* | $fbinders* | ⋁ $i < $t, $φ                     ]) =>
    `(disjLt (fun $i ↦ foFormula[ $binders* | $fbinders* | $φ ]) $t)
  | `(foFormula[ $binders* | $fbinders* | ∀ $xs*, $φ                        ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(foFormula[ $binders'* | $fbinders* | $φ ])
      (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∀' $ψ))
    return s
  | `(foFormula[ $binders* | $fbinders* | ∃ $xs*, $φ                        ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(foFormula[ $binders'* | $fbinders* | $φ ])
      (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∃' $ψ))
    return s
  | `(foFormula[ $binders* | $fbinders* | ∀' $φ ])                            => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀' foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ∃' $φ ])                            => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃' foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ∀[ $φ ] $ψ ])                       => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀[foFormula[ $binders'* | $fbinders* | $φ ]] foFormula[ $binders'* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | ∃[ $φ ] $ψ ])                       => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃[foFormula[ $binders'* | $fbinders* | $φ ]] foFormula[ $binders'* | $fbinders* | $ψ ])


-- @@ L362-363 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "“" ident* "| "  firstOrderFormula:0 "”" : term

-- @@ L364-365 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "“" ident* ". "  firstOrderFormula:0 "”" : term

-- @@ L366-367 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax "“" firstOrderFormula:0 "”" : term


-- @@ L369-372 expanded
macro_rules
  | `(foFormula[ | | $e:firstOrderFormula]) => `(foFormula[ | | $e])
  | `(foFormula[$binders* | | $e:firstOrderFormula]) => `(foFormula[$binders* | | $e])
  | `(foFormula[ | $fbinders* | $e:firstOrderFormula]) => `(foFormula[ | $fbinders* | $e])


-- @@ L374-375 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " = " firstOrderTerm:0 : firstOrderFormula

-- @@ L376-377 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " < " firstOrderTerm:0 : firstOrderFormula

-- @@ L378-379 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " > " firstOrderTerm:0 : firstOrderFormula

-- @@ L380-381 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ≤ " firstOrderTerm:0 : firstOrderFormula

-- @@ L382-383 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ≥ " firstOrderTerm:0 : firstOrderFormula

-- @@ L384-385 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ∈ " firstOrderTerm:0 : firstOrderFormula

-- @@ L386-387 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ∋ " firstOrderTerm:0 : firstOrderFormula

-- @@ L388-389 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ≠ " firstOrderTerm:0 : firstOrderFormula

-- @@ L390-391 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " </ " firstOrderTerm:0 : firstOrderFormula

-- @@ L392-393 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ≰ " firstOrderTerm:0 : firstOrderFormula

-- @@ L394-395 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ∉ " firstOrderTerm:0 : firstOrderFormula


-- @@ L397-398 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident " < " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L399-400 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident " ≤ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L401-402 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident " ∈ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L403-404 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident " < " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L405-406 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident " ≤ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

-- @@ L407-408 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident " ∈ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula


-- @@ L410-490 expanded
macro_rules
  |
  `(Semiformula.ballLT foTerm[$binders* | $fbinders* | $t]
        foFormula[$x$binders* | $fbinders* | $φ]) =>
    do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.ballLT foTerm[$binders* | $fbinders* | $t]
            foFormula[$binders'* | $fbinders* | $φ])
  |
  `(Semiformula.ballLE foTerm[$binders* | $fbinders* | $t]
        foFormula[$x$binders* | $fbinders* | $φ]) =>
    do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.ballLE foTerm[$binders* | $fbinders* | $t]
            foFormula[$binders'* | $fbinders* | $φ])
  |
  `(Semiformula.ballMem foTerm[$binders* | $fbinders* | $t]
        foFormula[$x$binders* | $fbinders* | $φ]) =>
    do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.ballMem foTerm[$binders* | $fbinders* | $t]
            foFormula[$binders'* | $fbinders* | $φ])
  |
  `(Semiformula.bexLT foTerm[$binders* | $fbinders* | $t]
        foFormula[$x$binders* | $fbinders* | $φ]) =>
    do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.bexLT foTerm[$binders* | $fbinders* | $t]
            foFormula[$binders'* | $fbinders* | $φ])
  |
  `(Semiformula.bexLE foTerm[$binders* | $fbinders* | $t]
        foFormula[$x$binders* | $fbinders* | $φ]) =>
    do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.bexLE foTerm[$binders* | $fbinders* | $t]
            foFormula[$binders'* | $fbinders* | $φ])
  |
  `(Semiformula.bexMem foTerm[$binders* | $fbinders* | $t]
        foFormula[$x$binders* | $fbinders* | $φ]) =>
    do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.bexMem foTerm[$binders* | $fbinders* | $t]
            foFormula[$binders'* | $fbinders* | $φ])
  |
  `(Semiformula.Operator.operator Operator.Eq.eq
        ![foTerm[$binders* | $fbinders* | $t:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $u:firstOrderTerm]]) =>
    `(Semiformula.Operator.operator Operator.Eq.eq
        ![foTerm[$binders* | $fbinders* | $t], foTerm[$binders* | $fbinders* | $u]])
  |
  `(Semiformula.Operator.operator Operator.LT.lt
        ![foTerm[$binders* | $fbinders* | $t:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $u:firstOrderTerm]]) =>
    `(Semiformula.Operator.operator Operator.LT.lt
        ![foTerm[$binders* | $fbinders* | $t], foTerm[$binders* | $fbinders* | $u]])
  |
  `(Semiformula.Operator.operator Operator.LT.lt
        ![foTerm[$binders* | $fbinders* | $u:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t:firstOrderTerm]]) =>
    `(Semiformula.Operator.operator Operator.LT.lt
        ![foTerm[$binders* | $fbinders* | $u], foTerm[$binders* | $fbinders* | $t]])
  |
  `(Semiformula.Operator.operator Operator.LE.le
        ![foTerm[$binders* | $fbinders* | $t:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $u:firstOrderTerm]]) =>
    `(Semiformula.Operator.operator Operator.LE.le
        ![foTerm[$binders* | $fbinders* | $t], foTerm[$binders* | $fbinders* | $u]])
  |
  `(Semiformula.Operator.operator Operator.LE.le
        ![foTerm[$binders* | $fbinders* | $u:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t:firstOrderTerm]]) =>
    `(Semiformula.Operator.operator Operator.LE.le
        ![foTerm[$binders* | $fbinders* | $u], foTerm[$binders* | $fbinders* | $t]])
  |
  `(Semiformula.Operator.operator Operator.Mem.mem
        ![foTerm[$binders* | $fbinders* | $t:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $u:firstOrderTerm]]) =>
    `(Semiformula.Operator.operator Operator.Mem.mem
        ![foTerm[$binders* | $fbinders* | $t], foTerm[$binders* | $fbinders* | $u]])
  |
  `(Semiformula.Operator.operator Operator.Mem.mem
        ![foTerm[$binders* | $fbinders* | $u:firstOrderTerm],
          foTerm[$binders* | $fbinders* | $t:firstOrderTerm]]) =>
    `(Semiformula.Operator.operator Operator.Mem.mem
        ![foTerm[$binders* | $fbinders* | $u], foTerm[$binders* | $fbinders* | $t]])
  |
  `(Tilde.tilde
        (Semiformula.Operator.operator Operator.Eq.eq
          ![foTerm[$binders* | $fbinders* | $t:firstOrderTerm],
            foTerm[$binders* | $fbinders* | $u:firstOrderTerm]])) =>
    `(Tilde.tilde
        (Semiformula.Operator.operator Operator.Eq.eq
          ![foTerm[$binders* | $fbinders* | $t], foTerm[$binders* | $fbinders* | $u]]))
  |
  `(Tilde.tilde
        (Semiformula.Operator.operator Operator.LT.lt
          ![foTerm[$binders* | $fbinders* | $t:firstOrderTerm],
            foTerm[$binders* | $fbinders* | $u:firstOrderTerm]])) =>
    `(Tilde.tilde
        (Semiformula.Operator.operator Operator.LT.lt
          ![foTerm[$binders* | $fbinders* | $t], foTerm[$binders* | $fbinders* | $u]]))
  |
  `(Tilde.tilde
        (Semiformula.Operator.operator Operator.LE.le
          ![foTerm[$binders* | $fbinders* | $t:firstOrderTerm],
            foTerm[$binders* | $fbinders* | $u:firstOrderTerm]])) =>
    `(Tilde.tilde
        (Semiformula.Operator.operator Operator.LE.le
          ![foTerm[$binders* | $fbinders* | $t], foTerm[$binders* | $fbinders* | $u]]))
  |
  `(Tilde.tilde
        (Semiformula.Operator.operator Operator.Mem.mem
          ![foTerm[$binders* | $fbinders* | $t:firstOrderTerm],
            foTerm[$binders* | $fbinders* | $u:firstOrderTerm]])) =>
    `(Tilde.tilde
        (Semiformula.Operator.operator Operator.Mem.mem
          ![foTerm[$binders* | $fbinders* | $t], foTerm[$binders* | $fbinders* | $u]]))


-- @@ L492-492 verbatim
section «lp_section_2»


-- @@ L494-497 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Language.Eq.eq]
meta def unexpsnderEq : Unexpander
  | `($_) => `(Operator.Eq.eq)


-- @@ L499-502 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Language.LT.lt]
meta def unexpsnderLe : Unexpander
  | `($_) => `(Operator.LT.lt)


-- @@ L504-510 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Wedge.wedge]
meta def unexpandAnd : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ ($φ ∧ $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ ($φ ∧ !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (!$t ∧ $ψ) ”)
  | _                                                           => throw ()


-- @@ L512-518 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Vee.vee]
meta def unexpandOr : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ ($φ ∨ $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ ($φ ∨ !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (!$t ∨ $ψ) ”)
  | _                                                           => throw ()


-- @@ L520-524 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Tilde.tilde]
meta def unexpandNeg : Unexpander
  | `($_ “ $φ:firstOrderFormula ”) => `(“ ¬$φ ”)
  | _                                => throw ()


-- @@ L526-530 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander UnivQuantifier.univ]
meta def unexpandUniv : Unexpander
  | `($_ “ $φ:firstOrderFormula ”) => `(“ ∀' $φ:firstOrderFormula ”)
  | _                                => throw ()


-- @@ L532-536 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander ExQuantifier.ex]
meta def unexpandEx : Unexpander
  | `($_ “ $φ:firstOrderFormula”) => `(“ ∃' $φ:firstOrderFormula ”)
  | _                                   => throw ()


-- @@ L538-544 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander ball]
meta def unexpandBall : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ (∀[$φ] $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ (∀[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (∀[!$t] $ψ) ”)
  | _                                                           => throw ()


-- @@ L546-552 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander bex]
meta def unexpandBex : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ (∃[$φ] $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ (∃[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (∃[!$t] $ψ) ”)
  | _                                                           => throw ()


-- @@ L554-560 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Arrow.arrow]
meta def unexpandArrow : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula”) => `(“ ($φ → $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                  ) => `(“ ($φ → !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula”) => `(“ (!$t → $ψ) ”)
  | _                                                          => throw ()


-- @@ L562-568 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander LogicalConnective.iff]
meta def unexpandIff : Unexpander
  | `($_ “ $φ:firstOrderFormula” “ $ψ:firstOrderFormula”) => `(“ ($φ ↔ $ψ) ”)
  | `($_ “ $φ:firstOrderFormula” $u:term                  ) => `(“ ($φ ↔ !$u) ”)
  | `($_ $t:term                   “ $ψ:firstOrderFormula”) => `(“ (!$t ↔ $ψ) ”)
  | _                                                         => throw ()


-- @@ L570-701 unexpanded
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiformula.Operator.operator]
meta def unexpandOpArith : Unexpander
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) =>
    `(“ $t:firstOrderTerm = $u   ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) =>
    `(“ $t:firstOrderTerm = #$y  ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) =>
    `(“ $t:firstOrderTerm = &$y  ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  $u                     ]) =>
    `(“ $t:firstOrderTerm = !!$u ”)
  | `($_ op(=) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ #$x                 = $u   ”)
  | `($_ op(=) ![#$x:term,                 #$y:term               ]) =>
    `(“ #$x                 = #$y  ”)
  | `($_ op(=) ![#$x:term,                 &$y:term               ]) =>
    `(“ #$x                 = &$y  ”)
  | `($_ op(=) ![#$x:term,                 $u                     ]) =>
    `(“ #$x                 = !!$u ”)
  | `($_ op(=) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ &$x                 = $u   ”)
  | `($_ op(=) ![&$x:term,                 #$y:term               ]) =>
    `(“ &$x                 = #$y  ”)
  | `($_ op(=) ![&$x:term,                 &$y:term               ]) =>
    `(“ &$x                 = &$y  ”)
  | `($_ op(=) ![&$x:term,                 $u                     ]) =>
    `(“ &$x                 = !!$u ”)
  | `($_ op(=) ![$t:term,                  ‘ $u:firstOrderTerm ’]) =>
    `(“ !!$t                = $u   ”)
  | `($_ op(=) ![$t:term,                  #$y:term               ]) =>
    `(“ !!$t                = #$y  ”)
  | `($_ op(=) ![$t:term,                  &$y:term               ]) =>
    `(“ !!$t                = &$y  ”)
  | `($_ op(=) ![$t:term,                  $u                     ]) =>
    `(“ !!$t                = !!$u ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) =>
    `(“ $t:firstOrderTerm < $u   ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) =>
    `(“ $t:firstOrderTerm < #$y  ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) =>
    `(“ $t:firstOrderTerm < &$y  ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  $u                     ]) =>
    `(“ $t:firstOrderTerm < !!$u ”)
  | `($_ op(<) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ #$x                 < $u   ”)
  | `($_ op(<) ![#$x:term,                 #$y:term               ]) =>
    `(“ #$x                 < #$y  ”)
  | `($_ op(<) ![#$x:term,                 &$y:term               ]) =>
    `(“ #$x                 < &$y  ”)
  | `($_ op(<) ![#$x:term,                 $u                     ]) =>
    `(“ #$x                 < !!$u ”)
  | `($_ op(<) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ &$x                 < $u   ”)
  | `($_ op(<) ![&$x:term,                 #$y:term               ]) =>
    `(“ &$x                 < #$y  ”)
  | `($_ op(<) ![&$x:term,                 &$y:term               ]) =>
    `(“ &$x                 < &$y  ”)
  | `($_ op(<) ![&$x:term,                 $u                     ]) =>
    `(“ &$x                 < !!$u ”)
  | `($_ op(<) ![$t:term,                  ‘ $u:firstOrderTerm ’]) =>
    `(“ !!$t                < $u   ”)
  | `($_ op(<) ![$t:term,                  #$y:term               ]) =>
    `(“ !!$t                < #$y  ”)
  | `($_ op(<) ![$t:term,                  &$y:term               ]) =>
    `(“ !!$t                < &$y  ”)
  | `($_ op(<) ![$t:term,                  $u                     ]) =>
    `(“ !!$t                < !!$u ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) =>
    `(“ $t:firstOrderTerm ≤ $u   ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) =>
    `(“ $t:firstOrderTerm ≤ #$y  ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) =>
    `(“ $t:firstOrderTerm ≤ &$y  ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  $u                     ]) =>
    `(“ $t:firstOrderTerm ≤ !!$u ”)
  | `($_ op(≤) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ #$x                 ≤ $u   ”)
  | `($_ op(≤) ![#$x:term,                 #$y:term               ]) =>
    `(“ #$x                 ≤ #$y  ”)
  | `($_ op(≤) ![#$x:term,                 &$y:term               ]) =>
    `(“ #$x                 ≤ &$y  ”)
  | `($_ op(≤) ![#$x:term,                 $u                     ]) =>
    `(“ #$x                 ≤ !!$u ”)
  | `($_ op(≤) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ &$x                 ≤ $u   ”)
  | `($_ op(≤) ![&$x:term,                 #$y:term               ]) =>
    `(“ &$x                 ≤ #$y  ”)
  | `($_ op(≤) ![&$x:term,                 &$y:term               ]) =>
    `(“ &$x                 ≤ &$y  ”)
  | `($_ op(≤) ![&$x:term,                 $u                     ]) =>
    `(“ &$x                 ≤ !!$u ”)
  | `($_ op(≤) ![$t:term,                  ‘ $u:firstOrderTerm ’]) =>
    `(“ !!$t                ≤ $u   ”)
  | `($_ op(≤) ![$t:term,                  #$y:term               ]) =>
    `(“ !!$t                ≤ #$y  ”)
  | `($_ op(≤) ![$t:term,                  &$y:term               ]) =>
    `(“ !!$t                ≤ &$y  ”)
  | `($_ op(≤) ![$t:term,                  $u                     ]) =>
    `(“ !!$t                ≤ !!$u ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) =>
    `(“ $t:firstOrderTerm ∈ $u   ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) =>
    `(“ $t:firstOrderTerm ∈ #$y  ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) =>
    `(“ $t:firstOrderTerm ∈ &$y  ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  $u                     ]) =>
    `(“ $t:firstOrderTerm ∈ !!$u ”)
  | `($_ op(∈) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ #$x                 ∈ $u   ”)
  | `($_ op(∈) ![#$x:term,                 #$y:term               ]) =>
    `(“ #$x                 ∈ #$y  ”)
  | `($_ op(∈) ![#$x:term,                 &$y:term               ]) =>
    `(“ #$x                 ∈ &$y  ”)
  | `($_ op(∈) ![#$x:term,                 $u                     ]) =>
    `(“ #$x                 ∈ !!$u ”)
  | `($_ op(∈) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ &$x                 ∈ $u   ”)
  | `($_ op(∈) ![&$x:term,                 #$y:term               ]) =>
    `(“ &$x                 ∈ #$y  ”)
  | `($_ op(∈) ![&$x:term,                 &$y:term               ]) =>
    `(“ &$x                 ∈ &$y  ”)
  | `($_ op(∈) ![&$x:term,                 $u                     ]) =>
    `(“ &$x                 ∈ !!$u ”)
  | `($_ op(∈) ![$t:term,                  ‘ $u:firstOrderTerm ’]) =>
    `(“ !!$t                ∈ $u   ”)
  | `($_ op(∈) ![$t:term,                  #$y:term               ]) =>
    `(“ !!$t                ∈ #$y  ”)
  | `($_ op(∈) ![$t:term,                  &$y:term               ]) =>
    `(“ !!$t                ∈ &$y  ”)
  | `($_ op(∈) ![$t:term,                  $u                     ]) =>
    `(“ !!$t                ∈ !!$u ”)
  | _                                                            => throw ()


-- @@ L703-703 verbatim
end «lp_section_2»


-- @@ L705-705 verbatim
end BinderNotation


-- @@ L707-707 verbatim
end FirstOrder

-- @@ L708-708 verbatim
end LO
