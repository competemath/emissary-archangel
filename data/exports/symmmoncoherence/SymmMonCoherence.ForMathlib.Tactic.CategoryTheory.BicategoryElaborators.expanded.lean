/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic


-- @@ L10-10 verbatim
public meta section


-- @@ L12-12 verbatim
namespace Mathlib.Tactic.CategoryTheory.bicategoryElaborators


-- @@ L14-14 verbatim
open Lean Elab Term Meta Mathlib.Tactic.Push _root_.CategoryTheory


-- @@ L16-16 verbatim
section lemmas


-- @@ L18-18 verbatim
universe w v u


-- @@ L20-20 verbatim
open Bicategory


-- @@ L22-25 verbatim
theorem congrWhiskerRight {C : Type u} [Bicategory.{w, v} C] {X Y : C}
    {f g : X ⟶ Y} {η θ : f ⟶ g} (w : η = θ) {Z : C} (h : Y ⟶ Z) :
    η ▷ h = θ ▷ h := by
  rw [w]


-- @@ L27-30 verbatim
theorem congrWhiskerLeft {C : Type u} [Bicategory.{w, v} C] {X Y : C}
    {f g : X ⟶ Y} {η θ : f ⟶ g} (w : η = θ) {Z : C} (h : Z ⟶ X) :
    h ◁ η = h ◁ θ := by
  rw [w]


-- @@ L32-32 verbatim
end lemmas


-- @@ L34-52 verbatim
/--
Given an equation `η = θ` between 2 morphisms `f ⟶ g` in a category,
where f g : X ⟶ Y
produce the equation `∀ {Z} (h : Y ⟶ Z), η ▷ h = θ ▷ h`,
but with whiskering right reassociated.
Also returns the category `C` and any instance metavariables that need to be solved for.
-/
def whiskerRightExprHom (e : Expr) : MetaM (Expr × Array MVarId) := do
  let lem₀ ← mkConstWithFreshMVarLevels ``congrWhiskerRight
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 9
  let inst := args[1]!
  inst.mvarId!.setKind .synthetic
  let w := args[8]!
  w.mvarId!.assignIfDefEq e
  withEnsuringLocalInstance inst.mvarId! do
    return (← simpType
      (fun e => simpOnlyNames [``Category.assoc, ``Bicategory.comp_whiskerRight] e
        (config := { decide := false }))
      (mkAppN lem₀ args), #[inst.mvarId!])


-- @@ L54-58 verbatim
def whiskerRightExpr (pf : Expr) : MetaM (Expr × Array MVarId) := do
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pf := mkAppN pf xs
    let (pf, insts) ← whiskerRightExprHom pf
    return (← mkLambdaFVars xs pf, insts)


-- @@ L60-70 verbatim
/--
Version of `whiskerRightExpr` for the `TermElabM` monad.
Handles instance metavariables automatically.
-/
def whiskerRightExpr' (pf : Expr) : TermElabM Expr := do
  let (e, insts) ← whiskerRightExpr pf
  for inst in insts do
    inst.withContext do
      unless ← Term.synthesizeInstMVarCore inst do
        Term.registerSyntheticMVarWithCurrRef inst (.typeClass none)
  return e


-- @@ L72-74 verbatim
elab "wr% " t:term : term => do
  let e ← Term.withSynthesizeLight <| Term.elabTerm t none
  whiskerRightExpr' e


-- @@ L76-94 verbatim
/--
Given an equation `η = θ` between 2 morphisms `f ⟶ g` in a category,
where f g : X ⟶ Y
produce the equation `∀ {Z} (h : Z ⟶ X), h ◁ η = h ◁ θ`,
but with whiskering left reassociated.
Also returns the category `C` and any instance metavariables that need to be solved for.
-/
def whiskerLeftExprHom (e : Expr) : MetaM (Expr × Array MVarId) := do
  let lem₀ ← mkConstWithFreshMVarLevels ``congrWhiskerLeft
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 9
  let inst := args[1]!
  inst.mvarId!.setKind .synthetic
  let w := args[8]!
  w.mvarId!.assignIfDefEq e
  withEnsuringLocalInstance inst.mvarId! do
    return (← simpType
      (fun e => simpOnlyNames [``Category.assoc, ``Bicategory.whiskerLeft_comp] e
        (config := { decide := false }))
      (mkAppN lem₀ args), #[inst.mvarId!])


-- @@ L96-100 verbatim
def whiskerLeftExpr (pf : Expr) : MetaM (Expr × Array MVarId) := do
  forallTelescopeReducing (← inferType pf) fun xs _ => do
    let pf := mkAppN pf xs
    let (pf, insts) ← whiskerLeftExprHom pf
    return (← mkLambdaFVars xs pf, insts)


-- @@ L102-112 verbatim
/--
Version of `whiskerLeftExpr` for the `TermElabM` monad.
Handles instance metavariables automatically.
-/
def whiskerLeftExpr' (pf : Expr) : TermElabM Expr := do
  let (e, insts) ← whiskerLeftExpr pf
  for inst in insts do
    inst.withContext do
      unless ← Term.synthesizeInstMVarCore inst do
        Term.registerSyntheticMVarWithCurrRef inst (.typeClass none)
  return e


-- @@ L114-116 verbatim
elab "wl% " t:term : term => do
  let e ← Term.withSynthesizeLight <| Term.elabTerm t none
  whiskerLeftExpr' e


-- @@ L118-132 verbatim
/-- Syntax for the `◁%` elaborator. -/
elab (name := whiskerLeftPercent) x:term "◁%" t:term : term => do
  let t ← (elabTerm t none)
  let x ← (elabTerm x none)
  mapForallTelescope (fun e => do
    match_expr ← inferType e with
    | Eq T _ _ =>
      let_expr Quiver.Hom _ _ u v := T | throwError "◁%: invalid term"
      let e₀ ← mkCongrArg (← mkAppOptM ``CategoryTheory.Bicategory.whiskerLeft
        #[none, none, none, none, none, x, u, v]) e
      let e₁ ←
        simpEq (fun e => simpOnlyNames [``CategoryTheory.Bicategory.whiskerLeft_comp] e
          (config := { decide := false })) (← inferType e₀) e₀
      return e₁.2
    | _ => throwError "◁%: invalid term") t


-- @@ L134-150 verbatim
/-- Syntax for the `▷%` elaborator. -/
elab (name := whiskerRightPercent) t:term "▷%" x:term : term => do
  let t ← (elabTerm t none)
  let x ← (elabTerm x none)
  mapForallTelescope (fun e => do
    match_expr ← inferType e with
    | Eq T _ _ =>
      let_expr Quiver.Hom _ _ u v := T | throwError "▷%: invalid term"
      let g ← mkFreshExprMVar T
      let e₀ ← mkCongrArg (← mkLambdaFVars #[g]
        (← mkAppOptM ``CategoryTheory.Bicategory.whiskerRight
          #[none, none, none, none, none, u, v, g, x])) e
      let e₁ ←
        simpEq (fun e => simpOnlyNames [``CategoryTheory.Bicategory.comp_whiskerRight] e
          (config := { decide := false })) (← inferType e₀) e₀
      return e₁.2
    | _ => throwError "▷%: invalid term") t


-- @@ L152-152 verbatim
end Mathlib.Tactic.CategoryTheory.bicategoryElaborators


-- @@ L154-154 verbatim
end
