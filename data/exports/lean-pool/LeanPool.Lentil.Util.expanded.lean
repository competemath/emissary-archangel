/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import Lean.Data.Options
public meta import Lean.Meta.Tactic.Simp.Simproc
meta import Lean.Meta.Tactic.Simp.Attr
import Lean.Meta.Tactic.Simp.RegisterCommand


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
open Lean


-- @@ L17-21 verbatim
/-- Whether to use the custom TLA delaborator when pretty-printing. -/
register_option lentil.pp.useDelab : Bool := {
  defValue := true
  descr := "Use the delaborator from `Lentil.Basic` for delaboration. "
}


-- @@ L23-27 verbatim
/-- Whether to automatically render `satisfies` with the `|=tla=` notation. -/
register_option lentil.pp.autoRenderSatisfies : Bool := {
  defValue := true
  descr := "Automatically render an application `p e` as `e |=tla= p` when `p` is a TLA formula. "
}


-- @@ L29-30 verbatim
/-- Marking the non-temporal parts of TLA. -/
register_simp_attr tla_nontemporal_def


-- @@ L32-33 verbatim
/-- Marking the TLA definitions. -/
register_simp_attr tlasimp_def


-- @@ L35-36 verbatim
/-- Marking the things to simplify when explicitly reasoning about `exec`. -/
register_simp_attr execsimp


-- @@ L38-39 verbatim
/-- Marking the definitions unfolded by `tlaFiniteWindow`. -/
register_simp_attr tla_finite_window_def


-- @@ L41-42 verbatim
/-- Marking the theorems that can be simplify reasoning at the TLA level. -/
register_simp_attr tlasimp


-- @@ L44-45 verbatim
/-- Marking the theorems that are dual to some existing theorems. -/
register_simp_attr tladual


-- @@ L47-48 verbatim
/-- Marking the theorems that are used for normalizing sequents. -/
register_simp_attr tlanormsimp


-- @@ L50-50 verbatim
initialize registerTraceClass `lentil.debug
