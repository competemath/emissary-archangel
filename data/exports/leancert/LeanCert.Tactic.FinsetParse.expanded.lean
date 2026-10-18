/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Meta.Numeral


-- @@ L9-15 verbatim
/-!
# Finset Parsing Utilities

Shared meta-level parsers for finite-sum tactics. This module intentionally stays
lightweight: it parses elaborated `Finset` expressions into lists of natural
indices, but does not import the finite-sum engines.
-/


-- @@ L17-17 verbatim
open Lean Meta


-- @@ L19-19 verbatim
namespace LeanCert.Tactic


-- @@ L21-23 verbatim
/-- Deterministic list representation for extracted finite sets. -/
def normalizeNatIndices (xs : List Nat) : List Nat :=
  xs.eraseDups.mergeSort (· < ·)


-- @@ L25-27 verbatim
/-- Try to extract a natural-number literal from an elaborated expression. -/
def extractNatLit (e : Lean.Expr) : MetaM (Option Nat) :=
  LeanCert.Meta.Numeral.toNat? e


-- @@ L29-36 verbatim
/-- Extract `(Finset, body)` from `Finset.sum S f`. -/
def extractFinsetSum (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Finset.sum && args.size ≥ 5 then
    some (args[3]!, args[4]!)
  else
    none


-- @@ L38-52 verbatim
/-- Extract `(a, b, f)` from `Finset.sum (Finset.Icc a b) f`. -/
def extractFinsetIccSum (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Finset.sum && args.size ≥ 5 then
    let s := args[3]!
    let f := args[4]!
    let sfn := s.getAppFn
    let sargs := s.getAppArgs
    if sfn.isConstOf ``Finset.Icc && sargs.size ≥ 5 then
      some (sargs[3]!, sargs[4]!, f)
    else
      none
  else
    none


-- @@ L54-77 verbatim
/-- Recursively extract elements from nested insert/singleton/empty Finset expressions. -/
partial def tryExtractExplicitFinset (e : Lean.Expr) : MetaM (Option (List Nat)) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Insert.insert && args.size ≥ 5 then
    if let some n := ← extractNatLit args[3]! then
      if let some rest := ← tryExtractExplicitFinset args[4]! then
        return some (n :: rest)
    return none
  if fn.isConstOf ``Finset.cons && args.size ≥ 4 then
    if let some n := ← extractNatLit args[1]! then
      if let some rest := ← tryExtractExplicitFinset args[2]! then
        return some (n :: rest)
    return none
  if fn.isConstOf ``Singleton.singleton && args.size ≥ 4 then
    if let some n := ← extractNatLit args[3]! then
      return some [n]
    return none
  if fn.isConstOf ``EmptyCollection.emptyCollection then
    return some []
  let e' ← whnf e
  if e' != e then
    return ← tryExtractExplicitFinset e'
  return none


-- @@ L79-107 verbatim
/-- Extract Nat elements from a Finset expression.
    Supports `Icc`, `Ico`, `Ioc`, `Ioo`, `range`, and explicit finite sets. -/
def extractFinsetElements (finsetExpr : Lean.Expr) : MetaM (Option (List Nat)) := do
  let sfn := finsetExpr.getAppFn
  let sargs := finsetExpr.getAppArgs
  if sfn.isConstOf ``Finset.Icc && sargs.size ≥ 5 then
    if let (some a, some b) := (← extractNatLit sargs[3]!, ← extractNatLit sargs[4]!) then
      return some (List.range' a (b + 1 - a))
    return none
  if sfn.isConstOf ``Finset.Ico && sargs.size ≥ 5 then
    if let (some a, some b) := (← extractNatLit sargs[3]!, ← extractNatLit sargs[4]!) then
      return some (List.range' a (b - a))
    return none
  if sfn.isConstOf ``Finset.Ioc && sargs.size ≥ 5 then
    if let (some a, some b) := (← extractNatLit sargs[3]!, ← extractNatLit sargs[4]!) then
      return some (List.range' (a + 1) (b - a))
    return none
  if sfn.isConstOf ``Finset.Ioo && sargs.size ≥ 5 then
    if let (some a, some b) := (← extractNatLit sargs[3]!, ← extractNatLit sargs[4]!) then
      if b > a + 1 then
        return some (List.range' (a + 1) (b - a - 1))
      else
        return some []
    return none
  if sfn.isConstOf ``Finset.range && sargs.size ≥ 1 then
    if let some n := ← extractNatLit sargs[0]! then
      return some (List.range n)
    return none
  return (← tryExtractExplicitFinset finsetExpr).map normalizeNatIndices


-- @@ L109-109 verbatim
end LeanCert.Tactic
